/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::{Context, ContextX, ErasureInfo};
use crate::external::{CrateItems, GeneralItemId, VerifOrExternal};
use crate::query::PreCrate;
use crate::reveal_hide::handle_reveal_hide;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{def_id_to_vir_path_option, mk_visibility};
use crate::rust_to_vir_func::{
    CheckItemFnEither, FunctionOrConstInfo, check_foreign_item_fn, check_item_fn,
};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::{err_span, err_span_vec};
use crate::verus_items::{self, VerusItem};
use crate::{unsupported_err, unsupported_err_vec, unsupported_err_vec_unless};
use renumber::{LOCAL_ID_TAG, Renumber, local_id_counts};
use rustc_data_structures::sync::{DynSend, DynSync, IntoDynSyncSend};
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

mod renumber;

use rustc_ast::IsAuto;
use rustc_hir::def::DefKind;
use rustc_hir::{
    ConstItemRhs, ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId,
    ItemKind, Mutability,
};

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{CrateId, Fun, FunX, FunctionKind, Krate, KrateX, Path, VirErr};
use vir::context::{WarningConfig, WarningCtx};

pub(crate) struct State {
    pub(crate) external_info: ExternalInfo,
    pub(crate) fun_warn_configs: HashMap<Fun, WarningConfig>,
    /// Module-level `broadcast use` directives, retained in item order.
    pub(crate) module_reveals: Vec<(Path, rustc_span::Span, vir::ast::ModuleReveals)>,
}

impl State {
    /// Creates empty item-local outputs with the shared extension map.
    fn for_item(external_trait_extension_impl_map: &HashMap<Path, Path>) -> State {
        let mut external_info = ExternalInfo::new();
        external_info.external_trait_extension_impl_map = external_trait_extension_impl_map.clone();
        State { external_info, fun_warn_configs: HashMap::new(), module_reveals: Vec::new() }
    }

    pub(crate) fn insert_fun_warn_config<'tcx>(
        &mut self,
        ctxt: &Context<'tcx>,
        name: &Fun,
        id: rustc_span::def_id::DefId,
    ) {
        self.fun_warn_configs
            .insert(name.clone(), crate::attributes::warning_config_walk_parents(ctxt.tcx, id));
    }
}

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    vir: &mut KrateX,
    infos: &mut Vec<FunctionOrConstInfo<'tcx>>,
    module_path: &Path,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
    crate_items: &CrateItems,
) -> Result<(), Vec<VirErr>> {
    let attrs = ctxt.tcx.hir_attrs(item.hir_id());
    let vattrs = ctxt.get_verifier_attrs(attrs).map_err(|e| vec![e])?;
    if vattrs.internal_reveal_fn {
        return Ok(());
    }
    if vattrs.internal_const_body {
        return Ok(());
    }
    if vattrs.external_fn_specification && !matches!(&item.kind, ItemKind::Fn { .. }) {
        return err_span_vec(item.span, "`external_fn_specification` attribute not supported here");
    }
    if vattrs.external_type_specification && !matches!(&item.kind, ItemKind::Struct(..)) {
        if matches!(&item.kind, ItemKind::Enum(..)) {
            return err_span_vec(
                item.span,
                "`external_type_specification` proxy type should use a struct with a single field to declare the external type (even if the external type is an enum)",
            );
        } else {
            return err_span_vec(
                item.span,
                "`external_type_specification` attribute not supported here",
            );
        }
    }

    let visibility = || mk_visibility(ctxt, item.owner_id.to_def_id());

    let mut handle_const_or_static = |body_id: &rustc_hir::BodyId| {
        let def_id = body_id.hir_id.owner.to_def_id();
        if vattrs.size_of_global {
            return Ok(()); // handled earlier
        }
        if vattrs.item_broadcast_use {
            let err = || crate::util::err_span_vec(item.span, "invalid module-level broadcast use");
            let ItemKind::Const(_ident, generics, _ty, ConstItemRhs::Body(body_id)) = item.kind
            else {
                return err();
            };
            unsupported_err_vec_unless!(
                generics.params.len() == 0 && generics.predicates.len() == 0,
                item.span,
                "const generics with broadcast"
            );
            let _def_id = body_id.hir_id.owner.to_def_id();

            let body = crate::rust_to_vir_func::find_body(ctxt, &body_id);

            let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
                return err();
            };

            let funs = block
                .stmts
                .iter()
                .map(|stmt| {
                    let err = || {
                        crate::util::err_span_vec(item.span, "invalid module-level broadcast use")
                    };

                    let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
                        return err();
                    };

                    let rustc_hir::ExprKind::Call(fun_target, args) = expr.kind else {
                        return err();
                    };

                    let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, fun_path)) =
                        &fun_target.kind
                    else {
                        return err();
                    };

                    let Some(VerusItem::Directive(verus_items::DirectiveItem::RevealHide)) =
                        ctxt.get_verus_item(fun_path.res.def_id())
                    else {
                        return err();
                    };

                    let args: Vec<_> = args.iter().collect();

                    let crate::reveal_hide::RevealHideResult::RevealItem(fun) = handle_reveal_hide(
                        ctxt,
                        expr,
                        args.len(),
                        &args,
                        ctxt.tcx,
                        None::<fn(vir::ast::ExprX) -> Result<vir::ast::Expr, VirErr>>,
                    )
                    .map_err(|e| vec![e])?
                    else {
                        panic!("handle_reveal_hide must return a RevealItem");
                    };

                    Ok(fun)
                })
                .collect::<Result<Vec<_>, _>>()?;

            // Merged into the module in crate-item order.
            state.module_reveals.push((
                module_path.clone(),
                item.span,
                ctxt.spanned_new(item.span, funs),
            ));

            return Ok(());
        }
        if vattrs.structural_const_wrapper {
            ctxt.erasure_info
                .borrow_mut()
                .ignored_functions
                .push((item.owner_id.to_def_id(), item.span.data()));
            return Ok(());
        }

        let mid_ty = ctxt.tcx.type_of(def_id).skip_binder();
        let vir_ty = ctxt.mid_ty_to_vir(def_id, item.span, &mid_ty, None).map_err(|e| vec![e])?;

        crate::rust_to_vir_func::check_item_const_or_static(
            ctxt,
            state,
            &mut *infos,
            item.span,
            item.owner_id.to_def_id(),
            visibility(),
            module_path,
            ctxt.tcx.hir_attrs(item.hir_id()),
            &vir_ty,
            body_id,
            matches!(item.kind, ItemKind::Static(_, _, _, _)),
            None,
        )
        .map_err(|e| vec![e])?;

        Ok(())
    };

    match &item.kind {
        ItemKind::Fn { sig, generics, body: body_id, .. } => {
            // let _ =
            //     check_fn_opaque_ty(ctxt, &mut vir.opaque_types, &item.owner_id.to_def_id()).map_err(|e| vec![e])?;
            check_item_fn(
                ctxt,
                state,
                &mut *infos,
                Some(&mut vir.reveal_groups),
                item.owner_id.to_def_id(),
                FunctionKind::Static,
                visibility(),
                module_path,
                ctxt.tcx.hir_attrs(item.hir_id()),
                crate::rust_to_vir_func::FnOrConstSig::sig(sig),
                None,
                generics,
                CheckItemFnEither::BodyId(body_id),
                None,
                None,
                None,
                &mut vir.opaque_types,
            )
            .map_err(|e| vec![e])?;
        }
        ItemKind::Use { .. } => {}
        ItemKind::ExternCrate { .. } => {}
        ItemKind::Mod { .. } => {}
        ItemKind::ForeignMod { .. } => {}
        ItemKind::Struct(_ident, generics, variant_data) => {
            // TODO use rustc_middle info here? if sufficient, it may allow for a single code path
            // for definitions of the local crate and imported crates
            // let adt_def = tcx.adt_def(item.def_id);
            //
            // UPDATE: We now use _some_ rustc_middle info with the adt_def, which we
            // use to get rustc_middle types. However, we don't exclusively use
            // rustc_middle; in fact, we still rely on attributes which we can only
            // get from the HIR data.

            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_struct(
                ctxt,
                vir,
                module_path,
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir_attrs(item.hir_id()),
                variant_data,
                generics,
                adt_def,
            )
            .map_err(|e| vec![e])?;
        }
        ItemKind::Enum(_ident, generics, enum_def) => {
            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            // TODO use rustc_middle? see `Struct` case
            check_item_enum(
                ctxt,
                vir,
                module_path,
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir_attrs(item.hir_id()),
                enum_def,
                generics,
                adt_def,
            )
            .map_err(|e| vec![e])?;
        }
        ItemKind::Union(_ident, generics, variant_data) => {
            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_union(
                ctxt,
                vir,
                module_path,
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir_attrs(item.hir_id()),
                variant_data,
                generics,
                adt_def,
            )
            .map_err(|e| vec![e])?;
        }
        ItemKind::Impl(impll) => {
            crate::rust_to_vir_impl::translate_impl(
                ctxt,
                state,
                vir,
                infos,
                item,
                impll,
                module_path.clone(),
                crate_items,
                attrs,
            )?;
        }
        ItemKind::Const(_ident, generics, _ty, ConstItemRhs::Body(body_id)) => {
            unsupported_err_vec_unless!(
                generics.params.len() == 0 && generics.predicates.len() == 0,
                item.span,
                "const generics"
            );
            handle_const_or_static(body_id)?;
        }
        ItemKind::Static(Mutability::Not, _ident, _ty, body_id) => {
            handle_const_or_static(body_id)?;
        }
        ItemKind::Static(Mutability::Mut, _ident, _ty, _body_id) => {
            unsupported_err_vec!(item.span, "static mut");
        }
        ItemKind::Macro(_, _, _) => {}
        ItemKind::Trait {
            constness: _,
            is_auto: IsAuto::No,
            safety,
            ident: _,
            generics: trait_generics,
            bounds: _,
            items: trait_items,
            impl_restriction: _,
        } => {
            let trait_def_id = item.owner_id.to_def_id();
            crate::rust_to_vir_trait::translate_trait(
                ctxt,
                state,
                vir,
                &mut *infos,
                item.span,
                trait_def_id,
                visibility(),
                module_path,
                trait_generics,
                trait_items,
                &vattrs,
                crate_items,
                *safety,
            )
            .map_err(|e| vec![e])?;
        }
        ItemKind::TyAlias(_ident, _ty, _generics) => {
            // type alias (like lines of the form `type X = ...;`
            // Nothing to do here - we can rely on Rust's type resolution to handle these
        }
        ItemKind::GlobalAsm { .. } =>
        //TODO(utaal): add a crate-level attribute to enable global_asm
        {
            return Ok(());
        }
        _ => {
            unsupported_err_vec!(item.span, "unsupported item", item);
        }
    }
    Ok(())
}

fn check_foreign_item<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    infos: &mut Vec<FunctionOrConstInfo<'tcx>>,
    _id: &ForeignItemId,
    item: &'tcx ForeignItem<'tcx>,
) -> Result<(), VirErr> {
    match &item.kind {
        ForeignItemKind::Fn(rustc_hir::FnSig { decl, .. }, ident_opts, generics) => {
            let idents = ident_opts.iter().flatten().collect::<Vec<_>>();
            check_foreign_item_fn(
                ctxt,
                state,
                infos,
                item.owner_id.to_def_id(),
                item.span,
                mk_visibility(ctxt, item.owner_id.to_def_id()),
                ctxt.tcx.hir_attrs(item.hir_id()),
                decl,
                idents.as_slice(),
                generics,
            )?;
        }
        _ => {
            unsupported_err!(item.span, "unsupported foreign item", item);
        }
    }
    Ok(())
}

/// Translate anonymous constants through executable VIR bodies for mode checking.
fn check_anon_consts<'tcx>(
    ctxt: &Context<'tcx>,
    state: &mut State,
    infos: &mut Vec<FunctionOrConstInfo<'tcx>>,
    crate_items: &CrateItems,
) -> Result<(), Vec<VirErr>> {
    let tcx = ctxt.tcx;
    for id in tcx.hir_body_owners() {
        if !matches!(tcx.def_kind(id), DefKind::AnonConst) {
            continue;
        }
        // Integer-literal discriminants cannot refer to ghost code,
        // and may intentionally wrap (e.g., `A = 255` under `#[repr(i8)]`).
        let body = tcx.hir_body_owned_by(id);
        if tcx.opt_parent(id.to_def_id()).is_some_and(|p| tcx.def_kind(p) == DefKind::Variant) {
            let mut value = body.value;
            if let rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Neg, e) = value.kind {
                value = e;
            }
            if matches!(value.kind, rustc_hir::ExprKind::Lit(_)) {
                continue;
            }
        }
        // Only check anonymous constants owned by verified items.
        // External code is trusted and is not mode-checked.
        // The erased copy that verus! generates for each const and const fn is external,
        // but its anonymous constants also appear in the unerased proxy, which is checked here.
        let mut owner = tcx.opt_parent(id.to_def_id());
        let module_path = loop {
            let Some(owner_id) = owner else { break None };
            if let Some(local) = owner_id.as_local() {
                if let Some(verif) = crate_items.map.get(&rustc_hir::OwnerId { def_id: local }) {
                    break match verif {
                        VerifOrExternal::VerusAware { module_path, external_body, .. } => {
                            // external_body trusts only the body of a function or const;
                            // its signature is still checked.
                            let in_body = || {
                                tcx.hir_maybe_body_owned_by(local).is_none_or(|b| {
                                    tcx.hir_parent_id_iter(tcx.local_def_id_to_hir_id(id))
                                        .any(|p| p == b.value.hir_id)
                                })
                            };
                            if *external_body && in_body() {
                                None
                            } else {
                                Some(module_path.clone())
                            }
                        }
                        _ => None,
                    };
                }
            }
            owner = tcx.opt_parent(owner_id);
        };
        let Some(module_path) = module_path else {
            continue;
        };
        let span = body.value.span;
        let mid_typ = tcx.type_of(id).skip_binder();
        let typ = ctxt.mid_ty_to_vir(id.to_def_id(), span, &mid_typ, None).map_err(|e| vec![e])?;
        crate::rust_to_vir_func::check_item_const_or_static(
            ctxt,
            state,
            infos,
            span,
            id.to_def_id(),
            vir::ast::Visibility { restricted_to: Some(module_path.clone()) },
            &module_path,
            &[],
            &typ,
            &body.id(),
            false,
            None,
        )
        .map_err(|e| vec![e])?;
    }
    Ok(())
}

pub(crate) fn get_root_module_path<'tcx>(ctxt: &ContextX<'tcx>) -> Path {
    ctxt.def_id_to_vir_path(rustc_hir::CRATE_OWNER_ID.to_def_id())
}

/// The code emitted by the Verus macros refers to these crates by absolute paths
/// (e.g., `::core::cfg!`, `::vstd::prelude`), so an `extern crate` item must not
/// make these names refer to a different crate.
const RESERVED_EXTERN_CRATE_NAMES: &[&str] =
    &["core", "vstd", "verus_builtin", "verus_builtin_macros"];

fn check_extern_crate_alias<'tcx>(item: &'tcx Item<'tcx>) -> Result<(), VirErr> {
    if let ItemKind::ExternCrate(Some(orig_name), ident) = &item.kind {
        let alias = ident.name.as_str();
        if RESERVED_EXTERN_CRATE_NAMES.contains(&alias) && orig_name.as_str() != alias {
            return err_span(
                item.span,
                format!("Verus does not support renaming a crate to `{alias}` with `extern crate`"),
            );
        }
    }
    Ok(())
}

/// Ordered outputs from one crate item.
struct ItemOutput<'tcx> {
    vir: KrateX,
    state: State,
    infos: Vec<FunctionOrConstInfo<'tcx>>,
    erasure_info: ErasureInfo,
    diagnostics: Vec<vir::ast::VirErrAs>,
    errors: Vec<VirErr>,
    /// Item-local next span and read-kind IDs.
    next_ids: (u64, u64),
}

/// Translates one crate item into item-local outputs.
fn translate_crate_item<'tcx>(
    ctxt: &ContextX<'tcx>,
    external_trait_extension_impl_map: &HashMap<Path, Path>,
    crate_items: &CrateItems,
    i: usize,
    local_ids: Option<(u64, u64)>,
) -> ItemOutput<'tcx> {
    let ctxt: Context<'tcx> = Rc::new(ctxt.fork_for_item(local_ids));
    let mut state = State::for_item(external_trait_extension_impl_map);
    let mut vir: KrateX = KrateX {
        functions: Vec::new(),
        reveal_groups: Vec::new(),
        datatypes: Vec::new(),
        opaque_types: Vec::new(),
        traits: Vec::new(),
        trait_impls: Vec::new(),
        assoc_type_impls: Vec::new(),
        modules: Vec::new(),
        external_fns: Vec::new(),
        external_types: Vec::new(),
        path_as_rust_names: Vec::new(),
        arch: vir::ast::Arch { word_bits: vir::ast::ArchWordBits::Either32Or64 },
    };
    let mut infos: Vec<FunctionOrConstInfo<'tcx>> = Vec::new();
    let mut errors = vec![];
    let crate_item = &crate_items.items[i];
    match &crate_item.verif {
        VerifOrExternal::VerusAware {
            module_path,
            const_directive: _,
            external_body: _,
            external_fn_specification: _,
        } => {
            match crate_item.id {
                GeneralItemId::ItemId(item_id) => {
                    let item = ctxt.tcx.hir_item(item_id);
                    if let Err(errs) = check_item(
                        &ctxt,
                        &mut state,
                        &mut vir,
                        &mut infos,
                        &module_path,
                        &item_id,
                        item,
                        &crate_items,
                    ) {
                        errors.extend(errs);
                    }
                }
                GeneralItemId::ForeignItemId(foreign_item_id) => {
                    let foreign_item = ctxt.tcx.hir_foreign_item(foreign_item_id);
                    if let Err(err) = check_foreign_item(
                        &ctxt,
                        &mut state,
                        &mut infos,
                        &foreign_item_id,
                        foreign_item,
                    ) {
                        errors.push(err);
                    }
                }
                GeneralItemId::ImplItemId(_impl_item_id) => {
                    // Processed as part of the impl (which is an Item)
                }
                GeneralItemId::TraitItemId(_trait_item_id) => {
                    // Processed as part of the impl (which is an Item)
                }
            }
        }
        VerifOrExternal::External { path: Some(my_path), path_string: _, explicit: _ } => {
            // If possible, track this item in the VIR Krate for diagnostic purposes
            let (is_fn, is_datatype) = match crate_item.id {
                GeneralItemId::ItemId(item_id) => {
                    let i = ctxt.tcx.hir_item(item_id);
                    match i.kind {
                        ItemKind::Fn { .. } | ItemKind::Const(..) => (true, false),
                        ItemKind::Struct(..) | ItemKind::Enum(..) | ItemKind::Union(..) => {
                            (false, true)
                        }
                        _ => (false, false),
                    }
                }
                GeneralItemId::ForeignItemId(foreign_item_id) => {
                    let i = ctxt.tcx.hir_foreign_item(foreign_item_id);
                    match i.kind {
                        ForeignItemKind::Fn(..) => (true, false),
                        _ => (false, false),
                    }
                }
                GeneralItemId::ImplItemId(impl_item_id) => {
                    let i = ctxt.tcx.hir_impl_item(impl_item_id);
                    match i.kind {
                        ImplItemKind::Fn(..) => (true, false),
                        _ => (false, false),
                    }
                }
                GeneralItemId::TraitItemId(_trait_item_id) => (false, false),
            };
            if is_fn {
                vir.external_fns.push(Arc::new(FunX { path: my_path.clone() }));
            }
            if is_datatype {
                vir.external_types.push(my_path.clone());
            }
        }
        VerifOrExternal::External { path: None, path_string: _, explicit: _ } => {}
    }
    let next_ids = ctxt.peek_next_ids();
    let erasure_info = std::mem::take(&mut *ctxt.erasure_info.borrow_mut());
    let diagnostics = std::mem::take(&mut *ctxt.diagnostics.lock().unwrap());
    ItemOutput { vir, state, infos, erasure_info, diagnostics, errors, next_ids }
}

/// Caps translation workers. Shared rustc interners and query caches limit scaling: on a
/// large crate at -Zthreads=16, 12 workers took about 0.98x and 16 about 1.06x the time of 8.
const MAX_PARALLEL_ITEM_JOBS: usize = 12;

/// Estimates item translation cost by the item's source length.
fn item_len<'tcx>(tcx: rustc_middle::ty::TyCtxt<'tcx>, item: &crate::external::CrateItem) -> u32 {
    let span = match (&item.verif, item.id) {
        (VerifOrExternal::VerusAware { .. }, GeneralItemId::ItemId(id)) => tcx.hir_item(id).span,
        (VerifOrExternal::VerusAware { .. }, GeneralItemId::ForeignItemId(id)) => {
            tcx.hir_foreign_item(id).span
        }
        _ => return 0,
    };
    let span = span.data();
    span.hi.0.saturating_sub(span.lo.0)
}

/// Runs `f` on every unit with up to `n_jobs` workers that claim one unit at a time,
/// costliest first, and returns the results in unit order.
///
/// A panicking unit is caught in its worker, so the other workers keep claiming units and
/// the payload is kept. Afterwards the payload of the lowest panicking unit index is
/// resumed, which is the unit serial translation would have panicked in (assuming each
/// unit panics deterministically). Units above the lowest panic seen so far are skipped, as
/// serial translation would never reach them. A `FatalErrorMarker` payload yields to the
/// lowest other payload, as in rustc's parallel guard: a wait on a query that another unit
/// poisoned by panicking raises `FatalErrorMarker`, which must not hide that unit's panic.
/// (If a unit genuinely raised `FatalErrorMarker`, a panic from an already started higher
/// unit can therefore win; either way the run fails.)
fn par_units<R: Send>(
    n_jobs: usize,
    costs: &[u32],
    f: impl Fn(usize) -> R + DynSync + DynSend,
) -> Vec<R> {
    let n = costs.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(costs[i]));
    let next = AtomicUsize::new(0);
    // Lowest unit index that has panicked so far, or `n`.
    let first_panic = AtomicUsize::new(n);
    let by_job: Vec<Vec<(usize, IntoDynSyncSend<std::thread::Result<R>>)>> =
        rustc_data_structures::sync::par_map(0..n_jobs.clamp(1, n.max(1)), |_| {
            let mut out = Vec::new();
            loop {
                let k = next.fetch_add(1, Ordering::Relaxed);
                if k >= n {
                    break;
                }
                let i = order[k];
                if i > first_panic.load(Ordering::Relaxed) {
                    continue;
                }
                let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(i)));
                if r.is_err() {
                    first_panic.fetch_min(i, Ordering::Relaxed);
                }
                out.push((i, IntoDynSyncSend(r)));
            }
            out
        });
    let mut results: Vec<Option<std::thread::Result<R>>> = (0..n).map(|_| None).collect();
    for (i, r) in by_job.into_iter().flatten() {
        results[i] = Some(r.0);
    }
    // Every unit below the lowest panic ran: `first_panic` only decreases, so it never
    // skipped them.
    let mut outputs = Vec::with_capacity(n);
    let mut fatal = None;
    for (i, r) in results.into_iter().enumerate() {
        match r {
            Some(Err(payload)) if payload.is::<rustc_span::fatal_error::FatalErrorMarker>() => {
                fatal.get_or_insert(payload);
            }
            Some(Err(payload)) => std::panic::resume_unwind(payload),
            Some(Ok(r)) => outputs.push(r),
            None if fatal.is_some() => {}
            None => unreachable!("unit {i} skipped below the lowest panicking unit"),
        }
    }
    if let Some(payload) = fatal {
        std::panic::resume_unwind(payload);
    }
    outputs
}

/// Assigns consecutive crate-wide ID ranges to forks in unit order and advances the shared
/// counters past them.
fn assign_id_ranges<'tcx>(
    ctxt: &ContextX<'tcx>,
    next_ids: impl Iterator<Item = (u64, u64)>,
) -> Vec<Renumber> {
    let first = ctxt.peek_next_ids();
    let (mut span_id, mut read_kind_id) = first;
    let renumbers = next_ids
        .map(|ids| {
            let counts = local_id_counts(ids);
            let renumber = Renumber::new((span_id, read_kind_id), counts);
            span_id += counts.0;
            read_kind_id += counts.1;
            renumber
        })
        .collect();
    ctxt.advance_ids(span_id - first.0, read_kind_id - first.1);
    renumbers
}

/// Renumbers each output with its range, in parallel, preserving order.
fn par_renumber<T: Send>(
    outputs: Vec<T>,
    renumbers: Vec<Renumber>,
    f: impl Fn(&mut T, Renumber) + DynSync + DynSend,
) -> Vec<T> {
    let units = outputs.into_iter().zip(renumbers).map(IntoDynSyncSend);
    let outputs: Vec<IntoDynSyncSend<T>> =
        rustc_data_structures::sync::par_map(units, |unit: IntoDynSyncSend<(T, Renumber)>| {
            let (mut out, renumber) = unit.0;
            f(&mut out, renumber);
            IntoDynSyncSend(out)
        });
    outputs.into_iter().map(|out| out.0).collect()
}

fn renumber_item_output(out: &mut ItemOutput<'_>, r: Renumber) {
    r.krate(&mut out.vir);
    out.state.module_reveals.iter_mut().for_each(|(_, _, reveals)| r.module_reveals(reveals));
    for info in out.infos.iter_mut() {
        let (stub, autospec, function_full) = info.parts_mut();
        r.function_stub(stub);
        autospec.into_iter().for_each(|stub| r.function_stub(stub));
        function_full.into_iter().for_each(|function| r.function(function));
    }
    r.erasure_info(&mut out.erasure_info);
    out.diagnostics.iter_mut().for_each(|d| r.message_as(d));
    out.errors.iter_mut().for_each(|e| r.message(e));
}

/// Outputs of finishing one function or const, which the serial pipeline would have added to
/// the shared context (erasure info, diagnostics) or returned (functions, error).
pub(crate) struct FinishOutput {
    pub(crate) functions: Vec<vir::ast::Function>,
    pub(crate) erasure_info: ErasureInfo,
    pub(crate) diagnostics: Vec<vir::ast::VirErrAs>,
    pub(crate) error: Option<VirErr>,
    /// Fork-local next span and read-kind IDs.
    next_ids: (u64, u64),
}

/// Finishes one function or const in a fork of `ctxt` that keeps its outputs separate.
/// With `local_ids`, the fork allocates tagged IDs; otherwise it shares `ctxt`'s counters.
fn finish_info<'tcx>(
    ctxt: &ContextX<'tcx>,
    info: &FunctionOrConstInfo<'tcx>,
    local_ids: Option<(u64, u64)>,
) -> FinishOutput {
    let ctxt: Context<'tcx> = Rc::new(ctxt.fork_for_item(local_ids));
    let mut functions = Vec::new();
    let error = crate::rust_to_vir_func::finish_item(&ctxt, info, &mut functions).err();
    let erasure_info = std::mem::take(&mut *ctxt.erasure_info.borrow_mut());
    let diagnostics = std::mem::take(&mut *ctxt.diagnostics.lock().unwrap());
    FinishOutput { functions, erasure_info, diagnostics, error, next_ids: ctxt.peek_next_ids() }
}

fn renumber_finish_output(out: &mut FinishOutput, r: Renumber) {
    out.functions.iter_mut().for_each(|f| r.function(f));
    r.erasure_info(&mut out.erasure_info);
    out.diagnostics.iter_mut().for_each(|d| r.message_as(d));
    out.error.iter_mut().for_each(|e| r.message(e));
}

/// Finishes every function or const of `infos` without reporting anything, with the IDs that
/// finishing them one at a time in `infos` order on `ctxt` would assign, and returns the
/// outputs in `infos` order. The caller replays each output where the serial pipeline would
/// have finished that item. With rustc's parallel mode the items are finished in parallel
/// forks with tagged IDs, which are then renumbered; otherwise they are finished in order.
///
/// If finishing an item panics, only the outputs of the items before it are returned (none in
/// parallel mode); the caller finishes the remaining items serially, which reproduces the
/// panic where the serial pipeline would raise it.
pub(crate) fn prefetch_finish_infos<'tcx>(
    ctxt: &ContextX<'tcx>,
    infos: &[Arc<FunctionOrConstInfo<'tcx>>],
) -> Vec<FinishOutput> {
    let tcx = ctxt.tcx;
    if !rustc_data_structures::sync::is_dyn_thread_safe() {
        // Shared counters: IDs are consumed in `infos` order, as serially.
        let mut outputs = Vec::with_capacity(infos.len());
        for info in infos {
            let finish = || finish_info(ctxt, info, None);
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(finish)) {
                Ok(out) => outputs.push(out),
                Err(_) => break,
            }
        }
        return outputs;
    }
    let n_jobs = tcx.sess.opts.jobs.frontend.map_or(1, |n| n.get()).min(MAX_PARALLEL_ITEM_JOBS);
    let costs: Vec<u32> = infos.iter().map(|info| info.body_len(tcx)).collect();
    let tagged = Some((LOCAL_ID_TAG, LOCAL_ID_TAG));
    let shared = IntoDynSyncSend(infos);
    let Ok(outputs) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        par_units(n_jobs, &costs, |i| finish_info(ctxt, &shared[i], tagged))
    })) else {
        // No IDs were consumed.
        return Vec::new();
    };
    let renumbers = assign_id_ranges(ctxt, outputs.iter().map(|out| out.next_ids));
    let outputs = par_renumber(outputs, renumbers, renumber_finish_output);
    if cfg!(debug_assertions) {
        for out in outputs.iter() {
            renumber::assert_untagged("finished functions", &out.functions);
            renumber::assert_untagged_erasure_info(&out.erasure_info);
            for d in out.diagnostics.iter() {
                let (vir::ast::VirErrAs::Warning(m) | vir::ast::VirErrAs::Note(m)) = d;
                renumber::assert_untagged("diagnostic", m);
            }
            renumber::assert_untagged("error", &out.error);
        }
    }
    outputs
}

/// Checks that no tagged ID survived renumbering in the merged outputs.
fn assert_untagged_outputs<'tcx>(
    ctxt: &ContextX<'tcx>,
    vir: &KrateX,
    infos: &[FunctionOrConstInfo<'tcx>],
    errors: &[VirErr],
) {
    renumber::assert_untagged("krate", vir);
    for info in infos {
        renumber::assert_untagged("function stub", &info.iter_stubs().collect::<Vec<_>>());
        if let Some(function) = info.foreign_function_full() {
            renumber::assert_untagged("foreign function", function);
        }
    }
    renumber::assert_untagged_erasure_info(&ctxt.erasure_info.borrow());
    for d in ctxt.diagnostics.lock().unwrap().iter() {
        let (vir::ast::VirErrAs::Warning(m) | vir::ast::VirErrAs::Note(m)) = d;
        renumber::assert_untagged("diagnostic", m);
    }
    renumber::assert_untagged("errors", errors);
}

pub(crate) fn crate_to_vir<'a, 'tcx>(
    mut ctxtx: ContextX<'tcx>,
    imported: &Vec<Krate>,
    crate_items: &CrateItems,
) -> Result<PreCrate<'tcx>, Vec<VirErr>> {
    let mut vir: KrateX = KrateX {
        functions: Vec::new(),
        reveal_groups: Vec::new(),
        datatypes: Vec::new(),
        opaque_types: Vec::new(),
        traits: Vec::new(),
        trait_impls: Vec::new(),
        assoc_type_impls: Vec::new(),
        modules: Vec::new(),
        external_fns: Vec::new(),
        external_types: Vec::new(),
        path_as_rust_names: Vec::new(),
        arch: vir::ast::Arch { word_bits: vir::ast::ArchWordBits::Either32Or64 },
    };
    let mut infos: Vec<FunctionOrConstInfo> = Vec::new();

    let tcx = ctxtx.tcx;

    let mut external_info = ExternalInfo::new();
    // Sized is fundamental enough that we always want it even with no-vstd
    external_info.trait_id_set.insert(tcx.lang_items().sized_trait().expect("lang_item"));
    // TODO: remove the following when we have full support for auto traits:
    external_info.trait_id_set.insert(tcx.lang_items().unpin_trait().expect("lang_item"));
    external_info.trait_id_set.insert(tcx.lang_items().sync_trait().expect("lang_item"));
    external_info
        .trait_id_set
        .insert(tcx.get_diagnostic_item(rustc_span::sym::Send).expect("send"));

    let fun_warn_configs = HashMap::new();
    let mut state = State { external_info, fun_warn_configs, module_reveals: Vec::new() };

    let mut errors = vec![];

    let mut typs_sizes_set: HashMap<TypIgnoreImplPaths, u128> = HashMap::new();
    for item in crate::util::iter_crate_free_items(tcx) {
        if let Err(err) = check_extern_crate_alias(item) {
            errors.push(err);
        }
        if let Err(err) =
            crate::rust_to_vir_global::process_const_early(&mut ctxtx, &mut typs_sizes_set, item)
        {
            errors.push(err);
        }
    }

    if errors.len() > 0 {
        return Err(errors);
    }

    let arch_word_bits = ctxtx.arch_word_bits.unwrap_or(vir::ast::ArchWordBits::Either32Or64);
    ctxtx.arch_word_bits = Some(arch_word_bits);
    vir.arch.word_bits = arch_word_bits;
    let ctxt = Rc::new(ctxtx);

    // Find all modules that contain at least 1 item of interest
    let mut used_modules = HashSet::<Path>::new();
    for crate_item in crate_items.items.iter() {
        match &crate_item.verif {
            VerifOrExternal::VerusAware {
                module_path,
                const_directive: _,
                external_body: _,
                external_fn_specification: _,
            } => {
                used_modules.insert(module_path.clone());
            }
            _ => {}
        }
    }
    // Insert those modules into vir.modules
    let root_module_path = get_root_module_path(&ctxt);
    if used_modules.contains(&root_module_path) {
        let owner = ctxt.tcx.hir_owner_node(rustc_hir::CRATE_OWNER_ID);
        vir.modules.push(ctxt.spanned_new(
            owner.span(),
            vir::ast::ModuleX { path: root_module_path.clone(), reveals: None },
        ));
    }
    for item in crate::util::iter_crate_free_items(tcx) {
        if let Item { kind: ItemKind::Mod(_ident, _module), owner_id, .. } = item {
            let path =
                def_id_to_vir_path_option(ctxt.tcx, Some(&ctxt.verus_items), owner_id.to_def_id());
            if let Some(path) = path {
                if used_modules.contains(&path) {
                    vir.modules.push(ctxt.spanned_new(
                        item.span,
                        vir::ast::ModuleX { path: path.clone(), reveals: None },
                    ));
                }
            }
        }
    }

    crate::rust_to_vir_trait::make_external_trait_extension_impl_map(
        &ctxt,
        &mut state.external_info,
        imported,
        &crate_items,
    )
    .map_err(|e| vec![e])?;

    // Item-local outputs are merged in crate order. Parallel forks allocate tagged IDs, which
    // are renumbered into the ranges that serial translation would have assigned.
    let n_items = crate_items.items.len();
    let ext_map: &HashMap<Path, Path> = &state.external_info.external_trait_extension_impl_map;
    let parallel = rustc_data_structures::sync::is_dyn_thread_safe();
    let n_jobs = tcx.sess.opts.jobs.frontend.map_or(1, |n| n.get()).min(MAX_PARALLEL_ITEM_JOBS);
    let outputs: Vec<ItemOutput<'tcx>> = if parallel {
        let ctxt_ref: &ContextX<'tcx> = &ctxt;
        let costs: Vec<u32> = crate_items.items.iter().map(|item| item_len(tcx, item)).collect();
        let tagged = Some((LOCAL_ID_TAG, LOCAL_ID_TAG));
        let outputs = par_units(n_jobs, &costs, |i| {
            translate_crate_item(ctxt_ref, ext_map, crate_items, i, tagged)
        });
        let renumbers = assign_id_ranges(&ctxt, outputs.iter().map(|out| out.next_ids));
        par_renumber(outputs, renumbers, renumber_item_output)
    } else {
        (0..n_items).map(|i| translate_crate_item(&ctxt, ext_map, crate_items, i, None)).collect()
    };

    {
        let mut erasure_info = ctxt.erasure_info.borrow_mut();
        let mut diagnostics = ctxt.diagnostics.lock().unwrap();
        for out in outputs {
            let ItemOutput {
                vir: mut item_vir,
                state: item_state,
                infos: mut item_infos,
                erasure_info: mut item_erasure_info,
                diagnostics: item_diagnostics,
                errors: item_errors,
                next_ids: _,
            } = out;
            for (module_path, span, reveals) in item_state.module_reveals {
                let module = vir
                    .modules
                    .iter_mut()
                    .find(|m| m.x.path == module_path)
                    .expect("cannot find current module");
                let module_reveals = &mut Arc::make_mut(module).x.reveals;
                if module_reveals.is_some() {
                    errors.push(crate::util::err_span_bare(
                        span,
                        "only one module-level `broadcast use` allowed for each module",
                    ));
                } else {
                    *module_reveals = Some(reveals);
                }
            }
            errors.extend(item_errors);
            vir.functions.append(&mut item_vir.functions);
            vir.reveal_groups.append(&mut item_vir.reveal_groups);
            vir.datatypes.append(&mut item_vir.datatypes);
            vir.opaque_types.append(&mut item_vir.opaque_types);
            vir.traits.append(&mut item_vir.traits);
            vir.trait_impls.append(&mut item_vir.trait_impls);
            vir.assoc_type_impls.append(&mut item_vir.assoc_type_impls);
            vir.external_fns.append(&mut item_vir.external_fns);
            vir.external_types.append(&mut item_vir.external_types);
            infos.append(&mut item_infos);
            assert!(item_vir.modules.is_empty());
            let ExternalInfo {
                local_trait_ids,
                internal_trait_impls,
                external_fn_specification_trait_method_impls,
                ..
            } = item_state.external_info;
            state.external_info.local_trait_ids.extend(local_trait_ids);
            state.external_info.internal_trait_impls.extend(internal_trait_impls);
            state
                .external_info
                .external_fn_specification_trait_method_impls
                .extend(external_fn_specification_trait_method_impls);
            state.fun_warn_configs.extend(item_state.fun_warn_configs);
            erasure_info.append(&mut item_erasure_info);
            diagnostics.extend(item_diagnostics);
        }
    }

    if parallel && cfg!(debug_assertions) {
        assert_untagged_outputs(&ctxt, &vir, &infos, &errors);
    }
    if errors.len() > 0 {
        return Err(errors);
    }

    vir.path_as_rust_names = vir::ast_util::get_path_as_rust_names_for_krate(&CrateId::Vstd);

    check_anon_consts(&ctxt, &mut state, &mut infos, crate_items)?;

    let function_stubs = infos.iter().flat_map(|info| info.iter_stubs()).cloned().collect();
    crate::rust_to_vir_impl::collect_external_trait_impls(
        &ctxt,
        imported,
        &mut vir,
        &mut state.external_info,
        &function_stubs,
    )
    .map_err(|e| vec![e])?;

    crate::rust_to_vir_adts::setup_type_invariants(&mut vir, &function_stubs)
        .map_err(|e| vec![e])?;

    let mut fun_warn_configs: HashMap<Fun, Option<WarningConfig>> = HashMap::new();
    for krate in imported {
        for function in &krate.functions {
            fun_warn_configs.insert(function.x.name.clone(), None);
        }
    }
    for (f, warn) in state.fun_warn_configs {
        fun_warn_configs.insert(f, Some(warn));
    }
    let warning_ctx = WarningCtx { fun_warn_configs };

    let infos = infos.into_iter().map(|info| Arc::new(info)).collect::<Vec<_>>();
    let mut fun_name_to_info = HashMap::<Fun, Arc<FunctionOrConstInfo>>::new();
    for info in infos.iter() {
        for stub in info.iter_stubs() {
            fun_name_to_info.insert(stub.x.name.clone(), info.clone());
        }
    }
    Ok(PreCrate {
        ctxt,
        warning_ctx: Arc::new(warning_ctx),
        krate_without_funs: Arc::new(vir),
        infos: infos,
        fun_name_to_info,
    })
}

#[cfg(test)]
mod tests {
    use super::par_units;
    use rustc_span::fatal_error::FatalErrorMarker;
    use std::sync::Mutex;

    #[derive(Debug, PartialEq)]
    enum Outcome {
        Unit(usize),
        Fatal,
    }

    /// `par_units` reads rustc's process-wide thread-safety mode; every test in this binary
    /// uses the parallel mode.
    fn init() {
        rustc_data_structures::sync::set_dyn_thread_safe_mode(true);
    }

    /// Runs `par_units` and returns the units in run order and the results or the resumed
    /// payload. Units in `panics` panic with their index, units in `fatal` raise
    /// `FatalErrorMarker`.
    fn run(
        n_jobs: usize,
        costs: &[u32],
        panics: &[usize],
        fatal: &[usize],
    ) -> (Vec<usize>, Result<Vec<usize>, Outcome>) {
        init();
        let ran = Mutex::new(Vec::new());
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            par_units(n_jobs, costs, |i| {
                ran.lock().unwrap().push(i);
                if panics.contains(&i) {
                    std::panic::panic_any(Outcome::Unit(i));
                }
                if fatal.contains(&i) {
                    std::panic::resume_unwind(Box::new(FatalErrorMarker));
                }
                i * 10
            })
        }));
        let r = r.map_err(|p| {
            if p.is::<FatalErrorMarker>() {
                Outcome::Fatal
            } else {
                *p.downcast::<Outcome>().expect("unit payload")
            }
        });
        (ran.into_inner().unwrap(), r.map(|v| v.iter().map(|x| x / 10).collect()))
    }

    #[test]
    fn par_units_returns_results_in_unit_order() {
        let (ran, r) = run(1, &[1, 5, 0, 3], &[], &[]);
        assert_eq!(ran, vec![1, 3, 0, 2]);
        assert_eq!(r, Ok(vec![0, 1, 2, 3]));
        assert_eq!(run(1, &[], &[], &[]), (vec![], Ok(vec![])));
        assert_eq!(run(4, &[], &[], &[]), (vec![], Ok(vec![])));
        let costs: Vec<u32> = (0..300).map(|i| (i * 37 % 101) as u32).collect();
        let (mut ran, r) = run(8, &costs, &[], &[]);
        assert_eq!(r, Ok((0..300).collect()));
        ran.sort();
        assert_eq!(ran, (0..300).collect::<Vec<_>>());
    }

    /// The lowest panicking index is resumed with its own payload even when a higher unit
    /// panicked first; units below the lowest panic all run.
    #[test]
    fn par_units_resumes_the_lowest_panicking_unit() {
        let (ran, r) = run(1, &[0, 1, 2, 3, 4], &[1, 3], &[]);
        assert_eq!(ran, vec![4, 3, 2, 1, 0]);
        assert_eq!(r, Err(Outcome::Unit(1)));
        let costs: Vec<u32> = (0..300).map(|i| (i * 37 % 101) as u32).collect();
        for _ in 0..20 {
            let (ran, r) = run(8, &costs, &[250, 41, 177, 42], &[]);
            assert_eq!(r, Err(Outcome::Unit(41)));
            assert!((0..41).all(|i| ran.contains(&i)));
        }
    }

    /// Units above a panicking unit are skipped once it has panicked.
    #[test]
    fn par_units_skips_units_above_a_panic() {
        let (ran, r) = run(1, &[4, 0, 3, 2, 1], &[0, 2], &[]);
        assert_eq!(ran, vec![0]);
        assert_eq!(r, Err(Outcome::Unit(0)));
        let (ran, r) = run(1, &[1, 4, 3, 2, 0], &[1], &[]);
        assert_eq!(ran, vec![1, 0]);
        assert_eq!(r, Err(Outcome::Unit(1)));
    }

    /// `FatalErrorMarker` yields to another unit's panic, but is resumed when it is the only
    /// kind of payload.
    #[test]
    fn par_units_prefers_a_panic_over_fatal_error_marker() {
        let (ran, r) = run(1, &[0, 1, 2, 3], &[3], &[1]);
        assert_eq!(ran, vec![3, 2, 1, 0]);
        assert_eq!(r, Err(Outcome::Unit(3)));
        let (ran, r) = run(1, &[0, 1, 2, 3], &[], &[1, 2]);
        assert_eq!(ran, vec![3, 2, 1, 0]);
        assert_eq!(r, Err(Outcome::Fatal));
        let (ran, r) = run(1, &[3, 2, 1, 0], &[3], &[1]);
        assert_eq!(ran, vec![0, 1]);
        assert_eq!(r, Err(Outcome::Fatal));
    }
}
