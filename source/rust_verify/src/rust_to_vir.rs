/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::{Context, ContextX, ErasureInfo};
use crate::external::{CrateItems, GeneralItemId, VerifOrExternal};
use crate::reveal_hide::handle_reveal_hide;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{def_id_to_vir_path_option, mk_visibility};
use crate::rust_to_vir_func::{
    CheckItemFnEither, FunctionOrConstInfo, check_foreign_item_fn, check_item_fn,
};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::err_span_vec;
use crate::verus_items::{self, VerusItem};
use crate::{unsupported_err, unsupported_err_vec, unsupported_err_vec_unless};
use rustc_data_structures::sync::IntoDynSyncSend;
use std::collections::HashSet;
use std::rc::Rc;

use rustc_ast::IsAuto;
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
    vir: &mut KrateX,
    _id: &ForeignItemId,
    item: &'tcx ForeignItem<'tcx>,
) -> Result<(), VirErr> {
    match &item.kind {
        ForeignItemKind::Fn(rustc_hir::FnSig { decl, .. }, ident_opts, generics) => {
            let idents = ident_opts.iter().flatten().collect::<Vec<_>>();
            check_foreign_item_fn(
                ctxt,
                state,
                vir,
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

pub(crate) fn get_root_module_path<'tcx>(ctxt: &ContextX<'tcx>) -> Path {
    ctxt.def_id_to_vir_path(rustc_hir::CRATE_OWNER_ID.to_def_id())
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
                        &mut vir,
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

pub fn crate_to_vir<'a, 'tcx>(
    mut ctxtx: ContextX<'tcx>,
    imported: &Vec<Krate>,
    crate_items: &CrateItems,
) -> Result<(Context<'tcx>, WarningCtx, Krate), Vec<VirErr>> {
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

    // Item-local outputs are merged in crate order. A counting pass assigns deterministic
    // span and read-kind ID ranges before the output-producing pass.
    let n_items = crate_items.items.len();
    let ext_map: &HashMap<Path, Path> = &state.external_info.external_trait_extension_impl_map;
    let outputs: Vec<ItemOutput<'tcx>> = if rustc_data_structures::sync::is_dyn_thread_safe() {
        let ctxt_ref: &ContextX<'tcx> = &ctxt;
        // Limits contention in shared translation caches.
        const MAX_PARALLEL_ITEM_JOBS: usize = 8;
        // Retains enough work units to balance uneven item costs.
        const MAX_ITEM_GROUPS: usize = 128;
        let group_size = n_items.div_ceil(MAX_ITEM_GROUPS).max(1);
        let n_groups = n_items.div_ceil(group_size);
        let n_jobs = n_groups.clamp(1, MAX_PARALLEL_ITEM_JOBS);
        let next_group = std::sync::atomic::AtomicUsize::new(0);
        let counts_by_job: Vec<Vec<(usize, (u64, u64))>> =
            rustc_data_structures::sync::par_map(0..n_jobs, |_| {
                let mut job_counts = Vec::with_capacity(n_items.div_ceil(n_jobs));
                loop {
                    let group = next_group.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if group >= n_groups {
                        break;
                    }
                    let start = group * group_size;
                    let end = (start + group_size).min(n_items);
                    for i in start..end {
                        let out =
                            translate_crate_item(ctxt_ref, ext_map, crate_items, i, Some((0, 0)));
                        job_counts.push((i, out.next_ids));
                    }
                }
                job_counts
            });
        let mut counts = vec![(0, 0); n_items];
        for job_counts in counts_by_job {
            for (i, count) in job_counts {
                counts[i] = count;
            }
        }
        let (first_span_id, first_read_kind_id) = ctxt.peek_next_ids();
        let mut first_ids: Vec<(u64, u64)> = Vec::with_capacity(n_items);
        let (mut span_id, mut read_kind_id) = (first_span_id, first_read_kind_id);
        for (span_ids, read_kind_ids) in counts {
            first_ids.push((span_id, read_kind_id));
            span_id += span_ids;
            read_kind_id += read_kind_ids;
        }
        let first_ids_ref: &Vec<(u64, u64)> = &first_ids;
        let next_group = std::sync::atomic::AtomicUsize::new(0);
        let outputs_by_job: Vec<Vec<(usize, IntoDynSyncSend<ItemOutput<'tcx>>)>> =
            rustc_data_structures::sync::par_map(0..n_jobs, |_| {
                let mut job_outputs = Vec::with_capacity(n_items.div_ceil(n_jobs));
                loop {
                    let group = next_group.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if group >= n_groups {
                        break;
                    }
                    let start = group * group_size;
                    let end = (start + group_size).min(n_items);
                    for i in start..end {
                        let out = translate_crate_item(
                            ctxt_ref,
                            ext_map,
                            crate_items,
                            i,
                            Some(first_ids_ref[i]),
                        );
                        job_outputs.push((i, IntoDynSyncSend(out)));
                    }
                }
                job_outputs
            });
        ctxt.advance_ids(span_id - first_span_id, read_kind_id - first_read_kind_id);
        let mut indexed_outputs: Vec<(usize, IntoDynSyncSend<ItemOutput<'tcx>>)> =
            outputs_by_job.into_iter().flatten().collect();
        indexed_outputs.sort_unstable_by_key(|(i, _)| *i);
        indexed_outputs.into_iter().map(|(_, out)| out.0).collect()
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

    if errors.len() > 0 {
        return Err(errors);
    }

    vir.path_as_rust_names = vir::ast_util::get_path_as_rust_names_for_krate(&CrateId::Vstd);

    for info in infos.into_iter() {
        if let Err(e) = crate::rust_to_vir_func::finish_item(&ctxt, info, &mut vir.functions) {
            errors.push(e);
        }
    }
    if errors.len() > 0 {
        return Err(errors);
    }

    crate::rust_to_vir_impl::collect_external_trait_impls(
        &ctxt,
        imported,
        &mut vir,
        &mut state.external_info,
    )
    .map_err(|e| vec![e])?;

    crate::rust_to_vir_adts::setup_type_invariants(&mut vir).map_err(|e| vec![e])?;
    vir::traits::set_krate_dyn_compatibility(imported, &mut vir);

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

    Ok((ctxt, warning_ctx, Arc::new(vir)))
}
