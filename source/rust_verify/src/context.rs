use crate::{erase::ResolvedCall, verus_items::VerusItems};
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::sync::{DynSend, DynSync, Lock, RwLock};
use rustc_hir::Attribute;
use rustc_hir::HirId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind, TypeckResults};
use rustc_mir_build_verus::verus::BodyErasure;
use rustc_span::SpanData;
use rustc_span::def_id::DefId;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::Sender;
use std::sync::{Arc, Mutex};
use vir::ast::{CrateId, Dt, Mode, Path, Pattern, Typ, TypX, VirErr};
use vir::messages::{AstId, WarningAllow};

#[derive(Default)]
pub struct ErasureInfo {
    /// Connect every PlaceX::Local, ExprX::Var, and ExprX::VarAt node to its
    /// HirId (an ExprKind::Path node that resolves to Local).
    ///
    /// Use None if there is no corresponding source node, e.g., from synthetically produced
    /// expressions.
    pub(crate) local_hir_vir_ids: Vec<(Option<HirId>, AstId)>,
    /// Connect every VIR Pattern binder onto its HirId (a PatKind::Binder)
    pub(crate) binder_hir_vir_ids: Vec<(Option<HirId>, AstId)>,
    /// Connect every non-tuple VIR Ctor onto its HirId (either a ExprKind::Struct, or a
    /// const-style constructor or call-style constructor).
    pub(crate) ctor_hir_vir_ids: Vec<(Option<HirId>, AstId)>,
    /// Details of each call in the first run's HIR.
    /// The last bool is "in ghost block?".
    /// (This is false for "boundary" calls like Ghost/Tracked
    /// though that shouldn't matter right now).
    pub(crate) resolved_calls: Vec<(HirId, SpanData, ResolvedCall, bool)>,
    /// Details of some patterns in first run's HIR
    pub(crate) resolved_pats: Vec<(SpanData, Pattern)>,
    /// Modes specified directly during rust_to_vir
    pub(crate) direct_var_modes: Vec<(HirId, Mode)>,
    /// List of function spans ignored by the verifier. These should not be erased
    pub(crate) ignored_functions: Vec<(DefId, SpanData)>,
    pub(crate) bodies: Vec<(LocalDefId, BodyErasure)>,
    pub(crate) shadow_check: Vec<HirId>,
    /// Extra nodes to erase, use this when a VIR tree gets dropped without getting to
    /// mode-checking.
    pub(crate) extra_erase_ast_ids: Vec<vir::messages::Span>,
    pub(crate) local_invariant_bodies: Vec<rustc_mir_build_verus::verus::LocalInvariantBody>,
}

impl ErasureInfo {
    /// Appends every ordered erasure output from `other`.
    pub(crate) fn append(&mut self, other: &mut ErasureInfo) {
        let ErasureInfo {
            local_hir_vir_ids,
            binder_hir_vir_ids,
            ctor_hir_vir_ids,
            resolved_calls,
            resolved_pats,
            direct_var_modes,
            ignored_functions,
            bodies,
            shadow_check,
            extra_erase_ast_ids,
            local_invariant_bodies,
        } = other;
        self.local_hir_vir_ids.append(local_hir_vir_ids);
        self.binder_hir_vir_ids.append(binder_hir_vir_ids);
        self.ctor_hir_vir_ids.append(ctor_hir_vir_ids);
        self.resolved_calls.append(resolved_calls);
        self.resolved_pats.append(resolved_pats);
        self.direct_var_modes.append(direct_var_modes);
        self.ignored_functions.append(ignored_functions);
        self.bodies.append(bodies);
        self.shadow_check.append(shadow_check);
        self.extra_erase_ast_ids.append(extra_erase_ast_ids);
        self.local_invariant_bodies.append(local_invariant_bodies);
    }
}

pub type Context<'tcx> = Rc<ContextX<'tcx>>;
/// Context for HIR-to-VIR translation.
///
/// Item forks share immutable or synchronized state and own their output accumulators and ID
/// counters.
pub struct ContextX<'tcx> {
    pub(crate) cmd_line_args: Arc<crate::config::Args>,
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) erasure_info: Lock<ErasureInfo>,
    pub(crate) spans: crate::spans::SpanContext,
    pub(crate) verus_items: Arc<VerusItems>,
    pub(crate) diagnostics: Arc<Mutex<Vec<vir::ast::VirErrAs>>>,
    pub(crate) no_vstd: bool,
    pub(crate) arch_word_bits: Option<vir::ast::ArchWordBits>,
    pub(crate) crate_name: CrateId,
    pub(crate) name_def_id_map: Arc<RwLock<HashMap<Path, DefId>>>,
    /// Item-local span IDs, or `None` for the shared span counter.
    local_span_ids: Option<AtomicU64>,
    pub(crate) next_read_kind_id: Arc<AtomicU64>,
    // Per-compilation lookup caches.
    externals_available_cache: Arc<RwLock<HashMap<DefId, bool>>>,
    get_field_many_variants_cache: Arc<RwLock<HashMap<DefId, bool>>>,
    mid_ty_cache: Arc<RwLock<FxHashMap<(Ty<'tcx>, DefId), Typ>>>,
}

// SAFETY: `crate_to_vir` shares this context only when rustc enables dynamic thread
// safety. TyCtxt satisfies rustc's marker traits; shared mutable accumulators,
// caches, maps, and counters are protected by Lock, RwLock, or atomics. The remaining
// fields are immutable or synchronized Arcs. VIR's erased span payload is Send + Sync but
// lacks rustc's marker implementations, which prevents a derived implementation here.
unsafe impl<'tcx> DynSend for ContextX<'tcx> {}
// SAFETY: The same ownership and synchronization guarantees apply to shared references.
unsafe impl<'tcx> DynSync for ContextX<'tcx> {}

/// The context in which a given header node might be interpretted
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HeaderSetting {
    /// Fn signature headers (requires, ensures, unwind, mask, decreases)
    /// Including closures
    Fn,
    /// Loops (invariants, ensures, etc.)
    Loop(HirId),
    /// Requires or ensures on an assert-by, assert-by-nonlinear, assert-by-forall etc.
    Assert,
}

#[derive(Clone)]
pub(crate) struct BodyCtxt<'tcx> {
    pub(crate) ctxt: Context<'tcx>,
    pub(crate) types: &'tcx TypeckResults<'tcx>,
    pub(crate) fun_id: DefId,
    pub(crate) external_trait_from_to: Option<Arc<(Path, Path, Option<Path>)>>,
    pub(crate) mode: Mode,
    pub(crate) external_body: bool,
    pub(crate) in_ghost: bool,
    pub(crate) atomically: Option<Arc<AtomicallyCtxt>>,
    pub(crate) migrate_postcondition_vars: Option<std::collections::HashSet<vir::ast::VarIdent>>,
    /// Context to interpret a header if we encounter one
    /// (this is used to determine when it's correct to set `in_fn_sig`).
    pub(crate) header_setting: HeaderSetting,
    /// Are we in the signature of a function or closure?
    pub(crate) in_fn_sig: bool,
    /// Are we in a postcondition of a function or closure? (implies in_fn_sig)
    pub(crate) in_postcondition: bool,
    /// Are we inside an "old" node? (new-mut-ref only)
    pub(crate) in_old: bool,
    /// Are we inside an "after_borrow" or "has_resolved" node? (new-mut-ref only)
    pub(crate) in_explicit_prophecy_node: bool,
    /// params for the enclosing function and all enclosing non-spec-closures
    pub(crate) params: Rc<Vec<Vec<vir::ast::VarIdent>>>,
    /// Assume specification defines a new opaque type for each opaque type in the external function.
    /// We use this map to resolve them later.
    pub(crate) external_opaque_type_map: Option<HashMap<Path, Path>>,
    /// Mapping for HirId found in an HIR Destination to the corresponding VIR Label.
    pub(crate) label_map: Rc<RefCell<(HashMap<HirId, vir::ast::Label>, usize)>>,
}

pub(crate) struct AtomicallyCtxt {
    pub(crate) update_binder: HirId,
    pub(crate) call_spans: Sender<vir::messages::Span>,
}

impl<'tcx> ContextX<'tcx> {
    pub(crate) fn new(
        cmd_line_args: crate::config::Args,
        tcx: TyCtxt<'tcx>,
        spans: crate::spans::SpanContext,
        verus_items: Arc<VerusItems>,
        no_vstd: bool,
        crate_name: CrateId,
    ) -> Self {
        ContextX {
            cmd_line_args: Arc::new(cmd_line_args),
            tcx,
            erasure_info: Lock::new(ErasureInfo::default()),
            spans,
            verus_items,
            diagnostics: Arc::new(Mutex::new(Vec::new())),
            no_vstd,
            arch_word_bits: None,
            crate_name,
            name_def_id_map: Arc::new(RwLock::new(HashMap::new())),
            local_span_ids: None,
            next_read_kind_id: Arc::new(AtomicU64::new(0)),
            externals_available_cache: Arc::new(RwLock::new(HashMap::new())),
            get_field_many_variants_cache: Arc::new(RwLock::new(HashMap::new())),
            mid_ty_cache: Arc::new(RwLock::new(FxHashMap::default())),
        }
    }

    /// Forks a context with empty outputs and optional item-local ID counters.
    pub(crate) fn fork_for_item(&self, local_ids: Option<(u64, u64)>) -> ContextX<'tcx> {
        ContextX {
            cmd_line_args: self.cmd_line_args.clone(),
            tcx: self.tcx,
            erasure_info: Lock::new(ErasureInfo::default()),
            spans: self.spans.clone(),
            verus_items: self.verus_items.clone(),
            diagnostics: Arc::new(Mutex::new(Vec::new())),
            no_vstd: self.no_vstd,
            arch_word_bits: self.arch_word_bits,
            crate_name: self.crate_name.clone(),
            name_def_id_map: self.name_def_id_map.clone(),
            local_span_ids: local_ids.map(|(span_id, _)| AtomicU64::new(span_id)),
            next_read_kind_id: match local_ids {
                Some((_, read_kind_id)) => Arc::new(AtomicU64::new(read_kind_id)),
                None => self.next_read_kind_id.clone(),
            },
            externals_available_cache: self.externals_available_cache.clone(),
            get_field_many_variants_cache: self.get_field_many_variants_cache.clone(),
            mid_ty_cache: self.mid_ty_cache.clone(),
        }
    }

    /// Returns the next span and read-kind IDs.
    pub(crate) fn peek_next_ids(&self) -> (u64, u64) {
        let span_id = match &self.local_span_ids {
            Some(c) => c.load(Ordering::SeqCst),
            None => self.spans.peek_next_span_id(),
        };
        (span_id, self.next_read_kind_id.load(Ordering::SeqCst))
    }

    /// Advances the span and read-kind ID counters.
    pub(crate) fn advance_ids(&self, span_ids: u64, read_kind_ids: u64) {
        match &self.local_span_ids {
            Some(c) => {
                c.fetch_add(span_ids, Ordering::SeqCst);
            }
            None => self.spans.advance_span_id(span_ids),
        }
        self.next_read_kind_id.fetch_add(read_kind_ids, Ordering::SeqCst);
    }

    pub(crate) fn next_span_id(&self) -> u64 {
        match &self.local_span_ids {
            Some(c) => c.fetch_add(1, Ordering::SeqCst),
            None => self.spans.get_next_span_id(),
        }
    }

    pub(crate) fn to_air_span(&self, span: rustc_span::Span) -> vir::messages::Span {
        self.spans.to_air_span_with_id(span, self.next_span_id())
    }

    /// Caches successful attribute parsing that emits no diagnostics.
    pub(crate) fn is_get_field_many_variants(&self, f: DefId) -> Result<bool, VirErr> {
        if let Some(b) = self.get_field_many_variants_cache.borrow().get(&f) {
            return Ok(*b);
        }
        // Verus attributes are `Unparsed` where get_all_attrs is acceptable per its
        // deprecation message.
        #[allow(deprecated)]
        let f_attrs = self.tcx.get_all_attrs(f);
        let mut diagnostics = self.diagnostics.lock().unwrap();
        let n_diagnostics = diagnostics.len();
        let b = crate::attributes::is_get_field_many_variants(f_attrs, Some(&mut *diagnostics))?;
        if diagnostics.len() == n_diagnostics {
            self.get_field_many_variants_cache.borrow_mut().insert(f, b);
        }
        Ok(b)
    }

    /// Caches external-declaration availability by definition.
    pub(crate) fn externals_available_without_declaration(&self, def_id: DefId) -> bool {
        if let Some(b) = self.externals_available_cache.borrow().get(&def_id) {
            return *b;
        }
        let b = crate::attributes::get_externals_available_without_declaration_walk_parents(
            self.tcx, def_id,
        );
        self.externals_available_cache.borrow_mut().insert(def_id, b);
        b
    }

    pub(crate) fn get_verus_item(&self, def_id: DefId) -> Option<&crate::verus_items::VerusItem> {
        self.verus_items.id_to_name.get(&def_id)
    }

    pub(crate) fn get_verifier_attrs(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::VerifierAttrs, VirErr> {
        crate::attributes::get_verifier_attrs(attrs, Some(&mut *self.diagnostics.lock().unwrap()))
    }

    pub(crate) fn get_verifier_attrs_no_check(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::VerifierAttrs, VirErr> {
        crate::attributes::get_verifier_attrs_no_check(
            attrs,
            Some(&mut *self.diagnostics.lock().unwrap()),
        )
    }

    pub(crate) fn get_external_attrs(
        &self,
        attrs: &[Attribute],
    ) -> Result<crate::attributes::ExternalAttrs, VirErr> {
        crate::attributes::get_external_attrs(attrs, Some(&mut *self.diagnostics.lock().unwrap()))
    }

    pub(crate) fn push_body_erasure(&self, local_def_id: LocalDefId, c: BodyErasure) {
        let mut r = self.erasure_info.borrow_mut();
        r.bodies.push((local_def_id, c));
    }

    // Merges path registrations without holding the shared lock across rustc queries.
    fn record_path_def_ids(&self, local: HashMap<Path, DefId>) {
        for (path, def_id) in local {
            self.record_path_def_id(path, def_id);
        }
    }

    // Avoids taking the write lock for an idempotent path registration.
    fn record_path_def_id(&self, path: Path, def_id: DefId) {
        if self.name_def_id_map.borrow().get(&path) == Some(&def_id) {
            return;
        }
        self.name_def_id_map.borrow_mut().insert(path, def_id);
    }

    pub(crate) fn def_id_to_vir_path(&self, def_id: DefId) -> Path {
        let mut local: HashMap<Path, DefId> = HashMap::new();
        let path = crate::rust_to_vir_base::def_id_to_vir_path(
            self.tcx,
            &self.verus_items,
            def_id,
            Some(&mut local),
        );
        self.record_path_def_ids(local);
        path
    }

    pub(crate) fn mid_ty_to_vir(
        &self,
        param_env_src: DefId,
        span: rustc_span::Span,
        ty: &rustc_middle::ty::Ty<'tcx>,
        assume_specification_opaque_type_map: Option<&HashMap<Path, Path>>,
    ) -> Result<vir::ast::Typ, VirErr> {
        self.mid_ty_to_vir_cached(
            param_env_src,
            span,
            ty,
            assume_specification_opaque_type_map,
            true,
        )
    }

    /// Caches successful conversions without opaque type maps.
    /// Cache hits replay datatype path registration; errors retain their call-site span.
    pub(crate) fn mid_ty_to_vir_cached(
        &self,
        param_env_src: DefId,
        span: rustc_span::Span,
        ty: &rustc_middle::ty::Ty<'tcx>,
        assume_specification_opaque_type_map: Option<&HashMap<Path, Path>>,
        record_path: bool,
    ) -> Result<vir::ast::Typ, VirErr> {
        let mut local: HashMap<Path, DefId> = HashMap::new();
        if assume_specification_opaque_type_map.is_some() {
            let typ = crate::rust_to_vir_base::mid_ty_to_vir(
                self.tcx,
                &self.verus_items,
                if record_path { Some(&mut local) } else { None },
                param_env_src,
                span,
                ty,
                assume_specification_opaque_type_map,
            );
            self.record_path_def_ids(local);
            return typ;
        }
        let key = (*ty, param_env_src);
        let cached = self.mid_ty_cache.borrow().get(&key).cloned();
        if let Some(typ) = cached {
            if record_path {
                if let (TyKind::Adt(adt_def, _), TypX::Datatype(Dt::Path(path), _, _)) =
                    (ty.kind(), &*typ)
                {
                    self.record_path_def_id(path.clone(), adt_def.did());
                }
            }
            return Ok(typ);
        }
        let typ = crate::rust_to_vir_base::mid_ty_to_vir(
            self.tcx,
            &self.verus_items,
            if record_path { Some(&mut local) } else { None },
            param_env_src,
            span,
            ty,
            None,
        );
        self.record_path_def_ids(local);
        let typ = typ?;
        self.mid_ty_cache.borrow_mut().insert(key, typ.clone());
        Ok(typ)
    }

    pub(crate) fn unique_read_kind_id(&self) -> u64 {
        self.next_read_kind_id.fetch_add(1, Ordering::SeqCst)
    }
}

impl<'tcx> BodyCtxt<'tcx> {
    pub(crate) fn is_copy(&self, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
        let typing_env = rustc_middle::ty::TypingEnv::new(
            self.ctxt.tcx.param_env(self.fun_id),
            rustc_middle::ty::TypingMode::non_body_analysis(),
        );
        self.ctxt.tcx.type_is_copy_modulo_regions(typing_env, ty)
    }

    pub(crate) fn mid_ty_to_vir(
        &self,
        span: rustc_span::Span,
        ty: &rustc_middle::ty::Ty<'tcx>,
    ) -> Result<vir::ast::Typ, VirErr> {
        self.ctxt.mid_ty_to_vir(self.fun_id, span, ty, self.external_opaque_type_map.as_ref())
    }
    pub(crate) fn is_param_migrated(&self, ident: &vir::ast::VarIdent) -> bool {
        let Some(vars) = &self.migrate_postcondition_vars else {
            return false;
        };
        vars.contains(ident)
    }

    pub(crate) fn is_param_for_fn_or_non_spec_closure(&self, ident: &vir::ast::VarIdent) -> bool {
        self.params.iter().any(|params| params.iter().any(|param| param == ident))
    }

    pub(crate) fn is_param_for_innermost_fn_or_non_spec_closure(
        &self,
        ident: &vir::ast::VarIdent,
    ) -> bool {
        self.params.last().unwrap().iter().any(|param| param == ident)
    }

    pub(crate) fn set_header_setting(&self, s: HeaderSetting) -> BodyCtxt<'tcx> {
        BodyCtxt { header_setting: s, ..self.clone() }
    }

    pub(crate) fn warning_maybe<S: Into<String>>(
        &self,
        span: rustc_span::Span,
        allow: &WarningAllow,
        note: impl FnOnce() -> S,
        emit: impl FnOnce(vir::messages::Message) -> (),
    ) {
        crate::attributes::warning_maybe(self.ctxt.tcx, self.fun_id, span, allow, note, emit);
    }

    pub(crate) fn fresh_label(
        &self,
        hir_id: HirId,
        label: &Option<rustc_ast::ast::Label>,
    ) -> vir::ast::Label {
        let (map, next_id) = &mut *self.label_map.borrow_mut();
        let label = vir::ast::Label { id: *next_id, name: label.map(|l| l.ident.to_string()) };
        *next_id += 1;
        let found = map.insert(hir_id, label.clone());
        assert!(found.is_none());
        label
    }

    pub(crate) fn label_from_dest(
        &self,
        span: rustc_span::Span,
        dest: &rustc_hir::Destination,
    ) -> Result<vir::ast::Label, VirErr> {
        match dest.target_id {
            Ok(hir_id) => {
                let (map, _next_id) = &*self.label_map.borrow();
                match map.get(&hir_id) {
                    None => crate::internal_err!(span, "unable to find loop label destination"),
                    Some(label) => Ok(label.clone()),
                }
            }
            Err(_err) => {
                // This should have already been reported by rustc
                crate::internal_err!(span, "unresolved loop label");
            }
        }
    }
}
