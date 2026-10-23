//! Moves item-local span and read-kind IDs into the crate-wide ID order.
//!
//! Parallel item forks allocate IDs from `LOCAL_ID_TAG` upward. Once every fork's count is
//! known, a prefix sum in item order assigns each fork the range that serial translation
//! would have used, and this walk rewrites every tagged ID in the fork's outputs. Untagged
//! IDs, including the 0 placeholder, are left unchanged, which makes the walk idempotent
//! across shared nodes.

use crate::context::ErasureInfo;
use std::sync::Arc;
use vir::ast::{
    Arm, ArmX, CallTarget, Datatype, DatatypeX, Expr, ExprX, Exprs, Function, FunctionStub,
    FunctionStubX, FunctionX, HeaderExpr, HeaderExprX, KrateX, MaskSpec, Module, ModuleX, Param,
    Params, Pattern, PatternX, Place, PlaceX, Stmt, StmtX, Trait, TraitImpl, TraitImplX, TraitX,
    UnfinalizedReadKind, UnwindSpec,
};
use vir::def::Spanned;
use vir::messages::{AstId, Message, MessageAs, Span};

/// First ID of every item-local span and read-kind counter.
pub(crate) const LOCAL_ID_TAG: u64 = 1 << 63;

/// Number of span and read-kind IDs allocated by a fork whose counters started at the tag.
pub(crate) fn local_id_counts((span_id, read_kind_id): (u64, u64)) -> (u64, u64) {
    assert!(span_id >= LOCAL_ID_TAG && read_kind_id >= LOCAL_ID_TAG);
    (span_id - LOCAL_ID_TAG, read_kind_id - LOCAL_ID_TAG)
}

/// Rebases tagged IDs of one fork onto its crate-wide range.
///
/// A tagged ID at or past the fork's count did not come from this fork (or the count is
/// wrong); rebasing it would alias an ID of a later fork, so it panics, also in release
/// builds. The serialized check in `assert_untagged` (debug builds) independently finds
/// tagged IDs that the walk misses.
#[derive(Clone, Copy)]
pub(crate) struct Renumber {
    span_base: u64,
    read_kind_base: u64,
    span_count: u64,
    read_kind_count: u64,
}

/// Returns a mutable reference to a statement, cloning a shared node by fields.
fn stmt_mut(stmt: &mut Stmt) -> &mut Spanned<StmtX> {
    if Arc::get_mut(stmt).is_none() {
        let x = match &stmt.x {
            StmtX::Expr(e) => StmtX::Expr(e.clone()),
            StmtX::Decl { pattern, mode, init, els, assert_irrefutable } => StmtX::Decl {
                pattern: pattern.clone(),
                mode: *mode,
                init: init.clone(),
                els: els.clone(),
                assert_irrefutable: *assert_irrefutable,
            },
        };
        *stmt = Arc::new(Spanned { span: stmt.span.clone(), x });
    }
    Arc::get_mut(stmt).unwrap()
}

/// Returns a mutable reference to a match arm, cloning a shared node by fields.
fn arm_mut(arm: &mut Arm) -> &mut Spanned<ArmX> {
    if Arc::get_mut(arm).is_none() {
        let ArmX { pattern, guard, body } = &arm.x;
        let x = ArmX { pattern: pattern.clone(), guard: guard.clone(), body: body.clone() };
        *arm = Arc::new(Spanned { span: arm.span.clone(), x });
    }
    Arc::get_mut(arm).unwrap()
}

/// Returns a mutable reference to a header, cloning a shared node by fields.
fn header_mut(header: &mut HeaderExpr) -> &mut HeaderExprX {
    if Arc::get_mut(header).is_none() {
        use HeaderExprX as H;
        let x = match &**header {
            H::UnwrapParameter(u) => H::UnwrapParameter(u.clone()),
            H::NoMethodBody => H::NoMethodBody,
            H::Requires(es) => H::Requires(es.clone()),
            H::Ensures(id, es) => H::Ensures(id.clone(), es.clone()),
            H::Returns(e) => H::Returns(e.clone()),
            H::Recommends(es) => H::Recommends(es.clone()),
            H::InvariantExceptBreak(es) => H::InvariantExceptBreak(es.clone()),
            H::Invariant(es) => H::Invariant(es.clone()),
            H::Decreases(es) => H::Decreases(es.clone()),
            H::DecreasesWhen(e) => H::DecreasesWhen(e.clone()),
            H::DecreasesBy(f) => H::DecreasesBy(f.clone()),
            H::OpensInvariantMask(m) => H::OpensInvariantMask(m.clone()),
            H::AtomicSpec(e) => H::AtomicSpec(e.clone()),
            H::AtomicCallLoop => H::AtomicCallLoop,
            H::Hide(f) => H::Hide(f.clone()),
            H::ExtraDependency(f) => H::ExtraDependency(f.clone()),
            H::NoUnwind => H::NoUnwind,
            H::NoUnwindWhen(e) => H::NoUnwindWhen(e.clone()),
            H::OpenVisibilityQualifier(v) => H::OpenVisibilityQualifier(v.clone()),
        };
        *header = Arc::new(x);
    }
    Arc::get_mut(header).unwrap()
}

impl Renumber {
    /// Maps the fork's `counts` tagged span and read-kind IDs onto ranges starting at `bases`.
    pub(crate) fn new(
        (span_base, read_kind_base): (u64, u64),
        (span_count, read_kind_count): (u64, u64),
    ) -> Self {
        Renumber { span_base, read_kind_base, span_count, read_kind_count }
    }

    /// Rebases a tagged ID with local index below `count` onto `base`.
    fn rebase(id: &mut u64, base: u64, count: u64, what: &str) {
        if *id >= LOCAL_ID_TAG {
            let local = *id - LOCAL_ID_TAG;
            assert!(local < count, "item-local {what} ID {local} outside the fork's {count} IDs");
            *id = base + local;
        }
    }

    pub(crate) fn span_id(&self, id: &mut AstId) {
        Self::rebase(id, self.span_base, self.span_count, "span");
    }

    fn span(&self, span: &mut Span) {
        self.span_id(&mut span.id);
    }

    fn read_kind(&self, rk: &mut UnfinalizedReadKind) {
        Self::rebase(&mut rk.id, self.read_kind_base, self.read_kind_count, "read-kind");
    }

    /// Renumbers a spanned node and returns its payload.
    fn spanned<'a, X: Clone>(&self, node: &'a mut Arc<Spanned<X>>) -> &'a mut X {
        let node = Arc::make_mut(node);
        self.span(&mut node.span);
        &mut node.x
    }

    pub(crate) fn message(&self, msg: &mut Message) {
        let msg = Arc::make_mut(msg);
        msg.spans.iter_mut().for_each(|s| self.span(s));
        msg.labels.iter_mut().for_each(|l| self.span(&mut l.span));
    }

    pub(crate) fn message_as(&self, msg: &mut MessageAs) {
        match msg {
            MessageAs::Warning(m) | MessageAs::Note(m) => self.message(m),
        }
    }

    pub(crate) fn erasure_info(&self, info: &mut ErasureInfo) {
        let ErasureInfo {
            local_hir_vir_ids,
            binder_hir_vir_ids,
            ctor_hir_vir_ids,
            resolved_calls: _,
            resolved_pats,
            direct_var_modes: _,
            ignored_functions: _,
            bodies: _,
            shadow_check: _,
            extra_erase_ast_ids,
            local_invariant_bodies: _,
        } = info;
        for ids in [local_hir_vir_ids, binder_hir_vir_ids, ctor_hir_vir_ids] {
            ids.iter_mut().for_each(|(_, id)| self.span_id(id));
        }
        resolved_pats.iter_mut().for_each(|(_, p)| self.pattern(p));
        extra_erase_ast_ids.iter_mut().for_each(|s| self.span(s));
    }

    pub(crate) fn krate(&self, krate: &mut KrateX) {
        let KrateX {
            functions,
            reveal_groups,
            datatypes,
            traits,
            trait_impls,
            assoc_type_impls,
            modules,
            external_fns: _,
            external_types: _,
            path_as_rust_names: _,
            arch: _,
            opaque_types,
        } = krate;
        functions.iter_mut().for_each(|f| self.function(f));
        reveal_groups.iter_mut().for_each(|g| _ = self.spanned(g));
        datatypes.iter_mut().for_each(|d| self.datatype(d));
        traits.iter_mut().for_each(|t| self.trait_(t));
        trait_impls.iter_mut().for_each(|t| self.trait_impl(t));
        assoc_type_impls.iter_mut().for_each(|a| _ = self.spanned(a));
        modules.iter_mut().for_each(|m| self.module(m));
        opaque_types.iter_mut().for_each(|o| _ = self.spanned(o));
    }

    pub(crate) fn module_reveals(&self, reveals: &mut vir::ast::ModuleReveals) {
        _ = self.spanned(reveals);
    }

    fn module(&self, module: &mut Module) {
        let ModuleX { path: _, reveals } = self.spanned(module);
        reveals.iter_mut().for_each(|r| self.module_reveals(r));
    }

    fn datatype(&self, datatype: &mut Datatype) {
        let DatatypeX {
            name: _,
            proxy,
            owning_module: _,
            visibility: _,
            transparency: _,
            typ_params: _,
            typ_bounds: _,
            variants: _,
            mode: _,
            ext_equal: _,
            user_defined_invariant_fn: _,
            sized_constraint: _,
            destructor: _,
        } = self.spanned(datatype);
        proxy.iter_mut().for_each(|p| self.span(&mut p.span));
    }

    fn trait_(&self, t: &mut Trait) {
        let TraitX {
            name: _,
            proxy,
            visibility: _,
            typ_params: _,
            typ_bounds: _,
            assoc_typs: _,
            assoc_typs_bounds: _,
            methods: _,
            is_unsafe: _,
            dyn_compatible: _,
            external_trait_extension: _,
        } = self.spanned(t);
        proxy.iter_mut().for_each(|p| self.span(&mut p.span));
    }

    fn trait_impl(&self, t: &mut TraitImpl) {
        let TraitImplX {
            impl_path: _,
            typ_params: _,
            typ_bounds: _,
            trait_path: _,
            trait_typ_args: _,
            trait_typ_arg_impls,
            owning_module: _,
            auto_imported: _,
            external_trait_blanket: _,
        } = self.spanned(t);
        _ = self.spanned(trait_typ_arg_impls);
    }

    pub(crate) fn function(&self, function: &mut Function) {
        let FunctionX {
            name: _,
            proxy,
            kind: _,
            visibility: _,
            body_visibility: _,
            opaqueness: _,
            owning_module: _,
            mode: _,
            typ_params: _,
            typ_bounds: _,
            params,
            outer_ret,
            inner_ret,
            require,
            ensure,
            returns,
            decrease,
            decrease_when,
            decrease_by: _,
            fndef_axioms,
            mask_spec,
            atomic_update,
            unwind_spec,
            item_kind: _,
            attrs: _,
            body,
            extra_dependencies: _,
            hidden: _,
        } = self.spanned(function);
        proxy.iter_mut().for_each(|p| self.span(&mut p.span));
        self.params(params);
        self.param(outer_ret);
        self.param(inner_ret);
        self.exprs(require);
        self.exprs(&mut ensure.0);
        self.exprs(&mut ensure.1);
        self.opt_expr(returns);
        self.exprs(decrease);
        self.opt_expr(decrease_when);
        fndef_axioms.iter_mut().for_each(|es| self.exprs(es));
        mask_spec.iter_mut().for_each(|m| self.mask_spec(m));
        self.opt_expr(atomic_update);
        unwind_spec.iter_mut().for_each(|u| self.unwind_spec(u));
        self.opt_expr(body);
    }

    pub(crate) fn function_stub(&self, stub: &mut FunctionStub) {
        let FunctionStubX {
            name: _,
            proxy,
            kind: _,
            visibility: _,
            body_visibility: _,
            opaqueness: _,
            owning_module: _,
            mode: _,
            typ_params: _,
            typ_bounds: _,
            params,
            outer_ret,
            item_kind: _,
            attrs: _,
            returns: _,
            decreases_len: _,
        } = self.spanned(stub);
        proxy.iter_mut().for_each(|p| self.span(&mut p.span));
        self.params(params);
        self.param(outer_ret);
    }

    fn param(&self, param: &mut Param) {
        _ = self.spanned(param);
    }

    fn params(&self, params: &mut Params) {
        Arc::make_mut(params).iter_mut().for_each(|p| self.param(p));
    }

    fn mask_spec(&self, mask: &mut MaskSpec) {
        match mask {
            MaskSpec::InvariantOpens(span, es) | MaskSpec::InvariantOpensExcept(span, es) => {
                self.span(span);
                self.exprs(es);
            }
            MaskSpec::InvariantOpensSet(e) => self.expr(e),
        }
    }

    fn unwind_spec(&self, unwind: &mut UnwindSpec) {
        match unwind {
            UnwindSpec::NoUnwind | UnwindSpec::MayUnwind => {}
            UnwindSpec::NoUnwindWhen(e) => self.expr(e),
        }
    }

    fn opt_expr(&self, e: &mut Option<Expr>) {
        e.iter_mut().for_each(|e| self.expr(e));
    }

    fn exprs(&self, es: &mut Exprs) {
        Arc::make_mut(es).iter_mut().for_each(|e| self.expr(e));
    }

    fn header(&self, header: &mut HeaderExpr) {
        use HeaderExprX as H;
        match header_mut(header) {
            H::UnwrapParameter(_)
            | H::NoMethodBody
            | H::DecreasesBy(_)
            | H::AtomicCallLoop
            | H::Hide(_)
            | H::ExtraDependency(_)
            | H::NoUnwind
            | H::OpenVisibilityQualifier(_) => {}
            H::Requires(es)
            | H::Recommends(es)
            | H::InvariantExceptBreak(es)
            | H::Invariant(es)
            | H::Decreases(es) => self.exprs(es),
            H::Ensures(_, (es0, es1)) => {
                self.exprs(es0);
                self.exprs(es1);
            }
            H::Returns(e) | H::DecreasesWhen(e) | H::AtomicSpec(e) | H::NoUnwindWhen(e) => {
                self.expr(e)
            }
            H::OpensInvariantMask(m) => self.mask_spec(m),
        }
    }

    fn expr(&self, expr: &mut Expr) {
        let expr = Arc::make_mut(expr);
        self.span(&mut expr.span);
        match &mut expr.x {
            ExprX::Const(_)
            | ExprX::Var(_)
            | ExprX::VarAt(..)
            | ExprX::ConstVar(..)
            | ExprX::StaticVar(_)
            | ExprX::NullaryOpr(_)
            | ExprX::ExecFnByName(_)
            | ExprX::Fuel(..)
            | ExprX::RevealString(_)
            | ExprX::RevealByteString(_)
            | ExprX::AtomicUpdateInitDummy
            | ExprX::AirStmt(_)
            | ExprX::Nondeterministic => {}
            ExprX::Call { target, args, post_args, body } => {
                match target {
                    CallTarget::FnSpec(e) => self.expr(e),
                    CallTarget::Fun(..)
                    | CallTarget::BuiltinSpecFun(..)
                    | CallTarget::AssumeExternal => {}
                }
                self.exprs(args);
                self.opt_expr(post_args);
                self.opt_expr(body);
            }
            ExprX::Ctor(_, _, binders, tail) => {
                for b in Arc::make_mut(binders).iter_mut() {
                    self.expr(&mut Arc::make_mut(b).a);
                }
                if let Some(tail) = tail {
                    self.place(&mut tail.place);
                    for (_, rk) in Arc::make_mut(&mut tail.taken_fields).iter_mut() {
                        self.read_kind(rk);
                    }
                }
            }
            ExprX::Unary(_, e)
            | ExprX::UnaryOpr(_, e)
            | ExprX::Quant(_, _, e)
            | ExprX::Closure(_, e)
            | ExprX::AssertAssumeUserDefinedTypeInvariant { expr: e, .. }
            | ExprX::AssertCompute(e, _)
            | ExprX::Atomically(_, _, e)
            | ExprX::Update(e)
            | ExprX::Ghost { expr: e, .. }
            | ExprX::ProofInSpec(e)
            | ExprX::NeverToAny(e)
            | ExprX::Old(e)
            | ExprX::Await(e) => self.expr(e),
            ExprX::Logical(_, a, b)
            | ExprX::Binary(_, a, b)
            | ExprX::BinaryOpr(_, a, b)
            | ExprX::OpenInvariant(a, _, b, _)
            | ExprX::TryOpenAtomicUpdate(a, _, b)
            | ExprX::EvalAndResolve(a, b)
            | ExprX::ShrRefStructWrap(a, b, ..)
            | ExprX::Choose { params: _, cond: a, body: b } => {
                self.expr(a);
                self.expr(b);
            }
            ExprX::Multi(_, es) | ExprX::ArrayLiteral(es) => self.exprs(es),
            ExprX::NonSpecClosure {
                params: _,
                proof_fn_modes: _,
                body,
                requires,
                ensures,
                ret: _,
                external_spec,
            } => {
                self.expr(body);
                self.exprs(requires);
                self.exprs(ensures);
                external_spec.iter_mut().for_each(|(_, e)| self.expr(e));
            }
            ExprX::WithTriggers { triggers, body } => {
                Arc::make_mut(triggers).iter_mut().for_each(|t| self.exprs(t));
                self.expr(body);
            }
            ExprX::Assign { place, rhs, op: _, typ: _, resolve: _ } => {
                self.place(place);
                self.expr(rhs);
            }
            ExprX::Header(h) => self.header(h),
            ExprX::AssertAssume { is_assume: _, expr, msg } => {
                self.expr(expr);
                msg.iter_mut().for_each(|m| self.message(m));
            }
            ExprX::AssertBy { vars: _, require, ensure, proof } => {
                self.expr(require);
                self.expr(ensure);
                self.expr(proof);
            }
            ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
                self.exprs(requires);
                self.exprs(ensures);
                self.expr(proof);
            }
            ExprX::If(c, t, e) => {
                self.expr(c);
                self.expr(t);
                self.opt_expr(e);
            }
            ExprX::Match(place, arms, _) => {
                self.place(place);
                Arc::make_mut(arms).iter_mut().for_each(|a| self.arm(a));
            }
            ExprX::Loop {
                loop_isolation: _,
                allow_complex_invariants: _,
                is_for_loop: _,
                assume_termination: _,
                label: _,
                cond,
                body,
                invs,
                decrease,
                atomic_call: _,
            } => {
                self.opt_expr(cond);
                self.expr(body);
                Arc::make_mut(invs).iter_mut().for_each(|inv| self.expr(&mut inv.inv));
                self.exprs(decrease);
            }
            ExprX::InvMask(m) => self.mask_spec(m),
            ExprX::Return(e) | ExprX::BreakOrContinue { label: _, is_break: _, value: e } => {
                self.opt_expr(e)
            }
            ExprX::Block(stmts, e) => {
                Arc::make_mut(stmts).iter_mut().for_each(|s| self.stmt(s));
                self.opt_expr(e);
            }
            ExprX::BorrowMut(p) | ExprX::TwoPhaseBorrowMut(p) | ExprX::BorrowMutTracked(p) => {
                self.place(p)
            }
            ExprX::ImplicitReborrowOrSpecRead(p, _, span) => {
                self.place(p);
                self.span(span);
            }
            ExprX::ReadPlace(p, rk) => {
                self.place(p);
                self.read_kind(rk);
            }
            ExprX::MatchGuardFreeze(p, e) => {
                self.place(p);
                self.expr(e);
            }
        }
    }

    fn place(&self, place: &mut Place) {
        let place = Arc::make_mut(place);
        self.span(&mut place.span);
        match &mut place.x {
            PlaceX::Field(_, p)
            | PlaceX::DerefMut(p)
            | PlaceX::ModeUnwrap(p, _)
            | PlaceX::UserDefinedTypInvariantObligation(p, _) => self.place(p),
            PlaceX::Index(p, e, _, _) | PlaceX::WithExpr(e, p) => {
                self.place(p);
                self.expr(e);
            }
            PlaceX::Local(_) => {}
            PlaceX::Temporary(e) => self.expr(e),
        }
    }

    fn pattern(&self, pattern: &mut Pattern) {
        let pattern = Arc::make_mut(pattern);
        self.span(&mut pattern.span);
        match &mut pattern.x {
            PatternX::Wildcard | PatternX::Var(_) => {}
            PatternX::Binding { binding: _, sub_pat: p }
            | PatternX::MutRef(p)
            | PatternX::ImmutRef(p) => self.pattern(p),
            PatternX::Constructor(_, _, binders) => {
                for b in Arc::make_mut(binders).iter_mut() {
                    self.pattern(&mut Arc::make_mut(b).a);
                }
            }
            PatternX::Or(a, b) => {
                self.pattern(a);
                self.pattern(b);
            }
            PatternX::Expr(e) => self.expr(e),
            PatternX::Range(lo, hi) => {
                self.opt_expr(lo);
                hi.iter_mut().for_each(|(e, _)| self.expr(e));
            }
            PatternX::Slice(ps) => Arc::make_mut(ps).iter_mut().for_each(|p| self.pattern(p)),
        }
    }

    fn stmt(&self, stmt: &mut Stmt) {
        let stmt = stmt_mut(stmt);
        self.span(&mut stmt.span);
        match &mut stmt.x {
            StmtX::Expr(e) => self.expr(e),
            StmtX::Decl { pattern, mode: _, init, els, assert_irrefutable: _ } => {
                self.pattern(pattern);
                init.iter_mut().for_each(|p| self.place(p));
                self.opt_expr(els);
            }
        }
    }

    fn arm(&self, arm: &mut Arm) {
        let arm = arm_mut(arm);
        self.span(&mut arm.span);
        let ArmX { pattern, guard, body } = &mut arm.x;
        self.pattern(pattern);
        self.expr(guard);
        self.expr(body);
    }
}

/// Panics if a tagged span or read-kind ID survives in serialized VIR. The serialized form
/// reaches every `id` field independently of the renumbering walk.
pub(crate) fn assert_untagged<T: serde::Serialize + ?Sized>(what: &str, value: &T) {
    use serde_json::Value;
    fn walk(what: &str, v: &Value) {
        match v {
            Value::Array(vs) => vs.iter().for_each(|v| walk(what, v)),
            Value::Object(m) => {
                if let Some(id) = m.get("id").and_then(Value::as_u64) {
                    assert!(id < LOCAL_ID_TAG, "item-local ID {id} survived renumbering in {what}");
                }
                m.values().for_each(|v| walk(what, v));
            }
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
        }
    }
    walk(what, &serde_json::to_value(value).expect("serialize VIR for ID check"));
}

/// Panics if a tagged ID survives in erasure outputs.
pub(crate) fn assert_untagged_erasure_info(info: &ErasureInfo) {
    let ErasureInfo {
        local_hir_vir_ids,
        binder_hir_vir_ids,
        ctor_hir_vir_ids,
        resolved_pats,
        extra_erase_ast_ids,
        ..
    } = info;
    for ids in [local_hir_vir_ids, binder_hir_vir_ids, ctor_hir_vir_ids] {
        assert!(ids.iter().all(|(_, id)| *id < LOCAL_ID_TAG), "item-local erasure AST ID");
    }
    let pats: Vec<&Pattern> = resolved_pats.iter().map(|(_, p)| p).collect();
    assert_untagged("erasure patterns", &pats);
    assert_untagged("erasure spans", extra_erase_ast_ids);
}

#[cfg(test)]
mod tests {
    use super::*;
    use vir::ast::ReadKind;

    fn read_kind(id: u64) -> UnfinalizedReadKind {
        UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id }
    }

    #[test]
    fn renumber_rebases_tagged_ids_in_range() {
        let r = Renumber::new((100, 200), (3, 2));
        let mut ids = [LOCAL_ID_TAG, LOCAL_ID_TAG + 2, 0, 7, LOCAL_ID_TAG - 1];
        ids.iter_mut().for_each(|id| r.span_id(id));
        assert_eq!(ids, [100, 102, 0, 7, LOCAL_ID_TAG - 1]);
        let mut rks = [read_kind(LOCAL_ID_TAG + 1), read_kind(5)];
        rks.iter_mut().for_each(|rk| r.read_kind(rk));
        assert_eq!(rks.map(|rk| rk.id), [201, 5]);
        assert_eq!(local_id_counts((LOCAL_ID_TAG + 3, LOCAL_ID_TAG)), (3, 0));
    }

    #[test]
    #[should_panic(expected = "item-local span ID 3 outside the fork's 3 IDs")]
    fn renumber_rejects_span_id_past_the_fork_count() {
        Renumber::new((100, 200), (3, 2)).span_id(&mut (LOCAL_ID_TAG + 3));
    }

    #[test]
    #[should_panic(expected = "item-local read-kind ID 0 outside the fork's 0 IDs")]
    fn renumber_rejects_read_kind_id_of_an_empty_fork() {
        Renumber::new((100, 200), (3, 0)).read_kind(&mut read_kind(LOCAL_ID_TAG));
    }
}
