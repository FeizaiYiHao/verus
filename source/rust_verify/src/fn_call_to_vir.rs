use crate::attributes::{
    get_custom_err_annotations, get_ghost_block_opt, get_trigger, get_var_mode, get_verifier_attrs,
    parse_attrs, Attr, GetVariantField, GhostBlockAttr,
};
use crate::context::{BodyCtxt, Context};
use crate::erase::{CompilableOperator, ResolvedCall};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, get_range,
    is_smt_arith, is_smt_equality, is_type_std_rc_or_arc_or_ref, local_to_var, mid_ty_simplify,
    mid_ty_to_vir, mid_ty_to_vir_datatype, mid_ty_to_vir_ghost, mk_range, typ_of_node,
    typ_of_node_expect_mut_ref, def_id_to_vir_path_option,
};
use crate::rust_to_vir_expr::{ExprModifier, record_fun, check_lit_int, extract_array, expr_to_vir, extract_ensures, extract_tuple, get_fn_path, extract_quant, extract_choose, pat_to_var, closure_to_vir, extract_assert_forall_by, is_expr_typ_mut_ref, mk_ty_clip};
use crate::util::{err_span, slice_vec_map_result, unsupported_err_span, vec_map, vec_map_result};
use crate::verus_items::{VerusItem, SpecItem, QuantItem, DirectiveItem, ExprItem, CompilableOprItem, self, RustItem, BinaryOpItem, EqualityItem, SpecOrdItem, ArithItem, SpecArithItem, ChainedItem, AssertItem, UnaryOpItem, SpecLiteralItem, SpecGhostTrackedItem, OpenInvariantBlockItem, BuiltinFunctionItem};
use crate::{unsupported_err, unsupported_err_unless};
use air::ast::{Binder, BinderX};
use air::ast_util::str_ident;
use rustc_ast::{Attribute, BorrowKind, ByRef, LitKind, Mutability};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{
    BinOpKind, BindingAnnotation, Block, Closure, Destination, Expr, ExprKind, Guard, HirId, Let,
    Local, LoopSource, Node, Pat, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use crate::rust_intrinsics_to_vir::int_intrinsic_constant_to_vir;
use rustc_middle::ty::subst::GenericArgKind;
use rustc_middle::ty::DefIdTree;
use rustc_middle::ty::{AdtDef, Clause, EarlyBinder, PredicateKind, TyCtxt, TyKind, VariantDef};
use rustc_span::def_id::DefId;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    ArithOp, ArmX, AssertQueryMode, AutospecUsage, BinaryOp, BitwiseOp, BuiltinSpecFun, CallTarget,
    ComputeMode, Constant, ExprX, FieldOpr, FunX, HeaderExpr, HeaderExprX, Ident, InequalityOp,
    IntRange, IntegerTypeBoundKind, InvAtomicity, Mode, ModeCoercion, MultiOp, PatternX, Quant,
    SpannedTyped, StmtX, Stmts, Typ, TypX, UnaryOp, UnaryOpr, VarAt, VirErr,
};
use vir::ast_util::{
    const_int_from_string, ident_binder, path_as_friendly_rust_name, types_equal, undecorate_typ,
};
use vir::def::positional_field_ident;

pub(crate) fn fn_call_to_vir<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    expr: &Expr<'tcx>,
    self_path: Option<vir::ast::Path>,
    f: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::subst::GenericArg<'tcx>>,
    fn_span: Span,
    args: Vec<&'tcx Expr<'tcx>>,
    outer_modifier: ExprModifier,
) -> Result<vir::ast::Expr, VirErr> {
    let tcx = bctx.ctxt.tcx;

    // DO NOT use f_name to find items (i.e. do not use f_name == "core::cmp::Eq"),
    // use `crate::verus_item::get_rust_item` instead
    let f_name = tcx.def_path_str(f);

    let verus_item = bctx.ctxt.get_verus_item(f);
    let rust_item = verus_items::get_rust_item(tcx, f);

    // TODO these were broken (they sometimes/often appear as std::cmp::*); do we need them?
    // let is_eq = f_name == "core::cmp::PartialEq::eq";
    // let is_ne = f_name == "core::cmp::PartialEq::ne";
    // let is_le = f_name == "core::cmp::PartialOrd::le";
    // let is_ge = f_name == "core::cmp::PartialOrd::ge";
    // let is_lt = f_name == "core::cmp::PartialOrd::lt";
    // let is_gt = f_name == "core::cmp::PartialOrd::gt";
    // let is_add = f_name == "std::ops::Add::add";
    // let is_sub = f_name == "std::ops::Sub::sub";
    // let is_mul = f_name == "std::ops::Mul::mul";

    let is_spec_op = matches!(verus_item, Some(
        VerusItem::BinaryOp(
            BinaryOpItem::SpecArith(_) | BinaryOpItem::SpecBitwise(_) | BinaryOpItem::Equality(_) | BinaryOpItem::SpecOrd(_)) |
        VerusItem::Chained(_) |
        VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(_) | UnaryOpItem::SpecCastInteger | UnaryOpItem::SpecNeg)
    ));

    // These functions are all no-ops in the SMT encoding, so we don't emit any VIR
    let is_smartptr_new = matches!(rust_item,
        Some(RustItem::BoxNew | RustItem::RcNew | RustItem::ArcNew));

    if let Some(VerusItem::OpenInvariantBlock(_)) = verus_item {
        // `open_invariant_begin` and `open_invariant_end` calls should only appear
        // through use of the `open_invariant!` macro, which creates an invariant block.
        // Thus, they should end up being processed by `invariant_block_to_vir` before
        // we get here. Thus, for any well-formed use of an invariant block, we should
        // not reach this point.
        return err_span(
            expr.span,
            format!(
                "{} should never be used except through open_atomic_invariant or open_local_invariant macro",
                f_name
            ),
        );
    }

    if bctx.external_body
        && !matches!(verus_item,
            Some(VerusItem::Spec(
                SpecItem::Requires
                | SpecItem::Recommends
                | SpecItem::Ensures
                | SpecItem::OpensInvariantsNone
                | SpecItem::OpensInvariantsAny
                | SpecItem::OpensInvariants
                | SpecItem::OpensInvariantsExcept
            ) | VerusItem::Directive(DirectiveItem::ExtraDependency))
        )
    {
        return Ok(bctx.spanned_typed_new(
            expr.span,
            &Arc::new(TypX::Bool),
            ExprX::Block(Arc::new(vec![]), None),
        ));
    }

    if matches!(rust_item, Some(RustItem::Panic)) {
        return err_span(
            expr.span,
            format!(
                "panic is not supported (if you used Rust's `assert!` macro, you may have meant to use Verus's `assert` function)"
            ),
        );
    }

    unsupported_err_unless!(
        bctx.ctxt
            .tcx
            .impl_of_method(f)
            .and_then(|method_def_id| bctx.ctxt.tcx.trait_id_of_impl(method_def_id))
            .is_none(),
        expr.span,
        "call of trait impl"
    );

    let is_spec_no_proof_args = 
        matches!(verus_item, Some(
            VerusItem::Spec(_) | VerusItem::Quant(_) | VerusItem::Directive(_) |
            VerusItem::Expr(
                ExprItem::Choose |
                ExprItem::ChooseTuple |
                ExprItem::Old |
                ExprItem::StrSliceLen |
                ExprItem::StrSliceGetChar |
                ExprItem::StrSliceIsAscii |
                ExprItem::ClosureToFnSpec |
                ExprItem::ArchWordBits |
                ExprItem::Height
            ) |
            VerusItem::Assert(_) |
            VerusItem::WithTriggers |
            VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(_))
        ));
    let is_spec_allow_proof_args_pre = is_spec_op
        || matches!(verus_item, Some(
            VerusItem::Expr(
                ExprItem::SignedMax |
                ExprItem::SignedMin |
                ExprItem::UnsignedMax
            ) |
            VerusItem::BinaryOp(BinaryOpItem::Arith(_))
        ));
    let is_compilable_operator = match verus_item {
        Some(VerusItem::CompilableOpr(compilable_opr)) => Some(match compilable_opr {
            CompilableOprItem::Implies => CompilableOperator::Implies,
            CompilableOprItem::NewStrLit => CompilableOperator::NewStrLit,
            CompilableOprItem::GhostExec | CompilableOprItem::GhostNew => CompilableOperator::GhostExec,
            CompilableOprItem::TrackedNew => CompilableOperator::TrackedNew,
            CompilableOprItem::TrackedExec => CompilableOperator::TrackedExec,
            CompilableOprItem::TrackedExecBorrow => CompilableOperator::TrackedExecBorrow,
            CompilableOprItem::TrackedGet => CompilableOperator::TrackedGet,
            CompilableOprItem::TrackedBorrow => CompilableOperator::TrackedBorrow,
            CompilableOprItem::TrackedBorrowMut => CompilableOperator::TrackedBorrowMut,
        }),
        None if is_smartptr_new => Some(CompilableOperator::SmartPtrNew),
        _ => None,
    };
    let needs_name = !(is_spec_no_proof_args
        || is_spec_allow_proof_args_pre
        || is_compilable_operator.is_some());
    let path = if !needs_name { None } else { Some(def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, f)) };

    let is_get_variant = {
        let fn_attrs = if f.as_local().is_some() {
            if let Some(rustc_hir::Node::ImplItem(
                impl_item @ rustc_hir::ImplItem { kind: rustc_hir::ImplItemKind::Fn(..), .. },
            )) = tcx.hir().get_if_local(f)
            {
                Some(bctx.ctxt.tcx.hir().attrs(impl_item.hir_id()))
            } else {
                None
            }
        } else {
            Some(bctx.ctxt.tcx.item_attrs(f))
        };
        if let Some(fn_attrs) = fn_attrs {
            let fn_vattrs = get_verifier_attrs(fn_attrs)?;
            let is_get_variant = if let Some(variant_ident) = fn_vattrs.is_variant {
                Some((variant_ident, None))
            } else if let Some((variant_ident, field_ident)) = fn_vattrs.get_variant {
                Some((variant_ident, Some(field_ident)))
            } else {
                None
            };
            is_get_variant
        } else {
            None
        }
    };

    let name =
        if let Some(path) = &path { Some(Arc::new(FunX { path: path.clone() })) } else { None };

    let is_spec_allow_proof_args = is_spec_allow_proof_args_pre || is_get_variant.is_some();
    let autospec_usage = if bctx.in_ghost { AutospecUsage::IfMarked } else { AutospecUsage::Final };

    let mk_typ_args =
        |substs: &rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>| -> Result<_, VirErr> {
            let mut typ_args: Vec<Typ> = Vec::new();
            for typ_arg in substs {
                match typ_arg.unpack() {
                    GenericArgKind::Type(ty) => {
                        typ_args.push(mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, expr.span, &ty, false)?);
                    }
                    GenericArgKind::Lifetime(_) => {}
                    GenericArgKind::Const(cnst) => {
                        typ_args.push(crate::rust_to_vir_base::mid_ty_const_to_vir(
                            tcx,
                            Some(expr.span),
                            &cnst,
                        )?);
                    }
                }
            }
            Ok(Arc::new(typ_args))
        };

    // Compute the 'target_kind'.
    //
    // If the target is a "trait function" then we try to resolve it to a statically known
    // implementation of that function. The target_kind stores this information,
    // known or unknown.
    //
    // If the resolution is statically known, we record the resolved function for the
    // to be used by lifetime_generate.

    let target_kind = if tcx.trait_of_item(f).is_none() {
        vir::ast::CallTargetKind::Static
    } else {
        let mut resolved = None;
        let param_env = tcx.param_env(bctx.fun_id);
        let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);
        let inst = rustc_middle::ty::Instance::resolve(tcx, param_env, f, normalized_substs);
        if let Ok(Some(inst)) = inst {
            if let rustc_middle::ty::InstanceDef::Item(item) = inst.def {
                if let rustc_middle::ty::WithOptConstParam { did, const_param_did: None } = item {
                    let typs = mk_typ_args(&inst.substs)?;
                    let f = Arc::new(FunX { path: def_id_to_vir_path(tcx, &bctx.ctxt.verus_items, did) });
                    resolved = Some((f, typs));
                }
            }
        }
        vir::ast::CallTargetKind::Method(resolved)
    };

    let record_name = match &target_kind {
        vir::ast::CallTargetKind::Method(Some((fun, _))) => Some(fun.clone()),
        _ => name.clone(),
    };

    record_fun(
        &bctx.ctxt,
        expr.hir_id,
        fn_span,
        &record_name,
        &f_name,
        is_spec_no_proof_args,
        is_spec_allow_proof_args,
        is_compilable_operator,
        autospec_usage,
    );

    let len = args.len();
    let expr_typ = || typ_of_node(bctx, expr.span, &expr.hir_id, false);
    let mk_expr = |x: ExprX| Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, x));
    let mk_expr_span = |span: Span, x: ExprX| Ok(bctx.spanned_typed_new(span, &expr_typ()?, x));

    match verus_item {
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(spec_literal_item))) => {
            unsupported_err_unless!(len == 1, expr.span, "expected spec_literal_*", &args);
            let arg = &args[0];
            let is_num = |s: &String| s.chars().count() > 0 && s.chars().all(|c| c.is_digit(10));
            match &args[0] {
                Expr { kind: ExprKind::Lit(Spanned { node: LitKind::Str(s, _), .. }), .. }
                    if is_num(&s.to_string()) =>
                {
                    // TODO: negative literals for is_spec_literal_int and is_spec_literal_integer
                    if spec_literal_item == &SpecLiteralItem::Integer {
                        // TODO: big integers for int, nat
                        let i: u128 = match s.to_string().parse() {
                            Ok(i) => i,
                            Err(err) => {
                                return err_span(arg.span, format!("integer out of range {}", err));
                            }
                        };
                        let in_negative_literal = false;
                        check_lit_int(&bctx.ctxt, expr.span, in_negative_literal, i, &expr_typ()?)?
                    }
                    return mk_expr(ExprX::Const(const_int_from_string(s.to_string())));
                }
                _ => {
                    return err_span(arg.span, "spec_literal_* requires a string literal");
                }
            }
        }
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecNeg | UnaryOpItem::SpecCastInteger | UnaryOpItem::SpecGhostTracked(_))) => {
            // handled separately later
        }
        Some(VerusItem::Spec(spec_item)) => match spec_item {
            SpecItem::NoMethodBody => {
                return mk_expr(ExprX::Header(Arc::new(HeaderExprX::NoMethodBody)));
            }
            SpecItem::Requires | SpecItem::Recommends => {
                unsupported_err_unless!(len == 1, expr.span, "expected requires/recommends", &args);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                        return err_span(arg.span, "requires/recommends needs a bool expression");
                    }
                }
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = match spec_item {
                    SpecItem::Requires => Arc::new(HeaderExprX::Requires(Arc::new(vir_args))),
                    SpecItem::Recommends => Arc::new(HeaderExprX::Recommends(Arc::new(vir_args))),
                    _ => unreachable!(),
                };
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::OpensInvariants | SpecItem::OpensInvariantsExcept => {
                return err_span(
                    expr.span,
                    "'is_opens_invariants' and 'is_opens_invariants_except' are not yet implemented",
                );
            }
            SpecItem::OpensInvariantsNone => {
                let header = Arc::new(HeaderExprX::InvariantOpens(Arc::new(Vec::new())));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::OpensInvariantsAny => {
                let header = Arc::new(HeaderExprX::InvariantOpensExcept(Arc::new(Vec::new())));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Ensures => {
                unsupported_err_unless!(len == 1, expr.span, "expected ensures", &args);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let header = extract_ensures(&bctx, args[0])?;
                let expr = mk_expr_span(args[0].span, ExprX::Header(header));
                // extract_ensures does most of the necessary work, so we can return at this point
                return expr;
            }
            SpecItem::Decreases => {
                unsupported_err_unless!(len == 1, expr.span, "expected decreases", &args);
                let subargs = extract_tuple(args[0]);
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = Arc::new(HeaderExprX::Decreases(Arc::new(vir_args)));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Invariant | SpecItem::InvariantEnsures => {
                unsupported_err_unless!(len == 1, expr.span, "expected invariant", &args);
                let subargs = extract_array(args[0]);
                for arg in &subargs {
                    if !matches!(bctx.types.node_type(arg.hir_id).kind(), TyKind::Bool) {
                        return err_span(arg.span, "invariant needs a bool expression");
                    }
                }
                let bctx = &BodyCtxt { external_body: false, in_ghost: true, ..bctx.clone() };
                let vir_args =
                    vec_map_result(&subargs, |arg| expr_to_vir(&bctx, arg, ExprModifier::REGULAR))?;
                let header = match spec_item {
                    SpecItem::Invariant => Arc::new(HeaderExprX::Invariant(Arc::new(vir_args))),
                    SpecItem::InvariantEnsures => Arc::new(HeaderExprX::InvariantEnsures(Arc::new(vir_args))),
                    _ => unreachable!(),
                };
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::DecreasesBy | SpecItem::RecommendsBy => {
                unsupported_err_unless!(len == 1, expr.span, "expected function", &args);
                let x = get_fn_path(bctx, &args[0])?;
                let header = Arc::new(HeaderExprX::DecreasesBy(x));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::DecreasesWhen | SpecItem::Admit | SpecItem::Assume => {
                // handled later, they require VIR args
            }
        },
        Some(VerusItem::Quant(quant_item)) => {
            unsupported_err_unless!(len == 1, expr.span, "expected forall/exists", &args);
            let quant = match quant_item {
                QuantItem::Forall | QuantItem::ForallArith => air::ast::Quant::Forall,
                QuantItem::Exists => air::ast::Quant::Exists,
            };
            let quant = Quant { quant, boxed_params: quant_item != &QuantItem::ForallArith };
            return extract_quant(bctx, expr.span, quant, args[0]);
        },
        Some(VerusItem::Directive(directive_item)) => match directive_item {
            DirectiveItem::ExtraDependency | DirectiveItem::Hide | DirectiveItem::Reveal => {
                unsupported_err_unless!(len == 1, expr.span, "expected hide/reveal", &args);
                let x = get_fn_path(bctx, &args[0])?;
                match directive_item {
                    DirectiveItem::Hide => {
                        let header = Arc::new(HeaderExprX::Hide(x));
                        return mk_expr(ExprX::Header(header));
                    }
                    DirectiveItem::ExtraDependency => {
                        let header = Arc::new(HeaderExprX::ExtraDependency(x));
                        return mk_expr(ExprX::Header(header));
                    }
                    DirectiveItem::Reveal => {
                        return mk_expr(ExprX::Fuel(x, 1));
                    }
                    _ => unreachable!(),
                }
            }
            DirectiveItem::RevealFuel => {
                unsupported_err_unless!(len == 2, expr.span, "expected reveal_fuel", &args);
                let x = get_fn_path(bctx, &args[0])?;
                match &expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?.x {
                    ExprX::Const(Constant::Int(i)) => {
                        let n =
                            vir::ast_util::const_int_to_u32(&bctx.ctxt.spans.to_air_span(expr.span), i)?;
                        return mk_expr(ExprX::Fuel(x, n));
                    }
                    _ => panic!("internal error: is_reveal_fuel"),
                }
            }
            DirectiveItem::RevealStrlit => {
                if let Some(s) = if let ExprKind::Lit(lit0) = &args[0].kind {
                    if let rustc_ast::LitKind::Str(s, _) = lit0.node { Some(s) } else { None }
                } else {
                    None
                } {
                    return mk_expr(ExprX::RevealString(Arc::new(s.to_string())));
                } else {
                    return err_span(args[0].span, "string literal expected".to_string());
                }
            }
        },
        Some(VerusItem::Expr(expr_item)) => match expr_item {
            crate::verus_items::ExprItem::Choose => {
                unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
                return extract_choose(bctx, expr.span, args[0], false, expr_typ()?);
            }
            crate::verus_items::ExprItem::ChooseTuple => {
                unsupported_err_unless!(len == 1, expr.span, "expected choose", &args);
                return extract_choose(bctx, expr.span, args[0], true, expr_typ()?);
            }
            crate::verus_items::ExprItem::Old => {
                if let ExprKind::Path(QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. })) =
                    &args[0].kind
                {
                    if let Node::Pat(pat) = tcx.hir().get(*id) {
                        let typ = typ_of_node_expect_mut_ref(bctx, args[0].span, &expr.hir_id)?;
                        return Ok(bctx.spanned_typed_new(
                            expr.span,
                            &typ,
                            ExprX::VarAt(Arc::new(pat_to_var(pat)?), VarAt::Pre),
                        ));
                    }
                }
                return err_span(expr.span, "only a variable binding is allowed as the argument to old");
            }
            crate::verus_items::ExprItem::StrSliceLen => {
                return match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrLen, arg0))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_len with one argument but did not receive it"
                    ),
                };
            }
            crate::verus_items::ExprItem::StrSliceGetChar => {
                return match &expr.kind {
                    ExprKind::Call(_, args) if args.len() == 2 => {
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR).expect(
                            "invalid parameter for builtin::strslice_get_char at arg0, arg0 must be self",
                        );
                        let arg1 = &args[1];
                        let arg1 = expr_to_vir(bctx, arg1, ExprModifier::REGULAR)
                            .expect("invalid parameter for builtin::strslice_get_char at arg1, arg1 must be an integer");
                        mk_expr(ExprX::Binary(BinaryOp::StrGetChar, arg0, arg1))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_get_char with two argument but did not receive it"
                    ),
                };
            }
            crate::verus_items::ExprItem::StrSliceIsAscii => {
                return match &expr.kind {
                    ExprKind::Call(_, args) => {
                        assert!(args.len() == 1);
                        let arg0 = args.first().unwrap();
                        let arg0 = expr_to_vir(bctx, arg0, ExprModifier::REGULAR)
                            .expect("internal compiler error");
                        mk_expr(ExprX::Unary(UnaryOp::StrIsAscii, arg0))
                    }
                    _ => panic!(
                        "Expected a call for builtin::strslice_is_ascii with one argument but did not receive it"
                    ),
                };
            }
            crate::verus_items::ExprItem::ArchWordBits => {
                assert!(args.len() == 0);
                let arg = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Int(IntRange::Int)),
                    ExprX::Const(vir::ast_util::const_int_from_u128(0)),
                );

                let kind = IntegerTypeBoundKind::ArchWordBits;

                return mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg));
            }
            ExprItem::ClosureToFnSpec => {
                unsupported_err_unless!(len == 1, expr.span, "expected closure_to_spec_fn", &args);
                if let ExprKind::Closure(..) = &args[0].kind {
                    return closure_to_vir(bctx, &args[0], expr_typ()?, true, ExprModifier::REGULAR);
                } else {
                    return err_span(
                        args[0].span,
                        "the argument to `closure_to_spec_fn` must be a closure",
                    );
                }
            }
            ExprItem::SignedMin | ExprItem::SignedMax | ExprItem::UnsignedMax => {
                assert!(args.len() == 1);
                let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let kind = match expr_item {
                    ExprItem::SignedMin => IntegerTypeBoundKind::SignedMin,
                    ExprItem::SignedMax => IntegerTypeBoundKind::SignedMax,
                    ExprItem::UnsignedMax => IntegerTypeBoundKind::UnsignedMax,
                    _ => unreachable!(),
                };
                return mk_expr(ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, Mode::Spec), arg));
            }
            ExprItem::Height => {
                assert!(args.len() == 1);
                let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::UnaryOpr(UnaryOpr::Height, arg));
            }
        },
        Some(VerusItem::CompilableOpr(compilable_opr)) => match compilable_opr {
            CompilableOprItem::NewStrLit => {
                let s = if let ExprKind::Lit(lit0) = &args[0].kind {
                    if let rustc_ast::LitKind::Str(s, _) = lit0.node {
                        s
                    } else {
                        panic!("unexpected arguments to new_strlit")
                    }
                } else {
                    panic!("unexpected arguments to new_strlit")
                };

                let c = vir::ast::Constant::StrSlice(Arc::new(s.to_string()));
                return mk_expr(ExprX::Const(c));
            }
            _ => {
                // handled later, they require VIR args
            }
        },
        Some(VerusItem::BinaryOp(_) | VerusItem::Chained(_)) => {
            // handled elsewhere
        }
        Some(VerusItem::Assert(assert_item)) => match assert_item {
            AssertItem::Assert => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert", &args);
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertAssume { is_assume: false, expr: exp });
            }
            AssertItem::AssertBy => {
                unsupported_err_unless!(len == 2, expr.span, "expected assert_by", &args);
                let vars = Arc::new(vec![]);
                let require = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(true)),
                );
                let ensure = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let proof = expr_to_vir(bctx, &args[1], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::Forall { vars, require, ensure, proof });
            }
            AssertItem::AssertByCompute => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert_by_compute", &args);
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertCompute(exp, ComputeMode::Z3));
            }
            AssertItem::AssertByComputeOnly => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert_by_compute_only", &args);
                let exp = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                return mk_expr(ExprX::AssertCompute(exp, ComputeMode::ComputeOnly));
            }
            AssertItem::AssertNonlinearBy | AssertItem::AssertBitvectorBy => {
                unsupported_err_unless!(
                    len == 1,
                    expr.span,
                    "expected assert_nonlinear_by/assert_bitvector_by with one argument",
                    &args
                );
                let mut vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let header = vir::headers::read_header(&mut vir_expr)?;
                let requires = if header.require.len() >= 1 {
                    header.require
                } else {
                    Arc::new(vec![bctx.spanned_typed_new(
                        expr.span,
                        &Arc::new(TypX::Bool),
                        ExprX::Const(Constant::Bool(true)),
                    )])
                };
                if header.ensure.len() == 0 {
                    return err_span(
                        expr.span,
                        "assert_nonlinear_by/assert_bitvector_by must have at least one ensures",
                    );
                }
                let ensures = header.ensure;
                let proof = vir_expr;

                let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                if expr_vattrs.spinoff_prover {
                    return err_span(
                        expr.span,
                        "#[verifier(spinoff_prover)] is implied for assert by nonlinear_arith and assert by bit_vector",
                    );
                }
                return mk_expr(ExprX::AssertQuery {
                    requires,
                    ensures,
                    proof,
                    mode: match assert_item {
                        AssertItem::AssertNonlinearBy => AssertQueryMode::NonLinear,
                        AssertItem::AssertBitvectorBy => AssertQueryMode::BitVector,
                        _ => unreachable!(),
                    },
                });
            }
            AssertItem::AssertForallBy => {
                unsupported_err_unless!(len == 1, expr.span, "expected assert_forall_by", &args);
                return extract_assert_forall_by(bctx, expr.span, args[0]);
            }
            // internally translate this into `assert_bitvector_by`. REVIEW: consider deprecating this at all
            AssertItem::AssertBitVector => {
                let vir_expr = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;
                let requires = Arc::new(vec![bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(true)),
                )]);
                let ensures = Arc::new(vec![vir_expr]);
                let proof = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Tuple(Arc::new(vec![]))),
                    ExprX::Block(Arc::new(vec![]), None),
                );
                return mk_expr(ExprX::AssertQuery {
                    requires,
                    ensures,
                    proof,
                    mode: AssertQueryMode::BitVector,
                });
            }
        }
        Some(VerusItem::WithTriggers) => {
            unsupported_err_unless!(len == 2, expr.span, "expected with_triggers", &args);
            let modifier = ExprModifier::REGULAR;
            let triggers_tuples = expr_to_vir(bctx, args[0], modifier)?;
            let body = expr_to_vir(bctx, args[1], modifier)?;
            let mut trigs: Vec<vir::ast::Exprs> = Vec::new();
            if let ExprX::Tuple(triggers) = &triggers_tuples.x {
                for trigger_tuple in triggers.iter() {
                    if let ExprX::Tuple(terms) = &trigger_tuple.x {
                        trigs.push(terms.clone());
                    } else {
                        return err_span(expr.span, "expected tuple arguments to with_triggers");
                    }
                }
            } else {
                return err_span(expr.span, "expected tuple arguments to with_triggers");
            }
            let triggers = Arc::new(trigs);
            return mk_expr(ExprX::WithTriggers { triggers, body });
        }
        Some(VerusItem::OpenInvariantBlock(_) | VerusItem::Pervasive(_, _) | VerusItem::Marker(_) | VerusItem::BuiltinType(_) | VerusItem::BuiltinFunction(_)) => {
        }
        None => (),
    }

    if is_smartptr_new {
        unsupported_err_unless!(len == 1, expr.span, "expected 1 argument", &args);
        let arg = expr_to_vir(bctx, &args[0], ExprModifier::REGULAR)?;

        return Ok(arg);
    }

    // TODO(main_new) is calling `subst` still correct with the new API?
    let raw_inputs =
        EarlyBinder(bctx.ctxt.tcx.fn_sig(f)).subst(tcx, node_substs).skip_binder().inputs();
    assert!(raw_inputs.len() == args.len());
    let vir_args = args
        .iter()
        .zip(raw_inputs)
        .map(|(arg, raw_param)| {
            let is_mut_ref_param = match raw_param.kind() {
                TyKind::Ref(_, _, rustc_hir::Mutability::Mut) => true,
                _ => false,
            };
            if matches!(verus_item, Some(
                VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut) |
                VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut))
            )) {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, outer_modifier)?)
            } else if is_mut_ref_param {
                let arg_x = match &arg.kind {
                    ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, e) => e,
                    _ => arg,
                };
                let deref_mut = match bctx.types.node_type(arg_x.hir_id).ref_mutability() {
                    Some(Mutability::Mut) => true,
                    _ => false,
                };
                let expr = expr_to_vir(bctx, arg_x, ExprModifier { addr_of: true, deref_mut })?;
                Ok(bctx.spanned_typed_new(arg.span, &expr.typ.clone(), ExprX::Loc(expr)))
            } else {
                expr_to_vir(bctx, arg, is_expr_typ_mut_ref(bctx, arg, ExprModifier::REGULAR)?)
            }
        })
        .collect::<Result<Vec<_>, _>>()?;

    match is_get_variant {
        Some((variant_name, None)) => {
            return mk_expr(ExprX::UnaryOpr(
                UnaryOpr::IsVariant {
                    datatype: self_path.expect("not builtin"),
                    variant: str_ident(&variant_name),
                },
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            ));
        }
        Some((variant_name, Some(variant_field))) => {
            let variant_name_ident = str_ident(&variant_name);
            return mk_expr(ExprX::UnaryOpr(
                UnaryOpr::Field(FieldOpr {
                    datatype: self_path.clone().expect("not builtin"),
                    variant: variant_name_ident.clone(),
                    field: match variant_field {
                        GetVariantField::Named(n) => str_ident(&n),
                        GetVariantField::Unnamed(i) => positional_field_ident(i),
                    },
                    get_variant: true,
                }),
                vir_args.into_iter().next().expect("missing arg for is_variant"),
            ));
        }
        None => {}
    }

    let is_smt_unary = if verus_item == Some(&VerusItem::UnaryOp(UnaryOpItem::SpecNeg)) {
        match *undecorate_typ(&typ_of_node(bctx, args[0].span, &args[0].hir_id, false)?) {
            TypX::Int(_) => true,
            _ => false,
        }
    } else {
        false
    };
    let is_smt_binary = match verus_item {
        Some(verus_item) => match verus_item {
            VerusItem::BinaryOp(BinaryOpItem::Equality(
                EqualityItem::Equal |
                EqualityItem::ExtEqual |
                EqualityItem::ExtEqualDeep
            )) => true,
            VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::SpecEq)) => {
                let t1 = typ_of_node(bctx, args[0].span, &args[0].hir_id, true)?;
                let t2 = typ_of_node(bctx, args[1].span, &args[1].hir_id, true)?;
                // REVIEW: there's some code that (harmlessly) uses == on types that are
                // different in decoration; Rust would reject this, but we currently allow it:
                let t1 = undecorate_typ(&t1);
                let t2 = undecorate_typ(&t2);
                if types_equal(&t1, &t2)
                    || is_smt_arith(bctx, args[0].span, args[1].span, &args[0].hir_id, &args[1].hir_id)?
                {
                    true
                } else {
                    return err_span(expr.span, "types must be compatible to use == or !=");
                }
            }
            VerusItem::CompilableOpr(CompilableOprItem::Implies) |
                VerusItem::BinaryOp(BinaryOpItem::Arith(_) | BinaryOpItem::SpecArith(_) | BinaryOpItem::SpecBitwise(_) | BinaryOpItem::SpecOrd(_)) => {
                is_smt_arith(bctx, args[0].span, args[1].span, &args[0].hir_id, &args[1].hir_id)?
            }
            _ => false
        }
        None => false,
    };

    match verus_item {
        Some(VerusItem::CompilableOpr(compilable_opr)) => match compilable_opr {
            CompilableOprItem::GhostExec | CompilableOprItem::TrackedExec => {
                // Handle some of the is_ghost_exec || is_tracked_exec cases here
                // (specifically, the exec-mode cases)
                unsupported_err_unless!(len == 1, expr.span, "expected Ghost/Tracked", &args);
                let arg = &args[0];
                if get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(expr.hir_id))
                    == Some(GhostBlockAttr::Wrapper)
                {
                    let vir_arg = vir_args[0].clone();
                    match (compilable_opr, get_ghost_block_opt(bctx.ctxt.tcx.hir().attrs(arg.hir_id))) {
                        (CompilableOprItem::GhostExec, Some(GhostBlockAttr::GhostWrapped)) => {
                            let exprx =
                                ExprX::Ghost { alloc_wrapper: true, tracked: false, expr: vir_arg.clone() };
                            return Ok(bctx.spanned_typed_new(arg.span, &vir_arg.typ.clone(), exprx));
                        }
                        (CompilableOprItem::TrackedExec, Some(GhostBlockAttr::TrackedWrapped)) => {
                            let exprx =
                                ExprX::Ghost { alloc_wrapper: true, tracked: true, expr: vir_arg.clone() };
                            return Ok(bctx.spanned_typed_new(arg.span, &vir_arg.typ.clone(), exprx));
                        }
                        (_, attr) => {
                            return err_span(
                                expr.span,
                                format!("unexpected ghost block attribute {:?}", attr),
                            );
                        }
                    }
                }
            }
            _ => {
                // handled later
            }
        }
        Some(VerusItem::Spec(spec_item)) => match spec_item {
            SpecItem::DecreasesWhen => {
                unsupported_err_unless!(len == 1, expr.span, "expected decreases_when", &args);
                let header = Arc::new(HeaderExprX::DecreasesWhen(vir_args[0].clone()));
                return mk_expr(ExprX::Header(header));
            }
            SpecItem::Admit => {
                unsupported_err_unless!(len == 0, expr.span, "expected admit", args);
                let f = bctx.spanned_typed_new(
                    expr.span,
                    &Arc::new(TypX::Bool),
                    ExprX::Const(Constant::Bool(false)),
                );
                return mk_expr(ExprX::AssertAssume { is_assume: true, expr: f });
            }
            SpecItem::Assume => {
                unsupported_err_unless!(len == 1, expr.span, "expected assume", args);
                return mk_expr(ExprX::AssertAssume { is_assume: true, expr: vir_args[0].clone() });
            }
            _ => unreachable!(),
        }
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecCastInteger)) => {
            unsupported_err_unless!(len == 1, expr.span, "spec_cast_integer", args);
            let source_vir = vir_args[0].clone();
            let source_ty = undecorate_typ(&source_vir.typ);
            let to_ty = undecorate_typ(&expr_typ()?);
            match (&*source_ty, &*to_ty) {
                (TypX::Int(IntRange::U(_)), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::USize), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::Nat), TypX::Int(IntRange::Nat)) => return Ok(source_vir),
                (TypX::Int(IntRange::Int), TypX::Int(IntRange::Nat)) => {
                    return Ok(mk_ty_clip(&to_ty, &source_vir, true));
                }
                (TypX::Int(_), TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                    return Ok(mk_ty_clip(&to_ty, &source_vir, expr_vattrs.truncate));
                }
                (TypX::Char, TypX::Int(_)) => {
                    let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                    let expr_vattrs = get_verifier_attrs(expr_attrs)?;
                    let source_unicode = mk_expr(ExprX::Unary(UnaryOp::CharToInt, source_vir.clone()))?;
                    return Ok(mk_ty_clip(&to_ty, &source_unicode, expr_vattrs.truncate));
                }
                _ => {
                    return err_span(
                        expr.span,
                        "Verus currently only supports casts from integer types and `char` to integer types",
                    );
                }
            }
        }
        _ => (),
    }

    if is_smt_unary {
        unsupported_err_unless!(len == 1, expr.span, "expected unary op", args);
        let varg = vir_args[0].clone();
        match verus_item {
            Some(&VerusItem::UnaryOp(UnaryOpItem::SpecNeg)) => {
                let zero_const = vir::ast_util::const_int_from_u128(0);
                let zero = mk_expr(ExprX::Const(zero_const))?;
                mk_expr(ExprX::Binary(BinaryOp::Arith(ArithOp::Sub, None), zero, varg))
            }
            _ => unreachable!("internal error")
        }
    } else if is_smt_binary {
        unsupported_err_unless!(len == 2, expr.span, "expected binary op", args);
        let lhs = vir_args[0].clone();
        let rhs = vir_args[1].clone();
        if let Some(
            VerusItem::BinaryOp(BinaryOpItem::Equality(ei@(EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep)))
        ) = verus_item {
            assert!(node_substs.len() == 1);
            let t = match node_substs[0].unpack() {
                GenericArgKind::Type(ty) => mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, expr.span, &ty, false)?,
                _ => panic!("unexpected ext_equal type argument"),
            };
            let vop = vir::ast::BinaryOpr::ExtEq(ei == &EqualityItem::ExtEqualDeep, t);
            return Ok(mk_expr(ExprX::BinaryOpr(vop, lhs, rhs))?);
        }
        let vop = match verus_item.expect("internal error") {
            VerusItem::BinaryOp(BinaryOpItem::Equality(equality_item)) => match equality_item {
                EqualityItem::Equal | EqualityItem::SpecEq => BinaryOp::Eq(Mode::Spec),
                EqualityItem::ExtEqual | EqualityItem::ExtEqualDeep => unreachable!(),
            }
            VerusItem::BinaryOp(BinaryOpItem::SpecOrd(spec_ord_item)) => match spec_ord_item {
                SpecOrdItem::Le => BinaryOp::Inequality(InequalityOp::Le),
                SpecOrdItem::Ge => BinaryOp::Inequality(InequalityOp::Ge),
                SpecOrdItem::Lt => BinaryOp::Inequality(InequalityOp::Lt),
                SpecOrdItem::Gt => BinaryOp::Inequality(InequalityOp::Gt),
            }
            VerusItem::BinaryOp(BinaryOpItem::Arith(arith_item)) => match arith_item {
                ArithItem::BuiltinAdd => BinaryOp::Arith(ArithOp::Add, Some(bctx.ctxt.infer_mode())),
                ArithItem::BuiltinSub => BinaryOp::Arith(ArithOp::Sub, Some(bctx.ctxt.infer_mode())),
                ArithItem::BuiltinMul => BinaryOp::Arith(ArithOp::Mul, Some(bctx.ctxt.infer_mode())),
            }
            VerusItem::BinaryOp(BinaryOpItem::SpecArith(spec_arith_item)) => match spec_arith_item {
                SpecArithItem::Add => BinaryOp::Arith(ArithOp::Add, None),
                SpecArithItem::Sub => BinaryOp::Arith(ArithOp::Sub, None),
                SpecArithItem::Mul => BinaryOp::Arith(ArithOp::Mul, None),
                SpecArithItem::EuclideanDiv => BinaryOp::Arith(ArithOp::EuclideanDiv, None),
                SpecArithItem::EuclideanMod => BinaryOp::Arith(ArithOp::EuclideanMod, None),
            }
            VerusItem::BinaryOp(BinaryOpItem::SpecBitwise(spec_bitwise)) => match spec_bitwise {
                verus_items::SpecBitwiseItem::BitAnd => BinaryOp::Bitwise(BitwiseOp::BitAnd, Mode::Spec),
                verus_items::SpecBitwiseItem::BitOr => BinaryOp::Bitwise(BitwiseOp::BitOr, Mode::Spec),
                verus_items::SpecBitwiseItem::BitXor => {
                    if matches!(*vir_args[0].typ, TypX::Bool) {
                        BinaryOp::Xor
                    } else {
                        BinaryOp::Bitwise(BitwiseOp::BitXor, Mode::Spec)
                    }
                },
                verus_items::SpecBitwiseItem::Shl => BinaryOp::Bitwise(BitwiseOp::Shl, Mode::Spec),
                verus_items::SpecBitwiseItem::Shr => BinaryOp::Bitwise(BitwiseOp::Shr, Mode::Spec),
            }
            VerusItem::CompilableOpr(CompilableOprItem::Implies) => BinaryOp::Implies,
            _ => unreachable!("internal error"),
        };
        let e = mk_expr(ExprX::Binary(vop, lhs, rhs))?;
        if matches!(verus_item, Some(
            VerusItem::BinaryOp(BinaryOpItem::Arith(_) | BinaryOpItem::SpecArith(_))
        )) {
            Ok(mk_ty_clip(&expr_typ()?, &e, true))
        } else {
            Ok(e)
        }
    } else if let Some(VerusItem::Chained(chained_item)) = verus_item {
        match chained_item {
            ChainedItem::Value => {
                unsupported_err_unless!(len == 1, expr.span, "spec_chained_value", &args);
                unsupported_err_unless!(
                    matches!(*undecorate_typ(&vir_args[0].typ), TypX::Int(_)),
                    expr.span,
                    "chained inequalities for non-integer types",
                    &args
                );
                let exprx =
                    ExprX::Multi(MultiOp::Chained(Arc::new(vec![])), Arc::new(vec![vir_args[0].clone()]));
                Ok(bctx.spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
            }
            ChainedItem::Cmp => {
                unsupported_err_unless!(len == 1, expr.span, "spec_chained_cmp", args);
                Ok(vir_args[0].clone())
            }
            ChainedItem::Le |
            ChainedItem::Lt |
            ChainedItem::Ge |
            ChainedItem::Gt => {
                unsupported_err_unless!(len == 2, expr.span, "chained inequality", &args);
                unsupported_err_unless!(
                    matches!(&vir_args[0].x, ExprX::Multi(MultiOp::Chained(_), _)),
                    expr.span,
                    "chained inequalities for non-integer types",
                    &args
                );
                unsupported_err_unless!(
                    matches!(*undecorate_typ(&vir_args[1].typ), TypX::Int(_)),
                    expr.span,
                    "chained inequalities for non-integer types",
                    &args
                );
                let op = match chained_item {
                    ChainedItem::Le => InequalityOp::Le,
                    ChainedItem::Lt => InequalityOp::Lt,
                    ChainedItem::Ge => InequalityOp::Ge,
                    ChainedItem::Gt => InequalityOp::Gt,
                    ChainedItem::Value | ChainedItem::Cmp => unreachable!(),
                };
                if let ExprX::Multi(MultiOp::Chained(ops), es) = &vir_args[0].x {
                    let mut ops = (**ops).clone();
                    let mut es = (**es).clone();
                    ops.push(op);
                    es.push(vir_args[1].clone());
                    let exprx = ExprX::Multi(MultiOp::Chained(Arc::new(ops)), Arc::new(es));
                    Ok(bctx.spanned_typed_new(expr.span, &Arc::new(TypX::Bool), exprx))
                } else {
                    panic!("is_chained_ineq")
                }
            }
        }
    } else if let Some(
        VerusItem::CompilableOpr(CompilableOprItem::GhostNew) |
        VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
            SpecGhostTrackedItem::GhostView |
            SpecGhostTrackedItem::GhostBorrow |
            SpecGhostTrackedItem::TrackedView
        ))
    ) = verus_item {
        assert!(vir_args.len() == 1);
        let is_ghost_new = verus_item == Some(&VerusItem::CompilableOpr(CompilableOprItem::GhostNew));
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Spec,
            from_mode: Mode::Spec,
            to_mode: if is_ghost_new { Mode::Proof } else { Mode::Spec },
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item,
        Some(VerusItem::CompilableOpr(CompilableOprItem::GhostExec))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Spec,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item,
        Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedNew))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item,
        Some(VerusItem::CompilableOpr(
            CompilableOprItem::TrackedExec | CompilableOprItem::TrackedExecBorrow
        ))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Exec,
            from_mode: Mode::Proof,
            to_mode: Mode::Exec,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item,
        Some(VerusItem::CompilableOpr(
            CompilableOprItem::TrackedGet | CompilableOprItem::TrackedBorrow
        ))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::Other,
        };
        mk_expr(ExprX::Unary(op, vir_args[0].clone()))
    } else if matches!(verus_item,
        Some(VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(SpecGhostTrackedItem::GhostBorrowMut)))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Spec,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
        Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else if matches!(verus_item,
        Some(VerusItem::CompilableOpr(CompilableOprItem::TrackedBorrowMut))) {
        assert!(vir_args.len() == 1);
        let op = UnaryOp::CoerceMode {
            op_mode: Mode::Proof,
            from_mode: Mode::Proof,
            to_mode: Mode::Proof,
            kind: ModeCoercion::BorrowMut,
        };
        let typ = typ_of_node(bctx, expr.span, &expr.hir_id, true)?;
        Ok(bctx.spanned_typed_new(expr.span, &typ, ExprX::Unary(op, vir_args[0].clone())))
    } else {
        let name = name.expect("not builtin");

        // filter out the Fn type parameters
        let mut fn_params: Vec<Ident> = Vec::new();
        for (x, _) in tcx.predicates_of(f).predicates {
            if let PredicateKind::Clause(Clause::Trait(t)) = x.kind().skip_binder() {
                let trait_ref_def_id = t.trait_ref.def_id;
                if let Some(RustItem::Fn) = verus_items::get_rust_item(tcx, trait_ref_def_id) {
                    for s in t.trait_ref.substs {
                        if let GenericArgKind::Type(ty) = s.unpack() {
                            if let TypX::TypParam(x) = &*mid_ty_to_vir(tcx, &bctx.ctxt.verus_items, expr.span, &ty, false)?
                            {
                                fn_params.push(x.clone());
                            }
                        }
                    }
                }
            }
        }

        // type arguments
        let typ_args = mk_typ_args(node_substs)?;
        let target = CallTarget::Fun(target_kind, name, typ_args, autospec_usage);
        Ok(bctx.spanned_typed_new(expr.span, &expr_typ()?, ExprX::Call(target, Arc::new(vir_args))))
    }
}

