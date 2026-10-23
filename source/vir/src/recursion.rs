use crate::ast::{
    AutospecUsage, CallTarget, CallTargetKind, Constant, CrateId, Dt, ExprX, Fun, Function,
    FunctionKind, GenericBoundX, ImplPath, IntRange, Path, SpannedTyped, TraitId, Typ, TypX, Typs,
    UnaryOpr, VarBinder, VirErr,
};
use crate::ast_to_sst::PreLocalDecl;
use crate::ast_to_sst::expr_to_exp_skip_checks;
use crate::ast_to_sst_func::params_to_pars;
use crate::ast_util::undecorate_typ;
use crate::ast_util::{air_unique_var, ident_var_binder, typ_to_diagnostic_str};
use crate::context::{Ctx, GraphBuilder};
use crate::def::{
    FUEL_PARAM, FUEL_TYPE, Spanned, decrease_at_entry, rename_rec_param, unique_bound, unique_local,
};
use crate::messages::{Span, error};
use crate::scc::{FxHashMap, Graph, NodeIndex};
use crate::sst::{
    BndX, CallFun, Dest, Exp, ExpX, Exps, InternalFun, LocalDecl, LocalDeclX, Stm, StmX,
    UniqueIdent,
};
use crate::sst_visitor::{exp_rename_vars, map_exp_visitor, map_stm_visitor};
use crate::util::vec_map_result;
use air::ast_util::str_typ;
use air::messages::Diagnostics;
use std::collections::{HashMap, HashSet};
use std::hash::BuildHasher;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Fun(Fun),
    Datatype(Dt),
    Trait(Path),
    TraitImpl(ImplPath),
    TraitReqEns(ImplPath, bool),
    ModuleReveal(Path),
    // Everything in crate c depends on Crate(c)
    // Crate(c) can depend on broadcast_use_by_default_when_this_crate_is_imported from other crates
    Crate(CrateId),
    // This is used to replace an X --> Y edge with X --> SpanInfo --> Y edges
    // to give more precise span information than X or Y alone provide
    SpanInfo { span_infos_index: usize, text: String },
}

// Same as the derived Hash, except that SpanInfo hashes only span_infos_index:
// equal nodes still hash equally (the derived Eq also compares the index),
// and each SpanInfo index is allocated once, so the text never needs hashing.
impl std::hash::Hash for Node {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Node::Fun(fun) => fun.hash(state),
            Node::Datatype(dt) => dt.hash(state),
            Node::Trait(path) => path.hash(state),
            Node::TraitImpl(impl_path) => impl_path.hash(state),
            Node::TraitReqEns(impl_path, b) => {
                impl_path.hash(state);
                b.hash(state);
            }
            Node::ModuleReveal(path) => path.hash(state),
            Node::Crate(krate) => krate.hash(state),
            Node::SpanInfo { span_infos_index, text: _ } => span_infos_index.hash(state),
        }
    }
}

#[derive(Clone)]
struct Ctxt<'a> {
    recursive_function_name: Fun,
    num_decreases: Option<usize>,
    scc_rep: Node,
    ctx: &'a Ctx,
    /// Types of the caller's decreases clauses (used to validate compatibility with callees)
    caller_decreases_typs: Vec<Typ>,
}

// Get edges, skipping past SpanInfo
pub(crate) fn get_edges_from<'a>(graph: &'a Graph<Node>, t: &Node) -> Vec<&'a Node> {
    let mut nodes: Vec<&'a Node> = Vec::new();
    for node in graph.get_edges_from(t) {
        if let Node::SpanInfo { .. } = node {
            nodes.extend(get_edges_from(graph, node));
        } else {
            nodes.push(node);
        }
    }
    nodes
}

pub(crate) fn get_callee(
    ctx: &Ctx,
    target: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
) -> Option<Fun> {
    if ctx.reveal_group_set.contains(target) {
        return Some(target.clone());
    }
    let fun = &ctx.func_map[target];
    if let FunctionKind::TraitMethodDecl { .. } = &fun.x.kind {
        resolved_method.clone().map(|(x, _)| x)
    } else {
        Some(target.clone())
    }
}

fn is_recursive_call(ctxt: &Ctxt, target: &Fun, resolved_method: &Option<(Fun, Typs)>) -> bool {
    if let Some(callee) = get_callee(ctxt.ctx, target, resolved_method) {
        let callee_node = Node::Fun(callee.clone());
        callee == ctxt.recursive_function_name
            || ctxt.ctx.global.func_call_graph.get_scc_rep(&callee_node) == ctxt.scc_rep
    } else {
        false
    }
}

pub fn height_is_int(typ: &Typ) -> bool {
    match &*undecorate_typ(typ) {
        TypX::Int(_) => true,
        _ => false,
    }
}

fn height_typ(_ctx: &Ctx, exp: &Exp) -> Typ {
    if height_is_int(&exp.typ) { Arc::new(TypX::Int(IntRange::Int)) } else { exp.typ.clone() }
}

fn exp_for_decrease(_ctx: &Ctx, exp: &Exp) -> Result<Exp, VirErr> {
    match &*undecorate_typ(&exp.typ) {
        TypX::Int(_) => Ok(exp.clone()),
        TypX::Datatype(..) => Ok(exp.clone()),
        _ => Err(error(
            &exp.span,
            format!(
                "internal error: unsupported type for decreases {}",
                typ_to_diagnostic_str(&exp.typ)
            ),
        )),
    }
}

pub(crate) fn check_decrease(
    ctx: &Ctx,
    span: &Span,
    loop_id: Option<u64>,
    exps: &Vec<Exp>,
    num_decreases: usize,
) -> Result<Exp, VirErr> {
    // When calling a function with more decreases clauses,
    // it's good enough to be equal on the shared decreases clauses
    // and to ignore the extra decreases clauses.
    let tbool = Arc::new(TypX::Bool);
    let when_equalx = ExpX::Const(Constant::Bool(num_decreases < exps.len()));
    let when_equal = SpannedTyped::new(span, &tbool, when_equalx);

    let mut dec_exp: Exp = when_equal;
    for (i, exp) in (0..num_decreases).zip(exps.iter()).rev() {
        let decreases_at_entryx = ExpX::Var(unique_local(&decrease_at_entry(loop_id, i)));
        let decreases_at_entry =
            SpannedTyped::new(&exp.span, &height_typ(ctx, exp), decreases_at_entryx);
        // 0 <= decreases_exp < decreases_at_entry

        let (args, call_fun) = {
            let call_fun = CallFun::InternalFun(InternalFun::CheckDecreaseHeight);
            // Coerce to Poly for loops (when we're called after poly.rs)
            // For recursive functions (loop_id.is_none()), poly.rs will handle this
            if loop_id.is_some() {
                let new = crate::poly::coerce_exp_to_poly(ctx, &exp_for_decrease(ctx, exp)?);
                let old = crate::poly::coerce_exp_to_poly(ctx, &decreases_at_entry);
                let args = vec![new, old, dec_exp];
                (args, call_fun)
            } else {
                let args = vec![exp_for_decrease(ctx, exp)?, decreases_at_entry, dec_exp];
                (args, call_fun)
            }
        };
        let call = ExpX::Call(call_fun, Arc::new(vec![]), Arc::new(args));
        dec_exp = SpannedTyped::new(&exp.span, &Arc::new(TypX::Bool), call);
    }
    Ok(dec_exp)
}

fn check_decrease_call(
    ctxt: &Ctxt,
    diagnostics: &impl Diagnostics,
    span: &Span,
    target: &Fun,
    resolved_method: &Option<(Fun, Typs)>,
    args: &Exps,
) -> Result<Exp, VirErr> {
    let name = if let Some(callee) = get_callee(ctxt.ctx, target, resolved_method) {
        callee
    } else {
        return Ok(SpannedTyped::new(
            span,
            &Arc::new(TypX::Bool),
            ExpX::Const(Constant::Bool(true)),
        ));
    };
    let function = &ctxt.ctx.func_map[&name];
    // check_decrease(let params = args in decreases_exp, decreases_at_entry)
    let params = &function.x.params;
    assert!(params.len() == args.len());
    let binders: Vec<VarBinder<Exp>> = params
        .iter()
        .zip(args.iter())
        .enumerate()
        .map(|(n, (param, arg))| {
            ident_var_binder(&rename_rec_param(&param.x.name, n), &arg.clone())
        })
        .collect();
    let renames: HashMap<UniqueIdent, UniqueIdent> = params
        .iter()
        .enumerate()
        .map(|(n, param)| {
            (unique_local(&param.x.name), unique_bound(&rename_rec_param(&param.x.name, n)))
        })
        .collect();
    let mut decreases_exps: Vec<Exp> = Vec::new();
    for expr in function.x.decrease.iter() {
        // use expr_to_exp_skip_checks here because checks in decreases done by func_def_to_air
        let decreases_exp = expr_to_exp_skip_checks(
            ctxt.ctx,
            diagnostics,
            &params_to_pars(&function.x.params),
            expr,
        )?;
        let dec_exp = exp_rename_vars(&decreases_exp, &renames);
        let e_decx = ExpX::Bind(
            Spanned::new(span.clone(), BndX::Let(Arc::new(binders.clone()))),
            dec_exp.clone(),
        );
        decreases_exps.push(SpannedTyped::new(&span, &dec_exp.typ, e_decx));
    }

    // Validate that the caller's and callee's decreases types are compatible.
    // All functions in a mutually recursive group must have decreases clauses
    // whose types match at each position (both int or both non-int).
    let num_decreases = ctxt.num_decreases.expect("num_decreases");
    let num_to_check = std::cmp::min(num_decreases, decreases_exps.len());
    for i in 0..num_to_check {
        let caller_is_int = height_is_int(&ctxt.caller_decreases_typs[i]);
        let callee_is_int = height_is_int(&decreases_exps[i].typ);
        if caller_is_int != callee_is_int {
            let caller_kind = if caller_is_int { "int" } else { "datatype" };
            let callee_kind = if callee_is_int { "int" } else { "datatype" };
            return Err(error(
                span,
                format!(
                    "in mutually recursive functions, decreases clauses at the same position \
                     must have compatible types: the caller's decreases clause #{} has {} type, \
                     but the callee's has {} type",
                    i + 1,
                    caller_kind,
                    callee_kind
                ),
            ));
        }
    }

    check_decrease(ctxt.ctx, span, None, &decreases_exps, num_decreases)
}

pub(crate) fn fun_is_recursive(ctx: &Ctx, function: &Function) -> bool {
    let name = &function.x.name;
    let node = Node::Fun(name.clone());
    ctx.global.func_call_graph.node_is_in_cycle(&node)
}

pub(crate) fn mk_decreases_at_entry(
    ctx: &Ctx,
    span: &Span,
    loop_id: Option<u64>,
    exps: &Vec<Exp>,
) -> Result<(Vec<LocalDecl>, Vec<Stm>), VirErr> {
    let mut decls: Vec<LocalDecl> = Vec::new();
    let mut stm_assigns: Vec<Stm> = Vec::new();
    for (i, exp) in exps.iter().enumerate() {
        let typ = height_typ(ctx, exp);
        let decl = Arc::new(LocalDeclX {
            ident: unique_local(&decrease_at_entry(loop_id, i)),
            typ: typ.clone(),
            kind: crate::sst::LocalDeclKind::Decreases,
        });
        let uniq_ident = unique_local(&decrease_at_entry(loop_id, i));
        let stm_assign = Spanned::new(
            span.clone(),
            StmX::Assign {
                lhs: Dest {
                    dest: SpannedTyped::new(&span, &typ, ExpX::VarLoc(uniq_ident)),
                    is_init: true,
                },
                rhs: exp_for_decrease(ctx, exp)?,
            },
        );
        decls.push(decl);
        stm_assigns.push(stm_assign);
    }
    Ok((decls, stm_assigns))
}

pub(crate) fn mk_decreases_at_entry_pre(
    ctx: &Ctx,
    loop_id: Option<u64>,
    exps: &Vec<Exp>,
) -> Result<Vec<PreLocalDecl>, VirErr> {
    let mut decls: Vec<PreLocalDecl> = Vec::new();
    for (i, exp) in exps.iter().enumerate() {
        let typ = height_typ(ctx, exp);
        let decl = PreLocalDecl {
            ident: unique_local(&decrease_at_entry(loop_id, i)),
            typ: typ.clone(),
            kind: crate::ast_to_sst::PreLocalDeclKind::Immutable(crate::ast_to_sst::Immutable(
                crate::sst::LocalDeclKind::Decreases,
            )),
        };
        decls.push(decl);
    }
    Ok(decls)
}

pub(crate) fn rewrite_spec_recursive_fun_with_fueled_rec_call(
    ctx: &Ctx,
    function: &crate::sst::FunctionSst,
    body: &Exp,
) -> Result<(Exp, crate::recursion::Node), VirErr> {
    let caller_node = Node::Fun(function.x.name.clone());
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&caller_node);
    if !function.x.has.is_recursive {
        return Ok((body.clone(), scc_rep));
    }
    if !function.x.has.has_decrease {
        return Err(error(&function.span, "recursive function must have a decreases clause"));
    }
    let ctxt = Ctxt {
        recursive_function_name: function.x.name.clone(),
        num_decreases: None,
        scc_rep: scc_rep.clone(),
        ctx,
        caller_decreases_typs: vec![], // Not used when num_decreases is None
    };

    // New body: substitute rec%f(args, fuel) for f(args)
    let resolve = |x: &Fun, typs: &Typs, resolved_method: &Option<(Fun, Typs)>| {
        if let Some((m, ts)) = resolved_method {
            (m.clone(), ts.clone())
        } else {
            (x.clone(), typs.clone())
        }
    };
    let body = map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(CallFun::Fun(x, resolved_method), typs, args)
            if is_recursive_call(&ctxt, x, resolved_method)
                && ctx.func_map[&resolve(x, typs, resolved_method).0].x.body.is_some() =>
        {
            let mut args = (**args).clone();
            let varx = ExpX::Var(unique_local(&air_unique_var(FUEL_PARAM)));
            let var_typ = Arc::new(TypX::Air(str_typ(FUEL_TYPE)));
            args.push(SpannedTyped::new(&exp.span, &var_typ, varx));
            let (name, ts) = resolve(x, typs, resolved_method);
            let callx = ExpX::Call(CallFun::Recursive(name), ts, Arc::new(args));
            SpannedTyped::new(&exp.span, &exp.typ, callx)
        }
        _ => exp.clone(),
    });

    Ok((body, scc_rep))
}

pub(crate) fn rewrite_rec_call_with_fuel_const(body: &Exp, fuel: usize) -> Exp {
    map_exp_visitor(&body, &mut |exp| match &exp.x {
        ExpX::Call(CallFun::Recursive(r), typs, args) => {
            let mut args = (**args).clone();
            let arg_fuel = args.last_mut().expect("args.last");
            *arg_fuel = arg_fuel.new_x(ExpX::FuelConst(fuel));
            exp.new_x(ExpX::Call(CallFun::Recursive(r.clone()), typs.clone(), Arc::new(args)))
        }
        _ => exp.clone(),
    })
}

fn check_termination<'a>(
    ctx: &'a Ctx,
    diagnostics: &impl Diagnostics,
    function: &Function,
    body: &Stm,
) -> Result<(Ctxt<'a>, Vec<Exp>, Stm), VirErr> {
    let num_decreases = function.x.decrease.len();
    if num_decreases == 0
        && (function.x.mode != crate::ast::Mode::Exec
            || (!function.x.attrs.exec_allows_no_decreases_clause
                && !function.x.attrs.exec_assume_termination))
    {
        let mut e = error(&function.span, "recursive function must have a decreases clause");
        if function.x.mode == crate::ast::Mode::Exec {
            e = e.help("to disable this check, use #[verifier::exec_allows_no_decreases_clause] on the function");
        }
        return Err(e);
    }

    // use expr_to_exp_skip_checks here because checks in decreases done by func_def_to_air
    let decreases_exps = vec_map_result(&function.x.decrease, |e| {
        expr_to_exp_skip_checks(ctx, diagnostics, &params_to_pars(&function.x.params), e)
    })?;
    let scc_rep = ctx.global.func_call_graph.get_scc_rep(&Node::Fun(function.x.name.clone()));
    let caller_decreases_typs: Vec<Typ> =
        decreases_exps.iter().map(|exp| height_typ(ctx, exp)).collect();
    let ctxt = Ctxt {
        recursive_function_name: function.x.name.clone(),
        num_decreases: Some(num_decreases),
        scc_rep,
        ctx,
        caller_decreases_typs,
    };
    let stm = map_stm_visitor(body, &mut |s| match &s.x {
        StmX::Call {
            fun: crate::sst::CallTarget::Fun(fun), resolved_method, args, dest, ..
        } if is_recursive_call(&ctxt, fun, resolved_method) => {
            let check =
                check_decrease_call(&ctxt, diagnostics, &s.span, fun, resolved_method, args)?;
            let error = error(&s.span, "could not prove termination");
            let stm_assert = Spanned::new(s.span.clone(), StmX::Assert(None, Some(error), check));

            let mut stms = vec![stm_assert, s.clone()];
            // REVIEW: when we support spec-ensures, we will need an assume here to get the ensures
            // of the recursive call just after it was proven to terminate
            // This is instead an interim fix for incompleteness in recommends checking, due to
            // the fact that we currently do not emit AIR calls to a spec function in the same SCC.
            // Even if we _did_ emit AIR calls to spec functions in the same SCC, they would be
            // uninterpreted, because the function definition axioms must be emitted later (so
            // they cannot be used to prove their own termination).
            // Because of this, the call's destination remains uninitialized, and lacks its typing
            // invariant, causeing imcompleteness (issue #564).
            // It _might_ be sound to emit just the functions' typing invariants first,
            // but we are not sure. So, as a partial fix for (some of) the resulting incompleteness),
            // we manually emit an assume with just the typing invariant of the destination.
            // It may be okay to emit this for non-spec functions too, but I have not checked, so
            // I'm restricting this to spec functions for now.
            if ctx.func_map[fun].x.mode == crate::ast::Mode::Spec {
                if let Some(Dest { dest, is_init: true }) = &dest {
                    let has_typx =
                        ExpX::UnaryOpr(UnaryOpr::HasType(dest.typ.clone()), dest.clone());
                    let has_typ = SpannedTyped::new(&s.span, &Arc::new(TypX::Bool), has_typx);
                    let has_typ_assume = Spanned::new(s.span.clone(), StmX::Assume(has_typ));
                    stms.push(has_typ_assume);
                }
            }
            let stm_block = Spanned::new(s.span.clone(), StmX::Block(Arc::new(stms)));
            Ok(stm_block)
        }
        StmX::Fuel(callee, fuel) if *fuel >= 1 => {
            let broadcast_forall = ctx.reveal_group_set.contains(callee)
                || ctx.func_map[callee].x.attrs.broadcast_forall;
            if broadcast_forall && is_recursive_call(&ctxt, callee, &None) {
                // This isn't needed for soundness, since the broadcast_forall axiom isn't
                // declared until after this SCC, but we might as well signal an error,
                // since this reveal will have no effect.
                return Err(error(&s.span, "cannot recursively use a broadcast proof fn"));
            }
            Ok(s.clone())
        }
        _ => Ok(s.clone()),
    })?;
    Ok((ctxt, decreases_exps, stm))
}

pub(crate) fn check_termination_stm(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    function: &Function,
    proof_body: Option<Stm>,
    body: &Stm,
    exec_with_no_termination_check: bool,
) -> Result<(Vec<LocalDecl>, crate::sst::Stms, Stm), VirErr> {
    if !fun_is_recursive(ctx, &function) {
        return Ok((vec![], Arc::new(vec![]), body.clone()));
    }

    if exec_with_no_termination_check && function.x.decrease.is_empty() {
        return Ok((vec![], Arc::new(vec![]), body.clone()));
    }

    let (ctxt, decreases_exps, stm) = check_termination(ctx, diagnostics, function, body)?;

    let (decls, stm_assigns) = mk_decreases_at_entry(&ctxt.ctx, &stm.span, None, &decreases_exps)?;
    let mut block_stms = stm_assigns.clone();
    if let Some(proof_body) = proof_body {
        block_stms.push(proof_body);
    }
    block_stms.push(stm.clone());
    let stm_block = Spanned::new(stm.span.clone(), StmX::Block(Arc::new(block_stms)));
    Ok((decls, Arc::new(stm_assigns), stm_block))
}

/// Node merge used by `GraphBuilder::replace` (context.rs) and the parallel call-graph recorder:
/// the node-merge map only has Trait and TraitImpl keys, so other nodes skip the lookup.
pub(crate) fn replace_node(replace_with: &HashMap<Node, Node>, value: Node) -> Node {
    if !matches!(value, Node::Trait(_) | Node::TraitImpl(_)) {
        return value;
    }
    if let Some(value) = replace_with.get(&value) { value.clone() } else { value }
}

/// Call-graph edges and span infos discovered for one function, recorded in discovery order.
/// Nodes are already merged by `replace_node` and interned locally: `nodes` lists each
/// distinct node once, in first-mention order, with its graph hash precomputed in `hashes`
/// (so the sequential replay does not hash), and `edges` refers to them by local index.
/// SpanInfo nodes carry indices local to `span_infos`; `replay` rebases (and rehashes) them.
pub(crate) struct CallGraphRecord {
    nodes: Vec<Node>,
    // hashes[i] == Graph::<Node>::hash_value(&nodes[i]) (for SpanInfo: of the local index)
    hashes: Vec<u64>,
    edges: Vec<(u32, u32)>,
    span_infos: Vec<Span>,
}

// Records up to this many distinct nodes are deduplicated by scanning `hashes`
const RECORD_LINEAR_DEDUP: usize = 32;

// a and b share their (Arc) allocation, so a == b
fn same_allocation(a: &Node, b: &Node) -> bool {
    match (a, b) {
        (Node::Fun(x), Node::Fun(y)) => Arc::ptr_eq(x, y),
        (Node::Trait(x), Node::Trait(y)) => Arc::ptr_eq(x, y),
        (
            Node::TraitImpl(ImplPath::TraitImplPath(x)),
            Node::TraitImpl(ImplPath::TraitImplPath(y)),
        ) => Arc::ptr_eq(x, y),
        _ => false,
    }
}

struct CallGraphRecorder<'a> {
    record: CallGraphRecord,
    replace_with: &'a HashMap<Node, Node>,
    // Local index of each node, only filled once there are more than RECORD_LINEAR_DEDUP
    // nodes (never iterated)
    node_index: FxHashMap<Node, u32>,
}

impl<'a> CallGraphRecorder<'a> {
    fn new(replace_with: &'a HashMap<Node, Node>) -> CallGraphRecorder<'a> {
        let record = CallGraphRecord {
            nodes: Vec::new(),
            hashes: Vec::new(),
            edges: Vec::new(),
            span_infos: Vec::new(),
        };
        CallGraphRecorder { record, replace_with, node_index: FxHashMap::default() }
    }

    fn local(&mut self, node: Node) -> u32 {
        let node = replace_node(self.replace_with, node);
        let r = &mut self.record;
        let len = r.nodes.len();
        if len <= RECORD_LINEAR_DEDUP {
            // Most repeated mentions reuse the same allocation (e.g. f_node), found without
            // hashing; equal allocations mean equal nodes, and nodes are distinct.
            for i in 0..len {
                if same_allocation(&r.nodes[i], &node) {
                    return i as u32;
                }
            }
        }
        let hash = crate::scc::FxBuildHasher::default().hash_one(&node);
        let new_index = u32::try_from(len).expect("call graph record size");
        if len <= RECORD_LINEAR_DEDUP {
            for i in 0..len {
                if r.hashes[i] == hash && r.nodes[i] == node {
                    return i as u32;
                }
            }
        } else {
            if self.node_index.is_empty() {
                for (i, n) in r.nodes.iter().enumerate() {
                    // nodes are distinct, so this keeps every index
                    self.node_index.insert(n.clone(), i as u32);
                }
            }
            if let Some(i) = self.node_index.get(&node) {
                return *i;
            }
            self.node_index.insert(node.clone(), new_index);
        }
        r.nodes.push(node);
        r.hashes.push(hash);
        new_index
    }

    fn add_edge(&mut self, src: Node, dst: Node) {
        let src = self.local(src);
        let dst = self.local(dst);
        self.record.edges.push((src, dst));
    }
}

impl CallGraphRecord {
    /// Applies the recorded edges to `call_graph` in recorded order, exactly as if they had
    /// been added directly with `call_graph.add_edge`, with SpanInfo indices shifted past the
    /// existing `span_infos`. (`expand_call_graph` already applied `call_graph.replace`, via
    /// `replace_node` on the same `replace_with` map; `replace` commutes with the SpanInfo
    /// rebase, which only changes SpanInfo nodes.)
    /// Each distinct node is looked up once. This preserves node indices: add_edge creates
    /// global nodes in order of first mention, and a node that is new to the global graph is
    /// first mentioned at its first local mention, so interning the local nodes in
    /// first-mention order creates the same global nodes in the same order. Edges are then
    /// pushed in recorded order, so every node's edge list is unchanged too.
    pub(crate) fn replay(self, call_graph: &mut GraphBuilder<Node>, span_infos: &mut Vec<Span>) {
        let base = span_infos.len();
        span_infos.extend(self.span_infos);
        let graph = &mut call_graph.graph;
        let global: Vec<NodeIndex> = self
            .nodes
            .into_iter()
            .zip(self.hashes)
            .map(|(node, hash)| match node {
                Node::SpanInfo { span_infos_index, text } => {
                    let node = Node::SpanInfo { span_infos_index: base + span_infos_index, text };
                    graph.intern_hashed(graph.hash_value(&node), node)
                }
                node => graph.intern_hashed(hash, node),
            })
            .collect();
        for (src, dst) in self.edges {
            graph.push_edge_idx(global[src as usize], global[dst as usize]);
        }
    }
}

/// Discovers `function`'s call-graph edges without mutating the shared graph.
/// `replace_with` must be the node-merge map of the target `GraphBuilder`; it is only read
/// (and applied to the recorded nodes).
pub(crate) fn expand_call_graph(
    func_map: &HashMap<Fun, Function>,
    trait_map: &HashMap<Path, crate::ast::Trait>,
    trait_impl_map: &HashMap<(Fun, Path), Fun>,
    trait_impl_from_extension: &HashMap<Path, Path>,
    reveal_group_set: &HashSet<Fun>,
    replace_with: &HashMap<Node, Node>,
    function: &Function,
) -> Result<CallGraphRecord, VirErr> {
    let mut recorder = CallGraphRecorder::new(replace_with);
    let call_graph = &mut recorder;
    // See recursive_types::check_traits for more documentation
    let f_node = Node::Fun(function.x.name.clone());

    // Add f -> T nodes for any dyn T in f
    use crate::ast_visitor::{AstVisitor, WalkTypVisitorEnv};
    let ft = &|call_graph: &mut CallGraphRecorder, t: &Typ| {
        if let Some(dst) = crate::recursive_types::trait_type_edge_target(t) {
            call_graph.add_edge(f_node.clone(), dst);
        }
        Ok(())
    };
    let mut visitor = WalkTypVisitorEnv { env: call_graph, ft };
    visitor.visit_function(function).unwrap();

    // Add T --> f if T declares method f
    if let FunctionKind::TraitMethodDecl { trait_path, has_default: _ } = &function.x.kind {
        if function.x.mode == crate::ast::Mode::Exec && function.x.attrs.impls_cannot_extend_spec {
            // We allow a particular form of nontermination of exec functions
            // by omitting the T --> f edge.
            // This is only safe for impls_cannot_extend_spec;
            // otherwise, call_ensures could be used to create an ill-founded spec expression..
        } else {
            // T --> f
            call_graph.add_edge(Node::Trait(trait_path.clone()), f_node.clone());
            // T --> ...typs...
        }
    }

    // Add D: T --> f and f --> T where f is one of D's methods that implements T
    // Also add ReqEns(D: T, true) --> f --> ReqEns(D: T, false) to make T's requires/ensures
    // as concrete as possible
    if let FunctionKind::TraitMethodImpl { trait_path, impl_path, .. } = function.x.kind.clone() {
        let t_node = Node::Trait(trait_path.clone());
        let impl_node = Node::TraitImpl(ImplPath::TraitImplPath(impl_path.clone()));
        let req_ens_node_t = Node::TraitReqEns(ImplPath::TraitImplPath(impl_path.clone()), true);
        let req_ens_node_f = Node::TraitReqEns(ImplPath::TraitImplPath(impl_path.clone()), false);
        call_graph.add_edge(impl_node, f_node.clone());
        call_graph.add_edge(f_node.clone(), t_node);
        // There's a special case for requires/ensures of f, because these requires/ensures
        // appear in the trait T, not in the implementation D: T.
        // If we didn't extra edges for this case, the calls in requires/ensures
        // might end up uninterpreted in the SMT encoding (which would be sound, but incomplete):
        call_graph.add_edge(f_node.clone(), req_ens_node_f);
        if function.x.mode == crate::ast::Mode::Spec {
            // req_ens_node_t represents the spec functions defined by D: T;
            // these spec functions may be useful for proving requires and ensures
            // of other functions f' who depend on D: T:
            // f' --> TraitReqEns(D': T' for f', false) --> TraitReqEns(D: T for f, true) --> f
            call_graph.add_edge(req_ens_node_t, f_node.clone());
        }
    }

    // Add f --> T for any function f with "where ...: T(...)"
    for bound in function.x.typ_bounds.iter() {
        if let FunctionKind::TraitMethodDecl { trait_path, has_default: _ } = &function.x.kind {
            if crate::recursive_types::suppress_bound_in_trait_decl(
                &trait_path,
                &function.x.typ_params,
                bound,
            ) {
                continue;
            }
            let t_node = Node::Trait(trait_path.clone());
            if let Some(origin_trait) = replace_with.get(&t_node) {
                if let Node::Trait(origin_trait) = origin_trait {
                    if crate::recursive_types::suppress_bound_in_trait_decl(
                        origin_trait,
                        &function.x.typ_params,
                        bound,
                    ) {
                        continue;
                    }
                }
            }
        }
        let tr = match &**bound {
            GenericBoundX::Trait(TraitId::Path(tr), _) => tr,
            GenericBoundX::Trait(TraitId::Sizedness(_), _) => {
                continue;
            }
            GenericBoundX::TypEquality(tr, _, _, _) => tr,
            GenericBoundX::ConstTyp(_, _) => {
                continue;
            }
        };
        call_graph.add_edge(f_node.clone(), Node::Trait(tr.clone()));
    }

    // Add f --> fd if fd is the decreases proof for f's definition
    if let Some(decrease_by) = &function.x.decrease_by {
        call_graph.add_edge(f_node.clone(), Node::Fun(decrease_by.clone()))
    }

    // Add f --> f2 edges where f calls f2
    // Add f --> D: T where one of f's expressions instantiates A: T with D: T
    //
    // When instantiating A: T with D: T, note that D: T could, from Rust's perspective,
    // be the Self: T bound that we remove (see the comments in recursive_types.rs) and
    // that therefore shouldn't be available here.  Fortunately, in this case,
    // rustc gives us the concrete D: T bound for the actual impl, so that
    // impl_paths contains the necessary impl_path to instantiate Self: T explicitly,
    // and we catch the nontermination resulting from Self: T.
    // See, for example, test_termination_1 in rust_verify_test/tests/traits.rs.
    //
    // However, for default methods, rustc does not provide the impl_path to us,
    // and we use a different way of catching uses of Self: T.
    // Specifically, we make sure there is an edge in the call graph from T to the
    // T's default methods, and any attempt by a default method to use Self: T
    // (say, when calling a function f<A: T>) will create an edge to someone who
    // uses T (in this example, f), which then creates a cycle that is reported as an error.
    // (See, for example, test_default14 in rust_verify_test/tests/traits.rs.)
    // The one exception to this is when a default method of T calls another default method of T;
    // this is not considered a cycle through T, but instead is treated as ordinary recursion.
    // (See, for example, test_default17 in rust_verify_test/tests/traits.rs.)
    let add_calls = &mut |expr: &crate::ast::Expr| {
        match &expr.x {
            ExprX::Call {
                target: CallTarget::Fun(kind, x, ts, impl_paths, attrs),
                args: _,
                post_args: _,
                body: _,
            } => {
                assert!(attrs.autospec == AutospecUsage::Final);
                let (callee, ts, impl_paths) = if let CallTargetKind::DynamicResolved {
                    resolved: x_resolved,
                    typs: ts_resolved,
                    impl_paths: x_impl_paths,
                    ..
                } = kind
                {
                    (x_resolved.clone(), ts_resolved.clone(), x_impl_paths.clone())
                } else {
                    (x.clone(), ts.clone(), impl_paths.clone())
                };

                let (callee, impl_paths) = crate::traits::redirect_calls_in_default_methods(
                    func_map,
                    trait_map,
                    trait_impl_map,
                    trait_impl_from_extension,
                    function,
                    &expr.span,
                    callee,
                    ts,
                    impl_paths,
                )?;

                for impl_path in impl_paths.iter() {
                    // f --> D: T
                    let expr_node = crate::recursive_types::new_span_info_node(
                        &mut call_graph.record.span_infos,
                        expr.span.clone(),
                        ": application of a function to some type arguments, which may depend on \
                            other trait implementations to satisfy trait bounds"
                            .to_string(),
                    );
                    call_graph.add_edge(f_node.clone(), expr_node.clone());
                    call_graph.add_edge(expr_node.clone(), Node::TraitImpl(impl_path.clone()));
                }

                // f --> f2
                call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
            }
            ExprX::ConstVar(callee, _) => {
                call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
            }
            ExprX::Call {
                target: CallTarget::BuiltinSpecFun(_bsf, _typs, impl_paths),
                args: _,
                post_args: _,
                body: _,
            } => {
                for impl_path in impl_paths.iter() {
                    call_graph.add_edge(f_node.clone(), Node::TraitImpl(impl_path.clone()));
                }
            }
            ExprX::UnaryOpr(UnaryOpr::ToDyn(_, impl_paths), _) => {
                for impl_path in impl_paths.iter() {
                    let expr_node = crate::recursive_types::new_span_info_node(
                        &mut call_graph.record.span_infos,
                        expr.span.clone(),
                        ": coercion to a trait object, which depends on trait implementations \
                            to satisfy the object's trait bounds"
                            .to_string(),
                    );
                    call_graph.add_edge(f_node.clone(), expr_node.clone());
                    call_graph.add_edge(expr_node, Node::TraitImpl(impl_path.clone()));
                }
            }
            ExprX::Fuel(callee, fuel, _is_broadcast_use) if *fuel >= 1 => {
                let broadcast_forall =
                    reveal_group_set.contains(callee) || func_map[callee].x.attrs.broadcast_forall;
                if broadcast_forall {
                    // f --> f2
                    call_graph.add_edge(f_node.clone(), Node::Fun(callee.clone()))
                }
            }
            ExprX::StaticVar(fun) => call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone())),
            ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: _, expr: _, fun } => {
                call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone()));

                let typ = undecorate_typ(&expr.typ);
                let impl_paths = match &*typ {
                    TypX::Datatype(_, _, impl_paths) => impl_paths,
                    _ => panic!("expected datatype"),
                };
                for impl_path in impl_paths.iter() {
                    let expr_node = crate::recursive_types::new_span_info_node(
                        &mut call_graph.record.span_infos,
                        expr.span.clone(),
                        ": constructor of datatype with some type arguments, which may depend on \
                            other trait implementations to satisfy trait bounds"
                            .to_string(),
                    );
                    call_graph.add_edge(f_node.clone(), expr_node.clone());
                    call_graph.add_edge(expr_node.clone(), Node::TraitImpl(impl_path.clone()));
                }
            }
            _ => {}
        }
        Ok(())
    };
    crate::ast_visitor::function_visitor_check::<VirErr, _>(function, add_calls)?;
    if let FunctionKind::TraitMethodImpl { inherit_body_from: Some(f_trait), .. } = &function.x.kind
    {
        crate::ast_visitor::function_visitor_check::<VirErr, _>(&func_map[f_trait], add_calls)?;
    }

    for fun in &function.x.extra_dependencies {
        call_graph.add_edge(f_node.clone(), Node::Fun(fun.clone()));
    }

    Ok(recorder.record)
}

#[cfg(test)]
mod tests {
    use super::{CallGraphRecorder, Node};
    use crate::ast::{CrateId, FunX, ImplPath, PathX};
    use crate::context::GraphBuilder;
    use crate::messages::{Span, SpanString};
    use crate::scc::Graph;
    use std::collections::HashMap;
    use std::hash::BuildHasher;
    use std::sync::Arc;

    struct Rng(u64);
    impl Rng {
        fn next(&mut self, bound: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % bound as u64) as usize
        }
    }

    fn path(kind: &str, i: usize) -> crate::ast::Path {
        let segments = vec![Arc::new("m".to_string()), Arc::new(format!("{kind}{i}"))];
        Arc::new(PathX { krate: CrateId::Vstd, segments: Arc::new(segments) })
    }

    fn random_node(rng: &mut Rng, n: usize) -> Node {
        let i = rng.next(n);
        match rng.next(4) {
            0 | 1 => Node::Fun(Arc::new(FunX { path: path("f", i) })),
            2 => Node::Trait(path("t", i)),
            _ => Node::TraitImpl(ImplPath::TraitImplPath(path("impl", i))),
        }
    }

    fn span(i: usize) -> Span {
        Span {
            raw_span: Arc::new(()),
            id: i as u64,
            data: vec![i as u64],
            as_string: SpanString::lazy(),
        }
    }

    fn builder(replace_with: &HashMap<Node, Node>) -> GraphBuilder<Node> {
        GraphBuilder { graph: Graph::new(), replace_with: replace_with.clone() }
    }

    // Interned record replay is identical to the previous replay, which called
    // GraphBuilder::add_edge on every recorded (rebased) edge
    #[test]
    fn interned_replay_matches_add_edge_replay() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        for round in 0..200 {
            let n = 1 + rng.next(if round < 100 { 6 } else { 40 });
            let mut replace_with: HashMap<Node, Node> = HashMap::new();
            for _ in 0..rng.next(n + 1) {
                let i = rng.next(n);
                let j = rng.next(n);
                if rng.next(2) == 0 {
                    replace_with.insert(Node::Trait(path("t", i)), Node::Trait(path("t", j)));
                } else {
                    let ip = |k| Node::TraitImpl(ImplPath::TraitImplPath(path("impl", k)));
                    replace_with.insert(ip(i), ip(j));
                }
            }
            let mut old_graph = builder(&replace_with);
            let mut new_graph = builder(&replace_with);
            let mut old_spans: Vec<Span> = vec![span(0)];
            let mut new_spans: Vec<Span> = vec![span(0)];
            let mut next_span = 1;
            for _ in 0..rng.next(10) {
                if rng.next(2) == 0 {
                    let node = random_node(&mut rng, n);
                    old_graph.add_node(node.clone());
                    new_graph.add_node(node);
                }
                let mut record = CallGraphRecorder::new(&replace_with);
                let mut raw: Vec<(Node, Node)> = Vec::new();
                let src = random_node(&mut rng, n);
                for _ in 0..rng.next(3 * n + 1) {
                    let src = if rng.next(4) == 0 { random_node(&mut rng, n) } else { src.clone() };
                    let dst = random_node(&mut rng, n);
                    if rng.next(4) == 0 {
                        let text = format!("text{}", rng.next(3));
                        let info = crate::recursive_types::new_span_info_node(
                            &mut record.record.span_infos,
                            span(next_span),
                            text,
                        );
                        next_span += 1;
                        raw.push((src.clone(), info.clone()));
                        record.add_edge(src.clone(), info.clone());
                        raw.push((info.clone(), dst.clone()));
                        record.add_edge(info, dst);
                    } else {
                        raw.push((src.clone(), dst.clone()));
                        record.add_edge(src, dst);
                    }
                }
                // previous replay
                let base = old_spans.len();
                let rebase = |n: Node| match n {
                    Node::SpanInfo { span_infos_index, text } => {
                        Node::SpanInfo { span_infos_index: base + span_infos_index, text }
                    }
                    n => n,
                };
                let record = record.record;
                old_spans.extend(record.span_infos.iter().cloned());
                for (src, dst) in raw {
                    old_graph.add_edge(rebase(src), rebase(dst));
                }
                record.replay(&mut new_graph, &mut new_spans);
            }
            let (mut old_graph, mut new_graph) = (old_graph.graph, new_graph.graph);
            assert_eq!(format!("{:?}", old_graph), format!("{:?}", new_graph));
            old_graph.compute_sccs();
            new_graph.compute_sccs();
            assert_eq!(format!("{:?}", old_graph), format!("{:?}", new_graph));
            let data = |spans: &Vec<Span>| spans.iter().map(|s| s.data.clone()).collect::<Vec<_>>();
            assert_eq!(data(&old_spans), data(&new_spans));
        }
    }

    #[test]
    fn span_info_hash_ignores_text_but_eq_does_not() {
        let b = crate::scc::FxBuildHasher::default();
        let a = Node::SpanInfo { span_infos_index: 3, text: "a".to_string() };
        let a2 = Node::SpanInfo { span_infos_index: 3, text: "b".to_string() };
        let c = Node::SpanInfo { span_infos_index: 4, text: "a".to_string() };
        assert_eq!(b.hash_one(&a), b.hash_one(&a2));
        assert_ne!(a, a2);
        assert_ne!(b.hash_one(&a), b.hash_one(&c));
        let mut m = crate::scc::FxHashMap::default();
        m.insert(a.clone(), 0);
        m.insert(a2.clone(), 1);
        assert_eq!((m[&a], m[&a2], m.get(&c)), (0, 1, None));
    }
}
