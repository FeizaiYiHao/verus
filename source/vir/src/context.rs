use crate::ast::{
    ArchWordBits, CrateId, Datatype, Dt, Fun, Function, FunctionAttrs, GenericBounds, Ident,
    ImplPath, IntRange, Krate, Mode, Module, OpaqueType, Path, Primitive, Trait, TraitImpl,
    TypPositives, TypX, Variants, VirErr,
};
use crate::ast_util::{dt_as_friendly_rust_name_raw, path_as_friendly_rust_name_raw};
use crate::datatype_to_air::is_datatype_transparent;
use crate::def::{FUEL_ID, NameCtxt};
use crate::messages::{Span, WarningAllow, error};
use crate::poly::MonoTyp;
use crate::recursion::Node;
use crate::scc::Graph;
use crate::sst::BndInfo;
use crate::sst_to_air::fun_to_air_ident;
use air::ast::{Command, CommandX, Commands, DeclX, MultiOp};
use air::ast_util::{mk_unnamed_axiom, str_typ};
use air::context::SmtSolver;
use num_bigint::BigUint;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::sync::Arc;

// Use decorated types in addition to undecorated types (see sst_to_air::typ_to_ids)
pub(crate) const DECORATE: bool = true;

pub type ChosenTrigger = Vec<(Span, String)>;
#[derive(Debug, Clone)]
pub struct ChosenTriggers {
    pub module: Path,
    pub span: Span,
    pub triggers: Vec<ChosenTrigger>,
    pub low_confidence: bool,
    pub manual: bool,
}

#[derive(Debug, Clone)]
pub struct WarningConfig(pub Vec<WarningAllow>);

impl crate::messages::CheckAllowForWarning for WarningConfig {
    fn allowed(&self, allow: &WarningAllow) -> bool {
        self.0.iter().any(|a| a == allow)
    }
}

#[derive(Debug, Clone)]
pub struct WarningCtx {
    // Map names of FunctionX in this crate (not imported from other crates)
    // to Some CheckAllowForWarning to be used to check that fun,
    // map names from other crates to None
    pub fun_warn_configs: HashMap<Fun, Option<WarningConfig>>,
}

/// Context for across all modules
pub struct GlobalCtx {
    pub(crate) chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>>, // diagnostics
    pub(crate) datatypes: Arc<HashMap<Path, (TypPositives, Variants)>>,
    pub(crate) fun_bounds: Arc<HashMap<Fun, GenericBounds>>,
    pub(crate) fun_attrs: Arc<HashMap<Fun, FunctionAttrs>>,
    /// Used for synthesized AST nodes that have no relation to any location in the original code:
    pub(crate) no_span: Span,
    pub func_call_graph: Arc<Graph<Node>>,
    pub func_call_sccs: Arc<Vec<Node>>,
    /// Maps call-graph nodes to positions in `func_call_sccs`.
    pub func_call_scc_index: Arc<HashMap<Node, usize>>,
    pub(crate) datatype_graph: Arc<Graph<crate::recursive_types::TypNode>>,
    pub(crate) datatype_graph_span_infos: Arc<Vec<Span>>,
    pub trait_impl_to_extensions: Arc<HashMap<Path, Vec<Path>>>,
    /// Map TSpec to T
    pub(crate) extension_to_trait: Arc<HashMap<Path, Path>>,
    pub(crate) warning_ctx: Arc<WarningCtx>,
    /// Connects quantifier identifiers to the original expression
    pub qid_map: RefCell<HashMap<String, BndInfo>>,
    pub(crate) rlimit: f32,
    pub(crate) interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
    pub(crate) func_call_graph_log: Arc<std::sync::Mutex<Option<FuncCallGraphLogFiles>>>,
    pub arch: crate::ast::ArchWordBits,
    pub crate_name: CrateId,
    pub solver: SmtSolver,
    pub check_api_safety: bool,
    pub axiom_usage_info: bool,
    pub no_bv_simplify: bool,
    pub report_long_running: bool,
}

// Context for verifying one function
#[derive(Debug)]
pub struct FunctionCtx {
    // false normally, true if we're just checking spec preconditions
    pub(crate) checking_spec_preconditions: bool,
    // false normally, true if we're just checking spec preconditions for a non-spec function
    // checking_spec_preconditions_for_non_spec <==> checking_spec_preconditions && mode != Spec
    pub(crate) checking_spec_preconditions_for_non_spec: bool,
    // false normally, true if we're just checking decreases of recursive spec function
    // Note: !(checking_spec_preconditions && checking_spec_decreases)
    pub(crate) checking_spec_decreases: bool,
    // used to print diagnostics for triggers
    pub(crate) module_for_chosen_triggers: Option<Path>,
    // used to create quantifier identifiers and for checking_spec_preconditions
    pub current_fun: Fun,
    pub(crate) current_fun_attrs: crate::ast::FunctionAttrs,
}

// Context for verifying one module
pub struct Ctx {
    pub(crate) module: Module,
    pub(crate) datatype_is_transparent: HashMap<Dt, bool>,
    pub(crate) datatypes_with_invariant: HashSet<Dt>,
    pub(crate) mono_types: Vec<MonoTyp>,
    pub(crate) spec_fn_types: Vec<usize>,
    pub(crate) reached_dyn_traits: HashSet<Path>,
    pub(crate) used_builtins: crate::prune::UsedBuiltins,
    pub(crate) fndef_types: Vec<Fun>,
    pub(crate) resolved_typs: Vec<crate::resolve_axioms::ResolvableType>,
    pub(crate) fndef_type_set: HashSet<Fun>,
    pub functions: Vec<Function>,
    pub func_map: HashMap<Fun, Function>,
    pub func_sst_map: HashMap<Fun, crate::sst::FunctionSst>,
    pub fun_ident_map: HashMap<Ident, Fun>,
    pub opaque_type_map: HashMap<Path, OpaqueType>,
    pub(crate) reveal_groups: Vec<crate::ast::RevealGroup>,
    pub(crate) reveal_group_set: HashSet<Fun>,
    // Ensure a unique identifier for each quantifier in a given function
    pub quantifier_count: RefCell<HashMap<Arc<String>, u64>>,
    pub(crate) funcs_with_ensure_predicate: HashMap<Fun, bool>,
    pub(crate) datatype_map: HashMap<Dt, Datatype>,
    pub(crate) trait_map: HashMap<Path, Trait>,
    pub(crate) impl_map: HashMap<Path, TraitImpl>,
    pub name_ctxt: NameCtxt,
    pub fun: Option<FunctionCtx>,
    pub global: GlobalCtx,
    // In the very unlikely case where we get sha512 collisions
    // we use this to panic rather than introduce unsoundness.
    // Of course it can be argued that accounting for sha512 collisions
    // is overkill, perhaps this should be revisited.
    pub(crate) string_hashes: RefCell<HashMap<BigUint, Arc<String>>>,
    pub(crate) byte_string_hashes: RefCell<HashMap<BigUint, Arc<Vec<u8>>>>,
    pub arch_word_bits: ArchWordBits,
}

impl Ctx {
    pub(crate) fn checking_spec_preconditions(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_preconditions: true, .. }) => true,
            _ => false,
        }
    }

    pub(crate) fn checking_spec_preconditions_for_non_spec(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_preconditions_for_non_spec: true, .. }) => true,
            _ => false,
        }
    }

    pub(crate) fn checking_spec_decreases(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_decreases: true, .. }) => true,
            _ => false,
        }
    }

    pub(crate) fn checking_spec_general(&self) -> bool {
        match self.fun {
            Some(FunctionCtx { checking_spec_preconditions: true, .. }) => true,
            Some(FunctionCtx { checking_spec_decreases: true, .. }) => true,
            _ => false,
        }
    }

    pub(crate) fn warning_maybe_if_in_local_crate<S: Into<String>>(
        &self,
        span: &Span,
        allow: &WarningAllow,
        note: impl FnOnce() -> S,
        emit: impl FnOnce(crate::messages::Message) -> (),
    ) {
        if let Some(function_ctx) = &self.fun {
            let check_allow = &self.global.warning_ctx.fun_warn_configs[&function_ctx.current_fun];
            crate::messages::warning_maybe_if_in_local_crate(check_allow, span, allow, note, emit);
        } else {
            // TODO: if we ever support verifier::allow on expressions,
            // we can make this warning configurable:
            emit(crate::messages::warning(span, note()));
        }
    }
}

fn datatypes_inv_visit(
    back_pointers: &HashMap<Dt, HashSet<Dt>>,
    has_inv: &mut HashSet<Dt>,
    root: &Dt,
) {
    if has_inv.contains(root) {
        return;
    }
    has_inv.insert(root.clone());
    for container_name in &back_pointers[root] {
        datatypes_inv_visit(back_pointers, has_inv, container_name);
    }
}

// If a datatype's fields have invariants, the datatype needs an invariant
fn datatypes_invs(
    module: &Path,
    datatype_is_transparent: &HashMap<Dt, bool>,
    datatypes: &Vec<Datatype>,
) -> HashSet<Dt> {
    let mut back_pointers: HashMap<Dt, HashSet<Dt>> =
        datatypes.iter().map(|d| (d.x.name.clone(), HashSet::new())).collect();
    let mut has_inv: HashSet<Dt> = HashSet::new();
    let mut roots: HashSet<Dt> = HashSet::new();
    for datatype in datatypes {
        if is_datatype_transparent(module, datatype) {
            let container_name = &datatype.x.name;
            for variant in datatype.x.variants.iter() {
                for field in variant.fields.iter() {
                    match &*crate::ast_util::undecorate_typ(&field.a.0) {
                        // Should be kept in sync with vir::sst_to_air::typ_invariant
                        TypX::Int(IntRange::Int) => {}
                        TypX::Int(_)
                        | TypX::Dyn(..)
                        | TypX::TypParam(_)
                        | TypX::Projection { .. }
                        | TypX::PointeeMetadata(_) => {
                            roots.insert(container_name.clone());
                        }
                        TypX::Real => {}
                        TypX::SpecFn(..) => {
                            roots.insert(container_name.clone());
                        }
                        TypX::Datatype(field_dt, _, _) => {
                            if datatype_is_transparent[field_dt] {
                                back_pointers
                                    .get_mut(field_dt)
                                    .expect("datatypes_invs")
                                    .insert(container_name.clone());
                            } else {
                                if crate::poly::typ_as_mono(&field.a.0).is_none() {
                                    roots.insert(container_name.clone());
                                }
                            }
                        }
                        TypX::FnDef(..) => {}
                        TypX::Decorate(..) => unreachable!("TypX::Decorate"),
                        TypX::Boxed(_) => {}
                        TypX::TypeId => {}
                        TypX::Opaque { .. } => {}
                        TypX::Bool => {}
                        TypX::Float(_) => {}
                        TypX::AnonymousClosure(..) => {}
                        TypX::Air(_) => panic!("datatypes_invs"),
                        TypX::ConstInt(_) => {}
                        TypX::ConstBool(_) => {}
                        TypX::Primitive(
                            Primitive::Array | Primitive::Slice | Primitive::Ptr,
                            _,
                        ) => {
                            // Each of these is like an abstract Datatype
                            if crate::poly::typ_as_mono(&field.a.0).is_none() {
                                roots.insert(container_name.clone());
                            }
                        }
                        TypX::Primitive(Primitive::StrSlice, _) => {}
                        TypX::Primitive(Primitive::Global, _) => {}
                        TypX::MutRef(_) => {
                            roots.insert(container_name.clone());
                        }
                    }
                }
            }
        }
    }
    for root in &roots {
        datatypes_inv_visit(&back_pointers, &mut has_inv, root);
    }
    has_inv
}

pub struct FuncCallGraphLogFiles {
    pub all_initial: File,
    pub all_simplified: File,
    pub nostd_initial: File,
    pub nostd_simplified: File,
}

// A wrapper around Graph that adds functionality to merge nodes as the graph is built
pub(crate) struct GraphBuilder<T: std::cmp::Eq + std::hash::Hash + Clone> {
    pub(crate) graph: Graph<T>,
    // Whenever we see node: T, replace it with replace_with[node]
    // This merges node and replace_with[node] together into a single node.
    pub(crate) replace_with: HashMap<T, T>,
}

impl GraphBuilder<Node> {
    pub(crate) fn replace(&self, value: Node) -> Node {
        // Shared with the parallel call-graph recorder, so the two cannot diverge.
        crate::recursion::replace_node(&self.replace_with, value)
    }
    pub(crate) fn add_node(&mut self, value: Node) {
        let value = self.replace(value);
        self.graph.add_node(value);
    }
    pub(crate) fn add_edge(&mut self, src: Node, dst: Node) {
        let src = self.replace(src);
        let dst = self.replace(dst);
        self.graph.add_edge(src, dst);
    }
}

impl GlobalCtx {
    pub fn new(
        krate: &Krate,
        crate_name: CrateId,
        no_span: Span,
        rlimit: f32,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
        func_call_graph_log: Arc<std::sync::Mutex<Option<FuncCallGraphLogFiles>>>,
        warning_ctx: Arc<WarningCtx>,
        solver: SmtSolver,
        after_simplify: bool,
        check_api_safety: bool,
        axiom_usage_info: bool,
        no_bv_simplify: bool,
        report_long_running: bool,
    ) -> Result<Self, VirErr> {
        let chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>> =
            std::cell::RefCell::new(Vec::new());

        let datatypes: HashMap<Path, (TypPositives, Variants)> = krate
            .datatypes
            .iter()
            .filter_map(|d| match &d.x.name {
                Dt::Path(path) => {
                    Some((path.clone(), (d.x.typ_params.clone(), d.x.variants.clone())))
                }
                Dt::Tuple(_) => None,
            })
            .collect();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        for function in krate.functions.iter() {
            assert!(!func_map.contains_key(&function.x.name));
            func_map.insert(function.x.name.clone(), function.clone());
        }
        let mut fun_bounds: HashMap<Fun, GenericBounds> = HashMap::new();
        let mut fun_attrs: HashMap<Fun, FunctionAttrs> = HashMap::new();
        let reveal_group_set: HashSet<Fun> =
            krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();

        let mut trait_map: HashMap<Path, Trait> = HashMap::new();
        for tr in krate.traits.iter() {
            assert!(!trait_map.contains_key(&tr.x.name));
            trait_map.insert(tr.x.name.clone(), tr.clone());
        }

        use crate::ast::TraitImpl;
        let mut extension_to_trait: HashMap<Path, Path> = HashMap::new();
        let mut trait_impl_to_extensions: HashMap<Path, Vec<Path>> = HashMap::new();
        let mut trait_impl_from_extension: HashMap<Path, Path> = HashMap::new();
        let mut trait_impl_map: HashMap<Path, TraitImpl> = HashMap::new();
        let mut replace_with: HashMap<Node, Node> = HashMap::new();
        for t in &krate.traits {
            // If TSpec extends T with spec functions, merge TSpec into T
            if let Some((extension, _)) = &t.x.external_trait_extension {
                let t_node = Node::Trait(t.x.name.clone());
                let extension_node = Node::Trait(extension.clone());
                assert!(!replace_with.contains_key(&extension_node));
                replace_with.insert(extension_node, t_node);
                assert!(!extension_to_trait.contains_key(extension));
                extension_to_trait.insert(extension.clone(), t.x.name.clone());
            }
        }
        for trait_impl in &krate.trait_impls {
            assert!(!trait_impl_map.contains_key(&trait_impl.x.impl_path));
            trait_impl_map.insert(trait_impl.x.impl_path.clone(), trait_impl.clone());
        }
        for trait_impl in &krate.trait_impls {
            if trait_impl.x.external_trait_blanket {
                continue;
            }
            // If TSpec extends T with spec functions,
            // merge 'impl TSpec for typ' into 'impl T for typ'.
            if let Some(t) = extension_to_trait.get(&trait_impl.x.trait_path) {
                let mut candidates: Vec<TraitImpl> = Vec::new();
                for imp in trait_impl.x.trait_typ_arg_impls.x.iter() {
                    if let ImplPath::TraitImplPath(imp) = imp {
                        if let Some(candidate) = trait_impl_map.get(imp) {
                            if &candidate.x.trait_path == t && !candidate.x.external_trait_blanket {
                                candidates.push(candidate.clone());
                            }
                        }
                    }
                }
                let origin_impl =
                    crate::traits::find_trait_impl_from_extension(trait_impl, candidates, t)?;
                let extension_node =
                    Node::TraitImpl(ImplPath::TraitImplPath(trait_impl.x.impl_path.clone()));
                let origin_node =
                    Node::TraitImpl(ImplPath::TraitImplPath(origin_impl.x.impl_path.clone()));
                assert!(!replace_with.contains_key(&extension_node));
                replace_with.insert(extension_node, origin_node);
                assert!(!trait_impl_from_extension.contains_key(&trait_impl.x.impl_path));
                trait_impl_from_extension
                    .insert(trait_impl.x.impl_path.clone(), origin_impl.x.impl_path.clone());
                trait_impl_to_extensions
                    .entry(origin_impl.x.impl_path.clone())
                    .or_default()
                    .push(trait_impl.x.impl_path.clone());
            }
        }
        let mut func_call_graph: GraphBuilder<Node> =
            GraphBuilder { graph: Graph::new(), replace_with };
        let crate_node = Node::Crate(crate_name.clone());
        func_call_graph.add_node(crate_node.clone());

        // Unlike in Coq or F*, Rust programs don't define a
        // total ordering on declarations, and the call graph only provides a partial order.
        // We topologically sort the strongly connected components of the call graph
        // to create a total order.
        // REVIEW: at some point, we should try to ensure that the order is as stable
        // as possible with respect to small changes in the graph.
        // For the moment, we have some legacy heuristics that used to be necessary,
        // should no longer be necessary, and may or may not make the ordering more stable.

        for t in &krate.trait_impls {
            if let Some(last) = &t.x.impl_path.segments.last() {
                if last.starts_with(crate::def::PREFIX_IMPL_TUPLE) {
                    // Our internally auto-generated tuple impls don't depend on any other impls,
                    // so they can always appear first.
                    // Furthermore, we currently lack the impl_path dependency edges that
                    // should point to the impl, so the impl isn't ordered in the
                    // strongly connected component graph, so we have to explicitly put them first.
                    func_call_graph
                        .add_node(Node::TraitImpl(ImplPath::TraitImplPath(t.x.impl_path.clone())));
                }
            }
        }
        for t in &krate.traits {
            crate::recursive_types::add_trait_to_graph(&mut func_call_graph, t);
        }
        for f in &krate.functions {
            // Heuristic: add all external_body functions first.
            // This is currently needed because external_body broadcast_forall functions
            // are currently implicitly imported.
            // In the future, this might become less important; we could remove this heuristic.
            use crate::ast::FunctionKind::TraitMethodImpl;
            let inherit_default =
                matches!(&f.x.kind, TraitMethodImpl { inherit_body_from: Some(_), .. });
            if f.x.body.is_none() && f.x.extra_dependencies.len() == 0 && !inherit_default {
                func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            }
        }
        for f in &krate.functions {
            // HACK: put spec functions early, because the call graph is currently missing some
            // dependencies that should explicitly force these functions to appear early.
            // TODO: add these dependencies to the call graph.
            if f.x.mode == Mode::Spec {
                func_call_graph.add_node(Node::Fun(f.x.name.clone()));
            }
        }
        for t in &krate.trait_impls {
            if t.x.external_trait_blanket {
                continue;
            }
            // Heuristic: put trait impls first, because they are likely to precede
            // many functions that rely on them.
            func_call_graph
                .add_node(Node::TraitImpl(ImplPath::TraitImplPath(t.x.impl_path.clone())));
        }

        let mut span_infos: Vec<Span> = Vec::new();
        for t in &krate.trait_impls {
            crate::recursive_types::add_trait_impl_to_graph(
                &mut span_infos,
                &mut func_call_graph,
                t,
            );
        }
        for a in &krate.assoc_type_impls {
            crate::recursive_types::add_assoc_type_impl_to_graph(
                &mut span_infos,
                &mut func_call_graph,
                a,
            );
        }

        // map (method, impl) to impl Fun
        let mut trait_impl_map: HashMap<(Fun, Path), Fun> = HashMap::new();
        // map impl Fun to impl
        let mut method_impl_map: HashMap<Fun, Path> = HashMap::new();
        for f in &krate.functions {
            if let crate::ast::FunctionKind::TraitMethodImpl { method, impl_path, .. } = &f.x.kind {
                let key = (method.clone(), impl_path.clone());
                assert!(!trait_impl_map.contains_key(&key));
                trait_impl_map.insert(key, f.x.name.clone());
                assert!(!method_impl_map.contains_key(&f.x.name));
                method_impl_map.insert(f.x.name.clone(), impl_path.clone());
            }
        }

        // Discover each function's call-graph edges in parallel against the read-only
        // replace_with map, then replay them below in krate.functions order. Replay performs
        // the same add_node/add_edge sequence and span_infos pushes as a sequential build,
        // so node indices, SCCs, and SpanInfo indices are unchanged.
        // Errors and panics are surfaced at the first failing function in that order; functions
        // after it are not expanded.
        let call_graph_records = {
            let replace_with = &func_call_graph.replace_with;
            crate::util::par_map_init_until_err(
                &krate.functions,
                || (),
                |_, f| {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        crate::recursion::expand_call_graph(
                            &func_map,
                            &trait_map,
                            &trait_impl_map,
                            &trait_impl_from_extension,
                            &reveal_group_set,
                            replace_with,
                            f,
                        )
                    }))
                },
                |record| !matches!(record, Ok(Ok(_))),
            )
        };
        for (f, record) in krate.functions.iter().zip(call_graph_records) {
            let record = record.expect("functions up to the first failure are expanded");
            fun_bounds.insert(f.x.name.clone(), f.x.typ_bounds.clone());
            let fun_node = Node::Fun(f.x.name.clone());
            let fndef_impl_node = Node::TraitImpl(ImplPath::FnDefImplPath(f.x.name.clone()));
            func_call_graph.add_node(fun_node.clone());
            func_call_graph.add_node(fndef_impl_node.clone());
            func_call_graph.add_edge(fndef_impl_node, fun_node);

            fun_attrs.insert(f.x.name.clone(), f.x.attrs.clone());

            match record {
                Ok(record) => record?.replay(&mut func_call_graph, &mut span_infos),
                Err(panic) => std::panic::resume_unwind(panic),
            }
        }

        for group in &krate.reveal_groups {
            let group_node = Node::Fun(group.x.name.clone());
            func_call_graph.add_node(group_node.clone());
            for member in group.x.members.iter() {
                let target = Node::Fun(member.clone());
                func_call_graph.add_node(target.clone());
                func_call_graph.add_edge(group_node.clone(), target);
            }
            if let Some(group_crate) = &group.x.broadcast_use_by_default_when_this_crate_is_imported
            {
                let is_imported = crate_name != *group_crate;
                if is_imported {
                    func_call_graph.add_edge(crate_node.clone(), group_node);
                }
            }
        }
        // Functions grouped by owning module, each group in krate.functions order
        let mut module_functions: HashMap<&Path, Vec<&Function>> = HashMap::new();
        for f in &krate.functions {
            if let Some(owning_module) = &f.x.owning_module {
                module_functions.entry(owning_module).or_default().push(f);
            }
        }
        for module in &krate.modules {
            let module_reveal_node = Node::ModuleReveal(module.x.path.clone());
            func_call_graph.add_node(module_reveal_node.clone());
            if module.x.path.krate == crate_name {
                func_call_graph.add_edge(module_reveal_node.clone(), crate_node.clone());
            }
            if let Some(ref reveals) = module.x.reveals {
                for fun in reveals.x.iter() {
                    let target = Node::Fun(fun.clone());
                    func_call_graph.add_node(target.clone());
                    func_call_graph.add_edge(module_reveal_node.clone(), target);
                }
            }
            for f in module_functions.get(&module.x.path).into_iter().flatten() {
                let source = Node::Fun(f.x.name.clone());
                func_call_graph.add_node(source.clone());
                func_call_graph.add_edge(source, module_reveal_node.clone());
            }
        }

        // First, create a preliminary call graph that may lack some Fun -> TraitImpl edges
        // Example:
        //   impl T for S {
        //     fn f1() {}
        //     fn f3() { f2() }
        //   }
        //   fn f2() { <S as T>::f1() }
        //   fn f4() { <S as T>::f1() }
        // For this example, we construct a dictionary { f1, f3 } for T for S.
        // In the graph, a TraitImpl Node represents this dictionary.
        // f4 is allowed to see this dictionary, but f2 is not, because f3 depends on f2,
        // so the dictionary is still under construction when f2 is defined.
        // In the preliminary call graph, neither f2 nor f4 has an edge to the TraitImpl.
        // In the final call graph, we add the edge Fun(f4) --> TraitImpl,
        // based on the fact that f4 calls one of { f1, f3 },
        // but the TraitImpl does not depend on f4.
        // The preliminary SCCs are computed in place on func_call_graph.graph (no clone):
        // fixups are only discovered while the SCCs are current, and are added afterwards as
        // edges between existing nodes, before reset_sccs + compute_sccs below.
        func_call_graph.graph.compute_sccs();
        let (preliminary_sccs, order) = func_call_graph.graph.sort_sccs_with_order();
        // A fixup only adds edges from node_f4 itself, so each node_f4's fixups are discovered in
        // parallel against the graph as it is before any fixup, then added in the sequential
        // order. Panics surface at the first panicking node_f4 in that order; nodes after it are
        // not examined.
        let f4_nodes: Vec<Node> = preliminary_sccs
            .iter()
            .flat_map(|scc| func_call_graph.graph.get_scc_nodes(scc))
            .filter(|node| matches!(node, Node::Fun(_)))
            .collect();
        let fixups = {
            let func_call_graph = &func_call_graph;
            let preliminary_call_graph = &func_call_graph.graph;
            crate::util::par_map_init_until_err(
                &f4_nodes,
                crate::scc::Visited::new,
                |visited, node_f4| {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        use crate::recursion::get_edges_from;
                        let mut added: Vec<Node> = Vec::new();
                        // The graph is not mutated while fixups are discovered.
                        let edges_f4 = get_edges_from(preliminary_call_graph, node_f4);
                        'f1: for node_f1 in edges_f4.iter() {
                            if let Node::Fun(f1) = node_f1 {
                                if let Some(trait_impl) = method_impl_map.get(f1) {
                                    let impl_path = ImplPath::TraitImplPath(trait_impl.clone());
                                    let trait_impl = Node::TraitImpl(impl_path);
                                    let trait_impl = func_call_graph.replace(trait_impl);
                                    // Do we already have f4 --> trait_impl?
                                    if edges_f4.iter().any(|ti| **ti == trait_impl) {
                                        continue 'f1;
                                    }
                                    if added.contains(&trait_impl) {
                                        continue 'f1;
                                    }
                                    // Is there a path trait_impl --*--> f4?
                                    if preliminary_call_graph.can_reach_with(
                                        visited,
                                        &trait_impl,
                                        node_f4,
                                        Some(&order),
                                    ) {
                                        continue 'f1;
                                    }
                                    // Add f4 --> trait_impl
                                    added.push(trait_impl);
                                }
                            }
                        }
                        added
                    }))
                },
                |fixup| fixup.is_err(),
            )
        };
        for (node_f4, fixup) in f4_nodes.iter().zip(fixups) {
            match fixup.expect("nodes up to the first panic are examined") {
                Ok(added) => {
                    for trait_impl in added {
                        func_call_graph.add_edge(node_f4.clone(), trait_impl);
                    }
                }
                Err(panic) => std::panic::resume_unwind(panic),
            }
        }
        // Now make the final call graph with the extra edges
        let mut func_call_graph = func_call_graph.graph;
        func_call_graph.reset_sccs();
        func_call_graph.compute_sccs();
        let func_call_sccs = func_call_graph.sort_sccs();
        // Like datatype_graph below, the SCC index is only read after simplification.
        let mut func_call_scc_index: HashMap<Node, usize> = HashMap::new();
        if after_simplify {
            for (i, scc_rep) in func_call_sccs.iter().enumerate() {
                for node in func_call_graph.get_scc_nodes(scc_rep) {
                    func_call_scc_index.insert(node, i);
                }
            }
        }

        if let Some(FuncCallGraphLogFiles {
            all_initial,
            all_simplified,
            nostd_initial,
            nostd_simplified,
        }) = &mut *func_call_graph_log.lock().expect("cannot lock call graph log file")
        {
            fn node_options(n: &Node) -> String {
                fn labelize(name: &str, s: String) -> String {
                    let label = s.replace("\"", "\\\"");
                    format!("margin=0.1, label=\"{}\\n{}\"", name, label)
                }
                #[rustfmt::skip] // v to work around attributes being experimental on expressions
                let v = match n {
                    Node::Fun(fun) =>                         labelize("Fun", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"cds\"",
                    Node::Datatype(path) =>                   labelize("Datatype", dt_as_friendly_rust_name_raw(path)) + ", shape=\"folder\"",
                    Node::Trait(path) =>                      labelize("Trait", path_as_friendly_rust_name_raw(path)) + ", shape=\"tab\"",
                    Node::TraitImpl(impl_path) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::TraitReqEns(impl_path, true) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("ReqEns?TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("ReqEns?FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::TraitReqEns(impl_path, false) => {
                        match impl_path {
                            ImplPath::TraitImplPath(path) =>  labelize("ReqEns!TraitImplPath", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                            ImplPath::FnDefImplPath(fun) =>   labelize("ReqEns!FnDefImplPath", path_as_friendly_rust_name_raw(&fun.path)) + ", shape=\"component\"",
                        }
                    }
                    Node::ModuleReveal(path) =>               labelize("ModuleReveal", path_as_friendly_rust_name_raw(path)) + ", shape=\"component\"",
                    Node::Crate(c) =>                         labelize("Crate", c.to_string()) + ", shape=\"component\"",
                    Node::SpanInfo { span_infos_index: _, text: _ } => {
                        format!("shape=\"point\"")
                    }
                };
                v
            }

            fn nostd_filter(n: &Node) -> (bool, bool) {
                fn is_not_std_crate(crate_name: &CrateId) -> bool {
                    match crate_name {
                        CrateId::Core | CrateId::Alloc | CrateId::Vstd => false,
                        _ => true,
                    }
                }
                fn is_not_std(path: &Path) -> bool {
                    is_not_std_crate(&path.krate)
                }
                let render = match n {
                    Node::Fun(fun) => is_not_std(&fun.path),
                    Node::Datatype(Dt::Path(path)) => is_not_std(path),
                    Node::Datatype(Dt::Tuple(_)) => true,
                    Node::Trait(path) => is_not_std(path),
                    Node::TraitImpl(ImplPath::TraitImplPath(path)) => is_not_std(path),
                    Node::TraitImpl(ImplPath::FnDefImplPath(fun)) => is_not_std(&fun.path),
                    Node::TraitReqEns(ImplPath::TraitImplPath(path), _) => is_not_std(path),
                    Node::TraitReqEns(ImplPath::FnDefImplPath(fun), _) => is_not_std(&fun.path),
                    Node::ModuleReveal(path) => is_not_std(path),
                    Node::Crate(c) => is_not_std_crate(c),
                    Node::SpanInfo { .. } => true,
                };
                (render, render && !matches!(n, Node::SpanInfo { .. }))
            }

            if !after_simplify {
                func_call_graph.to_dot(all_initial, |_| (true, true), node_options);
                func_call_graph.to_dot(nostd_initial, nostd_filter, node_options);
            } else {
                func_call_graph.to_dot(all_simplified, |_| (true, true), node_options);
                func_call_graph.to_dot(nostd_simplified, nostd_filter, node_options);
            }
        }

        for f in &krate.functions {
            let f_node = Node::Fun(f.x.name.clone());
            if f.x.attrs.is_decrease_by {
                for g_node in func_call_graph.get_scc_nodes(&f_node) {
                    if f_node != g_node {
                        let g_opt =
                            krate.functions.iter().find(|g| Node::Fun(g.x.name.clone()) == g_node);
                        let mut error = crate::messages::error(
                            &f.span,
                            "found cyclic dependency in decreases_by function",
                        );
                        if let Some(g) = g_opt {
                            error = error.secondary_span(&g.span);
                        }
                        return Err(error);
                    }
                }
            }
            if f.x.attrs.atomic {
                let fun_node = Node::Fun(f.x.name.clone());
                if func_call_graph.node_is_in_cycle(&fun_node) {
                    return Err(error(&f.span, "'atomic' cannot be used on a recursive function"));
                }
            }
        }
        let qid_map = RefCell::new(HashMap::new());

        // The pre-simplify GlobalCtx is only read by check_traits and simplify_krate, neither of
        // which reads datatype_graph or func_call_scc_index; simplify_krate replaces it with an
        // after_simplify GlobalCtx.
        // span_infos still holds every call-graph SpanInfo entry that check_traits indexes.
        let datatype_graph = if after_simplify {
            crate::recursive_types::build_datatype_graph(krate, &mut span_infos)
        } else {
            let mut empty = Graph::new();
            empty.compute_sccs();
            empty
        };

        Ok(GlobalCtx {
            chosen_triggers,
            datatypes: Arc::new(datatypes),
            fun_bounds: Arc::new(fun_bounds),
            fun_attrs: Arc::new(fun_attrs),
            no_span,
            func_call_graph: Arc::new(func_call_graph),
            func_call_sccs: Arc::new(func_call_sccs),
            func_call_scc_index: Arc::new(func_call_scc_index),
            datatype_graph: Arc::new(datatype_graph),
            datatype_graph_span_infos: Arc::new(span_infos),
            extension_to_trait: Arc::new(extension_to_trait),
            trait_impl_to_extensions: Arc::new(trait_impl_to_extensions),
            warning_ctx,
            qid_map,
            rlimit,
            interpreter_log,
            arch: krate.arch.word_bits,
            crate_name,
            func_call_graph_log,
            solver,
            check_api_safety,
            axiom_usage_info,
            no_bv_simplify,
            report_long_running,
        })
    }

    pub fn from_self_with_log(&self, interpreter_log: Arc<std::sync::Mutex<Option<File>>>) -> Self {
        let chosen_triggers: std::cell::RefCell<Vec<ChosenTriggers>> =
            std::cell::RefCell::new(Vec::new());
        let qid_map = RefCell::new(HashMap::new());

        GlobalCtx {
            chosen_triggers,
            datatypes: self.datatypes.clone(),
            fun_bounds: self.fun_bounds.clone(),
            fun_attrs: self.fun_attrs.clone(),
            no_span: self.no_span.clone(),
            func_call_graph: self.func_call_graph.clone(),
            datatype_graph: self.datatype_graph.clone(),
            datatype_graph_span_infos: self.datatype_graph_span_infos.clone(),
            func_call_sccs: self.func_call_sccs.clone(),
            func_call_scc_index: self.func_call_scc_index.clone(),
            extension_to_trait: self.extension_to_trait.clone(),
            trait_impl_to_extensions: self.trait_impl_to_extensions.clone(),
            warning_ctx: self.warning_ctx.clone(),
            qid_map,
            rlimit: self.rlimit,
            interpreter_log,
            arch: self.arch,
            crate_name: self.crate_name.clone(),
            func_call_graph_log: self.func_call_graph_log.clone(),
            solver: self.solver.clone(),
            check_api_safety: self.check_api_safety,
            axiom_usage_info: self.axiom_usage_info,
            no_bv_simplify: self.no_bv_simplify,
            report_long_running: self.report_long_running,
        }
    }

    pub fn merge(&mut self, other: Self) {
        self.qid_map.borrow_mut().extend(other.qid_map.into_inner());
        self.chosen_triggers.borrow_mut().extend(other.chosen_triggers.into_inner());
    }

    // Report chosen triggers as strings for printing diagnostics
    pub fn get_chosen_triggers(&self) -> Vec<ChosenTriggers> {
        self.chosen_triggers.borrow().clone()
    }

    pub fn set_interpreter_log_file(
        &mut self,
        interpreter_log: Arc<std::sync::Mutex<Option<File>>>,
    ) {
        self.interpreter_log = interpreter_log;
    }
}

impl Ctx {
    pub fn new(
        krate: &Krate,
        global: GlobalCtx,
        module: Module,
        mono_types: Vec<MonoTyp>,
        spec_fn_types: Vec<usize>,
        reached_dyn_traits: HashSet<Path>,
        used_builtins: crate::prune::UsedBuiltins,
        fndef_types: Vec<Fun>,
        resolved_typs: Vec<crate::resolve_axioms::ResolvableType>,
    ) -> Result<Self, VirErr> {
        let name_ctxt = NameCtxt::new();
        let mut datatype_is_transparent: HashMap<Dt, bool> = HashMap::new();
        for datatype in krate.datatypes.iter() {
            datatype_is_transparent
                .insert(datatype.x.name.clone(), is_datatype_transparent(&module.x.path, datatype));
        }
        let datatypes_with_invariant =
            datatypes_invs(&module.x.path, &datatype_is_transparent, &krate.datatypes);
        let mut functions: Vec<Function> = Vec::new();
        let mut func_map: HashMap<Fun, Function> = HashMap::new();
        let mut fun_ident_map: HashMap<Ident, Fun> = HashMap::new();
        let funcs_with_ensure_predicate: HashMap<Fun, bool> = HashMap::new();
        for function in krate.functions.iter() {
            func_map.insert(function.x.name.clone(), function.clone());
            fun_ident_map
                .insert(fun_to_air_ident(&name_ctxt, &function.x.name), function.x.name.clone());
            functions.push(function.clone());
        }
        let mut datatype_map: HashMap<Dt, Datatype> = HashMap::new();
        for datatype in krate.datatypes.iter() {
            datatype_map.insert(datatype.x.name.clone(), datatype.clone());
        }
        let mut trait_map: HashMap<Path, Trait> = HashMap::new();
        for tr in krate.traits.iter() {
            trait_map.insert(tr.x.name.clone(), tr.clone());
        }
        let mut impl_map: HashMap<Path, TraitImpl> = HashMap::new();
        for ti in krate.trait_impls.iter() {
            impl_map.insert(ti.x.impl_path.clone(), ti.clone());
        }
        let reveal_group_set: HashSet<Fun> =
            krate.reveal_groups.iter().map(|g| g.x.name.clone()).collect();
        fun_ident_map
            .extend(reveal_group_set.iter().map(|g| (fun_to_air_ident(&name_ctxt, &g), g.clone())));
        let quantifier_count = RefCell::new(HashMap::new());
        let string_hashes = RefCell::new(HashMap::new());
        let byte_string_hashes = RefCell::new(HashMap::new());

        let mut fndef_type_set = HashSet::new();
        for fndef_type in fndef_types.iter() {
            fndef_type_set.insert(fndef_type.clone());
        }
        let mut opaque_type_map: HashMap<Path, OpaqueType> = HashMap::new();
        for opaque_type in krate.opaque_types.iter() {
            opaque_type_map.insert(opaque_type.x.name.clone(), opaque_type.clone());
        }

        Ok(Ctx {
            module,
            datatype_is_transparent,
            datatypes_with_invariant,
            mono_types,
            spec_fn_types,
            reached_dyn_traits,
            used_builtins,
            fndef_types,
            resolved_typs,
            fndef_type_set,
            functions,
            func_map,
            func_sst_map: HashMap::new(),
            fun_ident_map,
            reveal_groups: krate.reveal_groups.clone(),
            reveal_group_set,
            quantifier_count,
            funcs_with_ensure_predicate,
            datatype_map,
            trait_map,
            impl_map,
            name_ctxt,
            fun: None,
            global,
            string_hashes,
            byte_string_hashes,
            arch_word_bits: krate.arch.word_bits,
            opaque_type_map,
        })
    }

    pub fn free(self) -> GlobalCtx {
        self.global
    }

    pub fn prelude(&self, prelude_config: crate::prelude::PreludeConfig) -> Commands {
        let nodes = crate::prelude::prelude_nodes(&self.name_ctxt, prelude_config);
        air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .expect("internal error: malformed prelude")
    }

    pub fn module_path(&self) -> Path {
        self.module.x.path.clone()
    }

    pub fn fuel(&self) -> Commands {
        let mut ids: Vec<air::ast::Expr> = Vec::new();
        let mut commands: Vec<Command> = Vec::new();
        let mut names: Vec<Fun> = Vec::new();
        for function in &self.functions {
            match (function.x.mode, function.x.body.as_ref(), function.x.attrs.broadcast_forall) {
                (Mode::Spec, Some(_), false) | (Mode::Proof, _, true) => {
                    names.push(function.x.name.clone());
                }
                _ => {}
            }
        }
        for group in &self.reveal_groups {
            names.push(group.x.name.clone());
        }
        for name in names {
            let id = crate::def::prefix_fuel_id(&fun_to_air_ident(&self.name_ctxt, &name));
            ids.push(air::ast_util::ident_var(&id));
            let decl = Arc::new(DeclX::Const(id, str_typ(&FUEL_ID)));
            commands.push(Arc::new(CommandX::Global(decl)));
        }
        let distinct = Arc::new(air::ast::ExprX::Multi(MultiOp::Distinct, Arc::new(ids)));
        let decl = mk_unnamed_axiom(distinct);
        commands.push(Arc::new(CommandX::Global(decl)));
        for group in &self.reveal_groups {
            crate::sst_to_air_func::broadcast_forall_group_axioms(
                self,
                &mut commands,
                group,
                &self.global.crate_name,
            );
        }
        crate::sst_to_air_func::module_reveal_axioms(self, &mut commands, &self.module.x.reveals);
        Arc::new(commands)
    }
}
