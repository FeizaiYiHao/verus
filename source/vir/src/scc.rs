/*
 * Create a graph and then compute the strongly-connected components
 * of that graph.
 * Based on pseudocode from
 * https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm
 *
 * All internal work is index-based: T values are hashed only once per public
 * query (see `index_of`), and SCC membership is stored per node index in
 * `node_scc`.
 *
 * SCC lifecycle: `compute_sccs` fills the SCC tables for the graph as it is at that
 * moment. The graph may afterwards be extended, but only with edges between nodes
 * that already exist, and only if no SCC query is made until `reset_sccs` followed
 * by `compute_sccs` has recomputed the tables; the recomputation is then identical
 * to computing SCCs on a fresh graph built by the same add sequence.
 */
use std::cmp::min;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::{BuildHasher, BuildHasherDefault, Hasher};

type SccId = usize;
pub type NodeIndex = usize;

const FX_SEED: u64 = 0x51_7c_c1_b7_27_22_0a_95;

/// Deterministic, non-cryptographic Fx-style hasher (the multiply-rotate scheme used by
/// rustc's FxHasher). Hash values depend only on the hashed data, never on a random seed.
/// Only use it for maps whose iteration order is never observed, or where a fixed order is
/// acceptable; it provides no protection against adversarial (HashDoS) keys.
#[derive(Default, Clone, Copy)]
pub struct FxHasher {
    hash: u64,
}

impl FxHasher {
    #[inline]
    fn add(&mut self, word: u64) {
        self.hash = (self.hash.rotate_left(5) ^ word).wrapping_mul(FX_SEED);
    }
}

impl Hasher for FxHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            self.add(u64::from_le_bytes(chunk.try_into().expect("8-byte chunk")));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.add(u64::from_le_bytes(word));
        }
    }
    #[inline]
    fn write_u8(&mut self, i: u8) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u16(&mut self, i: u16) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u32(&mut self, i: u32) {
        self.add(i as u64);
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.add(i);
    }
    #[inline]
    fn write_usize(&mut self, i: usize) {
        self.add(i as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        // The multiply leaves the best-mixed bits at the top; rotate some of them into the
        // low bits that select the hash table bucket.
        self.hash.rotate_left(26)
    }
}

pub type FxBuildHasher = BuildHasherDefault<FxHasher>;
pub type FxHashMap<K, V> = HashMap<K, V, FxBuildHasher>;

/// Hasher for keys that are already hash values (u64 written once): returns them unchanged.
#[derive(Default, Clone, Copy)]
struct PrehashedHasher {
    hash: u64,
}

impl Hasher for PrehashedHasher {
    fn write(&mut self, _bytes: &[u8]) {
        unreachable!("PrehashedHasher only hashes u64 values")
    }
    #[inline]
    fn write_u64(&mut self, i: u64) {
        self.hash = i;
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.hash
    }
}

const NO_NODE: NodeIndex = usize::MAX;

#[derive(Clone)]
pub struct Graph<T: std::cmp::Eq + std::hash::Hash + Clone, S: BuildHasher = FxBuildHasher> {
    // Hashes T values (see `hash_value`)
    hasher: S,
    // Map hash_value(t) to the most recently added node with that hash; earlier nodes with
    // the same hash follow through Node::next_same_hash. Together this maps each T to its
    // index in nodes, storing each T only once (in nodes). Only queried, never iterated.
    h: HashMap<u64, NodeIndex, BuildHasherDefault<PrehashedHasher>>,
    nodes: Vec<Node<T>>,

    has_run: bool,
    // A node or edge was added after compute_sccs, so the SCC tables are stale until
    // reset_sccs + compute_sccs
    stale_sccs: bool,

    // Map node index to SCC id (filled by compute_sccs, covers all nodes present at that time)
    node_scc: Vec<SccId>,
    // Nodes of SCC s are scc_nodes[scc_start[s]..scc_start[s + 1]], in Tarjan pop order;
    // the first one is the SCC representative.
    scc_nodes: Vec<NodeIndex>,
    scc_start: Vec<usize>,
}

#[derive(Clone)]
struct Node<T: std::cmp::Eq + std::hash::Hash + Clone> {
    t: T,
    edges: Vec<NodeIndex>,
    // Previously added node with the same hash_value, or NO_NODE
    next_same_hash: NodeIndex,
}

/// Position of every SCC in the result of `sort_sccs`, indexed by SCC id.
/// Only valid for the graph and SCC computation that produced it.
pub struct SccOrder {
    pos: Vec<usize>,
}

/// Reusable scratch space for `can_reach_with`; one per thread.
/// SCC ids are marked with the current epoch, so no clearing is needed between queries.
pub struct Visited {
    mark: Vec<u32>,
    epoch: u32,
    worklist: Vec<SccId>,
}

impl Visited {
    pub fn new() -> Visited {
        Visited { mark: Vec::new(), epoch: 0, worklist: Vec::new() }
    }

    // Start a query over num_sccs SCCs: afterwards no SCC is marked
    fn start(&mut self, num_sccs: usize) {
        if self.mark.len() < num_sccs {
            self.mark.resize(num_sccs, 0);
        }
        if self.epoch == u32::MAX {
            self.mark.fill(0);
            self.epoch = 0;
        }
        self.epoch += 1;
        self.worklist.clear();
    }

    // Mark s; returns true if s was not yet marked in this query
    #[inline]
    fn insert(&mut self, s: SccId) -> bool {
        if self.mark[s] == self.epoch {
            false
        } else {
            self.mark[s] = self.epoch;
            true
        }
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone> Graph<T> {
    pub fn new() -> Graph<T> {
        Graph::with_hasher(FxBuildHasher::default())
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone> Default for Graph<T> {
    fn default() -> Graph<T> {
        Graph::new()
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone, S: BuildHasher> Graph<T, S> {
    pub fn with_hasher(hasher: S) -> Graph<T, S> {
        Graph {
            hasher,
            h: HashMap::default(),
            nodes: Vec::new(),
            has_run: false,
            stale_sccs: false,
            node_scc: Vec::new(),
            scc_nodes: Vec::new(),
            scc_start: vec![0],
        }
    }

    pub fn add_node(&mut self, value: T) {
        self.get_or_add(value);
    }

    /// The hash under which `value` is indexed. Only depends on `value` and the hasher;
    /// for `Graph<T>` (the default Fx hasher) it is `FxBuildHasher::default().hash_one(value)`,
    /// so it can be computed ahead of time (e.g. in parallel) for `intern_hashed`.
    #[inline]
    pub fn hash_value(&self, value: &T) -> u64 {
        self.hasher.hash_one(value)
    }

    fn index_of_hashed(&self, hash: u64, value: &T) -> Option<NodeIndex> {
        let mut v = *self.h.get(&hash)?;
        while v != NO_NODE {
            let node = &self.nodes[v];
            if node.t == *value {
                return Some(v);
            }
            v = node.next_same_hash;
        }
        None
    }

    // Index of the node for value, if present
    fn index_of(&self, value: &T) -> Option<NodeIndex> {
        self.index_of_hashed(self.hash_value(value), value)
    }

    fn expect_index_of(&self, value: &T) -> NodeIndex {
        self.index_of(value).expect("key not present")
    }

    fn get_or_add_hashed(&mut self, hash: u64, value: T) -> NodeIndex {
        if let Some(v) = self.index_of_hashed(hash, &value) {
            return v;
        }
        let v = self.nodes.len();
        let next_same_hash = self.h.insert(hash, v).unwrap_or(NO_NODE);
        self.nodes.push(Node { t: value, edges: Vec::new(), next_same_hash });
        self.stale_sccs |= self.has_run;
        v
    }

    fn get_or_add(&mut self, value: T) -> NodeIndex {
        self.get_or_add_hashed(self.hash_value(&value), value)
    }

    /// Same as `add_node`, returning the node's index for use with `push_edge_idx`.
    /// Indices are assigned in first-insertion order and never change.
    pub fn intern(&mut self, value: T) -> NodeIndex {
        self.get_or_add(value)
    }

    /// Same as `intern`, with `hash` precomputed; it must equal `self.hash_value(&value)`.
    pub fn intern_hashed(&mut self, hash: u64, value: T) -> NodeIndex {
        debug_assert!(hash == self.hash_value(&value), "intern_hashed: wrong hash");
        self.get_or_add_hashed(hash, value)
    }

    /// Same as `add_edge` on the values that `intern` returned `src` and `dst` for.
    pub fn push_edge_idx(&mut self, src: NodeIndex, dst: NodeIndex) {
        assert!(dst < self.nodes.len());
        self.nodes[src].edges.push(dst);
        self.stale_sccs |= self.has_run;
    }

    pub fn add_edge(&mut self, src: T, dst: T) {
        let v = self.get_or_add(src);
        let w = self.get_or_add(dst);
        self.push_edge_idx(v, w);
    }

    #[allow(dead_code)]
    pub fn add_directed_edge_if_nodes_exist(&mut self, src: T, dst: T) {
        let v = self.index_of(&src);
        if let Some(v) = v {
            let w = self.index_of(&dst);
            if let Some(w) = w {
                self.nodes[v].edges.push(w);
                self.stale_sccs |= self.has_run;
            }
        }
    }

    fn num_sccs(&self) -> usize {
        self.scc_start.len() - 1
    }

    fn scc_members(&self, s: SccId) -> &[NodeIndex] {
        &self.scc_nodes[self.scc_start[s]..self.scc_start[s + 1]]
    }

    fn scc_rep(&self, s: SccId) -> NodeIndex {
        self.scc_nodes[self.scc_start[s]]
    }

    // Every SCC query goes through this check
    #[inline]
    fn assert_sccs(&self) {
        assert!(self.has_run);
        debug_assert!(!self.stale_sccs, "graph changed after compute_sccs; call reset_sccs");
    }

    // SCC id of t, or None if t is not a node covered by compute_sccs
    fn scc_of(&self, t: &T) -> Option<SccId> {
        self.index_of(t).and_then(|v| self.node_scc.get(v).copied())
    }

    fn expect_scc_of(&self, t: &T) -> SccId {
        self.scc_of(t).expect("node not present in SCC mapping")
    }

    /// Discards the SCC tables so that `compute_sccs` can run again on the same graph,
    /// avoiding a clone when SCCs are needed both before and after adding some edges.
    /// Invariant (see the module comment): between `compute_sccs` and `reset_sccs`, only
    /// edges between existing nodes may be added and no SCC query may be made.
    pub fn reset_sccs(&mut self) {
        self.has_run = false;
        self.stale_sccs = false;
        self.node_scc.clear();
        self.scc_nodes.clear();
        self.scc_start.clear();
        self.scc_start.push(0);
    }

    // Iterative Tarjan: visits edges and emits SCCs in exactly the same order as the
    // recursive formulation (each frame resumes at its next edge; on return from a
    // child the parent takes min(lowlink, child.lowlink)).
    pub fn compute_sccs(&mut self) {
        assert!(!self.has_run);
        self.has_run = true;
        self.stale_sccs = false;

        const UNVISITED: usize = usize::MAX;
        let n = self.nodes.len();
        let mut index: Vec<usize> = vec![UNVISITED; n];
        let mut lowlink: Vec<usize> = vec![UNVISITED; n];
        let mut on_stack: Vec<bool> = vec![false; n];
        let mut stack: Vec<NodeIndex> = Vec::with_capacity(n);
        // (node, next edge position)
        let mut calls: Vec<(NodeIndex, usize)> = Vec::new();
        let mut next_index = 0;
        self.node_scc.clear();
        self.node_scc.resize(n, UNVISITED);
        self.scc_nodes.clear();
        self.scc_nodes.reserve(n);
        self.scc_start.clear();
        self.scc_start.push(0);

        for root in 0..n {
            if index[root] != UNVISITED {
                continue;
            }
            index[root] = next_index;
            lowlink[root] = next_index;
            next_index += 1;
            stack.push(root);
            on_stack[root] = true;
            calls.push((root, 0));
            while let Some(frame) = calls.last_mut() {
                let v = frame.0;
                let edges = &self.nodes[v].edges;
                if frame.1 < edges.len() {
                    let w = edges[frame.1];
                    frame.1 += 1;
                    if index[w] == UNVISITED {
                        index[w] = next_index;
                        lowlink[w] = next_index;
                        next_index += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        calls.push((w, 0));
                    } else if on_stack[w] {
                        lowlink[v] = min(lowlink[v], index[w]);
                    }
                    continue;
                }
                calls.pop();
                if lowlink[v] == index[v] {
                    let id = self.num_sccs();
                    loop {
                        let w = stack.pop().expect("Tarjan stack");
                        on_stack[w] = false;
                        self.scc_nodes.push(w);
                        self.node_scc[w] = id;
                        if w == v {
                            break;
                        }
                    }
                    self.scc_start.push(self.scc_nodes.len());
                }
                if let Some(parent) = calls.last() {
                    let p = parent.0;
                    lowlink[p] = min(lowlink[p], lowlink[v]);
                }
            }
        }
    }

    // SCC ids sorted so that later SCCs point only to earlier SCCs.
    // (Iterative depth-first postorder over SCCs, in the same order as the recursive
    // traversal: SCCs by id, members in SCC order, edges in insertion order.)
    fn sorted_scc_ids(&self) -> Vec<SccId> {
        self.assert_sccs();
        let num_sccs = self.num_sccs();
        let mut visited: Vec<bool> = vec![false; num_sccs];
        let mut sorted: Vec<SccId> = Vec::with_capacity(num_sccs);
        // (scc, position in scc_nodes, next edge position of that member)
        let mut calls: Vec<(SccId, usize, usize)> = Vec::new();
        for s0 in 0..num_sccs {
            if visited[s0] {
                continue;
            }
            visited[s0] = true;
            calls.push((s0, self.scc_start[s0], 0));
            while let Some(frame) = calls.last_mut() {
                let (s, pos, e) = *frame;
                if pos == self.scc_start[s + 1] {
                    calls.pop();
                    sorted.push(s);
                    continue;
                }
                let edges = &self.nodes[self.scc_nodes[pos]].edges;
                if e == edges.len() {
                    *frame = (s, pos + 1, 0);
                    continue;
                }
                frame.2 = e + 1;
                let c = self.node_scc[edges[e]];
                if !visited[c] {
                    visited[c] = true;
                    calls.push((c, self.scc_start[c], 0));
                }
            }
        }
        sorted
    }

    // Return vector of representatives, one for each SCC, sorted so that later
    // elements point only to earlier elements.
    pub fn sort_sccs(&self) -> Vec<T> {
        self.sorted_scc_ids().into_iter().map(|s| self.nodes[self.scc_rep(s)].t.clone()).collect()
    }

    /// `sort_sccs`, together with each SCC's position in the result, for `can_reach_with`.
    pub fn sort_sccs_with_order(&self) -> (Vec<T>, SccOrder) {
        let ids = self.sorted_scc_ids();
        let mut pos = vec![0; ids.len()];
        for (i, s) in ids.iter().enumerate() {
            pos[*s] = i;
        }
        let sorted = ids.into_iter().map(|s| self.nodes[self.scc_rep(s)].t.clone()).collect();
        (sorted, SccOrder { pos })
    }

    pub fn node_has_direct_edge_to_itself(&self, t: &T) -> bool {
        self.assert_sccs();
        let v: NodeIndex = self.expect_index_of(t);
        self.nodes[v].edges.contains(&v)
    }

    pub fn get_edges_from<'a>(&'a self, t: &T) -> impl Iterator<Item = &'a T> + 'a + use<'a, T, S> {
        let v: NodeIndex = self.expect_index_of(t);
        self.nodes[v].edges.iter().map(move |i| &self.nodes[*i].t)
    }

    pub fn get_scc_size(&self, t: &T) -> usize {
        self.assert_sccs();
        match self.scc_of(t) {
            Some(s) => self.scc_members(s).len(),
            None => 1,
        }
    }

    /// Returns true if the given element is part of a cycle (including self-loops)
    pub fn node_is_in_cycle(&self, t: &T) -> bool {
        self.node_has_direct_edge_to_itself(t) || self.get_scc_size(t) > 1
    }

    pub fn get_scc_rep(&self, t: &T) -> T {
        self.assert_sccs();
        let s = self.expect_scc_of(t);
        self.nodes[self.scc_rep(s)].t.clone()
    }

    // Distinct SCCs have distinct representatives (distinct nodes have distinct T),
    // so comparing SCC ids is equivalent to comparing representatives.
    pub fn in_same_scc(&self, t1: &T, t2: &T) -> bool {
        if t1 == t2 {
            return true;
        }
        self.assert_sccs();
        let s1 = self.expect_scc_of(t1);
        let s2 = self.expect_scc_of(t2);
        s1 == s2
    }

    pub fn get_scc_nodes(&self, t: &T) -> Vec<T> {
        self.assert_sccs();
        let s = self.expect_scc_of(t);
        self.scc_members(s).iter().map(|i| self.nodes[*i].t.clone()).collect()
    }

    pub fn shortest_cycle_back_to_self(&self, t: &T) -> Vec<T> {
        self.assert_sccs();
        let root: NodeIndex = self.expect_index_of(t);
        // Every node on a cycle through root lies in root's SCC, so restricting the
        // breadth-first search to root's SCC drops only paths that can never return to
        // root; the first cycle found (and hence the result) is unchanged.
        // Each reached node has exactly one path (the one that first reached it), so we
        // store a parent pointer instead of a full path; a FIFO queue visits nodes in the
        // same order as the depth-by-depth path lists. (parent is never iterated.)
        let root_scc = self.node_scc.get(root).copied();
        let mut parent: FxHashMap<NodeIndex, NodeIndex> = FxHashMap::default();
        parent.insert(root, root);
        let mut queue: std::collections::VecDeque<NodeIndex> = std::collections::VecDeque::new();
        queue.push_back(root);
        while let Some(u) = queue.pop_front() {
            for edge in self.nodes[u].edges.iter() {
                if *edge == root {
                    // reached the root, found cycle
                    let mut path = vec![u];
                    while *path.last().expect("path") != root {
                        path.push(parent[path.last().expect("path")]);
                    }
                    return path.into_iter().rev().map(|i| self.nodes[i].t.clone()).collect();
                }
                if root_scc.is_some() && self.node_scc.get(*edge).copied() != root_scc {
                    continue;
                }
                parent.entry(*edge).or_insert_with(|| {
                    queue.push_back(*edge);
                    u
                });
            }
        }
        panic!("assertion failed: paths_at_depth.len() != 0")
    }

    // Can source reach target by traversing 0 or more edges?
    // (Note: if the graph is already sorted, we can optimize the traversal.)
    pub fn can_reach(
        &self,
        source: &T,
        target: &T,
        // if sort_sccs returns v: Vec<T>, map each T to its index in the sorted Vec<T>:
        sorted_order: Option<&HashMap<T, usize>>,
    ) -> bool {
        self.assert_sccs();
        let src = self.expect_scc_of(source);
        let tgt = self.expect_scc_of(target);
        let tgt_sort_index = sorted_order.map(|order| order[&self.nodes[self.scc_rep(tgt)].t]);
        let mut reached: HashSet<SccId> = HashSet::new();
        let mut worklist: Vec<SccId> = vec![src];
        while let Some(scc) = worklist.pop() {
            if scc == tgt {
                return true;
            }
            if !reached.insert(scc) {
                continue;
            }
            if let (Some(order), Some(tgt_sort_index)) = (sorted_order, tgt_sort_index) {
                let scc_sort_index = order[&self.nodes[self.scc_rep(scc)].t];
                if scc_sort_index < tgt_sort_index {
                    // optimization: scc has already passed the target in the sorted sccs,
                    // so we can't reach target from scc
                    continue;
                }
            }
            for v in self.scc_members(scc) {
                worklist.extend(self.nodes[*v].edges.iter().map(|w| self.node_scc[*w]));
            }
        }
        false
    }

    /// Same result as `can_reach`, but index-based: hashes only `source` and `target`,
    /// reuses the caller's `visited` buffer, and prunes with an `SccOrder` from
    /// `sort_sccs_with_order` on this graph's current SCCs.
    /// (Pruning only drops SCCs that sort strictly before the target, which cannot reach it.)
    /// SCCs are expanded in the same order as `can_reach` (depth-first, marked when popped,
    /// neighbors pushed in edge order); pruned SCCs are just not pushed, and the target is
    /// detected when pushed, so this never expands more SCCs.
    pub fn can_reach_with(
        &self,
        visited: &mut Visited,
        source: &T,
        target: &T,
        sorted_order: Option<&SccOrder>,
    ) -> bool {
        self.assert_sccs();
        let src = self.expect_scc_of(source);
        let tgt = self.expect_scc_of(target);
        if src == tgt {
            return true;
        }
        let num_sccs = self.num_sccs();
        let pos: &[usize] = match sorted_order {
            Some(order) => {
                assert!(order.pos.len() == num_sccs);
                &order.pos
            }
            None => &[],
        };
        let tgt_pos = pos.get(tgt).copied();
        if let Some(tgt_pos) = tgt_pos {
            if pos[src] < tgt_pos {
                return false;
            }
        }
        visited.start(num_sccs);
        visited.worklist.push(src);
        while let Some(scc) = visited.worklist.pop() {
            if !visited.insert(scc) {
                continue;
            }
            for v in self.scc_members(scc) {
                for w in self.nodes[*v].edges.iter() {
                    let c = self.node_scc[*w];
                    if c == tgt {
                        return true;
                    }
                    if let Some(tgt_pos) = tgt_pos {
                        if pos[c] < tgt_pos {
                            continue;
                        }
                    }
                    // (already-expanded SCCs are skipped when popped: checking here is slower)
                    visited.worklist.push(c);
                }
            }
        }
        false
    }

    pub fn to_dot(
        &self,
        mut w: impl std::io::Write,
        filter_by: impl Fn(&T) -> (/* always */ bool, /* only if reached */ bool),
        node_options: impl Fn(&T) -> String,
    ) {
        fn io_err<V>(o: Result<V, std::io::Error>) {
            o.unwrap_or_else(|err| panic!("i/o failed: {}", err));
        }

        io_err(writeln!(w, "digraph M {{"));
        io_err(writeln!(w, "  rankdir=LR;"));
        io_err(writeln!(w, "  node [shape=\"box\"];"));
        let mut render_nodes = BTreeSet::new();
        for (i, n) in self.nodes.iter().enumerate() {
            if n.edges.len() > 0 {
                if filter_by(&n.t).1 {
                    render_nodes.insert(i);
                }
            }
            for e in n.edges.iter() {
                if filter_by(&n.t).1 && filter_by(&self.nodes[*e].t).0 {
                    render_nodes.insert(*e);
                }
            }
        }
        for (i, n) in self.nodes.iter().enumerate() {
            if render_nodes.contains(&i) {
                io_err(writeln!(w, "  node_{} [{}]", i, node_options(&n.t)));
            }
        }
        io_err(writeln!(w, ""));
        for (i, n) in self.nodes.iter().enumerate().filter(|(i, _)| render_nodes.contains(i)) {
            for e in
                n.edges.iter().filter(|x| render_nodes.contains(x)).collect::<HashSet<_>>().iter()
            {
                io_err(writeln!(w, "  node_{} -> node_{}", i, e));
            }
        }
        io_err(writeln!(w, "}}"));
    }
}

impl<T: std::cmp::Eq + std::hash::Hash + Clone + std::fmt::Debug, S: BuildHasher> std::fmt::Debug
    for Graph<T, S>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Graph:\n")?;
        for node in self.nodes.iter() {
            write!(f, "    {:?}\n", node.t)?;
            for idx in node.edges.iter() {
                let succ_t = &self.nodes[*idx].t;
                write!(f, "     -> {:?}\n", succ_t)?;
            }
        }
        if self.has_run && self.stale_sccs {
            write!(f, "SCCs stale (graph changed after compute_sccs)")?;
        } else if self.has_run {
            write!(f, "SCCs:\n")?;
            let scc_reps = self.sort_sccs();
            for scc_rep in scc_reps.iter() {
                let nodes = self.get_scc_nodes(scc_rep);
                write!(f, "{{\n")?;
                for node in nodes {
                    write!(f, "    {:?}\n", node)?;
                }
                write!(f, "}}\n")?;
            }
        } else {
            write!(f, "SCC not yet run")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{FxBuildHasher, FxHashMap, FxHasher, Graph, Visited};
    use std::cmp::min;
    use std::collections::{HashMap, HashSet};
    use std::hash::BuildHasher;

    /// The previous hash-keyed recursive implementation, kept verbatim in behavior as
    /// the reference for SCC ids/members/representatives, sort order and reachability.
    struct RefGraph {
        edges: Vec<Vec<usize>>,
        index: Vec<usize>,
        lowlink: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        sccs: Vec<Vec<usize>>,
        mapping: HashMap<String, usize>,
    }

    fn name(i: usize) -> String {
        format!("node_{i}")
    }

    impl RefGraph {
        fn new(edges: Vec<Vec<usize>>) -> RefGraph {
            let n = edges.len();
            let mut g = RefGraph {
                edges,
                index: vec![usize::MAX; n],
                lowlink: vec![usize::MAX; n],
                on_stack: vec![false; n],
                stack: Vec::new(),
                next: 0,
                sccs: Vec::new(),
                mapping: HashMap::new(),
            };
            for i in 0..n {
                if g.index[i] == usize::MAX {
                    g.strongconnect(i);
                }
            }
            g
        }

        fn strongconnect(&mut self, v: usize) {
            self.index[v] = self.next;
            self.lowlink[v] = self.next;
            self.next += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for i in 0..self.edges[v].len() {
                let w = self.edges[v][i];
                if self.index[w] == usize::MAX {
                    self.strongconnect(w);
                    self.lowlink[v] = min(self.lowlink[v], self.lowlink[w]);
                } else if self.on_stack[w] {
                    self.lowlink[v] = min(self.lowlink[v], self.index[w]);
                }
            }
            if self.lowlink[v] == self.index[v] {
                let id = self.sccs.len();
                let mut comp = Vec::new();
                loop {
                    let w = self.stack.pop().unwrap();
                    self.on_stack[w] = false;
                    comp.push(w);
                    self.mapping.insert(name(w), id);
                    if w == v {
                        break;
                    }
                }
                self.sccs.push(comp);
            }
        }

        fn sort_node(&self, visited: &mut Vec<bool>, sorted: &mut Vec<String>, s: usize) {
            if visited[s] {
                return;
            }
            visited[s] = true;
            for v in self.sccs[s].iter() {
                for w in self.edges[*v].iter() {
                    self.sort_node(visited, sorted, self.mapping[&name(*w)]);
                }
            }
            sorted.push(name(self.sccs[s][0]));
        }

        fn sort_sccs(&self) -> Vec<String> {
            let mut visited = vec![false; self.sccs.len()];
            let mut sorted = Vec::new();
            for s in 0..self.sccs.len() {
                self.sort_node(&mut visited, &mut sorted, s);
            }
            sorted
        }

        fn shortest_cycle(&self, root: usize) -> Option<Vec<String>> {
            let mut paths = vec![vec![root]];
            let mut reached = HashSet::from([root]);
            while !paths.is_empty() {
                let mut next = Vec::new();
                for p in paths {
                    for e in self.edges[*p.last().unwrap()].iter() {
                        if *e == root {
                            return Some(p.into_iter().map(name).collect());
                        }
                        if reached.insert(*e) {
                            let mut q = p.clone();
                            q.push(*e);
                            next.push(q);
                        }
                    }
                }
                paths = next;
            }
            None
        }
    }

    // Naive reachability (0 or more edges) by breadth-first search
    fn reach(edges: &Vec<Vec<usize>>, s: usize) -> Vec<bool> {
        let mut seen = vec![false; edges.len()];
        let mut work = vec![s];
        seen[s] = true;
        while let Some(v) = work.pop() {
            for w in edges[v].iter() {
                if !seen[*w] {
                    seen[*w] = true;
                    work.push(*w);
                }
            }
        }
        seen
    }

    struct Rng(u64);
    impl Rng {
        fn next(&mut self, bound: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % bound as u64) as usize
        }
    }

    fn random_edges(rng: &mut Rng, n: usize, m: usize) -> Vec<Vec<usize>> {
        let mut edges = vec![Vec::new(); n];
        for _ in 0..m {
            let (a, b) = (rng.next(n), rng.next(n));
            edges[a].push(b);
        }
        edges
    }

    fn build(edges: &Vec<Vec<usize>>, rng: &mut Rng) -> Graph<String> {
        let mut g = Graph::new();
        // Mix add_node and add_edge so node indices follow first-mention order
        for (v, es) in edges.iter().enumerate() {
            if rng.next(2) == 0 {
                g.add_node(name(v));
            }
            for w in es.iter() {
                g.add_edge(name(v), name(*w));
            }
            g.add_node(name(v));
        }
        g.compute_sccs();
        g
    }

    // Node indices in `g` may differ from v, so build the reference over g's own order
    fn reference_for(g: &Graph<String>) -> (RefGraph, Vec<String>) {
        let names: Vec<String> = g.nodes.iter().map(|n| n.t.clone()).collect();
        let edges = g.nodes.iter().map(|n| n.edges.clone()).collect();
        (RefGraph::new(edges), names)
    }

    #[test]
    fn scc_matches_reference_on_random_graphs() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        // shared across rounds, so it is reused across graphs of different sizes
        let mut visited = Visited::new();
        for round in 0..400 {
            let n = 1 + rng.next(if round < 300 { 12 } else { 60 });
            let m = rng.next(3 * n + 1);
            let edges = random_edges(&mut rng, n, m);
            let g = build(&edges, &mut rng);
            let (r, names) = reference_for(&g);
            // reference uses positional names; translate to g's names
            let tr = |s: String| {
                names[s.strip_prefix("node_").unwrap().parse::<usize>().unwrap()].clone()
            };

            let sorted = g.sort_sccs();
            let ref_sorted: Vec<String> = r.sort_sccs().into_iter().map(tr).collect();
            assert_eq!(sorted, ref_sorted);
            let order: HashMap<String, usize> =
                sorted.iter().enumerate().map(|(i, s)| (s.clone(), i)).collect();
            let (sorted2, scc_order) = g.sort_sccs_with_order();
            assert_eq!(sorted2, sorted);
            for t in names.iter() {
                let s = g.node_scc[g.index_of(t).unwrap()];
                assert_eq!(scc_order.pos[s], order[&g.get_scc_rep(t)]);
            }
            // topological property: edges go only to earlier (or same) SCCs
            for (v, es) in r.edges.iter().enumerate() {
                for w in es.iter() {
                    assert!(order[&g.get_scc_rep(&names[*w])] <= order[&g.get_scc_rep(&names[v])]);
                }
            }

            let closure: Vec<Vec<bool>> = (0..n).map(|v| reach(&r.edges, v)).collect();
            for v in 0..n {
                let t = &names[v];
                let s = r.mapping[&name(v)];
                assert_eq!(g.get_scc_rep(t), names[r.sccs[s][0]]);
                let members: Vec<String> = r.sccs[s].iter().map(|i| names[*i].clone()).collect();
                assert_eq!(g.get_scc_nodes(t), members);
                assert_eq!(g.get_scc_size(t), members.len());
                assert_eq!(g.node_has_direct_edge_to_itself(t), r.edges[v].contains(&v));
                assert_eq!(g.node_is_in_cycle(t), r.edges[v].contains(&v) || members.len() > 1);
                if g.node_is_in_cycle(t) {
                    assert_eq!(
                        Some(g.shortest_cycle_back_to_self(t)),
                        r.shortest_cycle(v).map(|c| c.into_iter().map(tr).collect())
                    );
                }
                for w in 0..n {
                    let u = &names[w];
                    let mutual = closure[v][w] && closure[w][v];
                    assert_eq!(g.in_same_scc(t, u), mutual);
                    assert_eq!(mutual, r.mapping[&name(v)] == r.mapping[&name(w)]);
                    assert_eq!(g.can_reach(t, u, None), closure[v][w]);
                    assert_eq!(g.can_reach(t, u, Some(&order)), closure[v][w]);
                    assert_eq!(g.can_reach_with(&mut visited, t, u, None), closure[v][w]);
                    let r = g.can_reach_with(&mut visited, t, u, Some(&scc_order));
                    assert_eq!(r, closure[v][w]);
                }
            }
            assert_eq!(g.get_scc_size(&"absent".to_string()), 1);
        }
    }

    #[test]
    fn scc_deep_chain_does_not_overflow() {
        let n = 200_000;
        let mut g = Graph::new();
        for i in 0..n {
            g.add_edge(i, (i + 1) % n);
        }
        g.compute_sccs();
        assert_eq!(g.get_scc_size(&0), n);
        assert_eq!(g.sort_sccs().len(), 1);
        let mut g = Graph::new();
        for i in 0..n {
            g.add_edge(i, i + 1);
        }
        g.compute_sccs();
        let sorted = g.sort_sccs();
        assert_eq!(sorted.len(), n + 1);
        assert_eq!(sorted[0], n);
        assert!(g.can_reach(&0, &n, None));
        assert!(!g.can_reach(&n, &0, None));
        let (_, order) = g.sort_sccs_with_order();
        let mut visited = Visited::new();
        assert!(g.can_reach_with(&mut visited, &0, &n, None));
        assert!(g.can_reach_with(&mut visited, &0, &n, Some(&order)));
        assert!(!g.can_reach_with(&mut visited, &n, &0, None));
        assert!(!g.can_reach_with(&mut visited, &n, &0, Some(&order)));
    }

    // Everything observable about g: nodes, edges, SCC tables and sort order
    fn snapshot(
        g: &Graph<String>,
    ) -> (Vec<(String, Vec<usize>)>, Vec<usize>, Vec<usize>, Vec<usize>) {
        let nodes = g.nodes.iter().map(|n| (n.t.clone(), n.edges.clone())).collect();
        (nodes, g.node_scc.clone(), g.scc_nodes.clone(), g.scc_start.clone())
    }

    #[derive(Clone)]
    enum Op {
        Node(usize),
        Edge(usize, usize),
    }

    fn random_ops(rng: &mut Rng, n: usize, len: usize) -> Vec<Op> {
        (0..len)
            .map(|_| {
                if rng.next(4) == 0 {
                    Op::Node(rng.next(n))
                } else {
                    Op::Edge(rng.next(n), rng.next(n))
                }
            })
            .collect()
    }

    fn apply(g: &mut Graph<String>, op: &Op) {
        match op {
            Op::Node(v) => g.add_node(name(*v)),
            Op::Edge(v, w) => g.add_edge(name(*v), name(*w)),
        }
    }

    // compute_sccs, add edges between existing nodes, reset_sccs, compute_sccs:
    // identical to computing the SCCs once on a fresh graph with all edges
    #[test]
    fn reset_sccs_matches_fresh_graph() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        let mut visited = Visited::new();
        for round in 0..300 {
            let n = 1 + rng.next(if round < 200 { 10 } else { 50 });
            let len = rng.next(4 * n + 1);
            let ops = random_ops(&mut rng, n, len);
            let mut g = Graph::new();
            for op in ops.iter() {
                apply(&mut g, op);
            }
            g.compute_sccs();
            let first = snapshot(&g);
            let first_sorted = g.sort_sccs();
            // extra edges between existing nodes (possibly via the index API)
            let existing: Vec<usize> = g
                .nodes
                .iter()
                .map(|n| n.t.strip_prefix("node_").unwrap().parse::<usize>().unwrap())
                .collect();
            let mut extra: Vec<(usize, usize)> = Vec::new();
            if !existing.is_empty() {
                for _ in 0..rng.next(2 * n + 1) {
                    let v = existing[rng.next(existing.len())];
                    let w = existing[rng.next(existing.len())];
                    extra.push((v, w));
                }
            }
            for (v, w) in extra.iter() {
                if rng.next(2) == 0 {
                    g.add_edge(name(*v), name(*w));
                } else {
                    let (v, w) = (g.intern(name(*v)), g.intern(name(*w)));
                    g.push_edge_idx(v, w);
                }
            }
            assert!(g.stale_sccs == !extra.is_empty());
            g.reset_sccs();
            g.compute_sccs();

            let mut fresh = Graph::new();
            for op in ops.iter() {
                apply(&mut fresh, op);
            }
            if extra.is_empty() {
                fresh.compute_sccs();
                assert_eq!(snapshot(&fresh), first);
                assert_eq!(fresh.sort_sccs(), first_sorted);
            }
            for (v, w) in extra.iter() {
                fresh.add_edge(name(*v), name(*w));
            }
            if !extra.is_empty() {
                fresh.compute_sccs();
            }
            assert_eq!(snapshot(&g), snapshot(&fresh));
            assert_eq!(g.sort_sccs(), fresh.sort_sccs());
            let (_, order) = g.sort_sccs_with_order();
            let edges: Vec<Vec<usize>> = g.nodes.iter().map(|n| n.edges.clone()).collect();
            for v in 0..g.nodes.len() {
                let closure = reach(&edges, v);
                let t = g.nodes[v].t.clone();
                for w in 0..g.nodes.len() {
                    let u = g.nodes[w].t.clone();
                    assert_eq!(g.can_reach_with(&mut visited, &t, &u, Some(&order)), closure[w]);
                    assert_eq!(g.can_reach(&t, &u, None), closure[w]);
                }
            }
        }
    }

    // Recording edges with local interning (first-mention order, local index pairs) and
    // replaying them with one intern per distinct node gives the same graph as add_edge
    // on every recorded edge, including when a merge map identifies distinct local nodes.
    #[test]
    fn intern_replay_matches_add_edge() {
        let mut rng = Rng(0x853c49e6748fea9b);
        for round in 0..300 {
            let n = 1 + rng.next(if round < 200 { 10 } else { 60 });
            // merge some nodes into others (like GraphBuilder::replace)
            let merge: Vec<usize> =
                (0..n).map(|v| if rng.next(5) == 0 { rng.next(n) } else { v }).collect();
            let replace = |v: usize| name(merge[v]);
            let mut direct: Graph<String> = Graph::new();
            let mut replayed: Graph<String> = Graph::new();
            for _ in 0..rng.next(8) {
                // interleave plain node additions between records
                if rng.next(2) == 0 {
                    let v = rng.next(n);
                    direct.add_node(replace(v));
                    replayed.add_node(replace(v));
                }
                let edges: Vec<(usize, usize)> =
                    (0..rng.next(3 * n + 1)).map(|_| (rng.next(n), rng.next(n))).collect();
                for (v, w) in edges.iter() {
                    direct.add_edge(replace(*v), replace(*w));
                }
                // record
                let mut local_nodes: Vec<usize> = Vec::new();
                let mut local_index: FxHashMap<usize, u32> = FxHashMap::default();
                let mut local = |v: usize| {
                    *local_index.entry(v).or_insert_with(|| {
                        local_nodes.push(v);
                        (local_nodes.len() - 1) as u32
                    })
                };
                let local_edges: Vec<(u32, u32)> =
                    edges.iter().map(|(v, w)| (local(*v), local(*w))).collect();
                // replay
                let global: Vec<usize> =
                    local_nodes.iter().map(|v| replayed.intern(replace(*v))).collect();
                for (s, d) in local_edges {
                    replayed.push_edge_idx(global[s as usize], global[d as usize]);
                }
            }
            direct.compute_sccs();
            replayed.compute_sccs();
            assert_eq!(snapshot(&direct), snapshot(&replayed));
            assert_eq!(direct.sort_sccs(), replayed.sort_sccs());
            for t in direct.nodes.iter() {
                assert_eq!(direct.index_of(&t.t), replayed.index_of(&t.t));
            }
        }
    }

    // Every value hashes to one of `buckets` hashes, forcing long same-hash chains
    #[derive(Default)]
    struct FewBuckets<const BUCKETS: u64>(u64);
    impl<const BUCKETS: u64> std::hash::Hasher for FewBuckets<BUCKETS> {
        fn write(&mut self, bytes: &[u8]) {
            for b in bytes {
                self.0 = self.0.wrapping_mul(31).wrapping_add(*b as u64);
            }
        }
        fn finish(&self) -> u64 {
            self.0 % BUCKETS
        }
    }

    fn check_hasher<S: std::hash::BuildHasher>(fx: &Graph<String>, ops: &Vec<Op>, hasher: S) {
        let mut g: Graph<String, S> = Graph::with_hasher(hasher);
        for op in ops.iter() {
            match op {
                Op::Node(v) => g.add_node(name(*v)),
                Op::Edge(v, w) => g.add_edge(name(*v), name(*w)),
            }
        }
        g.compute_sccs();
        let nodes: Vec<(String, Vec<usize>)> =
            g.nodes.iter().map(|n| (n.t.clone(), n.edges.clone())).collect();
        let snap = (nodes, g.node_scc.clone(), g.scc_nodes.clone(), g.scc_start.clone());
        assert_eq!(snapshot(fx), snap);
        assert_eq!(fx.sort_sccs(), g.sort_sccs());
        for n in fx.nodes.iter() {
            assert_eq!(fx.index_of(&n.t), g.index_of(&n.t));
            assert_eq!(fx.get_scc_rep(&n.t), g.get_scc_rep(&n.t));
            assert_eq!(fx.get_scc_nodes(&n.t), g.get_scc_nodes(&n.t));
        }
        for absent in ["absent".to_string(), name(1_000_000)] {
            assert_eq!(g.index_of(&absent), None);
            assert_eq!(g.get_scc_size(&absent), 1);
        }
    }

    // The hasher only changes performance: graphs keyed with the std RandomState hasher or
    // with heavily colliding hashers have the same nodes, SCCs and order
    #[test]
    fn hasher_choice_does_not_change_graph() {
        let mut rng = Rng(0xda942042e4dd58b5);
        for _ in 0..100 {
            let n = 1 + rng.next(40);
            let len = rng.next(4 * n + 1);
            let ops = random_ops(&mut rng, n, len);
            let mut fx = Graph::new();
            for op in ops.iter() {
                apply(&mut fx, op);
            }
            fx.compute_sccs();
            check_hasher(&fx, &ops, std::collections::hash_map::RandomState::new());
            check_hasher(&fx, &ops, std::hash::BuildHasherDefault::<FewBuckets<1>>::default());
            check_hasher(&fx, &ops, std::hash::BuildHasherDefault::<FewBuckets<3>>::default());
        }
    }

    #[test]
    fn intern_hashed_matches_intern() {
        let mut rng = Rng(0x6c8e9cf570932bd5);
        for _ in 0..100 {
            let n = 1 + rng.next(40);
            let mut a: Graph<String> = Graph::new();
            let mut b: Graph<String> = Graph::new();
            for _ in 0..rng.next(4 * n + 1) {
                let (v, w) = (name(rng.next(n)), name(rng.next(n)));
                let (av, aw) = (a.intern(v.clone()), a.intern(w.clone()));
                a.push_edge_idx(av, aw);
                let hv = FxBuildHasher::default().hash_one(&v);
                assert_eq!(hv, b.hash_value(&v));
                let bv = b.intern_hashed(hv, v);
                let bw = b.intern_hashed(b.hash_value(&w), w);
                assert_eq!((av, aw), (bv, bw));
                b.push_edge_idx(bv, bw);
            }
            a.compute_sccs();
            b.compute_sccs();
            assert_eq!(snapshot(&a), snapshot(&b));
        }
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "intern_hashed: wrong hash")]
    fn intern_hashed_wrong_hash_panics_in_debug() {
        let mut g: Graph<String> = Graph::new();
        let h = g.hash_value(&name(1)).wrapping_add(1);
        g.intern_hashed(h, name(1));
    }

    #[test]
    fn fx_hasher_is_deterministic() {
        use std::hash::{Hash, Hasher};
        let b = FxBuildHasher::default();
        assert_eq!(b.hash_one("node_1"), FxBuildHasher::default().hash_one("node_1"));
        assert_ne!(b.hash_one("node_1"), b.hash_one("node_2"));
        assert_ne!(b.hash_one("abcdefgh1"), b.hash_one("abcdefgh2"));
        let mut h = FxHasher::default();
        (1u32, "x").hash(&mut h);
        assert_eq!(h.finish(), b.hash_one((1u32, "x")));
    }

    #[test]
    fn visited_epoch_wraps() {
        let mut g = Graph::new();
        for i in 0..10 {
            g.add_edge(i, i + 1);
        }
        g.compute_sccs();
        let (_, order) = g.sort_sccs_with_order();
        let mut visited = Visited::new();
        assert!(g.can_reach_with(&mut visited, &0, &10, None));
        visited.epoch = u32::MAX - 1;
        for _ in 0..4 {
            assert!(g.can_reach_with(&mut visited, &0, &10, None));
            assert!(g.can_reach_with(&mut visited, &2, &7, Some(&order)));
            assert!(!g.can_reach_with(&mut visited, &10, &0, None));
            assert!(!g.can_reach_with(&mut visited, &7, &2, Some(&order)));
        }
        // 12 traversals (pruned 7 -> 2 returns before starting one): MAX, then wraps to 1..=11
        assert_eq!(visited.epoch, 11);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "call reset_sccs")]
    fn query_after_mutation_panics_in_debug() {
        let mut g = Graph::new();
        g.add_edge(0, 1);
        g.compute_sccs();
        g.add_edge(1, 0);
        g.get_scc_size(&0);
    }
}
