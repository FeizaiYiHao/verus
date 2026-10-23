//! Speculative prefetch of `verus!` expansions (on by default).
//!
//! Gate: `VERUS_MACRO_PREFETCH` = unset/empty/`1`/`on`/`true` (the default),
//! `0`/`off`/`false` (opt-out), or `check`; any other value disables it. It
//! also needs the parallel path (`VERUS_MACRO_PARALLEL` unset, `1`, or
//! `check`), the worker substrate (`WORKER_JOBS_AVAILABLE`), at least one pool
//! thread, no rustdoc (`VERUSDOC=1`), and no `contrib-hooks` feature.
//! `VERUS_MACRO_PREFETCH_MEM` caps the speculative store (bytes, default 1 GiB).
//!
//! On the first `verus!` invocation per key `(cfg_erase(), use_spec_traits,
//! vstd_kind)`, once its input is frozen (so the token backend is settled), a
//! discovery thread walks the crate's module tree textually from
//! the crate root (the `.rs` argument of the process) and the call-site file:
//! `mod x;` resolves to `#[path]`, `x.rs`, or `x/mod.rs` with the usual
//! directory ownership, depth first in source order, within the source limits
//! below (regular files only, each read through a size-limited reader). Each
//! file is lexed in a speculative pool job (`lex_positional` over
//! `normalize_rustc_source` text), which collects every outermost
//! `verus ! {..}` block (never nested blocks, `macro_rules!` bodies, blocks
//! with `$` metavariables or non-ASCII identifiers) and freezes it with
//! `freeze_rejoin_text`. Each block then runs the parallel path's task kernel
//! as a single segment (`par_items::run_single_task`) in its own speculative
//! job. Speculative jobs queue behind every real task, at most
//! `par_items::speculative_cap` of them run at once, they never take the
//! invocation lock, and they pause while the store exceeds the memory cap.
//! Discovery gives up instead if one pause outlasts `MAX_CAP_WAIT` or the pool
//! has no thread.
//!
//! Hit path (`lookup`): the real input is frozen as one segment and matched by
//! location, then by input hash, requiring an equal key and identical frozen
//! input (`same_input`). A running entry is waited for. A pending entry is
//! removed and reported as a miss, so the caller runs the ordinary n-way
//! parallel path instead of a one-thread speculative run. A finished entry is
//! consumed (removed) and adopted onto the
//! real input (`ThawMetadata::adopt`); its output is thawed and its deferred
//! events are committed by the caller in serial order exactly like a parallel
//! result. Anything else (no entry, input or key mismatch, speculative failure,
//! adoption failure, panic) is a miss without side effects, and the caller
//! continues with the unchanged parallel/serial path. A location is expanded
//! once per key, so every other entry of the lookup's key at the looked-up
//! location is evicted (a running one when it finishes). In check mode the hit
//! is the parallel side of the existing comparison against the serial result.
//! `VERUS_MACRO_PARALLEL_VERBOSE=1` reports hits, misses, and discovery skips
//! with reasons and running counts.

use crate::EraseGhost;
use crate::par_items::{self, Prepared, SilentPanics, TaskInput, TaskOutput, Thaw};
use proc_macro2::{Delimiter, TokenStream};
use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::Range;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::{Condvar, Mutex, MutexGuard, OnceLock};
use verus_syn::worker_tokens::{self as wt, FrozenTokens, LexedFile, LexedKind, ThawMetadata};

impl Thaw for wt::Adopted<'_> {
    fn thaw_tokens(&self, frozen: &FrozenTokens) -> TokenStream {
        self.thaw(frozen)
    }
}

// ---------------------------------------------------------------------------
// Configuration.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Mode {
    Off,
    On,
    Check,
}

const MAX_TOTAL_SOURCE: u64 = 64 << 20;
const MAX_FILES: usize = 10_000;
const MAX_FILE_SIZE: u64 = 8 << 20;
const DEFAULT_MEM_CAP: usize = 1 << 30;
/// Longest single pause of discovery over the memory cap before discovery gives up.
const MAX_CAP_WAIT: std::time::Duration = std::time::Duration::from_secs(10 * 60);

/// Unset or empty selects the default (`On`); unknown values disable prefetch.
fn parse_mode(s: Option<&str>) -> Mode {
    match s.map(str::trim) {
        None | Some("") | Some("1") | Some("on") | Some("true") => Mode::On,
        Some("check") => Mode::Check,
        _ => Mode::Off,
    }
}

fn parse_mem_cap(s: Option<&str>) -> usize {
    s.and_then(|s| s.trim().parse::<usize>().ok()).unwrap_or(DEFAULT_MEM_CAP)
}

/// Why prefetching cannot run in this process, if it cannot.
fn gate_failure() -> Option<&'static str> {
    if cfg!(feature = "contrib-hooks") {
        Some("contrib-hooks")
    } else if !par_items::parallel_enabled() {
        Some("VERUS_MACRO_PARALLEL is off")
    } else if !wt::WORKER_JOBS_AVAILABLE {
        Some("worker substrate unavailable")
    } else if crate::rustdoc::env_rustdoc() {
        Some("rustdoc")
    } else if par_items::pool_threads() == 0 {
        Some("no worker threads")
    } else {
        None
    }
}

/// Effective prefetch mode (`Off` unless every gate passes).
pub(crate) fn mode() -> Mode {
    static MODE: OnceLock<Mode> = OnceLock::new();
    *MODE.get_or_init(|| {
        let mode = parse_mode(std::env::var("VERUS_MACRO_PREFETCH").ok().as_deref());
        if mode == Mode::Off {
            return Mode::Off;
        }
        match gate_failure() {
            Some(reason) => {
                verbose_line(&format!("disabled: {}", reason));
                Mode::Off
            }
            None => mode,
        }
    })
}

fn verbose_line(msg: &str) {
    if par_items::verbose() {
        eprintln!("verus! prefetch: {}", msg);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Key {
    pub(crate) erase_ghost: EraseGhost,
    pub(crate) use_spec_traits: bool,
    pub(crate) vstd_kind: u8,
}

/// Source location of a block: its file and the rustc line/column (both
/// 1-based, column in chars) of the first token inside the delimiters (what the
/// macro receives first).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Loc {
    pub(crate) file: PathBuf,
    pub(crate) pos: Pos,
}

pub(crate) type Pos = (u32, u32);

// ---------------------------------------------------------------------------
// Speculative store.

enum State {
    Pending,
    Running,
    Done(Box<TaskOutput>),
    Failed(String),
}

struct Entry {
    key: Key,
    loc: Option<Loc>,
    input: FrozenTokens,
    hash: u64,
    state: State,
    bytes: usize,
    /// Its location was looked up while it ran; removed when it finishes.
    stale: bool,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Stats {
    pub(crate) hits: usize,
    pub(crate) misses: usize,
    pub(crate) skips: usize,
    pub(crate) files: usize,
    pub(crate) blocks: usize,
    pub(crate) failed: usize,
    /// Entries removed without being adopted (pending lookups, stale locations).
    pub(crate) evicted: usize,
}

struct Store {
    entries: HashMap<u64, Entry>,
    by_loc: HashMap<Loc, Vec<u64>>,
    by_hash: HashMap<u64, Vec<u64>>,
    /// Pending entry ids. Queued speculative tokens + `parked` >= `pending.len()`
    /// and `parked` <= `pending.len()`; surplus tokens find nothing and end.
    pending: BTreeSet<u64>,
    /// Tokens that found the store over the cap and returned unused.
    parked: usize,
    mem: usize,
    cap: usize,
    next_id: u64,
    started: HashSet<Key>,
    stats: Stats,
}

pub(crate) struct Shared {
    store: Mutex<Store>,
    changed: Condvar,
}

impl Shared {
    pub(crate) fn new(cap: usize) -> Shared {
        Shared {
            store: Mutex::new(Store {
                entries: HashMap::new(),
                by_loc: HashMap::new(),
                by_hash: HashMap::new(),
                pending: BTreeSet::new(),
                parked: 0,
                mem: 0,
                cap,
                next_id: 0,
                started: HashSet::new(),
                stats: Stats::default(),
            }),
            changed: Condvar::new(),
        }
    }

    fn lock(&self) -> MutexGuard<'_, Store> {
        self.store.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn wait<'a>(&self, g: MutexGuard<'a, Store>) -> MutexGuard<'a, Store> {
        self.changed.wait(g).unwrap_or_else(|e| e.into_inner())
    }

    #[cfg(test)]
    pub(crate) fn stats(&self) -> Stats {
        self.lock().stats
    }

    /// Waits until no entry runs and every pending entry has a parked token.
    #[cfg(test)]
    pub(crate) fn settle(&self) {
        let mut st = self.lock();
        while st.pending.len() > st.parked
            || st.entries.values().any(|e| matches!(e.state, State::Running))
        {
            st = self.changed.wait_timeout(st, std::time::Duration::from_millis(20)).unwrap().0;
        }
    }

    /// (pending, running, done, failed) entry counts.
    #[cfg(test)]
    pub(crate) fn counts(&self) -> (usize, usize, usize, usize) {
        let st = self.lock();
        let mut c = (0, 0, 0, 0);
        for e in st.entries.values() {
            match e.state {
                State::Pending => c.0 += 1,
                State::Running => c.1 += 1,
                State::Done(_) => c.2 += 1,
                State::Failed(_) => c.3 += 1,
            }
        }
        c
    }

    #[cfg(test)]
    pub(crate) fn locs(&self) -> Vec<Loc> {
        let st = self.lock();
        let mut ids: Vec<&u64> = st.entries.keys().collect();
        ids.sort();
        ids.into_iter().filter_map(|id| st.entries[id].loc.clone()).collect()
    }

    #[cfg(test)]
    pub(crate) fn mem(&self) -> usize {
        self.lock().mem
    }

    #[cfg(test)]
    pub(crate) fn parked(&self) -> usize {
        self.lock().parked
    }
}

fn shared() -> &'static Shared {
    static SHARED: OnceLock<Shared> = OnceLock::new();
    SHARED.get_or_init(|| {
        Shared::new(parse_mem_cap(std::env::var("VERUS_MACRO_PREFETCH_MEM").ok().as_deref()))
    })
}

fn pool() -> &'static par_items::Pool {
    par_items::pool(par_items::pool_threads())
}

/// Queues one speculative token, which runs the oldest pending entry.
fn submit_token(sh: &'static Shared) -> bool {
    pool().submit(Box::new(move || run_token(sh)), true)
}

fn run_token(sh: &'static Shared) {
    let (id, input) = {
        let mut st = sh.lock();
        let id = match st.pending.iter().next() {
            Some(&id) => id,
            // Surplus token: its entry was removed while pending.
            None => return,
        };
        if st.mem >= st.cap {
            if st.parked < st.pending.len() {
                st.parked += 1;
            }
            return;
        }
        st.pending.remove(&id);
        let entry = st.entries.get_mut(&id).expect("pending entry");
        entry.state = State::Running;
        let input = TaskInput {
            task: 0,
            frozen: entry.input.clone(),
            erase_ghost: entry.key.erase_ghost,
            use_spec_traits: entry.key.use_spec_traits,
            rustdoc: false,
        };
        (id, input)
    };
    #[cfg(test)]
    tests::hold_point();
    let result = par_items::run_single_task(input);
    let mut st = sh.lock();
    let stale = {
        let st = &mut *st;
        let entry = st.entries.get_mut(&id).expect("running entry");
        match result {
            Ok(out) => {
                let bytes = out.approx_bytes();
                entry.bytes += bytes;
                st.mem += bytes;
                entry.state = State::Done(Box::new(out));
            }
            Err(reason) => {
                st.stats.failed += 1;
                entry.state = State::Failed(reason);
            }
        }
        entry.stale
    };
    if stale {
        st.stats.evicted += 1;
        consume(sh, &mut st, id);
    }
    let resume = st.parked > 0 && st.mem < st.cap;
    if resume {
        st.parked -= 1;
    }
    drop(st);
    sh.changed.notify_all();
    if resume && !submit_token(sh) {
        sh.lock().parked += 1;
    }
}

/// Inserts the frozen blocks of one file as pending entries and queues their tokens.
fn insert_blocks(sh: &'static Shared, key: Key, file: Option<&Path>, blocks: Vec<FrozenBlock>) {
    let n = blocks.len();
    {
        let mut st = sh.lock();
        for b in blocks {
            let id = st.next_id;
            st.next_id += 1;
            let loc = match (file, b.pos) {
                (Some(f), Some(pos)) => Some(Loc { file: f.to_path_buf(), pos }),
                _ => None,
            };
            let bytes = par_items::frozen_bytes(&b.frozen);
            st.mem += bytes;
            st.stats.blocks += 1;
            if let Some(loc) = &loc {
                st.by_loc.entry(loc.clone()).or_default().push(id);
            }
            st.by_hash.entry(b.hash).or_default().push(id);
            st.pending.insert(id);
            let (input, hash, state) = (b.frozen, b.hash, State::Pending);
            let entry = Entry { key, loc, input, hash, state, bytes, stale: false };
            st.entries.insert(id, entry);
        }
    }
    for _ in 0..n {
        if !submit_token(sh) {
            let mut st = sh.lock();
            if st.parked < st.pending.len() {
                st.parked += 1;
            }
        }
    }
}

/// Removes an entry that is not running (a pending one gives up its token) and
/// resumes parked tokens once under the cap.
fn consume(sh: &'static Shared, st: &mut Store, id: u64) -> Entry {
    let entry = st.entries.remove(&id).expect("consumed entry");
    if st.pending.remove(&id) && st.parked > st.pending.len() {
        st.parked -= 1;
    }
    if let Some(loc) = &entry.loc {
        if let Some(ids) = st.by_loc.get_mut(loc) {
            ids.retain(|&i| i != id);
            if ids.is_empty() {
                st.by_loc.remove(loc);
            }
        }
    }
    if let Some(ids) = st.by_hash.get_mut(&entry.hash) {
        ids.retain(|&i| i != id);
        if ids.is_empty() {
            st.by_hash.remove(&entry.hash);
        }
    }
    st.mem -= entry.bytes;
    if st.mem < st.cap {
        let n = st.parked.min(pool().size.max(1));
        st.parked -= n;
        for _ in 0..n {
            if !submit_token(sh) {
                st.parked += 1;
            }
        }
    }
    sh.changed.notify_all();
    entry
}

/// Evicts every other entry of `key` at the looked-up location `loc` (rustc
/// expands a location once per key): idle ones now, running ones when they
/// finish.
fn evict_location(sh: &'static Shared, st: &mut Store, key: Key, loc: &Loc, keep: Option<u64>) {
    let ids: Vec<u64> = match st.by_loc.get(loc) {
        Some(ids) => ids.iter().copied().filter(|&id| Some(id) != keep).collect(),
        None => return,
    };
    for id in ids {
        let e = st.entries.get_mut(&id).expect("indexed entry");
        if e.key != key {
            continue;
        }
        if matches!(e.state, State::Running) {
            e.stale = true;
        } else {
            st.stats.evicted += 1;
            consume(sh, st, id);
        }
    }
}

// ---------------------------------------------------------------------------
// Hit path.

fn key_now(erase_ghost: EraseGhost, use_spec_traits: bool) -> Key {
    Key { erase_ghost, use_spec_traits, vstd_kind: crate::vstd_kind() as u8 }
}

/// Main-thread lookup for a `verus!` invocation; `None` is a miss without side
/// effects. Starts discovery on the first invocation per key.
pub(crate) fn lookup(
    stream: &proc_macro::TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
) -> Option<Prepared> {
    par_items::install_silent_hook();
    let _silent = SilentPanics::new();
    if par_items::force_main_caches().is_err() {
        return None;
    }
    let sh = shared();
    let key = key_now(erase_ghost, use_spec_traits);
    let result = catch_unwind(AssertUnwindSafe(|| {
        let (frozen, meta) = wt::freeze_rejoin_main(TokenStream::from(stream.clone()));
        // The main-thread freeze settled the token backend; workers may start now.
        start_discovery(sh, key);
        // The first origin is the first input token's span (or a join starting there).
        let loc = meta.first_span().and_then(real_location);
        lookup_counted(sh, key, loc, &frozen, &meta)
    }))
    .unwrap_or_else(|p| Err(format!("main-thread panic: {}", par_items::panic_message(&*p))));
    result.ok()
}

/// Lookup for one real input (compiler or fallback tokens); counts and reports
/// the outcome.
#[cfg(test)]
pub(crate) fn lookup_tokens(
    sh: &'static Shared,
    key: Key,
    loc: Option<Loc>,
    input: TokenStream,
) -> Result<Prepared, String> {
    let (frozen, meta) = wt::freeze_rejoin_main(input);
    lookup_counted(sh, key, loc, &frozen, &meta)
}

fn lookup_counted(
    sh: &'static Shared,
    key: Key,
    loc: Option<Loc>,
    frozen: &FrozenTokens,
    meta: &ThawMetadata,
) -> Result<Prepared, String> {
    let result = lookup_frozen(sh, key, loc.as_ref(), frozen, meta);
    let mut st = sh.lock();
    match &result {
        Ok(_) => st.stats.hits += 1,
        Err(_) => st.stats.misses += 1,
    }
    let (hits, misses) = (st.stats.hits, st.stats.misses);
    drop(st);
    let at =
        loc.map_or(String::new(), |l| format!(" at {}:{}:{}", l.file.display(), l.pos.0, l.pos.1));
    match &result {
        Ok(_) => verbose_line(&format!("hit{} ({} hits, {} misses)", at, hits, misses)),
        Err(reason) => {
            verbose_line(&format!("miss{}: {} ({} hits, {} misses)", at, reason, hits, misses))
        }
    }
    result
}

fn lookup_frozen(
    sh: &'static Shared,
    key: Key,
    loc: Option<&Loc>,
    frozen: &FrozenTokens,
    meta: &ThawMetadata,
) -> Result<Prepared, String> {
    let mut st = sh.lock();
    let mut key_mismatch = false;
    let mut input_mismatch = false;
    // Location candidates first, compared directly; the input hash is computed
    // only for the hash fallback. Same choice as filtering by hash first: equal
    // inputs have equal hashes.
    let by_loc: &[u64] = loc.and_then(|l| st.by_loc.get(l)).map_or(&[], |ids| ids);
    let mut found = None;
    for &id in by_loc {
        let e = &st.entries[&id];
        if !frozen.same_input(&e.input) {
            input_mismatch = true;
        } else if e.key != key {
            key_mismatch = true;
        } else {
            found = Some(id);
            break;
        }
    }
    if found.is_none() {
        let hash = frozen.input_hash();
        for &id in st.by_hash.get(&hash).map_or(&[][..], |ids| ids) {
            if by_loc.contains(&id) {
                continue;
            }
            let e = &st.entries[&id];
            if !frozen.same_input(&e.input) {
                input_mismatch = true;
            } else if e.key != key {
                key_mismatch = true;
            } else {
                found = Some(id);
                break;
            }
        }
    }
    let id = match found {
        Some(id) => id,
        None => {
            if let Some(loc) = loc {
                evict_location(sh, &mut st, key, loc, None);
            }
            return Err(if key_mismatch {
                "key mismatch"
            } else if input_mismatch {
                "input mismatch"
            } else {
                "no speculative entry"
            }
            .to_string());
        }
    };
    if let Some(loc) = loc {
        evict_location(sh, &mut st, key, loc, Some(id));
    }
    // Found through the hash at another location after its own was looked up.
    st.entries.get_mut(&id).expect("found entry").stale = false;
    loop {
        match st.entries.get(&id).map(|e| &e.state) {
            None => return Err("speculative entry evicted".to_string()),
            Some(State::Pending) => {
                // The caller's n-way parallel path beats a one-thread speculative run.
                st.stats.evicted += 1;
                consume(sh, &mut st, id);
                return Err("speculative entry still pending".to_string());
            }
            Some(State::Running) => {}
            Some(State::Done(_)) | Some(State::Failed(_)) => break,
        }
        st = sh.wait(st);
    }
    let entry = consume(sh, &mut st, id);
    drop(st);
    match entry.state {
        State::Done(out) => {
            let adopted = meta.adopt(frozen, &entry.input).ok_or("adoption failed")?;
            par_items::prepare_outputs(&[&adopted], vec![*out])
        }
        State::Failed(reason) => Err(format!("speculative task failed: {}", reason)),
        State::Pending | State::Running => unreachable!(),
    }
}

/// File and rustc line/column of the first input token's span, from the compiler.
#[cfg(not(test))]
fn real_location(span: proc_macro2::Span) -> Option<Loc> {
    if !proc_macro::is_available() {
        return None;
    }
    let span = span.unwrap();
    let file = canonical_cached(span.local_file()?)?;
    Some(Loc { file, pos: (span.line() as u32, span.column() as u32) })
}

#[cfg(test)]
fn real_location(_span: proc_macro2::Span) -> Option<Loc> {
    None
}

#[cfg(not(test))]
fn canonical_cached(path: PathBuf) -> Option<PathBuf> {
    static CACHE: OnceLock<Mutex<HashMap<PathBuf, Option<PathBuf>>>> = OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(HashMap::new()));
    let mut cache = cache.lock().unwrap_or_else(|e| e.into_inner());
    cache.entry(path).or_insert_with_key(|p| std::fs::canonicalize(p).ok()).clone()
}

// ---------------------------------------------------------------------------
// Discovery.

#[cfg(not(test))]
fn call_site_file() -> Option<PathBuf> {
    if !proc_macro::is_available() {
        return None;
    }
    proc_macro::Span::call_site().local_file()
}

#[cfg(test)]
fn call_site_file() -> Option<PathBuf> {
    None
}

/// Crate root (the first existing `.rs` argument of this process; arguments
/// need not be UTF-8) and the call-site file.
fn discovery_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let is_root = |p: &Path| p.extension().map_or(false, |e| e == "rs") && p.is_file();
    if let Some(arg) = std::env::args_os().skip(1).map(PathBuf::from).find(|p| is_root(p)) {
        roots.push(arg);
    }
    if let Some(f) = call_site_file() {
        roots.push(f);
    }
    roots
}

fn start_discovery(sh: &'static Shared, key: Key) {
    if !sh.lock().started.insert(key) {
        return;
    }
    let roots = match catch_unwind(discovery_roots) {
        Ok(roots) => roots,
        Err(_) => {
            verbose_line("discovery: crate root query panicked");
            return;
        }
    };
    if roots.is_empty() {
        verbose_line("discovery: no crate root");
        return;
    }
    let spawned =
        std::thread::Builder::new().name("verus-macro-prefetch".to_string()).spawn(move || {
            // Discovery panics only end speculation; keep them off stderr.
            let _silent = SilentPanics::new();
            let _ = catch_unwind(AssertUnwindSafe(|| discover(sh, key, roots)));
        });
    if spawned.is_err() {
        verbose_line("discovery: thread spawn failed");
    }
}

fn skip(sh: &Shared, what: &str, reason: &str) {
    sh.lock().stats.skips += 1;
    verbose_line(&format!("skip {}: {}", what, reason));
}

/// Depth-first walk of the module tree from `roots`, lexing one file at a time.
pub(crate) fn discover(sh: &'static Shared, key: Key, roots: Vec<PathBuf>) {
    let mut stack: Vec<(PathBuf, bool)> = roots.into_iter().rev().map(|r| (r, true)).collect();
    let mut seen: HashSet<PathBuf> = HashSet::new();
    let mut total: u64 = 0;
    let mut files = 0;
    while let Some((path, mod_rs)) = stack.pop() {
        let path = match std::fs::canonicalize(&path) {
            Ok(p) => p,
            Err(_) => continue,
        };
        if !seen.insert(path.clone()) {
            continue;
        }
        if files >= MAX_FILES {
            skip(sh, &path.display().to_string(), "file limit reached");
            break;
        }
        let text = match read_source(&path) {
            Ok(t) => t,
            Err(reason) => {
                skip(sh, &path.display().to_string(), reason);
                continue;
            }
        };
        let size = text.len() as u64;
        if total + size > MAX_TOTAL_SOURCE {
            skip(sh, &path.display().to_string(), "total source limit reached");
            break;
        }
        total += size;
        files += 1;
        if !wait_under_cap(sh, MAX_CAP_WAIT) {
            skip(sh, &path.display().to_string(), "memory cap wait gave up");
            break;
        }
        let mods = match scan_file_on_pool(sh, key, &path, text) {
            Ok(mods) => mods,
            Err(reason) => {
                skip(sh, &path.display().to_string(), &reason);
                continue;
            }
        };
        sh.lock().stats.files += 1;
        let children = resolve_mods(&path, mod_rs, &mods);
        stack.extend(children.into_iter().rev());
    }
    let s = sh.lock().stats;
    verbose_line(&format!(
        "discovery done: {} files, {} blocks, {} skips",
        s.files, s.blocks, s.skips
    ));
}

/// Waits until the store is under the memory cap. Returns false, so that
/// discovery stops, if `limit` passes first or the pool has no thread to run
/// the speculative entries holding the memory.
fn wait_under_cap(sh: &Shared, limit: std::time::Duration) -> bool {
    let deadline = std::time::Instant::now() + limit;
    let mut st = sh.lock();
    while st.mem >= st.cap {
        let now = std::time::Instant::now();
        if now >= deadline || pool().size == 0 {
            return false;
        }
        // Wake at least once a second so the deadline holds even without notifications.
        let timeout = (deadline - now).min(std::time::Duration::from_secs(1));
        st = sh.changed.wait_timeout(st, timeout).unwrap_or_else(|e| e.into_inner()).0;
    }
    true
}

#[cfg(test)]
mod cap_wait_tests {
    use super::*;
    use std::time::{Duration, Instant};

    #[test]
    fn cap_wait_gives_up_after_limit() {
        let sh = Shared::new(1);
        sh.lock().mem = 1;
        let start = Instant::now();
        assert!(!wait_under_cap(&sh, Duration::from_millis(50)));
        assert!(start.elapsed() >= Duration::from_millis(50));
        sh.lock().mem = 0;
        assert!(wait_under_cap(&sh, Duration::ZERO));
    }

    #[test]
    fn cap_wait_resumes_once_under_cap() {
        let sh: &'static Shared = Box::leak(Box::new(Shared::new(1)));
        sh.lock().mem = 1;
        let freer = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(20));
            sh.lock().mem = 0;
            sh.changed.notify_all();
        });
        assert!(wait_under_cap(sh, Duration::from_secs(60)));
        freer.join().unwrap();
    }
}

/// Reads a regular source file of at most `MAX_FILE_SIZE` bytes. The type is
/// checked before opening (a FIFO would block the open) and again on the open
/// handle, and at most `MAX_FILE_SIZE + 1` bytes are ever read.
pub(crate) fn read_source(path: &Path) -> Result<String, &'static str> {
    use std::io::Read;
    if !std::fs::metadata(path).map_or(false, |m| m.is_file()) {
        return Err("not a regular file");
    }
    let file = std::fs::File::open(path).map_err(|_| "open failed")?;
    if !file.metadata().map_or(false, |m| m.is_file()) {
        return Err("not a regular file");
    }
    let mut bytes = Vec::new();
    file.take(MAX_FILE_SIZE + 1).read_to_end(&mut bytes).map_err(|_| "read failed")?;
    if bytes.len() as u64 > MAX_FILE_SIZE {
        return Err("file too large");
    }
    String::from_utf8(bytes).map_err(|_| "not UTF-8")
}

/// Lexes and scans `text` in a speculative job, inserts its blocks, and returns
/// its module declarations.
pub(crate) fn scan_file_on_pool(
    sh: &'static Shared,
    key: Key,
    path: &Path,
    text: String,
) -> Result<Vec<ModDecl>, String> {
    let (tx, rx) = std::sync::mpsc::channel();
    let job = Box::new(move || {
        let r = catch_unwind(AssertUnwindSafe(|| scan_file_job(&text)))
            .unwrap_or_else(|p| Err(format!("panic: {}", par_items::panic_message(&*p))));
        let _ = tx.send(r);
    });
    if !pool().submit(job, true) {
        return Err("worker pool unavailable".to_string());
    }
    let scanned = rx.recv().map_err(|_| "scan job lost".to_string())??;
    for (at, reason) in &scanned.skipped {
        skip(sh, &format!("{}:{}", path.display(), at), reason);
    }
    insert_blocks(sh, key, Some(path), scanned.blocks);
    Ok(scanned.mods)
}

pub(crate) struct FrozenBlock {
    pos: Option<Pos>,
    frozen: FrozenTokens,
    hash: u64,
}

struct Scanned {
    mods: Vec<ModDecl>,
    blocks: Vec<FrozenBlock>,
    skipped: Vec<(String, String)>,
}

fn scan_file_job(text: &str) -> Result<Scanned, String> {
    let text = wt::normalize_rustc_source(text);
    let file = {
        let _job = wt::begin_job();
        wt::lex_positional(&text).map_err(|e| format!("lex error at byte {}", e.offset))?
    };
    let found = scan_lexed(&file);
    let lines = LineIndex::new(&text);
    let mut blocks = Vec::new();
    let mut skipped = Vec::new();
    for range in found.blocks {
        let pos = file.toks.get(range.start).filter(|_| !range.is_empty()).map(|t| lines.pos(t.lo));
        let at = pos.map_or("?".to_string(), |(l, c)| format!("{}:{}", l, c));
        match block_skip_reason(&file, range.clone()) {
            Some(reason) => skipped.push((at, reason)),
            None => {
                let frozen = wt::freeze_rejoin_text(&file, range);
                let hash = frozen.input_hash();
                blocks.push(FrozenBlock { pos, frozen, hash });
            }
        }
    }
    Ok(Scanned { mods: found.mods, blocks, skipped })
}

/// rustc line/column (1-based, column in chars) of byte offsets.
struct LineIndex<'a> {
    text: &'a str,
    starts: Vec<u32>,
}

impl<'a> LineIndex<'a> {
    fn new(text: &'a str) -> LineIndex<'a> {
        let mut starts = vec![0];
        starts.extend(text.match_indices('\n').map(|(i, _)| i as u32 + 1));
        LineIndex { text, starts }
    }

    fn pos(&self, offset: u32) -> Pos {
        let line = self.starts.partition_point(|&s| s <= offset) - 1;
        let start = self.starts[line] as usize;
        let end = (offset as usize).min(self.text.len());
        let col = self.text.get(start..end).map_or(0, |t| t.chars().count());
        (line as u32 + 1, col as u32 + 1)
    }
}

// ---------------------------------------------------------------------------
// Textual scan over the positional lexing (preorder tokens; a group is
// followed by its `len` descendants).

/// Directory step contributed by an enclosing inline module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DirStep {
    Name(String),
    Path(String),
}

/// An outline module declaration `mod name;`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ModDecl {
    pub(crate) name: String,
    pub(crate) path: Option<String>,
    pub(crate) inline: Vec<DirStep>,
}

#[derive(Default, Debug)]
pub(crate) struct Found {
    pub(crate) mods: Vec<ModDecl>,
    /// Token ranges of the inputs of outermost `verus! { .. }` blocks.
    pub(crate) blocks: Vec<Range<usize>>,
}

pub(crate) fn scan_lexed(file: &LexedFile) -> Found {
    let mut found = Found::default();
    scan_level(file, 0..file.toks.len(), &mut Vec::new(), false, &mut found);
    found
}

fn kind(file: &LexedFile, i: usize) -> Option<&LexedKind> {
    file.toks.get(i).map(|t| &t.kind)
}

fn ident_at(file: &LexedFile, i: usize) -> Option<&str> {
    match kind(file, i) {
        Some(LexedKind::Ident { text, raw: false }) => Some(text),
        _ => None,
    }
}

fn punct_at(file: &LexedFile, i: usize, c: char) -> bool {
    matches!(kind(file, i), Some(LexedKind::Punct { ch, .. }) if *ch == c)
}

/// Delimiter and descendant count of a group token.
fn group_at(file: &LexedFile, i: usize) -> Option<(Delimiter, usize)> {
    match kind(file, i) {
        Some(LexedKind::Group { delim, len }) => Some((*delim, *len as usize)),
        _ => None,
    }
}

/// Index of the next sibling of token `i`.
fn next_sibling(file: &LexedFile, i: usize) -> usize {
    i + 1 + group_at(file, i).map_or(0, |(_, len)| len)
}

/// `path = "..."` attribute contents of the bracket group at `g`.
fn path_attr(file: &LexedFile, g: usize, len: usize) -> Option<String> {
    if len != 3 || ident_at(file, g + 1) != Some("path") || !punct_at(file, g + 2, '=') {
        return None;
    }
    match kind(file, g + 3) {
        Some(LexedKind::Literal { repr }) => string_literal_value(repr),
        _ => None,
    }
}

/// Value of a plain or raw string literal (plain ones only with `\\`/`\"` escapes).
fn string_literal_value(repr: &str) -> Option<String> {
    if let Some(rest) = repr.strip_prefix('r') {
        let hashes = rest.len() - rest.trim_start_matches('#').len();
        let body = rest[hashes..].strip_prefix('"')?;
        let body = body.strip_suffix(&"#".repeat(hashes))?.strip_suffix('"')?;
        return Some(body.to_string());
    }
    let body = repr.strip_prefix('"')?.strip_suffix('"')?;
    let mut out = String::new();
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next()? {
                '\\' => out.push('\\'),
                '"' => out.push('"'),
                _ => return None,
            }
        } else {
            out.push(c);
        }
    }
    Some(out)
}

fn scan_level(
    file: &LexedFile,
    range: Range<usize>,
    inline: &mut Vec<DirStep>,
    in_verus: bool,
    found: &mut Found,
) {
    let mut path: Option<String> = None;
    let mut i = range.start;
    while i < range.end {
        // Outer attributes (`#[..]`) and inner attributes (`#![..]`).
        if punct_at(file, i, '#') {
            let (inner, at) =
                if punct_at(file, i + 1, '!') { (true, i + 2) } else { (false, i + 1) };
            if let Some((Delimiter::Bracket, len)) = group_at(file, at) {
                if !inner {
                    if let Some(p) = path_attr(file, at, len) {
                        path = Some(p);
                    }
                }
                i = at + 1 + len;
                continue;
            }
        }
        // `macro_rules! name { .. }`: bodies are never scanned.
        if ident_at(file, i) == Some("macro_rules") && punct_at(file, i + 1, '!') {
            i += 2;
            while i < range.end && group_at(file, i).is_none() {
                i += 1;
            }
            i = next_sibling(file, i).min(range.end);
            path = None;
            continue;
        }
        if ident_at(file, i) == Some("mod") {
            let name = match kind(file, i + 1) {
                Some(LexedKind::Ident { text, .. }) => Some(text.clone()),
                _ => None,
            };
            if let Some(name) = name {
                if punct_at(file, i + 2, ';') {
                    found.mods.push(ModDecl { name, path: path.take(), inline: inline.clone() });
                    i += 3;
                    continue;
                }
                if let Some((Delimiter::Brace, len)) = group_at(file, i + 2) {
                    let step = match path.take() {
                        Some(p) => DirStep::Path(p),
                        None => DirStep::Name(name),
                    };
                    inline.push(step);
                    scan_level(file, i + 3..i + 3 + len, inline, in_verus, found);
                    inline.pop();
                    i += 3 + len;
                    continue;
                }
            }
        }
        if ident_at(file, i) == Some("verus") && punct_at(file, i + 1, '!') {
            if let Some((Delimiter::Brace, len)) = group_at(file, i + 2) {
                let inner = i + 3..i + 3 + len;
                if !in_verus {
                    found.blocks.push(inner.clone());
                }
                scan_level(file, inner, inline, true, found);
                path = None;
                i += 3 + len;
                continue;
            }
        }
        match group_at(file, i) {
            Some((delim, len)) => {
                scan_level(file, i + 1..i + 1 + len, &mut Vec::new(), in_verus, found);
                if delim == Delimiter::Brace {
                    path = None;
                }
            }
            None if punct_at(file, i, ';') => path = None,
            None => {}
        }
        i = next_sibling(file, i);
    }
}

/// Why the block input `range` is not prefetched, if it is not.
pub(crate) fn block_skip_reason(file: &LexedFile, range: Range<usize>) -> Option<String> {
    if range.is_empty() {
        return Some("empty block".to_string());
    }
    if file.has_non_ascii_ident_in(range.clone()) {
        return Some("non-ASCII identifier".to_string());
    }
    for tok in &file.toks[range] {
        match &tok.kind {
            LexedKind::Punct { ch: '$', .. } => return Some("macro metavariable".to_string()),
            LexedKind::Ident { text, .. } => {
                if par_items::has_marker(text) {
                    return Some("placeholder marker text".to_string());
                }
                if crate::contrib::PREPROCESSORS.iter().any(|p| p.0 == text) {
                    return Some(format!("contrib preprocessing (`{}`)", text));
                }
            }
            LexedKind::Literal { repr } if par_items::has_marker(repr) => {
                return Some("placeholder marker text".to_string());
            }
            _ => {}
        }
    }
    None
}

/// Candidate files of the outline modules of `file`, in declaration order.
pub(crate) fn resolve_mods(file: &Path, mod_rs: bool, mods: &[ModDecl]) -> Vec<(PathBuf, bool)> {
    let dir = file.parent().unwrap_or(Path::new("."));
    let base =
        if mod_rs { dir.to_path_buf() } else { dir.join(file.file_stem().unwrap_or_default()) };
    let mut out = Vec::new();
    for m in mods {
        let mut d = base.clone();
        for step in &m.inline {
            match step {
                DirStep::Name(n) | DirStep::Path(n) => d.push(n),
            }
        }
        match &m.path {
            // Path files own their directory like `mod.rs`.
            Some(p) if m.inline.is_empty() => out.push((dir.join(p), true)),
            Some(p) => out.push((d.join(p), true)),
            None => {
                let flat = d.join(format!("{}.rs", m.name));
                let nested = d.join(&m.name).join("mod.rs");
                if flat.is_file() {
                    out.push((flat, false));
                } else if nested.is_file() {
                    out.push((nested, true));
                }
            }
        }
    }
    out
}

#[cfg(test)]
#[path = "prefetch_tests.rs"]
mod tests;
