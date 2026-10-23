//! Parallel rewrite of the top-level items of `verus!` (on by default).
//!
//! Gate: `VERUS_MACRO_PARALLEL` = unset/empty/`1`/`on`/`true` (parallel with
//! serial fallback, the default), `0`/`off`/`false` (serial opt-out), or `check`
//! (run both, emit only the serial result, and panic if the parallel result
//! differs); any other value selects serial. `VERUS_MACRO_THREADS` sets
//! the persistent worker pool size (default `min(available_parallelism - 1, 8)`;
//! `0` disables). `VERUS_MACRO_PARALLEL_VERBOSE=1` reports fallback reasons.
//!
//! Pipeline: the main thread splits the input at candidate top-level item
//! boundaries into one contiguous segment per task and freezes each segment
//! (`verus_syn::worker_tokens`, which also applies Verus operator rejoining).
//! Each task, on its own pool thread inside a `proc_macro2` worker job, melts and
//! parses its segment (so every segment must independently parse as whole items)
//! and runs the serial prefilter/visit/post kernels per item. Diagnostics and
//! external-fn-specification UID requests are deferred as events. The main thread
//! then replays the events in exact serial order, thaws the outputs, and
//! concatenates them in serial list order. Any worker panic, parse failure, or
//! unsupported construct discards all worker results before any side effect and
//! falls back to the unchanged serial path. Unsupported (serial fallback): rustdoc
//! (`VERUSDOC=1`), the `contrib-hooks` feature, stock proc-macro2 without worker
//! jobs (`WORKER_JOBS_AVAILABLE` false; no pool threads are created), any contrib
//! preprocessing macro name (`contrib::PREPROCESSORS`) in the input, `global`
//! layout items, empty atomic perm tuples (named from a process-global counter),
//! contrib-appended items, prefilter transforms that change the leaked Visitor
//! state, leaked state the per-item reset does not clear, segment parse failures,
//! placeholder marker text in the input, inner `#![trigger ..]` lists that do not
//! re-parse, worker or main-thread panics while preparing, and channel/pool
//! failures. The main thread first prepares the complete thawed result inside
//! `catch_unwind` and only then commits the side effects (`commit`).
//!
//! Serial state threading that the kernels cannot see is reproduced explicitly:
//! the unerased-proxy prefilter pass visits erased copies with one shared Visitor
//! whose leftover plain-value state (`ParLeakState`) flows into later items, the
//! later prefilter steps, and the first visited item. Tasks report the state left
//! by their proxy pass, the main thread chains it in source order (asking a task
//! to redo its proxy pass from the true incoming state when needed), and then
//! broadcasts the final state.

use crate::EraseGhost;
use crate::syntax::{Items, ParLeakState, Visitor};
use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream, TokenTree};
use quote::ToTokens;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet, VecDeque};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::sync::{Condvar, Mutex, OnceLock};
use verus_syn::worker_tokens::{self as wt, FrozenTokens, ThawMetadata};
use verus_syn::{ImplItem, Item};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DiagLevel {
    Warning,
    Error,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParMode {
    Off,
    On,
    Check,
}

struct Config {
    mode: ParMode,
    threads: usize,
    verbose: bool,
}

const MAX_THREADS: usize = 64;
const WORKER_STACK_SIZE: usize = 64 << 20;

fn config() -> &'static Config {
    static CONFIG: OnceLock<Config> = OnceLock::new();
    CONFIG.get_or_init(|| {
        let mode = std::env::var("VERUS_MACRO_PARALLEL").ok();
        let threads = std::env::var("VERUS_MACRO_THREADS").ok();
        let avail = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
        let (mode, threads) = parse_config(mode.as_deref(), threads.as_deref(), avail);
        let verbose = std::env::var("VERUS_MACRO_PARALLEL_VERBOSE").map_or(false, |s| s == "1");
        Config { mode, threads, verbose }
    })
}

/// Whether `VERUS_MACRO_PARALLEL` enables the parallel path (`1` or `check`).
pub(crate) fn parallel_enabled() -> bool {
    config().mode != ParMode::Off
}

/// Configured pool size.
pub(crate) fn pool_threads() -> usize {
    config().threads
}

/// `VERUS_MACRO_PARALLEL_VERBOSE=1`.
pub(crate) fn verbose() -> bool {
    config().verbose
}

/// Mode and pool size from the environment values. Unset or empty selects the
/// parallel default, `0`/`off`/`false` and unknown values the serial mode;
/// unknown sizes select the default size.
fn parse_config(mode: Option<&str>, threads: Option<&str>, avail: usize) -> (ParMode, usize) {
    let mode = match mode.map(str::trim) {
        None | Some("") | Some("1") | Some("on") | Some("true") => ParMode::On,
        Some("check") => ParMode::Check,
        _ => ParMode::Off,
    };
    let default_threads = avail.saturating_sub(1).min(8);
    let threads = threads.and_then(|s| s.trim().parse::<usize>().ok()).unwrap_or(default_threads);
    (mode, threads.min(MAX_THREADS))
}

/// Entry point for `verus!`.
pub(crate) fn rewrite_items_entry(
    stream: proc_macro::TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
) -> proc_macro::TokenStream {
    let cfg = config();
    if cfg.mode == ParMode::Off {
        return crate::syntax::rewrite_items_serial(stream, erase_ghost, use_spec_traits);
    }
    let prefetch = crate::prefetch::mode();
    let hit = match prefetch {
        crate::prefetch::Mode::Off => None,
        _ => crate::prefetch::lookup(&stream, erase_ghost, use_spec_traits),
    };
    let check = cfg.mode == ParMode::Check || prefetch == crate::prefetch::Mode::Check;
    if !check || (hit.is_none() && cfg.mode != ParMode::Check) {
        if let Some(p) = hit {
            let r = commit(p, true);
            return proc_macro::TokenStream::from(r.tokens);
        }
        if cfg.threads >= 2 {
            let input = TokenStream::from(stream.clone());
            match run_parallel(input, erase_ghost, use_spec_traits, cfg.threads, true) {
                Ok(r) => {
                    if cfg.verbose {
                        eprintln!("verus! parallel rewrite: {} tasks", r.tasks);
                    }
                    return proc_macro::TokenStream::from(r.tokens);
                }
                Err(reason) => report_fallback(&reason),
            }
        }
        return crate::syntax::rewrite_items_serial(stream, erase_ghost, use_spec_traits);
    }
    let (par, label) = match hit {
        Some(p) => (Ok(commit(p, false)), "VERUS_MACRO_PREFETCH=check: prefetched"),
        None => {
            let input = TokenStream::from(stream.clone());
            let par = run_parallel(input, erase_ghost, use_spec_traits, cfg.threads.max(1), false);
            (par, "VERUS_MACRO_PARALLEL=check: parallel")
        }
    };
    check_against_serial(par, label, stream, erase_ghost, use_spec_traits)
}

/// Check mode: runs the serial path, compares `par` (computed first, without
/// side effects) with it, panics on any difference, and returns the serial result.
fn check_against_serial(
    par: Result<ParResult, String>,
    label: &str,
    stream: proc_macro::TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
) -> proc_macro::TokenStream {
    let uid_base = crate::syntax::EX_IDENT_UID.load(std::sync::atomic::Ordering::Relaxed);
    let (out, serial_diags) = {
        let _record = MainRecord::start();
        let out = crate::syntax::rewrite_items_serial(stream, erase_ghost, use_spec_traits);
        (out, MAIN_RECORD.with(|r| r.borrow_mut().take()).unwrap_or_default())
    };
    let uid_count =
        crate::syntax::EX_IDENT_UID.load(std::sync::atomic::Ordering::Relaxed) - uid_base;
    match par {
        Ok(par) => {
            let serial_tokens = TokenStream::from(out.clone());
            let problems = check_problems(&par, &serial_tokens, &serial_diags, uid_count);
            if !problems.is_empty() {
                panic!("{} rewrite differs from serial: {}", label, problems.join("; "));
            }
        }
        Err(reason) => report_fallback(&reason),
    }
    out
}

/// Differences of a side-effect-free result from the serial tokens,
/// diagnostics, and UID allocation count.
pub(crate) fn check_problems(
    par: &ParResult,
    serial_tokens: &TokenStream,
    serial_diags: &[DiagRecord],
    uid_count: u64,
) -> Vec<String> {
    let mut problems = Vec::new();
    if let Err(e) = compare_streams("", &par.tokens, serial_tokens) {
        problems.push(e);
    }
    if par.diags != serial_diags {
        problems.push(format!(
            "diagnostics differ: parallel {:?} vs serial {:?}",
            par.diags, serial_diags
        ));
    }
    if par.uid_count != uid_count {
        problems.push(format!(
            "UID allocations differ: parallel {} vs serial {}",
            par.uid_count, uid_count
        ));
    }
    problems
}

fn report_fallback(reason: &str) {
    if config().verbose {
        eprintln!("verus! parallel rewrite: serial fallback: {}", reason);
    }
}

// ---------------------------------------------------------------------------
// Worker-side sinks used by `syntax.rs` and `enum_synthesize.rs`.

/// A side effect deferred by a worker and replayed on the main thread.
enum Event {
    /// `spans` freezes one `#` punct per diagnostic span.
    Diag { level: DiagLevel, spans: FrozenTokens, msg: String },
    /// External-fn-specification name request for `placeholder`.
    Uid { path: FrozenTokens, placeholder: String },
}

struct WorkerCtx {
    task: usize,
    events: Vec<Event>,
    unsupported: Option<String>,
    placeholders: HashSet<String>,
}

thread_local! {
    static CTX: RefCell<Option<WorkerCtx>> = RefCell::new(None);
    /// Panics on this thread are caught and turned into serial fallback, so the
    /// panic hook stays silent (always on pool threads; on the main thread while
    /// a parallel result is prepared).
    static SILENT_PANICS: Cell<bool> = Cell::new(false);
    static MAIN_RECORD: RefCell<Option<Vec<DiagRecord>>> = RefCell::new(None);
}

/// Text of every placeholder ident starts with this; any other input or output
/// text containing `PARUID` (case-insensitively) is unsupported.
const PLACEHOLDER_PREFIX: &str = "_verus_external_fn_specification_PARUID_";

pub(crate) fn has_marker(s: &str) -> bool {
    s.to_ascii_lowercase().contains("paruid")
}

/// True on a parallel worker thread while it runs a task.
pub(crate) fn in_worker() -> bool {
    CTX.with(|c| c.borrow().is_some())
}

/// On a worker, mark the current task unsupported (forcing serial fallback).
/// No-op on the main thread.
pub(crate) fn worker_unsupported(reason: &str) {
    CTX.with(|c| {
        if let Some(ctx) = c.borrow_mut().as_mut() {
            if ctx.unsupported.is_none() {
                ctx.unsupported = Some(reason.to_string());
            }
        }
    })
}

/// Emit (main thread) or defer (worker) a compiler diagnostic.
pub(crate) fn emit_diagnostic(level: DiagLevel, spans: Vec<Span>, msg: &str) {
    let deferred = CTX.with(|c| match c.borrow_mut().as_mut() {
        Some(ctx) => {
            let marks: TokenStream = spans
                .iter()
                .map(|s| {
                    let mut p = Punct::new('#', Spacing::Alone);
                    p.set_span(*s);
                    TokenTree::Punct(p)
                })
                .collect();
            let spans = wt::freeze_worker(marks);
            ctx.events.push(Event::Diag { level, spans, msg: msg.to_string() });
            true
        }
        None => false,
    });
    if !deferred {
        emit_main(level, spans, msg);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DiagRecord {
    level: DiagLevel,
    spans: Vec<String>,
    msg: String,
}

/// Records main-thread diagnostics until dropped (also when the recorded serial
/// run panics), so no later invocation keeps recording.
struct MainRecord;

impl MainRecord {
    fn start() -> MainRecord {
        MAIN_RECORD.with(|r| *r.borrow_mut() = Some(Vec::new()));
        MainRecord
    }
}

impl Drop for MainRecord {
    fn drop(&mut self) {
        MAIN_RECORD.with(|r| *r.borrow_mut() = None);
    }
}

/// Main-thread emission; in check mode the serial run also records it.
fn emit_main(level: DiagLevel, spans: Vec<Span>, msg: &str) {
    MAIN_RECORD.with(|r| {
        if let Some(rec) = r.borrow_mut().as_mut() {
            rec.push(DiagRecord {
                level,
                spans: spans.iter().map(|s| format!("{:?}", s)).collect(),
                msg: msg.to_string(),
            });
        }
    });
    #[cfg(all(verus_keep_ghost, not(test)))]
    {
        let spans: Vec<proc_macro::Span> = spans.into_iter().map(|s| s.unwrap()).collect();
        let level = match level {
            DiagLevel::Warning => proc_macro::Level::Warning,
            DiagLevel::Error => proc_macro::Level::Error,
        };
        proc_macro::Diagnostic::spanned(spans, level, msg).emit();
    }
    // Unit tests run outside the compiler and only record diagnostics.
    #[cfg(any(not(verus_keep_ghost), test))]
    {
        let _ = (level, spans, msg);
    }
}

/// On a worker, defer allocation of an external-fn-specification UID name and
/// return a placeholder ident; on the main thread return `None`.
pub(crate) fn defer_ex_ident(expr_path_tokens: &TokenStream, span: Span) -> Option<Ident> {
    CTX.with(|c| {
        let mut b = c.borrow_mut();
        let ctx = b.as_mut()?;
        let placeholder = format!("{}{}_{}_", PLACEHOLDER_PREFIX, ctx.task, ctx.placeholders.len());
        ctx.placeholders.insert(placeholder.clone());
        let path = wt::freeze_worker(expr_path_tokens.clone());
        ctx.events.push(Event::Uid { path, placeholder: placeholder.clone() });
        Some(Ident::new(&placeholder, span))
    })
}

fn take_events() -> Vec<Event> {
    CTX.with(|c| c.borrow_mut().as_mut().map(|ctx| std::mem::take(&mut ctx.events)))
        .unwrap_or_default()
}

fn check_supported() -> Result<(), String> {
    match CTX.with(|c| c.borrow().as_ref().and_then(|ctx| ctx.unsupported.clone())) {
        Some(reason) => Err(format!("unsupported: {}", reason)),
        None => Ok(()),
    }
}

struct CtxGuard;

impl CtxGuard {
    fn new(task: usize) -> CtxGuard {
        CTX.with(|c| {
            *c.borrow_mut() = Some(WorkerCtx {
                task,
                events: Vec::new(),
                unsupported: None,
                placeholders: HashSet::new(),
            })
        });
        CtxGuard
    }
}

impl Drop for CtxGuard {
    fn drop(&mut self) {
        CTX.with(|c| *c.borrow_mut() = None);
    }
}

pub(crate) struct SilentPanics(bool);

impl SilentPanics {
    pub(crate) fn new() -> SilentPanics {
        SilentPanics(SILENT_PANICS.with(|f| f.replace(true)))
    }
}

impl Drop for SilentPanics {
    fn drop(&mut self) {
        SILENT_PANICS.with(|f| f.set(self.0));
    }
}

/// Panics caught for serial fallback (which re-raises them if they are real) stay
/// silent: always on pool threads, on the main thread under `SilentPanics`; other
/// panics keep the previous hook.
pub(crate) fn install_silent_hook() {
    static HOOK: std::sync::Once = std::sync::Once::new();
    HOOK.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SILENT_PANICS.with(|f| f.get()) {
                prev(info)
            }
        }));
    });
}

// ---------------------------------------------------------------------------
// Persistent bounded pool.

pub(crate) type Job = Box<dyn FnOnce() + Send + 'static>;

/// Real jobs (tasks of the current invocation) always run before speculative
/// (prefetch) jobs, and at most `speculative_cap` speculative jobs run at once
/// so a real n-way invocation finds most threads free.
#[derive(Default)]
struct Queues {
    real: VecDeque<Job>,
    speculative: VecDeque<Job>,
    speculative_running: usize,
}

pub(crate) struct Pool {
    queues: Mutex<Queues>,
    ready: Condvar,
    pub(crate) size: usize,
    speculative_cap: usize,
}

/// Concurrent speculative jobs allowed on a pool of `size` threads.
pub(crate) fn speculative_cap(size: usize) -> usize {
    (size / 2).max(1)
}

impl Pool {
    /// Queues `job`; false when the pool has no threads.
    pub(crate) fn submit(&self, job: Job, speculative: bool) -> bool {
        if self.size == 0 {
            return false;
        }
        let mut q = self.queues.lock().unwrap_or_else(|e| e.into_inner());
        if speculative {
            q.speculative.push_back(job)
        } else {
            q.real.push_back(job)
        }
        drop(q);
        // Any idle thread can take a real job, and a speculative one if under
        // the cap (otherwise `finish_speculative` wakes a thread for it).
        self.ready.notify_one();
        true
    }

    /// Next job and whether it is speculative.
    fn next_job(&self) -> (Job, bool) {
        let mut q = self.queues.lock().unwrap_or_else(|e| e.into_inner());
        loop {
            if let Some(job) = q.real.pop_front() {
                return (job, false);
            }
            if q.speculative_running < self.speculative_cap {
                if let Some(job) = q.speculative.pop_front() {
                    q.speculative_running += 1;
                    return (job, true);
                }
            }
            q = self.ready.wait(q).unwrap_or_else(|e| e.into_inner());
        }
    }

    fn finish_speculative(&self) {
        let mut q = self.queues.lock().unwrap_or_else(|e| e.into_inner());
        q.speculative_running -= 1;
        let more = !q.speculative.is_empty();
        drop(q);
        if more {
            self.ready.notify_one();
        }
    }

    /// Speculative jobs running right now.
    #[cfg(test)]
    pub(crate) fn speculative_running(&self) -> usize {
        self.queues.lock().unwrap_or_else(|e| e.into_inner()).speculative_running
    }
}

pub(crate) fn pool(size: usize) -> &'static Pool {
    static POOL: OnceLock<Pool> = OnceLock::new();
    static SPAWN: std::sync::Once = std::sync::Once::new();
    let pool = POOL.get_or_init(|| {
        install_silent_hook();
        // Without the worker substrate every job would fail; spawn nothing.
        let size = if wt::WORKER_JOBS_AVAILABLE { size } else { 0 };
        let mut spawned = 0;
        for i in 0..size {
            let ok = std::thread::Builder::new()
                .name(format!("verus-macro-worker-{}", i))
                .stack_size(WORKER_STACK_SIZE)
                .spawn(move || {
                    SILENT_PANICS.with(|f| f.set(true));
                    // Threads start only after the pool is published below.
                    SPAWN.wait();
                    let pool = POOL.get().expect("pool published");
                    loop {
                        let (job, speculative) = pool.next_job();
                        // Jobs catch their own panics; a stray one must not kill the thread.
                        let _ = catch_unwind(AssertUnwindSafe(job));
                        if speculative {
                            pool.finish_speculative();
                        }
                    }
                })
                .is_ok();
            if ok {
                spawned += 1;
            }
        }
        Pool {
            queues: Mutex::new(Queues::default()),
            ready: Condvar::new(),
            size: spawned,
            speculative_cap: speculative_cap(spawned),
        }
    });
    SPAWN.call_once(|| {});
    pool
}

/// Serializes parallel invocations so each task of an invocation has its own
/// pool thread (tasks block on the main thread between phases).
static INVOCATION_LOCK: Mutex<()> = Mutex::new(());

// ---------------------------------------------------------------------------
// Task protocol.

pub(crate) struct TaskInput {
    pub(crate) task: usize,
    pub(crate) frozen: FrozenTokens,
    pub(crate) erase_ghost: EraseGhost,
    pub(crate) use_spec_traits: bool,
    pub(crate) rustdoc: bool,
}

enum ToTask {
    Redo(ParLeakState),
    Continue { leak: ParLeakState, first_owner: bool },
    Abort,
}

struct PhaseA {
    has_proxy: bool,
    end: ParLeakState,
    p_count: usize,
}

const CLASS_P: usize = 0;
const CLASS_X: usize = 1;

/// One output list entry: the item followed by its synthesized enum item.
struct EntryOut {
    tokens: FrozenTokens,
    has_placeholder: bool,
}

pub(crate) struct TaskOutput {
    /// Prefilter proxy-pass events, in root order.
    pre2: Vec<Event>,
    /// Prefilter transform events per class, in entry order.
    pre6: [Vec<Event>; 2],
    /// Per level, per class: entries, visit events, post events.
    levels: Vec<[(Vec<EntryOut>, Vec<Event>, Vec<Event>); 2]>,
    /// Per class: assume-specification extra impl items and their count.
    extra: [(EntryOut, usize); 2],
}

enum FromTask {
    PhaseA(usize, PhaseA),
    Redone(usize, ParLeakState),
    Done(usize, TaskOutput),
    Failed(usize, String),
    Exited,
}

pub(crate) fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "non-string panic".to_string()
    }
}

/// The task side of the task protocol.
trait Link {
    /// False when the driver is gone.
    fn send(&mut self, m: FromTask) -> bool;
    /// `None` when the driver is gone.
    fn recv(&mut self) -> Option<ToTask>;
}

struct ChanLink {
    rx: Receiver<ToTask>,
    tx: Sender<FromTask>,
}

impl Link for ChanLink {
    fn send(&mut self, m: FromTask) -> bool {
        self.tx.send(m).is_ok()
    }

    fn recv(&mut self) -> Option<ToTask> {
        self.rx.recv().ok()
    }
}

fn run_task(input: TaskInput, rx: Receiver<ToTask>, tx: Sender<FromTask>) {
    let task = input.task;
    let mut link = ChanLink { rx, tx };
    let result = catch_unwind(AssertUnwindSafe(|| task_body(&input, &mut link)));
    let failure = match result {
        Ok(Ok(())) => None,
        Ok(Err(reason)) => Some(reason),
        Err(payload) => Some(format!("worker panic: {}", panic_message(&*payload))),
    };
    if let Some(reason) = failure {
        let _ = link.tx.send(FromTask::Failed(task, reason));
    }
    let _ = link.tx.send(FromTask::Exited);
}

/// In-thread driver of a single-task invocation, answering like `drive_tasks`
/// for `n == 1`.
#[derive(Default)]
struct LocalLink {
    reply: Option<ToTask>,
    done: Option<TaskOutput>,
    failed: Option<String>,
}

impl Link for LocalLink {
    fn send(&mut self, m: FromTask) -> bool {
        match m {
            FromTask::PhaseA(_, pa) => match single_task_continue(&pa) {
                Ok(reply) => self.reply = Some(reply),
                Err(reason) => {
                    self.failed = Some(reason);
                    self.reply = Some(ToTask::Abort);
                }
            },
            FromTask::Done(_, out) => self.done = Some(out),
            FromTask::Failed(_, reason) => self.failed = Some(reason),
            FromTask::Redone(..) => {
                self.failed = Some("protocol: unexpected redo".to_string());
                self.reply = Some(ToTask::Abort);
            }
            FromTask::Exited => {}
        }
        true
    }

    fn recv(&mut self) -> Option<ToTask> {
        self.reply.take()
    }
}

/// `drive_tasks` for one task: its own proxy pass starts from the initial
/// state, so its end state is the leaked state; the same leak-state rules apply.
fn single_task_continue(pa: &PhaseA) -> Result<ToTask, String> {
    let leak = if pa.has_proxy { pa.end } else { ParLeakState::INITIAL };
    if !leak.initial_after_item_reset() {
        return Err("prefilter leaves visitor state the item reset does not clear".to_string());
    }
    let first_owner = pa.p_count > 0;
    if leak != ParLeakState::INITIAL && !first_owner {
        return Err("leaked prefilter state without a first item".to_string());
    }
    Ok(ToTask::Continue { leak, first_owner })
}

/// Runs `input` as the only task of an invocation on the current (non-compiler)
/// thread, inside its own worker job.
pub(crate) fn run_single_task(input: TaskInput) -> Result<TaskOutput, String> {
    let mut link = LocalLink::default();
    let result = catch_unwind(AssertUnwindSafe(|| task_body(&input, &mut link)));
    match result {
        Ok(Ok(())) => {}
        Ok(Err(reason)) => return Err(reason),
        Err(payload) => return Err(format!("worker panic: {}", panic_message(&*payload))),
    }
    if let Some(reason) = link.failed {
        return Err(reason);
    }
    link.done.ok_or_else(|| "task produced no output".to_string())
}

/// Runs prefilter step 2 over `roots` from `start`, threading Visitor state.
fn proxy_pass(
    v: &mut Visitor,
    roots: Vec<Item>,
    start: ParLeakState,
) -> Result<(Vec<Vec<Item>>, Vec<Event>, ParLeakState), String> {
    v.par_set_leak_state(&start);
    let mut lists = Vec::with_capacity(roots.len());
    let mut events = Vec::new();
    for root in roots {
        let list =
            if v.par_needs_proxy(&root) { v.par_prefilter_proxies(root) } else { vec![root] };
        lists.push(list);
        events.extend(take_events());
        check_supported()?;
    }
    let end = v.par_leak_state().ok_or("proxy pass left impl context or additional items")?;
    Ok((lists, events, end))
}

/// Checks every ident/literal of `ts` for placeholder text; returns whether an
/// issued placeholder occurs.
fn scan_placeholders(ts: &TokenStream, issued: &HashSet<String>) -> Result<bool, String> {
    let mut found = false;
    for tt in ts.clone() {
        match tt {
            TokenTree::Group(g) => found |= scan_placeholders(&g.stream(), issued)?,
            TokenTree::Ident(id) => {
                let s = id.to_string();
                if has_marker(&s) {
                    if issued.contains(&s) {
                        found = true;
                    } else {
                        return Err("placeholder text escaped into other tokens".to_string());
                    }
                }
            }
            TokenTree::Literal(l) => {
                if has_marker(&l.to_string()) {
                    return Err("placeholder text escaped into a literal".to_string());
                }
            }
            TokenTree::Punct(_) => {}
        }
    }
    Ok(found)
}

/// Rejects inputs the worker path does not support: placeholder marker text and
/// any contrib preprocessing macro name (contrib runs serially).
fn scan_input(ts: &TokenStream) -> Result<(), String> {
    for tt in ts.clone() {
        match tt {
            TokenTree::Group(g) => scan_input(&g.stream())?,
            TokenTree::Ident(id) => {
                let s = id.to_string();
                if has_marker(&s) {
                    return Err("input contains placeholder marker text".to_string());
                }
                if crate::contrib::PREPROCESSORS.iter().any(|p| p.0 == s) {
                    return Err(format!("contrib preprocessing (`{}`)", s));
                }
            }
            TokenTree::Literal(l) => {
                if has_marker(&l.to_string()) {
                    return Err("input contains placeholder marker text".to_string());
                }
            }
            TokenTree::Punct(_) => {}
        }
    }
    Ok(())
}

fn freeze_out(ts: TokenStream) -> Result<EntryOut, String> {
    let has_placeholder = CTX.with(|c| match c.borrow().as_ref() {
        Some(ctx) => scan_placeholders(&ts, &ctx.placeholders),
        None => scan_placeholders(&ts, &HashSet::new()),
    })?;
    Ok(EntryOut { tokens: wt::freeze_worker(ts), has_placeholder })
}

fn task_body(input: &TaskInput, link: &mut dyn Link) -> Result<(), String> {
    let task = input.task;
    let _job = wt::begin_job();
    let _ctx = CtxGuard::new(task);
    #[cfg(test)]
    if task == 1 && tests::INJECT_WORKER_PANIC.load(std::sync::atomic::Ordering::SeqCst) {
        panic!("injected worker panic");
    }

    let ts = wt::melt_worker(&input.frozen);
    scan_input(&ts)?;
    let items: Items = wt::parse2_prejoined(ts).map_err(|e| format!("segment parse: {}", e))?;
    if items.items.is_empty() {
        return Err("empty segment".to_string());
    }
    let mut v = Visitor::new_for_items(input.erase_ghost, input.use_spec_traits, input.rustdoc);

    // Step 1 (contrib) is stateless.
    let mut roots = Vec::with_capacity(items.items.len());
    for item in items.items {
        roots.push(Visitor::par_prefilter_contrib(item)?);
    }
    if !take_events().is_empty() {
        return Err("events in contrib step".to_string());
    }
    check_supported()?;

    // Step 2 (unerased proxies) speculatively from the initial state.
    let has_proxy = roots.iter().any(|r| v.par_needs_proxy(r));
    let saved = if has_proxy { Some(roots.clone()) } else { None };
    let (mut p_lists, mut pre2, end) = proxy_pass(&mut v, roots, ParLeakState::INITIAL)?;
    let p_count =
        p_lists.iter().map(|l| l.iter().filter(|i| v.par_keeps_erase_all(i)).count()).sum();
    if !link.send(FromTask::PhaseA(task, PhaseA { has_proxy, end, p_count })) {
        return Ok(());
    }
    let (leak, first_owner) = loop {
        match link.recv() {
            Some(ToTask::Redo(start)) => {
                let roots = saved.clone().ok_or("redo without proxy items")?;
                let (lists, events, end) = proxy_pass(&mut v, roots, start)?;
                p_lists = lists;
                pre2 = events;
                if !link.send(FromTask::Redone(task, end)) {
                    return Ok(());
                }
            }
            Some(ToTask::Continue { leak, first_owner }) => break (leak, first_owner),
            Some(ToTask::Abort) | None => return Ok(()),
        }
    };

    // Step 3 (extension traits): appended items form class X, after all class P.
    let mut x_items = Vec::new();
    for list in p_lists.iter_mut() {
        x_items.extend(v.par_prefilter_ext_traits(list));
    }
    if !take_events().is_empty() {
        return Err("events in extension-trait step".to_string());
    }
    check_supported()?;
    let p_items: Vec<Item> = p_lists.into_iter().flatten().collect();

    // Steps 4-6 (erase_all retain, erase stubs, transforms), run with the state
    // the serial proxy pass leaves behind.
    let mut pre6: [Vec<Event>; 2] = [Vec::new(), Vec::new()];
    let mut extra: [Vec<ImplItem>; 2] = [Vec::new(), Vec::new()];
    let mut level: [Vec<Item>; 2] = [Vec::new(), Vec::new()];
    for (class, entries) in [(CLASS_P, p_items), (CLASS_X, x_items)] {
        for mut item in entries {
            v.par_set_leak_state(&leak);
            let keep = v.par_prefilter_entry(&mut item, &mut extra[class]);
            pre6[class].extend(take_events());
            check_supported()?;
            if v.par_leak_state() != Some(leak) {
                return Err("prefilter transform changed visitor state".to_string());
            }
            if keep {
                level[class].push(item);
            }
        }
    }

    // Main loop and post pass, level by level (serial list order is level-major).
    let mut levels = Vec::new();
    let mut first = first_owner;
    loop {
        if level[CLASS_P].is_empty() && level[CLASS_X].is_empty() {
            break;
        }
        let mut next: [Vec<Item>; 2] = [Vec::new(), Vec::new()];
        let mut outs: [(Vec<EntryOut>, Vec<Event>, Vec<Event>); 2] =
            [(Vec::new(), Vec::new(), Vec::new()), (Vec::new(), Vec::new(), Vec::new())];
        for class in [CLASS_P, CLASS_X] {
            for mut item in std::mem::take(&mut level[class]) {
                let start = if first { leak } else { ParLeakState::INITIAL };
                first = false;
                v.par_set_leak_state(&start);
                let adds = v.par_visit_entry(&mut item);
                outs[class].1.extend(take_events());
                check_supported()?;
                if v.par_leak_state() != Some(ParLeakState::INITIAL) {
                    return Err("visit leaked visitor state".to_string());
                }
                next[class].extend(adds);
                let synthesized = v.par_post_entry(&mut item);
                outs[class].2.extend(take_events());
                check_supported()?;
                let mut ts = item.into_token_stream();
                if let Some(s) = synthesized {
                    s.to_tokens(&mut ts);
                }
                outs[class].0.push(freeze_out(ts)?);
            }
        }
        levels.push(outs);
        level = next;
    }

    let mut extra_out = Vec::new();
    for items in extra {
        let n = items.len();
        let mut ts = TokenStream::new();
        for item in items {
            item.to_tokens(&mut ts);
        }
        extra_out.push((freeze_out(ts)?, n));
    }
    let extra_x = extra_out.pop().unwrap();
    let extra_p = extra_out.pop().unwrap();
    check_supported()?;
    let output = TaskOutput { pre2, pre6, levels, extra: [extra_p, extra_x] };
    let _ = link.send(FromTask::Done(task, output));
    Ok(())
}

// ---------------------------------------------------------------------------
// Main-thread driver.

pub(crate) struct ParResult {
    pub(crate) tokens: TokenStream,
    pub(crate) diags: Vec<DiagRecord>,
    pub(crate) uid_count: u64,
    /// Number of parallel tasks (segments) used.
    pub(crate) tasks: usize,
}

const STARTERS: &[&str] = &[
    "pub",
    "fn",
    "struct",
    "enum",
    "union",
    "impl",
    "trait",
    "mod",
    "use",
    "const",
    "static",
    "type",
    "extern",
    "unsafe",
    "async",
    "auto",
    "macro_rules",
    "spec",
    "proof",
    "exec",
    "open",
    "closed",
    "uninterp",
    "broadcast",
    "tracked",
    "ghost",
    "axiom",
    "global",
    "assume_specification",
];

/// Whether a new item may start at `tts[i]` (candidate split point; every
/// resulting segment is still independently parsed).
fn is_boundary(tts: &[TokenTree], i: usize) -> bool {
    let prev_ends = match &tts[i - 1] {
        TokenTree::Punct(p) => p.as_char() == ';',
        TokenTree::Group(g) => g.delimiter() == Delimiter::Brace,
        _ => false,
    };
    prev_ends
        && match &tts[i] {
            TokenTree::Punct(p) if p.as_char() == '#' => matches!(
                tts.get(i + 1),
                Some(TokenTree::Group(g)) if g.delimiter() == Delimiter::Bracket
            ),
            TokenTree::Ident(id) => STARTERS.contains(&id.to_string().as_str()),
            _ => false,
        }
}

fn start_offset(tt: &TokenTree) -> usize {
    tt.span().byte_range().start
}

/// Splits `tts` into at most `n` contiguous index ranges at candidate
/// boundaries, balanced by the source start offsets of the candidates (byte
/// ranges are only queried at candidates), or by token index when the offsets
/// span no source range.
fn split_segments(tts: &[TokenTree], n: usize) -> Vec<std::ops::Range<usize>> {
    let len = tts.len();
    let mut cuts = Vec::new();
    if n > 1 && len > 1 {
        let base = start_offset(&tts[0]);
        let end = tts[len - 1].span().byte_range().end;
        let by_offset = end > base;
        let total = if by_offset { end - base } else { len };
        for i in 1..len {
            let k = cuts.len() + 1;
            if k >= n {
                break;
            }
            if !is_boundary(tts, i) {
                continue;
            }
            let pos = if by_offset { start_offset(&tts[i]).saturating_sub(base) } else { i };
            if pos * n >= total * k {
                cuts.push(i);
            }
        }
    }
    let mut segments = Vec::with_capacity(cuts.len() + 1);
    let mut pos = 0;
    for cut in cuts {
        segments.push(pos..cut);
        pos = cut;
    }
    segments.push(pos..len);
    segments
}

/// Main-only lazily initialized configuration (`vstd_kind` may query compiler
/// cfgs); forced before workers start so workers only read the cached value. A
/// panic here (silent; the caller holds `SilentPanics`) means serial would panic
/// too and report it.
pub(crate) fn force_main_caches() -> Result<(), String> {
    catch_unwind(|| {
        let _ = crate::vstd_kind();
    })
    .map_err(|_| "configuration query panicked".to_string())
}

struct Abort<'a> {
    to_tasks: &'a [Sender<ToTask>],
}

impl Drop for Abort<'_> {
    fn drop(&mut self) {
        for tx in self.to_tasks {
            let _ = tx.send(ToTask::Abort);
        }
    }
}

fn recv_from(rx: &Receiver<FromTask>, exited: &mut usize) -> Result<FromTask, String> {
    loop {
        match rx.recv() {
            Ok(FromTask::Exited) => *exited += 1,
            Ok(FromTask::Failed(task, reason)) => return Err(format!("task {}: {}", task, reason)),
            Ok(m) => return Ok(m),
            Err(_) => return Err("worker channel closed".to_string()),
        }
    }
}

/// Exchange with the tasks; returns their outputs in task order.
fn drive_tasks(
    rx: &Receiver<FromTask>,
    to_tasks: &[Sender<ToTask>],
    exited: &mut usize,
) -> Result<Vec<TaskOutput>, String> {
    let n = to_tasks.len();
    let mut phase_a: Vec<Option<PhaseA>> = (0..n).map(|_| None).collect();
    for _ in 0..n {
        match recv_from(rx, exited)? {
            FromTask::PhaseA(task, pa) => phase_a[task] = Some(pa),
            _ => return Err("protocol: expected phase A".to_string()),
        }
    }
    let phase_a: Vec<PhaseA> = phase_a.into_iter().map(Option::unwrap).collect();
    let mut state = ParLeakState::INITIAL;
    for (task, pa) in phase_a.iter().enumerate() {
        if !pa.has_proxy {
            continue;
        }
        if state == ParLeakState::INITIAL {
            state = pa.end;
        } else {
            to_tasks[task].send(ToTask::Redo(state)).map_err(|_| "task gone")?;
            match recv_from(rx, exited)? {
                FromTask::Redone(t, end) if t == task => {
                    #[cfg(test)]
                    tests::REDOS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    state = end
                }
                _ => return Err("protocol: expected redo".to_string()),
            }
        }
    }
    let leak = state;
    if !leak.initial_after_item_reset() {
        return Err("prefilter leaves visitor state the item reset does not clear".to_string());
    }
    let first_owner = phase_a.iter().position(|pa| pa.p_count > 0);
    if leak != ParLeakState::INITIAL && first_owner.is_none() {
        return Err("leaked prefilter state without a first item".to_string());
    }
    for (task, tx) in to_tasks.iter().enumerate() {
        let first_owner = first_owner == Some(task);
        tx.send(ToTask::Continue { leak, first_owner }).map_err(|_| "task gone")?;
    }
    let mut outputs: Vec<Option<TaskOutput>> = (0..n).map(|_| None).collect();
    for _ in 0..n {
        match recv_from(rx, exited)? {
            FromTask::Done(task, out) => outputs[task] = Some(out),
            _ => return Err("protocol: expected output".to_string()),
        }
    }
    Ok(outputs.into_iter().map(Option::unwrap).collect())
}

enum Replay {
    Diag { level: DiagLevel, spans: Vec<Span>, msg: String },
    Uid { placeholder: String, toks: String },
}

fn prepare_events(meta: &dyn Thaw, events: Vec<Event>, replay: &mut Vec<Replay>) {
    for event in events {
        replay.push(match event {
            Event::Diag { level, spans, msg } => {
                let spans = meta.thaw_tokens(&spans).into_iter().map(|tt| tt.span()).collect();
                Replay::Diag { level, spans, msg }
            }
            Event::Uid { path, placeholder } => {
                Replay::Uid { placeholder, toks: meta.thaw_tokens(&path).to_string() }
            }
        });
    }
}

fn rename_placeholders(ts: TokenStream, names: &HashMap<String, String>) -> TokenStream {
    ts.into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) => {
                let mut ng = Group::new(g.delimiter(), rename_placeholders(g.stream(), names));
                ng.set_span(g.span());
                TokenTree::Group(ng)
            }
            TokenTree::Ident(id) => match names.get(&id.to_string()) {
                Some(name) => TokenTree::Ident(Ident::new(name, id.span())),
                None => TokenTree::Ident(id),
            },
            tt => tt,
        })
        .collect()
}

/// Runs the parallel pipeline. With `emit`, replays diagnostics and allocates
/// UIDs for real; otherwise (check mode) records diagnostics and simulates UIDs.
/// Returns `Err` with no side effects when the serial path must be used.
fn run_parallel(
    input: TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
    threads: usize,
    emit: bool,
) -> Result<ParResult, String> {
    if cfg!(feature = "contrib-hooks") {
        return Err("contrib-hooks".to_string());
    }
    if crate::rustdoc::env_rustdoc() {
        return Err("rustdoc".to_string());
    }
    if !wt::WORKER_JOBS_AVAILABLE {
        return Err("worker jobs unavailable".to_string());
    }
    install_silent_hook();
    let prepared = {
        let _silent = SilentPanics::new();
        force_main_caches()?;
        catch_unwind(AssertUnwindSafe(|| {
            run_parallel_core(input, erase_ghost, use_spec_traits, threads, emit)
        }))
    };
    match prepared {
        Ok(Ok(p)) => Ok(commit(p, emit)),
        Ok(Err(reason)) => Err(reason),
        Err(payload) => Err(format!("main-thread panic: {}", panic_message(&*payload))),
    }
}

/// `run_parallel` after the global gates (contrib hooks, rustdoc, cached config):
/// everything up to, but excluding, the side effects.
fn run_parallel_core(
    input: TokenStream,
    erase_ghost: EraseGhost,
    use_spec_traits: bool,
    threads: usize,
    emit: bool,
) -> Result<Prepared, String> {
    let rustdoc = false;
    let pool = pool(threads);
    let n = threads.min(pool.size);
    if n == 0 {
        return Err("no worker threads".to_string());
    }
    let tts: Vec<TokenTree> = input.into_iter().collect();
    if tts.is_empty() {
        return Err("empty input".to_string());
    }
    let segments = split_segments(&tts, n);
    if emit && segments.len() < 2 {
        return Err("fewer than two segments".to_string());
    }
    let mut metas = Vec::with_capacity(segments.len());
    let mut frozen = Vec::with_capacity(segments.len());
    for seg in segments {
        let (f, m) = wt::freeze_rejoin_main_trees(&tts[seg]);
        frozen.push(f);
        metas.push(m);
    }
    wt::release_main_trees(tts);

    let _lock = INVOCATION_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let (from_tx, from_rx) = channel::<FromTask>();
    let mut to_tasks = Vec::with_capacity(frozen.len());
    let mut dispatched = 0;
    for (task, frozen) in frozen.into_iter().enumerate() {
        let (to_tx, to_rx) = channel::<ToTask>();
        to_tasks.push(to_tx);
        let input = TaskInput { task, frozen, erase_ghost, use_spec_traits, rustdoc };
        let from_tx = from_tx.clone();
        let job: Job = Box::new(move || run_task(input, to_rx, from_tx));
        if pool.submit(job, false) {
            dispatched += 1;
        } else {
            break;
        }
    }
    drop(from_tx);
    let mut exited = 0;
    let outputs = {
        let _abort = Abort { to_tasks: &to_tasks };
        if dispatched < to_tasks.len() {
            Err("worker pool unavailable".to_string())
        } else {
            drive_tasks(&from_rx, &to_tasks, &mut exited)
        }
    };
    // Wait until every task has ended its worker job and released its thread.
    while exited < dispatched {
        match from_rx.recv() {
            Ok(FromTask::Exited) => exited += 1,
            Ok(_) => {}
            Err(_) => break,
        }
    }
    drop(_lock);
    let outputs = outputs?;
    let thaws: Vec<&dyn Thaw> = metas.iter().map(|m| m as &dyn Thaw).collect();
    prepare_outputs(&thaws, outputs)
}

/// Rebuilds main-thread tokens from one task's frozen output.
pub(crate) trait Thaw {
    fn thaw_tokens(&self, frozen: &FrozenTokens) -> TokenStream;
}

impl Thaw for ThawMetadata {
    fn thaw_tokens(&self, frozen: &FrozenTokens) -> TokenStream {
        self.thaw(frozen)
    }
}

impl TaskOutput {
    /// Rough heap footprint, for the prefetch memory cap.
    pub(crate) fn approx_bytes(&self) -> usize {
        fn ev(events: &[Event]) -> usize {
            events
                .iter()
                .map(|e| match e {
                    Event::Diag { spans, msg, .. } => frozen_bytes(spans) + msg.len(),
                    Event::Uid { path, placeholder } => frozen_bytes(path) + placeholder.len(),
                })
                .sum()
        }
        let mut n = ev(&self.pre2) + ev(&self.pre6[0]) + ev(&self.pre6[1]);
        for level in &self.levels {
            for (entries, visit, post) in level {
                n += entries.iter().map(|e| frozen_bytes(&e.tokens)).sum::<usize>();
                n += ev(visit) + ev(post);
            }
        }
        n + frozen_bytes(&self.extra[0].0.tokens) + frozen_bytes(&self.extra[1].0.tokens)
    }
}

/// Rough heap footprint of frozen tokens (nodes, text arena, recipes, and the
/// three shared allocations' headers).
pub(crate) fn frozen_bytes(f: &FrozenTokens) -> usize {
    64 + f.heap_bytes()
}

/// Thaws every task output (`thaws[task]` belongs to task `task`) and orders
/// the deferred events and output streams exactly as the serial path would.
/// No side effect happens here.
pub(crate) fn prepare_outputs(
    thaws: &[&dyn Thaw],
    outputs: Vec<TaskOutput>,
) -> Result<Prepared, String> {
    let tasks = outputs.len();
    if thaws.len() != tasks {
        return Err("thaw metadata count differs from task count".to_string());
    }
    let mut replay = Vec::new();
    let mut levels: Vec<Vec<[(Vec<EntryOut>, Vec<Event>, Vec<Event>); 2]>> = Vec::new();
    let mut extras: Vec<[(EntryOut, usize); 2]> = Vec::new();
    let mut pre6_by_task: Vec<[Vec<Event>; 2]> = Vec::new();
    for (task, out) in outputs.into_iter().enumerate() {
        prepare_events(thaws[task], out.pre2, &mut replay);
        pre6_by_task.push(out.pre6);
        levels.push(out.levels);
        extras.push(out.extra);
    }
    for class in [CLASS_P, CLASS_X] {
        for (task, pre6) in pre6_by_task.iter_mut().enumerate() {
            prepare_events(thaws[task], std::mem::take(&mut pre6[class]), &mut replay);
        }
    }
    let max_level = levels.iter().map(|l| l.len()).max().unwrap_or(0);
    let mut visit_events = Vec::new();
    let mut post_events = Vec::new();
    let mut streams: Vec<(TokenStream, bool)> = Vec::new();
    let mut extra_streams: Vec<(TokenStream, bool)> = Vec::new();
    let mut extra_count = 0;
    for class in [CLASS_P, CLASS_X] {
        for (task, extra) in extras.iter().enumerate() {
            let (out, count) = &extra[class];
            extra_count += count;
            extra_streams.push((thaws[task].thaw_tokens(&out.tokens), out.has_placeholder));
        }
    }
    for lvl in 0..max_level {
        for class in [CLASS_P, CLASS_X] {
            for (task, task_levels) in levels.iter_mut().enumerate() {
                if let Some(level) = task_levels.get_mut(lvl) {
                    let (entries, visit, post) = &mut level[class];
                    prepare_events(thaws[task], std::mem::take(visit), &mut visit_events);
                    prepare_events(thaws[task], std::mem::take(post), &mut post_events);
                    for e in entries.iter() {
                        streams.push((thaws[task].thaw_tokens(&e.tokens), e.has_placeholder));
                    }
                }
            }
        }
        if lvl == 0 && extra_count > 0 {
            let impls: Vec<TokenStream> = extra_streams.drain(..).map(|(ts, _)| ts).collect();
            let has_placeholder = true;
            streams.push((crate::syntax::assume_spec_extra_impl_tokens(impls), has_placeholder));
        }
    }
    replay.extend(visit_events);
    replay.extend(post_events);

    // Every placeholder left in the output must be named by a replayed request
    // (speculative proxy passes may issue placeholders that are later discarded).
    let requested: HashSet<String> = replay
        .iter()
        .filter_map(|r| match r {
            Replay::Uid { placeholder, .. } => Some(placeholder.clone()),
            Replay::Diag { .. } => None,
        })
        .collect();
    for (ts, has_placeholder) in streams.iter() {
        if *has_placeholder {
            scan_placeholders(ts, &requested)?;
        }
    }

    Ok(Prepared { replay, streams, tasks })
}

/// A fully thawed parallel result whose side effects have not happened yet.
pub(crate) struct Prepared {
    replay: Vec<Replay>,
    streams: Vec<(TokenStream, bool)>,
    tasks: usize,
}

/// Performs the side effects of `p` in exact serial order and assembles the
/// output. With `emit`, emits diagnostics and allocates UIDs for real; otherwise
/// (check mode) records diagnostics and simulates UIDs from the current counter.
pub(crate) fn commit(p: Prepared, emit: bool) -> ParResult {
    let Prepared { replay, streams, tasks } = p;
    let mut diags = Vec::new();
    let mut names = HashMap::new();
    let mut uid_count = 0u64;
    let uid_base = crate::syntax::EX_IDENT_UID.load(std::sync::atomic::Ordering::Relaxed);
    for r in replay {
        match r {
            Replay::Diag { level, spans, msg } => {
                if emit {
                    emit_main(level, spans, &msg);
                } else {
                    diags.push(DiagRecord {
                        level,
                        spans: spans.iter().map(|s| format!("{:?}", s)).collect(),
                        msg,
                    });
                }
            }
            Replay::Uid { placeholder, toks } => {
                let uid = if emit {
                    crate::syntax::EX_IDENT_UID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
                } else {
                    uid_base + uid_count
                };
                uid_count += 1;
                names.insert(placeholder, crate::syntax::ex_ident_name(uid, &toks));
            }
        }
    }
    // One concatenation of all streams, in order (same trees as appending each).
    let mut tokens = TokenStream::new();
    tokens.extend(streams.into_iter().map(|(ts, has_placeholder)| {
        if has_placeholder && !names.is_empty() { rename_placeholders(ts, &names) } else { ts }
    }));
    ParResult { tokens, diags, uid_count, tasks }
}

// ---------------------------------------------------------------------------
// Check-mode comparison.

fn span_key(s: Span) -> String {
    format!("{:?}", s)
}

pub(crate) fn compare_streams(path: &str, a: &TokenStream, b: &TokenStream) -> Result<(), String> {
    let a: Vec<TokenTree> = a.clone().into_iter().collect();
    let b: Vec<TokenTree> = b.clone().into_iter().collect();
    for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
        let p = format!("{}[{}]", path, i);
        let same = match (x, y) {
            (TokenTree::Group(x), TokenTree::Group(y)) => {
                if x.delimiter() != y.delimiter()
                    || span_key(x.span()) != span_key(y.span())
                    || span_key(x.span_open()) != span_key(y.span_open())
                    || span_key(x.span_close()) != span_key(y.span_close())
                {
                    false
                } else {
                    compare_streams(&p, &x.stream(), &y.stream())?;
                    true
                }
            }
            (TokenTree::Ident(x), TokenTree::Ident(y)) => {
                x.to_string() == y.to_string() && span_key(x.span()) == span_key(y.span())
            }
            (TokenTree::Punct(x), TokenTree::Punct(y)) => {
                x.as_char() == y.as_char()
                    && x.spacing() == y.spacing()
                    && span_key(x.span()) == span_key(y.span())
            }
            (TokenTree::Literal(x), TokenTree::Literal(y)) => {
                x.to_string() == y.to_string() && span_key(x.span()) == span_key(y.span())
            }
            _ => false,
        };
        if !same {
            return Err(format!("token {} differs: parallel {:?} vs serial {:?}", p, x, y));
        }
    }
    if a.len() != b.len() {
        return Err(format!(
            "token count at {:?} differs: parallel {} vs serial {}",
            path,
            a.len(),
            b.len()
        ));
    }
    Ok(())
}

#[cfg(test)]
#[path = "par_items_tests.rs"]
pub(crate) mod tests;
