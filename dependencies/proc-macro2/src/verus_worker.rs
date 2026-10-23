//! Verus worker-job mode (hidden, not part of the upstream proc-macro2 API).
//!
//! A worker job is a thread-local mode in which a non-main thread inside a
//! proc-macro invocation builds and manipulates fallback tokens. Spans created
//! inside a job are identifiers into a per-thread recipe table; the main thread
//! later rebuilds ("thaws") them into real compiler spans.
//!
//! Encoding inside `fallback::Span { lo, hi }`:
//! - `{ lo: 0, hi: 0 }` is `call_site` == [`WorkerSpanId::CALL_SITE`] ==
//!   [`SpanRecipe::CallSite`];
//! - every other worker span is `{ lo: WORKER_TAG | index, hi: generation }`
//!   where `index` is the recipe-table index and `generation` is the nonzero,
//!   process-unique generation of its job. Since `lo > hi`, such a span never
//!   collides with a source-map span (which always has `lo <= hi`), so a
//!   worker span that outlives its job is recognized and rejected everywhere.
//!
//! Thread discipline: [`prepare_main_thread`] (or any other proc-macro2 use on
//! the compiler thread) must run the global backend detection before a worker
//! job starts; [`begin_job`] refuses to start on a thread where the compiler's
//! proc-macro bridge is available, or before detection has run.

use crate::fallback;
use crate::{Ident, Literal, Span};
use alloc::borrow::ToOwned as _;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::marker::PhantomData;
use core::sync::atomic::{AtomicU32, Ordering};
use std::thread_local;

pub use crate::verus_lex::{
    lex_positional, normalize_rustc_source, LexError, LexedFile, LexedKind, LexedTok,
};

/// Identifier of a span inside the current worker job.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct WorkerSpanId(u32);

impl WorkerSpanId {
    pub const CALL_SITE: WorkerSpanId = WorkerSpanId(0);

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

/// How to rebuild a worker span on the main thread. Child ids are always
/// smaller than the id of the recipe that references them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpanRecipe {
    CallSite,
    MixedSite,
    /// Main-thread span id.
    Input(u32),
    /// `span.resolved_at(at)`.
    ResolvedAt {
        span: WorkerSpanId,
        at: WorkerSpanId,
    },
    /// `span.located_at(at)`.
    LocatedAt {
        span: WorkerSpanId,
        at: WorkerSpanId,
    },
    /// `first.join(second).unwrap_or(first)`.
    JoinOrFirst {
        first: WorkerSpanId,
        second: WorkerSpanId,
    },
}

const WORKER_TAG: u32 = 1 << 31;
const MAX_GENERATION: u32 = WORKER_TAG - 1;

/// Source of process-unique job generations (wraps within `1..=MAX_GENERATION`).
static NEXT_GENERATION: AtomicU32 = AtomicU32::new(1);

fn next_generation() -> u32 {
    loop {
        let generation = NEXT_GENERATION.fetch_add(1, Ordering::Relaxed) & MAX_GENERATION;
        if generation != 0 {
            return generation;
        }
    }
}

struct JobState {
    /// Generation of the current job; 0 when no job is active.
    generation: u32,
    /// Recipe table; index 0 is always `CallSite` while a job is active.
    table: Vec<SpanRecipe>,
    /// Cached id of the job's single `MixedSite` recipe.
    mixed_site: Option<WorkerSpanId>,
    /// Nonzero nonce of the one frozen segment this job is bound to.
    nonce: Option<u64>,
}

thread_local! {
    static IN_JOB: Cell<bool> = const { Cell::new(false) };
    static STATE: RefCell<JobState> = const {
        RefCell::new(JobState {
            generation: 0,
            table: Vec::new(),
            mixed_site: None,
            nonce: None,
        })
    };
}

#[cfg(test)]
thread_local! {
    static COMPILER_THREAD_OVERRIDE_FOR_TEST: Cell<Option<bool>> = const { Cell::new(None) };
}

/// Guard for an active worker job on the current thread. Dropping it (also
/// during unwinding) ends the job.
#[must_use]
pub struct WorkerJob {
    _not_send_sync: PhantomData<*const ()>,
}

impl WorkerJob {
    pub fn end(self) {
        drop(self);
    }
}

impl Drop for WorkerJob {
    fn drop(&mut self) {
        let _ = STATE.try_with(|state| {
            if let Ok(mut state) = state.try_borrow_mut() {
                state.table = Vec::new();
                state.mixed_site = None;
                state.nonce = None;
                state.generation = 0;
            }
        });
        let _ = IN_JOB.try_with(|in_job| in_job.set(false));
    }
}

/// Whether the compiler's proc-macro bridge is connected to this thread.
fn on_compiler_thread() -> bool {
    #[cfg(test)]
    if let Some(compiler) = COMPILER_THREAD_OVERRIDE_FOR_TEST.with(Cell::get) {
        return compiler;
    }
    #[cfg(all(wrap_proc_macro, not(no_is_available)))]
    return proc_macro::is_available();
    #[cfg(not(all(wrap_proc_macro, not(no_is_available))))]
    false
}

/// Runs proc-macro2's process-wide backend detection on the current thread
/// (the compiler/main thread) and returns whether it selected the compiler
/// backend. Must be called outside a worker job, before workers start.
#[track_caller]
pub fn prepare_main_thread() -> bool {
    if in_worker_job() {
        panic!("proc_macro2::__verus_worker::prepare_main_thread called inside a worker job");
    }
    #[cfg(wrap_proc_macro)]
    return crate::detection::inside_proc_macro();
    #[cfg(not(wrap_proc_macro))]
    false
}

/// Whether the global backend detection has run (trivially true without a
/// compiler backend).
fn detection_initialized() -> bool {
    #[cfg(wrap_proc_macro)]
    return crate::detection::is_initialized();
    #[cfg(not(wrap_proc_macro))]
    true
}

/// Starts a worker job on the current thread. Panics if one is already active,
/// if this thread is connected to the compiler's proc-macro bridge, or if the
/// backend detection has not run yet (see [`prepare_main_thread`]); a worker
/// thread must never be the one that initializes the global detection.
#[track_caller]
pub fn begin_job() -> WorkerJob {
    if in_worker_job() {
        panic!(
            "proc_macro2::__verus_worker::begin_job: a worker job is already active on this thread"
        );
    }
    if on_compiler_thread() {
        panic!("proc_macro2::__verus_worker::begin_job: called on the compiler proc-macro thread");
    }
    if !detection_initialized() {
        panic!(
            "proc_macro2::__verus_worker::begin_job: backend detection has not run on the main thread"
        );
    }
    let generation = next_generation();
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        state.generation = generation;
        state.table.clear();
        state.table.push(SpanRecipe::CallSite);
        state.mixed_site = None;
        state.nonce = None;
    });
    IN_JOB.with(|in_job| in_job.set(true));
    WorkerJob {
        _not_send_sync: PhantomData,
    }
}

/// Binds the current job to the frozen segment with the given nonzero nonce.
/// Rebinding to the same nonce is a no-op; binding a different one panics.
#[track_caller]
pub fn bind_job_nonce(nonce: u64) {
    require_job("bind_job_nonce");
    assert!(
        nonce != 0,
        "proc_macro2::__verus_worker::bind_job_nonce: zero nonce"
    );
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        match state.nonce {
            None => state.nonce = Some(nonce),
            Some(bound) if bound == nonce => {}
            Some(bound) => panic!(
                "proc_macro2::__verus_worker::bind_job_nonce: job bound to segment {} cannot take segment {}",
                bound, nonce
            ),
        }
    });
}

/// Nonce bound by [`bind_job_nonce`] in the current job, if any.
#[track_caller]
pub fn job_nonce() -> Option<u64> {
    require_job("job_nonce");
    STATE.with(|state| state.borrow().nonce)
}

/// Whether a worker job is active on the current thread.
#[inline]
pub fn in_worker_job() -> bool {
    IN_JOB.with(Cell::get)
}

#[track_caller]
pub(crate) fn require_job(what: &str) {
    if !in_worker_job() {
        panic!(
            "proc_macro2::__verus_worker::{} called outside a worker job",
            what
        );
    }
}

#[track_caller]
pub(crate) fn fallback_span(span: Span, what: &str) -> fallback::Span {
    #[cfg(wrap_proc_macro)]
    match span.inner {
        crate::imp::Span::Fallback(span) => span,
        crate::imp::Span::Compiler(_) => panic!(
            "proc_macro2::__verus_worker::{}: compiler span inside a worker job",
            what
        ),
    }
    #[cfg(not(wrap_proc_macro))]
    {
        let _ = what;
        span.inner
    }
}

fn record(recipe: SpanRecipe) -> fallback::Span {
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let index = state.table.len();
        assert!(
            index < WORKER_TAG as usize,
            "proc_macro2::__verus_worker: too many spans in one worker job"
        );
        state.table.push(recipe);
        fallback::Span {
            lo: WORKER_TAG | index as u32,
            hi: state.generation,
        }
    })
}

/// Whether `span` carries the worker-span tag (`lo > hi` with the tag bit).
#[inline]
fn is_tagged(span: fallback::Span) -> bool {
    span.lo & WORKER_TAG != 0 && span.lo > span.hi
}

/// Id of a fallback span inside the current job; panics on stale or
/// non-worker spans.
#[track_caller]
pub(crate) fn fallback_span_id(span: fallback::Span) -> WorkerSpanId {
    if span.lo == 0 && span.hi == 0 {
        return WorkerSpanId::CALL_SITE;
    }
    if !is_tagged(span) || span.hi == 0 {
        panic!(
            "proc_macro2::__verus_worker: span {:?} is not a worker-job span",
            span
        );
    }
    let index = span.lo & !WORKER_TAG;
    let valid = STATE.with(|state| {
        let state = state.borrow();
        state.generation != 0
            && span.hi == state.generation
            && index != 0
            && (index as usize) < state.table.len()
    });
    if !valid {
        panic!(
            "proc_macro2::__verus_worker: span {:?} belongs to another (ended) worker job",
            span
        );
    }
    WorkerSpanId(index)
}

/// Guard of every fallback location/derivation operation: inside a job the
/// span must belong to the current job; outside a job no worker span is valid.
#[inline]
#[track_caller]
pub(crate) fn check_span(span: fallback::Span, in_job: bool) {
    if in_job {
        let _ = fallback_span_id(span);
    } else if is_tagged(span) {
        stale_outside_job(span);
    }
}

#[cold]
#[track_caller]
fn stale_outside_job(span: fallback::Span) -> ! {
    panic!(
        "proc_macro2::__verus_worker: worker-job span {:?} used outside its worker job",
        span
    )
}

/// Panics for an operation whose result cannot be expressed by a worker-job
/// span recipe; the caller's job then fails and is rerun serially.
#[cold]
#[track_caller]
pub(crate) fn unsupported_in_job(what: &str) -> ! {
    panic!(
        "proc_macro2::__verus_worker: {} is unsupported inside a worker job",
        what
    )
}

pub(crate) fn job_mixed_site() -> fallback::Span {
    let cached = STATE.with(|state| state.borrow().mixed_site);
    let id = match cached {
        Some(id) => id,
        None => {
            let id = WorkerSpanId(record(SpanRecipe::MixedSite).lo & !WORKER_TAG);
            STATE.with(|state| state.borrow_mut().mixed_site = Some(id));
            id
        }
    };
    id_to_span(id)
}

#[track_caller]
pub(crate) fn job_resolved_at(span: fallback::Span, at: fallback::Span) -> fallback::Span {
    let (span, at) = (fallback_span_id(span), fallback_span_id(at));
    record(SpanRecipe::ResolvedAt { span, at })
}

#[track_caller]
pub(crate) fn job_located_at(span: fallback::Span, at: fallback::Span) -> fallback::Span {
    let (span, at) = (fallback_span_id(span), fallback_span_id(at));
    record(SpanRecipe::LocatedAt { span, at })
}

#[track_caller]
pub(crate) fn job_join(first: fallback::Span, second: fallback::Span) -> fallback::Span {
    let (first, second) = (fallback_span_id(first), fallback_span_id(second));
    record(SpanRecipe::JoinOrFirst { first, second })
}

fn id_to_span(id: WorkerSpanId) -> fallback::Span {
    if id == WorkerSpanId::CALL_SITE {
        return fallback::Span::call_site();
    }
    let generation = STATE.with(|state| state.borrow().generation);
    fallback::Span {
        lo: WORKER_TAG | id.0,
        hi: generation,
    }
}

/// Span standing for the main-thread span with the given id.
#[track_caller]
pub fn input_span(id: u32) -> Span {
    require_job("input_span");
    Span::_new_fallback(record(SpanRecipe::Input(id)))
}

/// Id of a span of the current job.
#[track_caller]
pub fn span_id(span: Span) -> WorkerSpanId {
    require_job("span_id");
    fallback_span_id(fallback_span(span, "span_id"))
}

/// Recipe of a span id of the current job.
#[track_caller]
pub fn span_recipe(id: WorkerSpanId) -> SpanRecipe {
    require_job("span_recipe");
    match STATE.with(|state| state.borrow().table.get(id.0 as usize).copied()) {
        Some(recipe) => recipe,
        None => panic!(
            "proc_macro2::__verus_worker::span_recipe: unknown span id {}",
            id.0
        ),
    }
}

/// Builds an identifier without validating `sym`.
#[track_caller]
pub fn ident_unchecked(sym: &str, raw: bool, span: Span) -> Ident {
    require_job("ident_unchecked");
    let span = fallback_span(span, "ident_unchecked");
    Ident::_new_fallback(if raw {
        fallback::Ident::new_raw_unchecked(sym, span)
    } else {
        fallback::Ident::new_unchecked(sym, span)
    })
}

/// Symbol text (without `r#`) and rawness of a fallback identifier.
#[track_caller]
pub fn ident_sym_raw(ident: &Ident) -> (&str, bool) {
    require_job("ident_sym_raw");
    #[cfg(wrap_proc_macro)]
    let ident = match &ident.inner {
        crate::imp::Ident::Fallback(ident) => ident,
        crate::imp::Ident::Compiler(_) => {
            panic!("proc_macro2::__verus_worker::ident_sym_raw: compiler ident")
        }
    };
    #[cfg(not(wrap_proc_macro))]
    let ident = &ident.inner;
    ident.sym_raw()
}

/// Builds a literal from its source representation without lexing it.
#[track_caller]
pub fn literal_from_repr(repr: &str, span: Span) -> Literal {
    require_job("literal_from_repr");
    let mut literal = fallback::Literal::_new(repr.to_owned());
    literal.set_span(fallback_span(span, "literal_from_repr"));
    Literal::_new_fallback(literal)
}

/// Source representation of a fallback literal.
#[track_caller]
pub fn literal_repr(literal: &Literal) -> &str {
    require_job("literal_repr");
    #[cfg(wrap_proc_macro)]
    let literal = match &literal.inner {
        crate::imp::Literal::Fallback(literal) => literal,
        crate::imp::Literal::Compiler(_) => {
            panic!("proc_macro2::__verus_worker::literal_repr: compiler literal")
        }
    };
    #[cfg(not(wrap_proc_macro))]
    let literal = &literal.inner;
    &literal.repr
}

/// Releases `group` without the compiler bridge's drop request. A compiler
/// group's only resource is its stream handle in the bridge server's handle
/// store, which is created per macro expansion and frees every remaining
/// handle when that expansion returns; so the leak is bounded by the groups
/// released during one expansion. Fallback groups are dropped normally.
pub fn release_group(group: crate::Group) {
    #[cfg(wrap_proc_macro)]
    if let crate::imp::Group::Compiler(_) = &group.inner {
        core::mem::forget(group);
        return;
    }
    drop(group);
}

/// Whether `a` and `b` are compiler spans whose interned `a.end()` and
/// `b.start()` spans are equal (the same source position and context). `false`
/// when this cannot be decided cheaply (fallback spans, no span equality).
pub fn compiler_end_eq_start(a: Span, b: Span) -> bool {
    #[cfg(all(wrap_proc_macro, proc_macro_span))]
    if let (crate::imp::Span::Compiler(a), crate::imp::Span::Compiler(b)) = (a.inner, b.inner) {
        return a.end().eq(&b.start());
    }
    let _ = (a, b);
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Delimiter, Group, LineColumn, TokenStream, TokenTree};
    use alloc::string::ToString as _;
    use core::str::FromStr;
    use std::panic;

    /// Starts a job after running detection on this (test) thread, as the
    /// compiler thread does before workers start.
    #[track_caller]
    fn test_job() -> WorkerJob {
        let _ = prepare_main_thread();
        begin_job()
    }

    fn assert_all_call_site(stream: TokenStream) {
        for tt in stream {
            assert_eq!(span_id(tt.span()), WorkerSpanId::CALL_SITE);
            if let TokenTree::Group(group) = tt {
                assert_eq!(span_id(group.span_open()), WorkerSpanId::CALL_SITE);
                assert_all_call_site(group.stream());
            }
        }
    }

    #[test]
    fn begin_end_cleanup() {
        assert!(!in_worker_job());
        let job = test_job();
        assert!(in_worker_job());
        let span = input_span(7);
        let id = span_id(span);
        assert_eq!(id.as_u32(), 1);
        job.end();
        assert!(!in_worker_job());
        STATE.with(|state| assert!(state.borrow().table.is_empty()));

        let job = test_job();
        drop(job);
        assert!(!in_worker_job());

        let result = panic::catch_unwind(|| {
            let _job = test_job();
            let _ = input_span(1);
            panic!("boom");
        });
        assert!(result.is_err());
        assert!(!in_worker_job());
        STATE.with(|state| assert!(state.borrow().table.is_empty()));
    }

    #[test]
    #[should_panic(expected = "another (ended) worker job")]
    fn new_job_rejects_old_spans() {
        let job = test_job();
        let old = input_span(3);
        job.end();
        let _job = test_job();
        let _ = input_span(4);
        let _ = span_id(old);
    }

    #[test]
    #[should_panic(expected = "already active")]
    fn nested_begin_panics() {
        let _job = test_job();
        let _job2 = begin_job();
    }

    #[test]
    #[should_panic(expected = "outside a worker job")]
    fn accessor_outside_job_panics() {
        let _ = span_id(Span::call_site());
    }

    #[test]
    fn call_site_and_input() {
        let _job = test_job();
        assert_eq!(span_id(Span::call_site()), WorkerSpanId::CALL_SITE);
        assert_eq!(WorkerSpanId::CALL_SITE.as_u32(), 0);
        assert_eq!(span_recipe(WorkerSpanId::CALL_SITE), SpanRecipe::CallSite);
        let a = span_id(input_span(10));
        let b = span_id(input_span(20));
        assert_ne!(a, b);
        assert_eq!(span_recipe(a), SpanRecipe::Input(10));
        assert_eq!(span_recipe(b), SpanRecipe::Input(20));
    }

    #[test]
    fn recipes_recorded() {
        let _job = test_job();
        let a = input_span(1);
        let b = input_span(2);
        let (ia, ib) = (span_id(a), span_id(b));

        let m = Span::mixed_site();
        let im = span_id(m);
        assert_eq!(span_recipe(im), SpanRecipe::MixedSite);
        assert_eq!(span_id(Span::mixed_site()), im);

        let r = a.resolved_at(b);
        let ir = span_id(r);
        assert_eq!(span_recipe(ir), SpanRecipe::ResolvedAt { span: ia, at: ib });
        let l = a.located_at(m);
        let il = span_id(l);
        assert_eq!(span_recipe(il), SpanRecipe::LocatedAt { span: ia, at: im });
        let j = r.join(Span::call_site()).unwrap();
        let ij = span_id(j);
        assert_eq!(
            span_recipe(ij),
            SpanRecipe::JoinOrFirst {
                first: ir,
                second: WorkerSpanId::CALL_SITE,
            }
        );
        assert!(ia.as_u32() < ir.as_u32() && ib.as_u32() < ir.as_u32());
        assert!(im.as_u32() < il.as_u32() && ir.as_u32() < ij.as_u32());

        // Worker spans have no source location; querying one aborts the job.
        assert!(panics(|| a.byte_range()));
        assert!(panics(|| a.start()));
        assert!(panics(|| a.end()));
        assert!(panics(|| a.file()));
        assert!(panics(|| a.local_file()));
        assert!(panics(|| a.source_text()));
        assert!(panics(|| Span::call_site().byte_range()));
    }

    #[test]
    fn group_open_close_whole_span() {
        let _job = test_job();
        let span = input_span(5);
        let mut group = Group::new(Delimiter::Brace, TokenStream::new());
        group.set_span(span);
        let id = span_id(span);
        assert_eq!(span_id(group.span()), id);
        assert_eq!(span_id(group.span_open()), id);
        assert_eq!(span_id(group.span_close()), id);
        let delim = group.delim_span();
        assert_eq!(span_id(delim.join()), id);
        assert_eq!(span_id(delim.open()), id);
        assert_eq!(span_id(delim.close()), id);
    }

    #[cfg(not(fuzzing))]
    #[test]
    fn from_str_call_site_without_source_map() {
        let before = fallback::source_map_file_count();
        let _job = test_job();
        let stream = TokenStream::from_str("fn f(x: [u8; 2]) { /// doc\n x + -1i32 }").unwrap();
        assert_all_call_site(stream);
        let lit = Literal::from_str("-12u8").unwrap();
        assert_eq!(span_id(lit.span()), WorkerSpanId::CALL_SITE);
        assert_eq!(literal_repr(&lit), "-12u8");
        let err = TokenStream::from_str("a ( b").unwrap_err();
        assert_eq!(span_id(err.span()), WorkerSpanId::CALL_SITE);
        let err = TokenStream::from_str("a ) b").unwrap_err();
        assert_eq!(span_id(err.span()), WorkerSpanId::CALL_SITE);
        assert_eq!(fallback::source_map_file_count(), before);
        drop(_job);

        // Outside a job, from_str still registers a file with real spans.
        let stream = TokenStream::from_str("a").unwrap();
        assert_eq!(fallback::source_map_file_count(), before + 1);
        let span = stream.into_iter().next().unwrap().span();
        assert_eq!(span.end(), LineColumn { line: 1, column: 1 });
    }

    #[cfg(wrap_proc_macro)]
    #[test]
    fn detection_not_flipped() {
        let _ = prepare_main_thread();
        std::thread::spawn(|| {
            let calls = &crate::detection::INITIALIZE_CALLS_FOR_TEST;
            let before = crate::detection::works_for_test();
            let job = begin_job();
            assert!(!crate::detection::inside_proc_macro());
            let _ = Span::call_site();
            let _ = Span::mixed_site();
            let _ = Literal::i32_suffixed(1);
            let _ = TokenStream::from_str("a b").unwrap();
            assert!(!crate::detection::inside_proc_macro());
            job.end();
            // Detection ran on the spawning thread; the worker never ran it.
            assert_ne!(before, 0);
            assert_eq!(calls.with(Cell::get), 0);
            assert_eq!(crate::detection::works_for_test(), before);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn ident_literal_accessors() {
        let _job = test_job();
        let span = input_span(9);
        let id = ident_unchecked("foo", false, span);
        assert_eq!(ident_sym_raw(&id), ("foo", false));
        assert_eq!(span_id(id.span()), span_id(span));
        let raw = ident_unchecked("type", true, Span::call_site());
        assert_eq!(ident_sym_raw(&raw), ("type", true));
        assert_eq!(raw.to_string(), "r#type");
        let parsed = match TokenStream::from_str("r#match").unwrap().into_iter().next() {
            Some(TokenTree::Ident(ident)) => ident,
            _ => panic!("expected ident"),
        };
        assert_eq!(ident_sym_raw(&parsed), ("match", true));

        let neg = Literal::i32_suffixed(-1);
        assert_eq!(literal_repr(&neg), "-1i32");
        let lit = literal_from_repr("\"a\\nb\"", span);
        assert_eq!(literal_repr(&lit), "\"a\\nb\"");
        assert_eq!(span_id(lit.span()), span_id(span));
        assert_eq!(lit.to_string(), "\"a\\nb\"");
    }

    #[test]
    fn negative_literal_stays_single_token_in_job() {
        let _job = test_job();
        let stream: TokenStream = [TokenTree::Literal(Literal::i32_suffixed(-1))]
            .into_iter()
            .collect();
        let tokens: Vec<TokenTree> = stream.into_iter().collect();
        assert_eq!(tokens.len(), 1);
        match &tokens[0] {
            TokenTree::Literal(lit) => assert_eq!(literal_repr(lit), "-1i32"),
            _ => panic!("expected a single negative literal"),
        }
        drop(_job);
        // Outside a job the upstream fallback split is unchanged.
        let stream: TokenStream = [TokenTree::Literal(Literal::i32_suffixed(-1))]
            .into_iter()
            .collect();
        assert_eq!(stream.into_iter().count(), 2);
    }

    fn panics<R>(f: impl FnOnce() -> R) -> bool {
        panic::catch_unwind(panic::AssertUnwindSafe(f)).is_err()
    }

    #[cfg(wrap_proc_macro)]
    #[test]
    fn begin_job_requires_detection_and_never_initializes_it() {
        std::thread::spawn(|| {
            let calls = &crate::detection::INITIALIZE_CALLS_FOR_TEST;
            let flag = &crate::detection::INITIALIZED_OVERRIDE_FOR_TEST;
            flag.with(|f| f.set(Some(false)));
            let result = panic::catch_unwind(|| begin_job());
            let message = *result.err().unwrap().downcast::<&str>().unwrap();
            assert!(message.contains("backend detection"), "{}", message);
            assert!(!in_worker_job());
            assert_eq!(calls.with(Cell::get), 0);
            flag.with(|f| f.set(None));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn begin_job_rejects_compiler_thread() {
        let _ = prepare_main_thread();
        COMPILER_THREAD_OVERRIDE_FOR_TEST.with(|f| f.set(Some(true)));
        let result = panic::catch_unwind(|| begin_job());
        COMPILER_THREAD_OVERRIDE_FOR_TEST.with(|f| f.set(None));
        let message = *result.err().unwrap().downcast::<&str>().unwrap();
        assert!(
            message.contains("compiler proc-macro thread"),
            "{}",
            message
        );
        assert!(!in_worker_job());
        // Outside the compiler, a test thread is not a compiler thread.
        assert!(!on_compiler_thread());
    }

    #[test]
    fn prepare_main_thread_rejected_in_job() {
        let _job = test_job();
        assert!(panics(prepare_main_thread));
    }

    fn location_ops_panic(span: Span) -> Vec<&'static str> {
        let mut ok = Vec::new();
        let other = Span::call_site();
        let checks: [(&'static str, &dyn Fn()); 12] = [
            ("byte_range", &|| {
                let _ = span.byte_range();
            }),
            ("start", &|| {
                let _ = span.start();
            }),
            ("end", &|| {
                let _ = span.end();
            }),
            ("file", &|| {
                let _ = span.file();
            }),
            ("local_file", &|| {
                let _ = span.local_file();
            }),
            ("source_text", &|| {
                let _ = span.source_text();
            }),
            ("join", &|| {
                let _ = span.join(other);
            }),
            ("join_rhs", &|| {
                let _ = other.join(span);
            }),
            ("resolved_at", &|| {
                let _ = span.resolved_at(other);
            }),
            ("located_at", &|| {
                let _ = other.located_at(span);
            }),
            ("span_open", &|| {
                let mut group = Group::new(Delimiter::Brace, TokenStream::new());
                group.set_span(span);
                let _ = group.span_open();
            }),
            ("span_close", &|| {
                let mut group = Group::new(Delimiter::Brace, TokenStream::new());
                group.set_span(span);
                let _ = group.span_close();
            }),
        ];
        for (name, check) in checks {
            if !panics(check) {
                ok.push(name);
            }
        }
        ok
    }

    #[test]
    fn stale_worker_span_rejected_by_location_ops() {
        let job = test_job();
        let stale = input_span(3).located_at(Span::mixed_site());
        // Inside its own job, derivation ops are defined and location queries are rejected.
        assert_eq!(
            location_ops_panic(stale),
            [
                "join",
                "join_rhs",
                "resolved_at",
                "located_at",
                "span_open",
                "span_close"
            ]
        );
        job.end();
        // Outside any job.
        assert!(
            location_ops_panic(stale).is_empty(),
            "{:?}",
            location_ops_panic(stale)
        );
        // Inside a later job.
        let _job = test_job();
        let _ = input_span(3).located_at(Span::mixed_site());
        assert!(
            location_ops_panic(stale).is_empty(),
            "{:?}",
            location_ops_panic(stale)
        );
        assert!(panics(|| span_id(stale)));
        drop(_job);
        // Ordinary source-map spans are unaffected outside jobs.
        let parsed = TokenStream::from_str("a")
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
            .span();
        assert_eq!(location_ops_panic(parsed).len(), 12);
    }

    #[test]
    fn source_map_span_rejected_inside_job() {
        let parsed = TokenStream::from_str("a")
            .unwrap()
            .into_iter()
            .next()
            .unwrap()
            .span();
        let _job = test_job();
        assert!(location_ops_panic(parsed).is_empty());
        assert!(panics(|| span_id(parsed)));
    }

    #[test]
    fn generations_are_unique_across_threads() {
        let _ = prepare_main_thread();
        let raw = std::thread::spawn(|| {
            let _job = begin_job();
            let span = fallback_span(input_span(1), "test");
            (span.lo, span.hi)
        })
        .join()
        .unwrap();
        std::thread::spawn(move || {
            let _job = begin_job();
            let _ = input_span(1);
            let foreign = fallback::Span {
                lo: raw.0,
                hi: raw.1,
            };
            assert!(panics(|| fallback_span_id(foreign)));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn literal_subspan_rejected_in_job_then_later_job_healthy() {
        let job = test_job();
        let lit = literal_from_repr("0.1", input_span(4));
        let result = panic::catch_unwind(panic::AssertUnwindSafe(|| lit.subspan(0..1)));
        let message = result.err().unwrap();
        let message = message.downcast_ref::<std::string::String>().unwrap();
        assert!(
            message.contains("Literal::subspan is unsupported"),
            "{}",
            message
        );
        // A call-site literal is rejected too: no coordinates exist in a job.
        let call_site = Literal::f64_unsuffixed(0.5);
        assert!(panics(|| call_site.subspan(1..2)));
        assert!(in_worker_job());
        drop(job);
        assert!(!in_worker_job());

        // The stale worker span is rejected outside its job, not truncated.
        assert!(panics(|| lit.subspan(0..1)));

        // A later job is healthy.
        let _job = test_job();
        let span = input_span(11);
        assert_eq!(span_id(span).as_u32(), 1);
        assert_eq!(span_recipe(span_id(span)), SpanRecipe::Input(11));
        let joined = span.join(Span::call_site()).unwrap();
        assert_eq!(
            span_recipe(span_id(joined)),
            SpanRecipe::JoinOrFirst {
                first: span_id(span),
                second: WorkerSpanId::CALL_SITE,
            }
        );
        drop(_job);

        // Outside jobs, source-map literal subspans behave as upstream.
        let parsed = match TokenStream::from_str("12.5").unwrap().into_iter().next() {
            Some(TokenTree::Literal(lit)) => lit,
            _ => panic!("expected literal"),
        };
        let whole = parsed.span().byte_range();
        let sub = parsed.subspan(1..3).unwrap();
        assert_eq!(sub.byte_range(), whole.start + 1..whole.start + 3);
        assert!(parsed.subspan(1..9).is_none());
    }

    #[cfg(procmacro2_semver_exempt)]
    #[test]
    fn def_site_and_eq_rejected_in_job() {
        let job = test_job();
        assert!(panics(Span::def_site));
        let span = input_span(1);
        assert!(panics(|| span.eq(&span)));
        assert!(in_worker_job());
        drop(job);
        let _ = Span::def_site();
        assert!(Span::call_site().eq(&Span::call_site()));
    }

    #[test]
    fn job_nonce_binding() {
        assert!(panics(|| bind_job_nonce(1)));
        assert!(panics(job_nonce));
        let job = test_job();
        assert_eq!(job_nonce(), None);
        assert!(panics(|| bind_job_nonce(0)));
        bind_job_nonce(7);
        bind_job_nonce(7);
        assert_eq!(job_nonce(), Some(7));
        assert!(panics(|| bind_job_nonce(8)));
        assert_eq!(job_nonce(), Some(7));
        job.end();
        let _job = test_job();
        assert_eq!(job_nonce(), None);
    }

    #[test]
    fn release_group_and_end_eq_start_on_fallback_tokens() {
        // Fallback groups are dropped normally (their shared stream stays valid).
        let inner = TokenStream::from_str("a b").unwrap();
        let group = Group::new(Delimiter::Parenthesis, inner.clone());
        let copy = group.clone();
        release_group(group);
        assert_eq!(copy.stream().to_string(), inner.to_string());
        // Without compiler spans the fast path never claims equality.
        let toks: Vec<TokenTree> = TokenStream::from_str("a=b").unwrap().into_iter().collect();
        assert!(!compiler_end_eq_start(toks[0].span(), toks[1].span()));
        assert!(!compiler_end_eq_start(Span::call_site(), Span::call_site()));
    }
}
