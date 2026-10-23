pub(crate) fn vec_map<A, B, F: Fn(&A) -> B>(v: &Vec<A>, f: F) -> Vec<B> {
    v.iter().map(f).collect::<Vec<B>>()
}

pub(crate) fn vec_map_result<A, B, C, F>(v: &Vec<A>, f: F) -> Result<Vec<B>, C>
where
    F: FnMut(&A) -> Result<B, C>,
{
    v.iter().map(f).collect::<Result<Vec<B>, C>>()
}

// Bounds contention in the shared type and path caches.
const MAX_PARALLEL_VIR_THREADS: usize = 16;
// VIR visitors recurse deeply, so workers need at least the rustc stack size.
const VIR_WORKER_STACK_SIZE: usize = 64 * 1024 * 1024;
static PAR_NUM_THREADS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// Sets the worker count for parallel VIR passes.
pub fn set_par_num_threads(n: usize) {
    PAR_NUM_THREADS
        .store(n.clamp(1, MAX_PARALLEL_VIR_THREADS), std::sync::atomic::Ordering::Relaxed);
}

fn par_num_threads() -> usize {
    let configured = PAR_NUM_THREADS.load(std::sync::atomic::Ordering::Relaxed);
    if configured > 0 {
        configured
    } else {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
            .min(MAX_PARALLEL_VIR_THREADS)
    }
}

fn par_stack_size() -> usize {
    let min_stack = std::env::var("RUST_MIN_STACK").ok().and_then(|s| s.parse::<usize>().ok());
    min_stack.unwrap_or(0).max(VIR_WORKER_STACK_SIZE)
}

#[cfg(test)]
thread_local! {
    // Number of VIR worker spawns that succeed on this thread before spawning fails (tests only).
    static TEST_SPAWN_LIMIT: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}

/// Spawns the `k`-th VIR worker thread of a parallel pass.
fn spawn_vir_worker<'scope, 'env, O, W>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    k: usize,
    worker: W,
) -> std::io::Result<std::thread::ScopedJoinHandle<'scope, O>>
where
    O: Send + 'scope,
    W: FnOnce() -> O + Send + 'scope,
{
    #[cfg(test)]
    if TEST_SPAWN_LIMIT.with(|l| l.get()).is_some_and(|limit| k >= limit) {
        return Err(std::io::Error::other("injected VIR worker spawn failure"));
    }
    #[cfg(not(test))]
    let _ = k;
    std::thread::Builder::new()
        .name("verus-vir-worker".to_string())
        .stack_size(par_stack_size())
        .spawn_scoped(scope, worker)
}

/// Runs `worker` on up to `n_threads` scoped threads and returns the outcome of every run.
///
/// If a thread cannot be spawned, no further threads are spawned and the calling thread runs
/// `worker` once itself, so the pass degrades to sequential execution when no thread can be
/// spawned. Every run must take items from one shared queue until it is empty.
fn par_run_workers<O, W>(n_threads: usize, worker: W) -> Vec<std::thread::Result<O>>
where
    O: Send,
    W: Fn() -> O + Sync,
{
    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(n_threads);
        let mut spawn_failed = false;
        for k in 0..n_threads {
            match spawn_vir_worker(scope, k, &worker) {
                Ok(handle) => handles.push(handle),
                Err(_) => {
                    spawn_failed = true;
                    break;
                }
            }
        }
        let mut outcomes = Vec::with_capacity(handles.len() + 1);
        if spawn_failed {
            outcomes.push(std::panic::catch_unwind(std::panic::AssertUnwindSafe(&worker)));
        }
        outcomes.extend(handles.into_iter().map(|handle| handle.join()));
        outcomes
    })
}

/// Applies `f` in parallel with worker-local state and returns results in input order.
///
/// Calls to `f` must not depend on state retained from an earlier item. Worker panics are
/// propagated after all workers stop. If worker threads cannot be spawned, the remaining items
/// run on the calling thread.
pub fn par_map_init<T, S, R, I, F>(items: &[T], init: I, f: F) -> Vec<R>
where
    T: Sync,
    R: Send,
    I: Fn() -> S + Sync,
    F: Fn(&mut S, &T) -> R + Sync,
{
    let n_threads = par_num_threads().min(items.len());
    if n_threads <= 1 {
        let mut state = init();
        return items.iter().map(|item| f(&mut state, item)).collect();
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let worker = || {
        let mut state = init();
        let mut out: Vec<(usize, R)> = Vec::new();
        loop {
            let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if i >= items.len() {
                break;
            }
            out.push((i, f(&mut state, &items[i])));
        }
        out
    };
    let mut results: Vec<Option<R>> = Vec::new();
    results.resize_with(items.len(), || None);
    let mut panic = None;
    for outcome in par_run_workers(n_threads, worker) {
        match outcome {
            Ok(out) => {
                for (i, r) in out {
                    results[i] = Some(r);
                }
            }
            Err(e) => {
                if panic.is_none() {
                    panic = Some(e);
                }
            }
        }
    }
    if let Some(e) = panic {
        std::panic::resume_unwind(e);
    }
    results.into_iter().map(|r| r.expect("par_map_init result")).collect()
}

thread_local! {
    static PAR_CANCEL: std::cell::RefCell<Option<std::sync::Arc<std::sync::atomic::AtomicBool>>> =
        const { std::cell::RefCell::new(None) };
}

/// Runs `f` with `cancel` as this thread's cancellation flag for par_map_init_until_err.
///
/// Once `cancel` is set, par_map_init_until_err calls made by `f` on this thread stop claiming
/// items, so their results may lack any item; callers then return par_cancelled_err. Set it only
/// when the caller will discard every result `f` produces.
pub fn with_par_cancel<R>(
    cancel: &std::sync::Arc<std::sync::atomic::AtomicBool>,
    f: impl FnOnce() -> R,
) -> R {
    struct Restore(Option<std::sync::Arc<std::sync::atomic::AtomicBool>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            PAR_CANCEL.with(|c| *c.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(PAR_CANCEL.with(|c| c.replace(Some(cancel.clone()))));
    f()
}

/// The error returned by a pass whose par_map_init_until_err results were cut short by a
/// with_par_cancel flag. The caller discards it.
pub(crate) fn par_cancelled_err() -> crate::ast::VirErr {
    crate::messages::error_bare("verus internal: VIR pass cancelled")
}

/// Like par_map_init, but skips items that a sequential in-order consumer stopping at the first
/// failure would never read.
///
/// `failed(r)` marks a result at which that consumer stops; a panic in `f` also counts as a
/// failure. Every item up to and including the first failure in input order is computed, so
/// `result[i]` is Some for every `i` up to that failure (or for every `i` if no item fails);
/// later entries may be None. If this thread's with_par_cancel flag is set, any entry may be
/// None.
///
/// A panic in `f` is re-raised only if its item is the first failure, which is where the
/// sequential consumer would have panicked. A panic in an item after an earlier failing result
/// is dropped, since that consumer never reaches it; its message may still have been printed
/// by the panic hook. Panics in `init` or `failed` are always re-raised. If worker threads
/// cannot be spawned, the remaining items run on the calling thread.
pub(crate) fn par_map_init_until_err<T, S, R, I, F, P>(
    items: &[T],
    init: I,
    f: F,
    failed: P,
) -> Vec<Option<R>>
where
    T: Sync,
    R: Send,
    I: Fn() -> S + Sync,
    F: Fn(&mut S, &T) -> R + Sync,
    P: Fn(&R) -> bool + Sync,
{
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    let cancel = PAR_CANCEL.with(|c| c.borrow().clone());
    let not_cancelled = AtomicBool::new(false);
    let cancel: &AtomicBool = cancel.as_deref().unwrap_or(&not_cancelled);
    let n_threads = par_num_threads().min(items.len());
    let mut results: Vec<Option<R>> = Vec::new();
    results.resize_with(items.len(), || None);
    if n_threads <= 1 {
        // This run stops at its first failure, so a panic in `f` is always the first failure.
        let mut state = init();
        for (i, slot) in results.iter_mut().enumerate() {
            if cancel.load(Ordering::Relaxed) {
                break;
            }
            let r = f(&mut state, &items[i]);
            let stop = failed(&r);
            *slot = Some(r);
            if stop {
                break;
            }
        }
        return results;
    }
    // Lowest index of an item known to fail. It only holds indices of computed failing items,
    // so an item is skipped only when an earlier item fails.
    let first_failure = AtomicUsize::new(usize::MAX);
    let next = AtomicUsize::new(0);
    let worker = || {
        let mut state = init();
        let mut out: Vec<(usize, R)> = Vec::new();
        loop {
            let i = next.fetch_add(1, Ordering::Relaxed);
            // Claims are increasing, so once one is skipped every later claim is too.
            if i >= items.len() || i > first_failure.load(Ordering::Relaxed) {
                break;
            }
            if cancel.load(Ordering::Relaxed) {
                break;
            }
            let state = &mut state;
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(state, &items[i]))) {
                Ok(r) => {
                    if failed(&r) {
                        first_failure.fetch_min(i, Ordering::Relaxed);
                    }
                    out.push((i, r));
                }
                Err(e) => {
                    // The worker state may be inconsistent after a panic, so this worker stops.
                    first_failure.fetch_min(i, Ordering::Relaxed);
                    return (out, Some((i, e)));
                }
            }
        }
        (out, None)
    };
    let mut item_panic: Option<(usize, Box<dyn std::any::Any + Send>)> = None;
    let mut worker_panic = None;
    for outcome in par_run_workers(n_threads, worker) {
        match outcome {
            Ok((out, panic)) => {
                for (i, r) in out {
                    results[i] = Some(r);
                }
                if let Some((i, e)) = panic {
                    if item_panic.as_ref().is_none_or(|(j, _)| i < *j) {
                        item_panic = Some((i, e));
                    }
                }
            }
            Err(e) => {
                if worker_panic.is_none() {
                    worker_panic = Some(e);
                }
            }
        }
    }
    if let Some(e) = worker_panic {
        std::panic::resume_unwind(e);
    }
    if let Some((i, e)) = item_panic {
        if i == first_failure.load(Ordering::Relaxed) {
            std::panic::resume_unwind(e);
        }
    }
    results
}

static VERUS_GITHUB_BUG_REPORT_URL: std::sync::RwLock<Option<std::sync::Arc<String>>> =
    std::sync::RwLock::new(None);

pub fn set_verus_github_bug_report_url(s: String) {
    *VERUS_GITHUB_BUG_REPORT_URL.write().unwrap() = Some(std::sync::Arc::new(s));
}

#[inline(always)]
pub fn get_verus_github_bug_report_url() -> Option<std::sync::Arc<String>> {
    VERUS_GITHUB_BUG_REPORT_URL.read().unwrap().clone()
}

pub(crate) fn err_span<A, S: Into<String>>(
    span: crate::messages::Span,
    msg: S,
) -> Result<A, crate::ast::VirErr> {
    Err(crate::messages::error(&span, msg))
}

pub fn internal_err_span<A>(
    span: crate::messages::Span,
    msg: String,
) -> Result<A, crate::ast::VirErr> {
    let mut e = err_span(span, format!("verus internal error: {}", msg));
    if let Some(verus_github_bug_report_url) = get_verus_github_bug_report_url() {
        e = e.map_err(|e| {
            e.help(format!(
                "This is a bug in the verifier. Please report it at {}.",
                verus_github_bug_report_url
            ))
        });
    }
    e
}

#[macro_export]
macro_rules! internal_err {
    ($span: expr, $msg: expr) => {{
        $crate::util::internal_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
    ($span: expr, $msg: expr, $info: expr) => {{
        dbg!($info);
        $crate::util::internal_err_span($span, $msg.to_string())?;
        unreachable!()
    }};
}

#[allow(unused_macros)]
macro_rules! dbg_backtrace {
    ($val: expr) => {
        match $val {
            tmp => {
                std::eprintln!(
                    "[{}:{}:{}] {} = {:#?}",
                    std::file!(),
                    std::line!(),
                    std::column!(),
                    std::stringify!($val),
                    &tmp
                );
                eprintln!(
                    "[{}:{}:{}]\n{}",
                    std::file!(),
                    std::line!(),
                    std::column!(),
                    std::backtrace::Backtrace::force_capture()
                );
                tmp
            }
        }
    };
}

#[allow(unused_imports)]
pub(crate) use dbg_backtrace;

#[allow(unused_macros)]
macro_rules! backtrace {
    () => {
        eprintln!(
            "[{}:{}:{}]\n{}",
            std::file!(),
            std::line!(),
            std::column!(),
            std::backtrace::Backtrace::force_capture()
        );
    };
}

#[allow(unused_imports)]
pub(crate) use backtrace;

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    #[test]
    fn until_err_without_failure_matches_par_map_init() {
        let items: Vec<usize> = (0..1000).collect();
        let r = par_map_init_until_err(&items, || (), |_, i| i * 2, |_| false);
        let expected: Vec<Option<usize>> = items.iter().map(|i| Some(i * 2)).collect();
        assert_eq!(r, expected);
        let plain: Vec<Option<usize>> =
            par_map_init(&items, || (), |_, i| i * 2).into_iter().map(Some).collect();
        assert_eq!(plain, expected);
    }

    #[test]
    fn until_err_computes_every_item_up_to_first_failure() {
        let items: Vec<usize> = (0..4096).collect();
        for first in [0, 1, 17, 2000, 4095] {
            let calls = AtomicUsize::new(0);
            let r = par_map_init_until_err(
                &items,
                || (),
                |_, &i| {
                    calls.fetch_add(1, Ordering::Relaxed);
                    if i != first {
                        std::thread::sleep(std::time::Duration::from_micros(20));
                    }
                    if i >= first && i % 3 == first % 3 { Err(i) } else { Ok(i) }
                },
                |r| r.is_err(),
            );
            for (i, r) in r.iter().enumerate().take(first + 1) {
                let expected = if i == first { Err(i) } else { Ok(i) };
                assert_eq!(*r, Some(expected));
            }
            if first == 0 {
                assert!(calls.load(Ordering::Relaxed) < items.len());
            }
        }
    }

    #[test]
    fn until_err_propagates_panic_and_skips_later_items() {
        let items: Vec<usize> = (0..4096).collect();
        let calls = AtomicUsize::new(0);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            par_map_init_until_err(
                &items,
                || (),
                |_, &i| {
                    calls.fetch_add(1, Ordering::Relaxed);
                    if i == 0 {
                        panic!("item 0");
                    }
                    std::thread::sleep(std::time::Duration::from_micros(20));
                    i
                },
                |_| false,
            )
        }));
        assert!(result.is_err());
        assert!(calls.load(Ordering::Relaxed) < items.len());
    }

    #[test]
    fn until_err_observes_cancel_and_restores_previous_flag() {
        let items: Vec<usize> = (0..100).collect();
        let cancel = Arc::new(AtomicBool::new(true));
        let r = with_par_cancel(&cancel, || {
            par_map_init_until_err(&items, || (), |_, i| *i, |_| false)
        });
        assert!(r.iter().all(Option::is_none));
        assert!(PAR_CANCEL.with(|c| c.borrow().is_none()));
        let r = par_map_init_until_err(&items, || (), |_, i| *i, |_| false);
        assert!(r.iter().all(Option::is_some));
    }

    // Waits until `flag` is set, giving up after a few seconds so a single-core run cannot hang.
    fn wait_for(flag: &AtomicBool) {
        let start = std::time::Instant::now();
        while !flag.load(Ordering::SeqCst) && start.elapsed() < std::time::Duration::from_secs(5) {
            std::thread::yield_now();
        }
    }

    #[test]
    fn until_err_drops_panic_after_earlier_failure() {
        // Item 0 fails only after item 3 has started panicking, so the panic is above the failure.
        let items: Vec<usize> = (0..64).collect();
        let panicking = AtomicBool::new(false);
        let r = par_map_init_until_err(
            &items,
            || (),
            |_, &i| match i {
                0 => {
                    wait_for(&panicking);
                    Err(0)
                }
                3 => {
                    panicking.store(true, Ordering::SeqCst);
                    panic!("item 3 after an earlier failure");
                }
                _ => Ok(i),
            },
            |r: &Result<usize, usize>| r.is_err(),
        );
        assert_eq!(r[0], Some(Err(0)));
    }

    #[test]
    fn until_err_propagates_panic_before_later_failure() {
        // Item 0 panics only after item 3 has failed, so the panic is the first failure.
        let items: Vec<usize> = (0..64).collect();
        let failed = AtomicBool::new(false);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            par_map_init_until_err(
                &items,
                || (),
                |_, &i| match i {
                    0 => {
                        wait_for(&failed);
                        panic!("item 0 before a later failure");
                    }
                    3 => {
                        failed.store(true, Ordering::SeqCst);
                        Err(3)
                    }
                    _ => Ok(i),
                },
                |r: &Result<usize, usize>| r.is_err(),
            )
        }));
        assert!(result.is_err());
    }

    fn with_spawn_limit<R>(limit: usize, f: impl FnOnce() -> R) -> R {
        TEST_SPAWN_LIMIT.with(|l| l.set(Some(limit)));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
        TEST_SPAWN_LIMIT.with(|l| l.set(None));
        r.unwrap_or_else(|e| std::panic::resume_unwind(e))
    }

    #[test]
    fn spawn_failure_falls_back_to_calling_thread() {
        let items: Vec<usize> = (0..1000).collect();
        let expected: Vec<usize> = items.iter().map(|i| i * 2).collect();
        let caller = std::thread::current().id();
        for limit in [0, 1, 2] {
            let on_caller = AtomicUsize::new(0);
            let r = with_spawn_limit(limit, || {
                par_map_init(
                    &items,
                    || (),
                    |_, i| {
                        if std::thread::current().id() == caller {
                            on_caller.fetch_add(1, Ordering::Relaxed);
                        }
                        i * 2
                    },
                )
            });
            assert_eq!(r, expected);
            if limit == 0 {
                assert_eq!(on_caller.load(Ordering::Relaxed), items.len());
            }
            let r = with_spawn_limit(limit, || {
                par_map_init_until_err(&items, || (), |_, i| i * 2, |_| false)
            });
            assert_eq!(r, expected.iter().map(|i| Some(*i)).collect::<Vec<_>>());
            let r = with_spawn_limit(limit, || {
                par_map_init_until_err(
                    &items,
                    || (),
                    |_, &i| if i == 500 { Err(i) } else { Ok(i) },
                    |r| r.is_err(),
                )
            });
            for (i, r) in r.iter().enumerate().take(501) {
                assert_eq!(*r, Some(if i == 500 { Err(i) } else { Ok(i) }));
            }
        }
    }
}
