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

/// Applies `f` in parallel with worker-local state and returns results in input order.
///
/// Calls to `f` must not depend on state retained from an earlier item. Worker panics are
/// propagated after all workers stop.
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
    let stack_size = par_stack_size();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let mut results: Vec<Option<R>> = Vec::new();
    results.resize_with(items.len(), || None);
    std::thread::scope(|scope| {
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
        let handles: Vec<_> = (0..n_threads)
            .map(|_| {
                std::thread::Builder::new()
                    .name("verus-vir-worker".to_string())
                    .stack_size(stack_size)
                    .spawn_scoped(scope, worker)
                    .expect("failed to spawn VIR worker thread")
            })
            .collect();
        let mut panic = None;
        for handle in handles {
            match handle.join() {
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
    });
    results.into_iter().map(|r| r.expect("par_map_init result")).collect()
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
