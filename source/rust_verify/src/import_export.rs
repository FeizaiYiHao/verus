use crate::config::Args;
use crate::spans::FileStartEndPos;
use crate::verifier::io_vir_err;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use vir::ast::{Krate, Mode, VirErr};

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateMetadata {
    pub crate_id: u64,
    pub original_files: HashMap<Vec<u8>, FileStartEndPos>,
}

#[derive(Debug, Deserialize, Serialize)]
pub(crate) struct CrateWithMetadata {
    krate: Krate,
    metadata: CrateMetadata,
}

pub(crate) struct ImportOutput {
    pub(crate) vir_crates: Vec<Krate>,
    pub(crate) metadatas: Vec<CrateMetadata>,
}

/// Why one imported library file could not be loaded.  Workers produce only this plain
/// data; the diagnostic is built on the compiler thread by `decode_error`.
#[derive(Debug)]
pub(crate) enum DecodeError {
    Open(std::io::Error),
    Decode,
}

type Decoded = Result<CrateWithMetadata, DecodeError>;
/// Loads one imported library file.  Production code always uses `read_and_decode`;
/// tests substitute instrumented loaders.
type DecodeFn = fn(&str) -> Decoded;

/// Decode one value from `bytes`, requiring that the encoding consumes every byte.
pub(crate) fn decode_exact<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Option<T> {
    match bincode_next::serde::decode_from_slice(bytes, bincode_next::config::legacy()) {
        Ok((value, len)) if len == bytes.len() => Some(value),
        _ => None,
    }
}

/// Read a whole imported library file and decode it.  Opening and reading are separate so
/// that an open failure keeps its own message, as in the stream-decoding implementation.
fn read_and_decode(file_path: &str) -> Decoded {
    use std::io::Read;
    let mut file = std::fs::File::open(file_path).map_err(DecodeError::Open)?;
    let mut bytes = Vec::new();
    if let Some(len) = file.metadata().ok().and_then(|m| usize::try_from(m.len()).ok()) {
        let _ = bytes.try_reserve_exact(len);
    }
    file.read_to_end(&mut bytes).map_err(|_| DecodeError::Decode)?;
    decode_exact(&bytes).ok_or(DecodeError::Decode)
}

fn decode_error(file_path: &str, err: DecodeError) -> VirErr {
    match err {
        DecodeError::Open(err) => {
            io_vir_err(format!("could not open imported library file `{file_path}`"), err)
        }
        DecodeError::Decode => crate::util::error(format!(
            "failed to deserialize imported library file `{file_path}` - it may need to be rebuilt by Verus"
        )),
    }
}

/// The outcome of loading an ordered list of files, identical to a sequential loop that
/// stops at the first failure: the crates of the files before the first failing file, and
/// that file's error (its index is `crates.len()`).
#[derive(Default)]
struct Loaded {
    crates: Vec<CrateWithMetadata>,
    error: Option<DecodeError>,
}

impl Loaded {
    /// Continue with the files after this list, unless this list already failed.
    fn then(mut self, rest: impl FnOnce() -> Loaded) -> Loaded {
        if self.error.is_none() {
            let Loaded { crates, error } = rest();
            self.crates.extend(crates);
            self.error = error;
        }
        self
    }
}

/// Upper bound on concurrently decoding worker threads.
const MAX_DECODE_WORKERS: usize = 4;
/// Decoding deeply nested VIR recurses deeply.
const DECODE_STACK_SIZE: usize = 64 * 1024 * 1024;

/// Decoding of a fixed, ordered list of imported library files on bounded worker
/// threads.  Workers claim files in list order and store results per index, so the order
/// in which files finish never affects the outcome.  No file after the first known
/// failure is claimed.  Dropping without `join` cancels: workers claim no further files
/// and exit after their current one; they are detached, not waited for, and touch only
/// their own `Arc`-shared data, never the compiler.
pub(crate) struct ImportDecoding {
    paths: Arc<Vec<String>>,
    shared: Arc<DecodeShared>,
    workers: Vec<std::thread::JoinHandle<()>>,
}

type Slot = Option<std::thread::Result<Decoded>>;

struct DecodeShared {
    decode: DecodeFn,
    next: AtomicUsize,
    /// Smallest index known to have failed or panicked (`usize::MAX` if none).
    first_failure: AtomicUsize,
    cancelled: AtomicBool,
    slots: std::sync::Mutex<Vec<Slot>>,
}

fn decode_claimed(paths: &[String], shared: &DecodeShared) {
    let decode = shared.decode;
    while !shared.cancelled.load(Ordering::Acquire) {
        let i = shared.next.fetch_add(1, Ordering::Relaxed);
        // Claims are in index order, so every index before `i` is already claimed; a file
        // after a failure is never needed.
        if i >= paths.len() || i > shared.first_failure.load(Ordering::Acquire) {
            return;
        }
        let path = &paths[i];
        let decoded = std::panic::catch_unwind(|| decode(path));
        if !matches!(decoded, Ok(Ok(_))) {
            shared.first_failure.fetch_min(i, Ordering::AcqRel);
        }
        shared.slots.lock().unwrap_or_else(|e| e.into_inner())[i] = Some(decoded);
    }
}

impl ImportDecoding {
    /// Start `workers` threads (capped by MAX_DECODE_WORKERS, available parallelism, and
    /// the number of files).  A thread that cannot be spawned is not an error: `join`
    /// decodes every unclaimed file on the calling thread.
    pub(crate) fn start(paths: Vec<String>, workers: usize) -> ImportDecoding {
        Self::start_with(paths, workers, read_and_decode)
    }

    fn start_with(paths: Vec<String>, workers: usize, decode: DecodeFn) -> ImportDecoding {
        let available = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
        let workers = workers.min(MAX_DECODE_WORKERS).min(available).min(paths.len());
        let shared = Arc::new(DecodeShared {
            decode,
            next: AtomicUsize::new(0),
            first_failure: AtomicUsize::new(usize::MAX),
            cancelled: AtomicBool::new(false),
            slots: std::sync::Mutex::new((0..paths.len()).map(|_| None).collect()),
        });
        let mut decoding = ImportDecoding { paths: Arc::new(paths), shared, workers: Vec::new() };
        for _ in 0..workers {
            let (paths, shared) = (decoding.paths.clone(), decoding.shared.clone());
            let spawned = std::thread::Builder::new()
                .name("verus-import-decode".to_string())
                .stack_size(DECODE_STACK_SIZE)
                .spawn(move || decode_claimed(&paths, &shared));
            match spawned {
                Ok(handle) => decoding.workers.push(handle),
                Err(_) => break,
            }
        }
        decoding
    }

    pub(crate) fn paths(&self) -> &[String] {
        &self.paths
    }

    /// Wait for the files up to the first failure, helping with unclaimed ones, and
    /// return the sequential outcome.  A panic while decoding a file is resumed on the
    /// calling thread only if every earlier file succeeded, i.e. exactly when the
    /// sequential loop would have reached that file.
    fn join(mut self) -> Loaded {
        decode_claimed(&self.paths, &self.shared);
        for worker in std::mem::take(&mut self.workers) {
            // Decoding panics are caught per file; anything else is resumed here.
            if let Err(panic) = worker.join() {
                std::panic::resume_unwind(panic);
            }
        }
        let slots =
            std::mem::take(&mut *self.shared.slots.lock().unwrap_or_else(|e| e.into_inner()));
        let mut crates = Vec::with_capacity(slots.len());
        for slot in slots {
            match slot.expect("every import file before the first failure was decoded") {
                Ok(Ok(decoded)) => crates.push(decoded),
                Ok(Err(err)) => return Loaded { crates, error: Some(err) },
                Err(panic) => std::panic::resume_unwind(panic),
            }
        }
        Loaded { crates, error: None }
    }
}

impl Drop for ImportDecoding {
    fn drop(&mut self) {
        self.shared.cancelled.store(true, Ordering::Release);
    }
}

/// Decode `paths` on up to `workers` threads plus the calling thread; an empty list
/// starts nothing.
fn decode_in_parallel(paths: Vec<String>, workers: usize, decode: DecodeFn) -> Loaded {
    if paths.is_empty() {
        return Loaded::default();
    }
    ImportDecoding::start_with(paths, workers, decode).join()
}

/// The sequential loop: stop at the first failing file.
fn decode_sequentially(paths: &[String], decode: DecodeFn) -> Loaded {
    let mut crates = Vec::with_capacity(paths.len());
    for path in paths {
        match decode(path) {
            Ok(decoded) => crates.push(decoded),
            Err(err) => return Loaded { crates, error: Some(err) },
        }
    }
    Loaded { crates, error: None }
}

/// The directly imported library files, in import order: `--import` arguments, then
/// direct cargo dependencies.
pub(crate) fn direct_import_paths(
    args: &Args,
    import_virs_via_cargo: &[(String, String)],
) -> Vec<String> {
    args.import.iter().chain(import_virs_via_cargo.iter()).map(|(_, p)| p.clone()).collect()
}

/// Start decoding the direct imports in the background (unless `-V import-decode-sequential`).
pub(crate) fn start_direct_import_decoding(
    args: &Args,
    import_virs_via_cargo: &[(String, String)],
) -> Option<ImportDecoding> {
    if !args.import_decode_early {
        return None;
    }
    let paths = direct_import_paths(args, import_virs_via_cargo);
    if paths.is_empty() {
        return None;
    }
    Some(ImportDecoding::start(paths, MAX_DECODE_WORKERS))
}

fn encode<T: Serialize>(value: &T) -> Vec<u8> {
    bincode_next::serde::encode_to_vec(value, bincode_next::config::legacy())
        .expect("import decode check serialization")
}

/// Equality of decoded files.  original_files is a HashMap, so it is compared as a sorted
/// list; the crate itself has a deterministic encoding.
fn same_crate(a: &CrateWithMetadata, b: &CrateWithMetadata) -> bool {
    let files = |m: &CrateMetadata| {
        let mut files: Vec<_> =
            m.original_files.iter().map(|(k, v)| (k.clone(), encode(v))).collect();
        files.sort();
        files
    };
    a.metadata.crate_id == b.metadata.crate_id
        && files(&a.metadata) == files(&b.metadata)
        && encode(&a.krate) == encode(&b.krate)
}

fn same_error(a: &Option<DecodeError>, b: &Option<DecodeError>) -> bool {
    match (a, b) {
        (None, None) | (Some(DecodeError::Decode), Some(DecodeError::Decode)) => true,
        (Some(DecodeError::Open(a)), Some(DecodeError::Open(b))) => a.to_string() == b.to_string(),
        _ => false,
    }
}

/// The index of the first file on which two outcomes differ, if any.
fn first_difference(a: &Loaded, b: &Loaded) -> Option<usize> {
    let common = a.crates.iter().zip(b.crates.iter()).position(|(a, b)| !same_crate(a, b));
    common.or_else(|| {
        let same = a.crates.len() == b.crates.len() && same_error(&a.error, &b.error);
        (!same).then(|| a.crates.len().min(b.crates.len()))
    })
}

/// Load every imported library file: the direct imports (`--import`, then direct cargo
/// dependencies), then `transitive` cargo dependencies.  The outcome, including which
/// error is reported, its text, and whether a decoding panic propagates, is that of
/// loading the files sequentially in that order and stopping at the first failure.
///
/// `early` is the background decoding started by `start_direct_import_decoding`; its
/// results are used only if it decoded exactly the current list of direct imports.
pub(crate) fn import_crates(
    args: &Args,
    import_virs_via_cargo: Vec<(String, String)>,
    transitive: Vec<(String, String)>,
    early: Option<ImportDecoding>,
) -> Result<ImportOutput, VirErr> {
    import_crates_with(args, import_virs_via_cargo, transitive, early, read_and_decode)
}

fn import_crates_with(
    args: &Args,
    import_virs_via_cargo: Vec<(String, String)>,
    transitive: Vec<(String, String)>,
    early: Option<ImportDecoding>,
    decode: DecodeFn,
) -> Result<ImportOutput, VirErr> {
    let direct = direct_import_paths(args, &import_virs_via_cargo);
    let transitive: Vec<String> = transitive.into_iter().map(|(_, p)| p).collect();
    let all: Vec<String> = direct.iter().chain(transitive.iter()).cloned().collect();
    // The calling thread helps every join, so fresh pools get one worker fewer.
    let loaded = if args.import_decode_early {
        let direct_loaded = match early {
            Some(early) if early.paths() == &direct[..] => early.join(),
            mismatched => {
                drop(mismatched);
                decode_in_parallel(direct, MAX_DECODE_WORKERS - 1, decode)
            }
        };
        direct_loaded.then(|| decode_in_parallel(transitive, MAX_DECODE_WORKERS - 1, decode))
    } else {
        drop(early);
        decode_sequentially(&all, decode)
    };
    if args.import_decode_check {
        let sequential = decode_sequentially(&all, decode);
        if let Some(i) = first_difference(&loaded, &sequential) {
            return Err(crate::util::error(format!(
                "import decode check failed: background and sequential decoding of `{}` differ",
                all[i]
            )));
        }
    }
    let Loaded { crates, error } = loaded;
    if let Some(err) = error {
        return Err(decode_error(&all[crates.len()], err));
    }
    let mut metadatas = Vec::with_capacity(crates.len());
    let mut vir_crates = Vec::with_capacity(crates.len());
    for CrateWithMetadata { krate, metadata } in crates {
        vir_crates.push(krate);
        metadatas.push(metadata);
    }
    Ok(ImportOutput { vir_crates, metadatas })
}

pub(crate) fn export_crate(
    args: &Args,
    export_vir_path_via_cargo: &Option<std::path::PathBuf>,
    vir_metadata: CrateMetadata,
    vir_crate: Krate,
) -> Result<(), VirErr> {
    let export = args.export.as_ref().map(|s| s.clone().into());
    if let Some(file_path) = export.as_ref().or(export_vir_path_via_cargo.as_ref()) {
        // for efficiency's sake, prune out elements of AST that won't be needed by importers:
        let mut kratex = (*vir_crate).clone();
        kratex.functions.retain(|f| f.x.visibility.restricted_to.is_none());
        for func in kratex.functions.iter_mut() {
            let mut functionx = func.x.clone();
            functionx.decrease_by = None;
            if (functionx.mode != Mode::Spec || !functionx.body_visibility.is_public())
                && !matches!(&functionx.kind, vir::ast::FunctionKind::TraitMethodDecl { .. })
            {
                functionx.body = None;
            }
            *func = func.new_x(functionx);
        }
        let vir_crate = Arc::new(kratex);

        let mut file = std::io::BufWriter::new(match std::fs::File::create(file_path) {
            Ok(file) => file,
            Err(err) => {
                return Err(io_vir_err(
                    format!("could not create exported library file `{:?}`", file_path),
                    err,
                ));
            }
        });
        let krate_with_metadata = CrateWithMetadata { krate: vir_crate, metadata: vir_metadata };
        bincode_next::serde::encode_into_std_write(
            &krate_with_metadata,
            &mut file,
            bincode_next::config::legacy(),
        )
        .expect("write crate to file");
        //serde_json::to_writer(file, &vir_crate).expect("write crate to file");
        //serde_json::to_writer_pretty(file, &vir_crate).expect("write crate to file");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Duration, Instant};
    use vir::ast::{Arch, ArchWordBits, KrateX};

    fn tmp_dir(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "verus-import-decode-test-{}-{}",
            name,
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// A small library file whose crate is told apart by `tag` (stored in external_types).
    fn library_bytes(tag: &str, crate_id: u64) -> Vec<u8> {
        let path = Arc::new(vir::ast::PathX {
            krate: vir::ast::CrateId::Vstd,
            segments: Arc::new(vec![Arc::new(tag.to_string())]),
        });
        let krate = Arc::new(KrateX {
            functions: vec![],
            reveal_groups: vec![],
            datatypes: vec![],
            traits: vec![],
            trait_impls: vec![],
            assoc_type_impls: vec![],
            modules: vec![],
            external_fns: vec![],
            external_types: vec![path],
            path_as_rust_names: vec![],
            arch: Arch { word_bits: ArchWordBits::Exactly(64) },
            opaque_types: vec![],
        });
        let metadata = CrateMetadata { crate_id, original_files: HashMap::new() };
        encode(&CrateWithMetadata { krate, metadata })
    }

    fn tag(c: &CrateWithMetadata) -> String {
        c.krate.external_types[0].segments[0].to_string()
    }

    /// Write `name.vir` in `dir`: a library, garbage for names starting with "bad", and
    /// nothing for names starting with "missing".
    fn file(dir: &std::path::Path, name: &str, i: u64) -> (String, String) {
        let p = dir.join(format!("{name}.vir"));
        if name.starts_with("bad") {
            std::fs::write(&p, b"garbage").unwrap();
        } else if !name.starts_with("missing") {
            std::fs::write(&p, library_bytes(name, i)).unwrap();
        }
        (name.to_string(), p.to_str().unwrap().to_string())
    }

    fn paths(files: &[(String, String)]) -> Vec<String> {
        files.iter().map(|(_, p)| p.clone()).collect()
    }

    /// Every path passed to an instrumented loader, across all tests.
    static READS: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());

    fn reads_in(dir: &std::path::Path) -> Vec<String> {
        let dir = dir.to_str().unwrap();
        READS.lock().unwrap().iter().filter(|p| p.starts_with(dir)).cloned().collect()
    }

    /// Records the read; panics for files whose name starts with "panic".
    fn recording_decode(path: &str) -> Decoded {
        READS.lock().unwrap().push(path.to_string());
        let name = std::path::Path::new(path).file_name().unwrap().to_str().unwrap();
        if name.starts_with("panic") {
            panic!("synthetic import decode panic");
        }
        read_and_decode(path)
    }

    fn slow_decode(path: &str) -> Decoded {
        READS.lock().unwrap().push(path.to_string());
        std::thread::sleep(Duration::from_millis(200));
        read_and_decode(path)
    }

    fn import_args(direct: &[(String, String)], early: bool) -> Args {
        let mut argsx = crate::config::ArgsX::new();
        argsx.import = direct.to_vec();
        argsx.import_decode_early = early;
        argsx.import_decode_check = early;
        Arc::new(argsx)
    }

    #[test]
    fn decode_matches_stream_decoding_and_requires_full_consumption() {
        let bytes = library_bytes("a", 7);
        let streamed: CrateWithMetadata = bincode_next::serde::decode_from_std_read(
            &mut std::io::Cursor::new(&bytes),
            bincode_next::config::legacy(),
        )
        .unwrap();
        let sliced: CrateWithMetadata = decode_exact(&bytes).unwrap();
        assert_eq!(encode(&streamed), encode(&sliced));
        assert_eq!(encode(&sliced), bytes);
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(decode_exact::<CrateWithMetadata>(&trailing).is_none());
        assert!(decode_exact::<CrateWithMetadata>(&bytes[..bytes.len() - 1]).is_none());
    }

    #[test]
    fn parallel_decoding_keeps_order_and_first_error() {
        let dir = tmp_dir("order");
        let good: Vec<_> = (0..9).map(|i| file(&dir, &format!("t{i}"), i)).collect();
        let mut failing = good.clone();
        failing[4] = file(&dir, "bad4", 4);
        failing[6] = file(&dir, "missing6", 6);
        let mut open_first = good.clone();
        open_first[3] = file(&dir, "missing3", 3);
        open_first[5] = file(&dir, "bad5", 5);
        for workers in [0, 1, 3, 4] {
            let all = ImportDecoding::start(paths(&good), workers).join();
            assert!(all.error.is_none());
            let tags: Vec<String> = all.crates.iter().map(tag).collect();
            assert_eq!(tags, (0..9).map(|i| format!("t{i}")).collect::<Vec<_>>());
            for (list, at) in [(&failing, 4), (&open_first, 3)] {
                let r = ImportDecoding::start(paths(list), workers).join();
                let s = decode_sequentially(&paths(list), read_and_decode);
                assert!(first_difference(&r, &s).is_none());
                assert_eq!(r.crates.len(), at);
                match at {
                    4 => assert!(matches!(r.error, Some(DecodeError::Decode))),
                    _ => assert!(matches!(r.error, Some(DecodeError::Open(_)))),
                }
            }
        }
        // The first failing file in order is reported, with the sequential message.
        for early in [false, true] {
            let args = import_args(&failing, early);
            let err = import_crates(&args, vec![], vec![], None).err().unwrap();
            assert!(err.note.starts_with("failed to deserialize imported library file"));
            assert!(err.note.contains("bad4.vir"));
            let args = import_args(&open_first, early);
            let err = import_crates(&args, vec![], vec![], None).err().unwrap();
            assert!(err.note.starts_with("could not open imported library file"), "{}", err.note);
            assert!(err.note.contains("missing3.vir"));
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn earlier_failure_hides_later_panic_like_the_sequential_loop() {
        let dir = tmp_dir("hidden-failure");
        let list = vec![file(&dir, "a0", 0), file(&dir, "bad1", 1), file(&dir, "panic2", 2)];
        let list = [list, (3..8).map(|i| file(&dir, &format!("a{i}"), i)).collect()].concat();
        for _ in 0..20 {
            for workers in [0, 1, 3, 4] {
                let r = ImportDecoding::start_with(paths(&list), workers, recording_decode).join();
                assert_eq!(r.crates.len(), 1);
                assert!(matches!(r.error, Some(DecodeError::Decode)));
            }
        }
        let s = decode_sequentially(&paths(&list), recording_decode);
        assert!(matches!(s.error, Some(DecodeError::Decode)));
        for early in [false, true] {
            let args = import_args(&list, early);
            let started = early.then(|| {
                ImportDecoding::start_with(paths(&list), MAX_DECODE_WORKERS, recording_decode)
            });
            let err = import_crates_with(&args, vec![], vec![], started, recording_decode);
            let err = err.err().unwrap();
            assert!(err.note.starts_with("failed to deserialize imported library file"));
            assert!(err.note.contains("bad1.vir"), "{}", err.note);
        }
        // A panic in a file that the sequential loop reaches is resumed.
        let reached = vec![file(&dir, "a0", 0), file(&dir, "panic1", 1), file(&dir, "bad2", 2)];
        for workers in [0, 1, 3] {
            let d = ImportDecoding::start_with(paths(&reached), workers, recording_decode);
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| d.join()));
            assert!(r.is_err());
        }
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn sequential_and_direct_failures_stop_reading() {
        let dir = tmp_dir("stop");
        let direct = vec![file(&dir, "d0", 0), file(&dir, "bad1", 1), file(&dir, "d2", 2)];
        let transitive = vec![file(&dir, "t0", 3), file(&dir, "t1", 4)];
        let s = decode_sequentially(&paths(&direct), recording_decode);
        assert_eq!(s.crates.len(), 1);
        assert_eq!(reads_in(&dir), paths(&direct[..2]));
        for early in [false, true] {
            for matching in [true, false] {
                let args = import_args(&direct, early);
                let started = early.then(|| {
                    let list = if matching { paths(&direct) } else { paths(&direct[..1]) };
                    ImportDecoding::start_with(list, MAX_DECODE_WORKERS, recording_decode)
                });
                let err = import_crates_with(
                    &args,
                    vec![],
                    transitive.clone(),
                    started,
                    recording_decode,
                );
                assert!(err.err().unwrap().note.contains("bad1.vir"));
            }
        }
        let reads = reads_in(&dir);
        assert!(reads.iter().all(|p| !p.ends_with("/t0.vir") && !p.ends_with("/t1.vir")));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn dropping_cancels_without_waiting() {
        let dir = tmp_dir("cancel");
        let list: Vec<_> = (0..20).map(|i| file(&dir, &format!("c{i}"), i)).collect();
        let decoding = ImportDecoding::start_with(paths(&list), 1, slow_decode);
        while reads_in(&dir).is_empty() {
            std::thread::sleep(Duration::from_millis(1));
        }
        let t = Instant::now();
        drop(decoding);
        assert!(t.elapsed() < Duration::from_millis(100));
        std::thread::sleep(Duration::from_millis(700));
        let n = reads_in(&dir).len();
        assert!(n <= 2, "{n} files read after cancellation");
        std::thread::sleep(Duration::from_millis(300));
        assert_eq!(reads_in(&dir).len(), n);
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn empty_lists_start_no_workers() {
        let d = ImportDecoding::start(vec![], MAX_DECODE_WORKERS);
        assert!(d.workers.is_empty());
        let r = d.join();
        assert!(r.crates.is_empty() && r.error.is_none());
        let r = decode_in_parallel(vec![], MAX_DECODE_WORKERS, recording_decode);
        assert!(r.crates.is_empty() && r.error.is_none());
        for early in [false, true] {
            let out = import_crates(&import_args(&[], early), vec![], vec![], None).unwrap();
            assert!(out.vir_crates.is_empty() && out.metadatas.is_empty());
        }
    }

    #[test]
    fn background_decoding_joins_with_transitive_imports_in_order() {
        let dir = tmp_dir("background");
        let direct = vec![file(&dir, "d0", 0), file(&dir, "d1", 1)];
        let cargo = vec![file(&dir, "c0", 2)];
        let transitive = vec![file(&dir, "t0", 3), file(&dir, "t1", 4)];
        let args = import_args(&direct, true);
        let early = start_direct_import_decoding(&args, &cargo).expect("started");
        assert_eq!(early.paths().len(), 3);
        let out = import_crates(&args, cargo.clone(), transitive.clone(), Some(early)).unwrap();
        let tags: Vec<String> =
            out.vir_crates.iter().map(|k| k.external_types[0].segments[0].to_string()).collect();
        assert_eq!(tags, vec!["d0", "d1", "c0", "t0", "t1"]);
        let ids: Vec<u64> = out.metadatas.iter().map(|m| m.crate_id).collect();
        assert_eq!(ids, vec![0, 1, 2, 3, 4]);
        // Background results for a different direct list are not used.
        let early = start_direct_import_decoding(&args, &[]).expect("started");
        let out = import_crates(&args, cargo.clone(), transitive, Some(early)).unwrap();
        let ids: Vec<u64> = out.metadatas.iter().map(|m| m.crate_id).collect();
        assert_eq!(ids, vec![0, 1, 2, 3, 4]);
        // Errors surface at the join, for the first failing file in order.
        let mut argsx = crate::config::ArgsX::new();
        argsx.import = direct.clone();
        argsx.import_decode_early = true;
        let args = Arc::new(argsx);
        std::fs::write(&direct[1].1, b"bad").unwrap();
        std::fs::remove_file(&direct[0].1).unwrap();
        let early = start_direct_import_decoding(&args, &[]).expect("started");
        let err = import_crates(&args, vec![], vec![], Some(early)).err().unwrap();
        assert!(err.note.starts_with("could not open imported library file"), "{}", err.note);
        assert!(err.note.contains("d0.vir"));
        // Without the option nothing starts early.
        let mut argsx = crate::config::ArgsX::new();
        argsx.import_decode_early = false;
        assert!(start_direct_import_decoding(&argsx.into(), &cargo).is_none());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
