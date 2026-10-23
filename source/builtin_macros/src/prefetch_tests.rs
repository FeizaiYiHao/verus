//! Unit tests for the speculative `verus!` prefetch, on fallback tokens.
//!
//! The speculative side lexes source text positionally on the real pool; the
//! real side is the same block text lexed by the fallback lexer on the test
//! thread. A hit is committed without side effects (check mode) and compared
//! with the serial reference of `par_items` tests (tokens, spans, diagnostics,
//! UID count).

use super::*;
use crate::par_items::tests::{
    ALL_MODES, IDENTITY_CORPORA, general_block, serial, setup, tokens, with_uid_items,
};
use crate::par_items::{check_problems, commit};
use crate::syntax::EX_IDENT_UID;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static HOLD: Mutex<bool> = Mutex::new(false);
static HOLD_CV: Condvar = Condvar::new();
static HELD: AtomicUsize = AtomicUsize::new(0);

/// Called by every speculative token right after it marks its entry running.
pub(super) fn hold_point() {
    let mut hold = HOLD.lock().unwrap_or_else(|e| e.into_inner());
    if *hold {
        HELD.fetch_add(1, Ordering::SeqCst);
        while *hold {
            hold = HOLD_CV.wait(hold).unwrap_or_else(|e| e.into_inner());
        }
    }
}

fn set_hold(on: bool) {
    *HOLD.lock().unwrap() = on;
    HOLD_CV.notify_all();
}

fn fresh(cap: usize) -> &'static Shared {
    Box::leak(Box::new(Shared::new(cap)))
}

fn key(erase_ghost: EraseGhost) -> Key {
    key_now(erase_ghost, true)
}

fn block(src: &str) -> String {
    format!("verus! {{\n{}\n}}\n", src)
}

/// Speculates `text` as file `path` and waits until every entry settled.
fn speculate(sh: &'static Shared, k: Key, path: &str, text: String) -> Vec<ModDecl> {
    let mods = scan_file_on_pool(sh, k, Path::new(path), text).expect("scan");
    sh.settle();
    mods
}

/// Looks `src` up as real input, commits the hit without side effects, and
/// asserts identity with the serial path.
fn assert_hit(sh: &'static Shared, eg: EraseGhost, loc: Option<Loc>, src: &str) {
    let input = tokens(src);
    let base = EX_IDENT_UID.load(Ordering::Relaxed);
    let prepared = match lookup_tokens(sh, key(eg), loc, input.clone()) {
        Ok(p) => p,
        Err(reason) => panic!("expected a hit, got a miss: {}", reason),
    };
    let par = commit(prepared, false);
    assert_eq!(EX_IDENT_UID.load(Ordering::Relaxed), base, "check-mode hit consumed UIDs");
    assert_eq!(par.tasks, 1);
    let ser = serial(input, eg);
    let problems = check_problems(&par, &ser.tokens, &ser.diags, ser.uid_count);
    assert!(problems.is_empty(), "prefetched result differs: {}", problems.join("; "));
}

fn assert_miss(sh: &'static Shared, eg: EraseGhost, loc: Option<Loc>, src: &str, reason: &str) {
    let base = EX_IDENT_UID.load(Ordering::Relaxed);
    match lookup_tokens(sh, key(eg), loc, tokens(src)) {
        Ok(_) => panic!("expected a miss ({})", reason),
        Err(e) => assert!(e.contains(reason), "miss reason {:?} lacks {:?}", e, reason),
    }
    assert_eq!(EX_IDENT_UID.load(Ordering::Relaxed), base, "miss consumed UIDs");
}

fn lex(text: &str) -> LexedFile {
    let _ = wt::freeze_rejoin_main(TokenStream::new());
    let _job = wt::begin_job();
    wt::lex_positional(&wt::normalize_rustc_source(text)).expect("lex")
}

#[test]
fn hit_identity_across_existing_corpus_all_modes() {
    let _g = setup();
    let text: String = IDENTITY_CORPORA.iter().map(|(_, src)| block(&src())).collect();
    for eg in ALL_MODES {
        let sh = fresh(DEFAULT_MEM_CAP);
        speculate(sh, key(eg), "/virtual/lib.rs", text.clone());
        assert_eq!(sh.counts(), (0, 0, IDENTITY_CORPORA.len(), 0), "{:?}", eg);
        for (_, src) in IDENTITY_CORPORA {
            assert_hit(sh, eg, None, &src());
        }
        assert_eq!(sh.counts(), (0, 0, 0, 0), "entries are freed on consumption");
        assert_eq!(sh.mem(), 0);
        let s = sh.stats();
        assert_eq!((s.hits, s.misses, s.failed), (IDENTITY_CORPORA.len(), 0, 0));
    }
}

#[test]
fn hit_by_location_and_consumed_once() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let src = general_block(0);
    let text = format!("// header\n{}{}", block(&src), block(&src));
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", text);
    let locs = sh.locs();
    // Line 2 is `verus! {`, line 3 the corpus' leading newline, then 8 spaces.
    assert_eq!(locs.len(), 2);
    assert_eq!(locs[0], Loc { file: PathBuf::from("/virtual/lib.rs"), pos: (4, 9) });
    assert_hit(sh, EraseGhost::Keep, Some(locs[1].clone()), &src);
    assert_hit(sh, EraseGhost::Keep, Some(locs[0].clone()), &src);
    // Both identical blocks are consumed now.
    assert_miss(sh, EraseGhost::Keep, None, &src, "no speculative entry");
}

#[test]
fn mismatch_falls_back_and_evicts_only_the_looked_up_location() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", block(&general_block(0)));
    let loc = sh.locs()[0].clone();
    // Without a location nothing is evicted.
    assert_miss(sh, EraseGhost::Keep, None, &general_block(1), "no speculative entry");
    assert_eq!(sh.counts(), (0, 0, 1, 0), "a location-less miss keeps the entry");
    // Another key's lookup at the location leaves this key's entry.
    assert_miss(sh, EraseGhost::Erase, Some(loc.clone()), &general_block(0), "key mismatch");
    assert_eq!(sh.counts(), (0, 0, 1, 0), "another key keeps the entry");
    // The location is expanded with other input: its entry is stale.
    assert_miss(sh, EraseGhost::Keep, Some(loc.clone()), &general_block(1), "input mismatch");
    assert_eq!(sh.counts(), (0, 0, 0, 0), "the looked-up location is evicted");
    assert_eq!(sh.mem(), 0);
    assert_miss(sh, EraseGhost::Keep, Some(loc), &general_block(0), "no speculative entry");
    let s = sh.stats();
    assert_eq!((s.hits, s.misses, s.evicted), (0, 4, 1));
}

#[test]
fn location_mismatch_falls_back_to_hash_lookup() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let (a, b) = (general_block(0), general_block(1));
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", format!("{}{}", block(&a), block(&b)));
    let locs = sh.locs();
    assert_eq!(locs.len(), 2);
    // `b` looked up at `a`'s location: the location candidate differs, the hash
    // fallback finds `b`'s entry, and `a`'s entry at the expanded location is
    // stale and evicted.
    assert_hit(sh, EraseGhost::Keep, Some(locs[0].clone()), &b);
    assert_eq!(sh.locs(), Vec::<Loc>::new());
    assert_eq!(sh.stats().evicted, 1);
    // A location hit (no hash needed), then nothing is left.
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", block(&a));
    let loc = sh.locs()[0].clone();
    assert_hit(sh, EraseGhost::Keep, Some(loc.clone()), &a);
    assert_miss(sh, EraseGhost::Keep, Some(loc), &a, "no speculative entry");
    // A location candidate with another key reports the key mismatch.
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", block(&a));
    let loc = sh.locs()[0].clone();
    assert_miss(sh, EraseGhost::Erase, Some(loc.clone()), &a, "key mismatch");
    assert_hit(sh, EraseGhost::Keep, Some(loc), &a);
}

#[test]
fn key_mismatch_falls_back() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let src = general_block(0);
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", block(&src));
    assert_miss(sh, EraseGhost::Erase, None, &src, "key mismatch");
    assert_miss(sh, EraseGhost::EraseAll, None, &src, "key mismatch");
    let other = Key { use_spec_traits: false, ..key(EraseGhost::Keep) };
    match lookup_tokens(sh, other, None, tokens(&src)) {
        Ok(_) => panic!("use_spec_traits differs"),
        Err(e) => assert!(e.contains("key mismatch"), "{}", e),
    }
    assert_hit(sh, EraseGhost::Keep, None, &src);
}

#[test]
fn failed_speculation_falls_back() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let src = with_uid_items("fn broken() -> { }");
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", block(&src));
    assert_eq!(sh.counts(), (0, 0, 0, 1));
    assert_miss(sh, EraseGhost::Keep, None, &src, "speculative task failed");
    assert_eq!(sh.counts(), (0, 0, 0, 0), "a failed entry is consumed");
    assert_eq!(sh.stats().failed, 1);
}

#[test]
fn in_flight_entry_is_waited_for() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let src = general_block(0);
    let before = HELD.load(Ordering::SeqCst);
    set_hold(true);
    scan_file_on_pool(sh, key(EraseGhost::Keep), Path::new("/virtual/lib.rs"), block(&src))
        .expect("scan");
    let deadline = Instant::now() + Duration::from_secs(30);
    while HELD.load(Ordering::SeqCst) == before {
        assert!(Instant::now() < deadline, "token never started");
        std::thread::sleep(Duration::from_millis(5));
    }
    assert_eq!(sh.counts(), (0, 1, 0, 0));
    static RELEASED: AtomicBool = AtomicBool::new(false);
    RELEASED.store(false, Ordering::SeqCst);
    let releaser = std::thread::spawn(|| {
        std::thread::sleep(Duration::from_millis(100));
        RELEASED.store(true, Ordering::SeqCst);
        set_hold(false);
    });
    assert_hit(sh, EraseGhost::Keep, None, &src);
    assert!(RELEASED.load(Ordering::SeqCst), "lookup returned before the entry finished");
    releaser.join().unwrap();
}

#[test]
fn pending_entries_are_consumed_as_misses() {
    let _g = setup();
    // Cap 0: every token parks, entries stay pending.
    let sh = fresh(0);
    let srcs: Vec<String> = (0..3).map(general_block).collect();
    let text: String = srcs.iter().map(|s| block(s)).collect();
    speculate(sh, key(EraseGhost::Keep), "/virtual/lib.rs", text);
    assert_eq!(sh.counts(), (3, 0, 0, 0), "speculation must pause over the cap");
    // A pending entry is a miss (the caller's n-way path runs it) and is removed
    // together with its parked token.
    assert_miss(sh, EraseGhost::Keep, None, &srcs[1], "still pending");
    assert_eq!(sh.counts(), (2, 0, 0, 0));
    assert_miss(sh, EraseGhost::Keep, None, &srcs[1], "no speculative entry");
    assert_miss(sh, EraseGhost::Keep, None, &srcs[0], "still pending");
    assert_miss(sh, EraseGhost::Keep, None, &srcs[2], "still pending");
    assert_eq!(sh.counts(), (0, 0, 0, 0));
    assert_eq!(sh.mem(), 0);
    assert_eq!(sh.stats().evicted, 3);
    // Every parked token was released with its entry.
    sh.settle();
    assert_eq!(sh.parked(), 0);
}

#[test]
fn stale_running_entry_is_evicted_when_it_finishes() {
    let _g = setup();
    let sh = fresh(DEFAULT_MEM_CAP);
    let src = general_block(0);
    let before = HELD.load(Ordering::SeqCst);
    set_hold(true);
    scan_file_on_pool(sh, key(EraseGhost::Keep), Path::new("/virtual/lib.rs"), block(&src))
        .expect("scan");
    let deadline = Instant::now() + Duration::from_secs(30);
    while HELD.load(Ordering::SeqCst) == before {
        assert!(Instant::now() < deadline, "token never started");
        std::thread::sleep(Duration::from_millis(5));
    }
    let loc = sh.locs()[0].clone();
    // The location is expanded with other input while its entry runs.
    assert_miss(sh, EraseGhost::Keep, Some(loc), &general_block(1), "input mismatch");
    assert_eq!(sh.counts(), (0, 1, 0, 0), "a running entry is not removed early");
    set_hold(false);
    sh.settle();
    assert_eq!(sh.counts(), (0, 0, 0, 0), "the stale entry is evicted when it finishes");
    assert_eq!(sh.mem(), 0);
    assert_eq!(sh.stats().evicted, 1);
}

#[test]
fn speculative_jobs_are_capped_and_real_jobs_overtake() {
    let _g = setup();
    let pool = pool();
    let cap = crate::par_items::speculative_cap(pool.size);
    assert_eq!(cap, (pool.size / 2).max(1));
    assert!(cap < pool.size, "test pool must leave threads for real jobs");
    static GATE: Mutex<bool> = Mutex::new(true);
    static GATE_CV: Condvar = Condvar::new();
    static STARTED: AtomicUsize = AtomicUsize::new(0);
    STARTED.store(0, Ordering::SeqCst);
    *GATE.lock().unwrap() = true;
    let blocked = || {
        STARTED.fetch_add(1, Ordering::SeqCst);
        let mut g = GATE.lock().unwrap_or_else(|e| e.into_inner());
        while *g {
            g = GATE_CV.wait(g).unwrap_or_else(|e| e.into_inner());
        }
    };
    for _ in 0..pool.size {
        assert!(pool.submit(Box::new(blocked), true));
    }
    let deadline = Instant::now() + Duration::from_secs(30);
    while STARTED.load(Ordering::SeqCst) < cap {
        assert!(Instant::now() < deadline, "speculative jobs never started");
        std::thread::sleep(Duration::from_millis(5));
    }
    std::thread::sleep(Duration::from_millis(100));
    assert_eq!(STARTED.load(Ordering::SeqCst), cap, "more than the cap started");
    assert_eq!(pool.speculative_running(), cap);
    // Real jobs still find free threads, one per remaining thread at once.
    let (tx, rx) = std::sync::mpsc::channel();
    for _ in 0..pool.size - cap {
        let tx = tx.clone();
        assert!(pool.submit(Box::new(move || tx.send(()).unwrap()), false));
    }
    for _ in 0..pool.size - cap {
        rx.recv_timeout(Duration::from_secs(30)).expect("real job starved");
    }
    *GATE.lock().unwrap() = false;
    GATE_CV.notify_all();
    while STARTED.load(Ordering::SeqCst) < pool.size || pool.speculative_running() > 0 {
        assert!(Instant::now() < deadline, "speculative jobs never finished");
        std::thread::sleep(Duration::from_millis(5));
    }
}

struct TempTree(PathBuf);

impl TempTree {
    fn new(name: &str, files: &[(&str, &str)]) -> TempTree {
        let root = std::env::temp_dir().join(format!(
            "verus-prefetch-test-{}-{}",
            std::process::id(),
            name
        ));
        let _ = std::fs::remove_dir_all(&root);
        for (path, text) in files {
            let p = root.join(path);
            std::fs::create_dir_all(p.parent().unwrap()).unwrap();
            std::fs::write(&p, text).unwrap();
        }
        TempTree(std::fs::canonicalize(&root).unwrap())
    }

    fn path(&self, p: &str) -> PathBuf {
        self.0.join(p)
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn discovery_follows_mod_and_path_depth_first() {
    let _g = setup();
    let tree = TempTree::new(
        "discovery",
        &[
            (
                "lib.rs",
                "mod a;\n#[path = \"other/b_impl.rs\"]\npub mod b;\nmod c { mod d; }\n\
                 macro_rules! m { () => { mod zz; } }\nmod x;\nmod missing;\n\
                 verus! { fn root() {} }\n",
            ),
            ("a.rs", "mod a1;\nverus! { fn fa() {} }\n"),
            ("a/a1.rs", "verus! { fn fa1() {} }\n"),
            ("other/b_impl.rs", "mod b1;\nverus! { fn fb() {} }\n"),
            ("other/b1.rs", "verus! { fn fb1() {} }\n"),
            ("c/d.rs", "verus! { fn fd() {} }\n"),
            ("x/mod.rs", "verus! { mod y; fn fx() {} }\n"),
            ("x/y.rs", "verus! { fn fy() {} }\n"),
            ("zz.rs", "verus! { fn never() {} }\n"),
        ],
    );
    let sh = fresh(DEFAULT_MEM_CAP);
    discover(sh, key(EraseGhost::Keep), vec![tree.path("lib.rs")]);
    sh.settle();
    let files: Vec<PathBuf> = sh.locs().into_iter().map(|l| l.file).collect();
    let expected: Vec<PathBuf> = [
        "lib.rs",
        "a.rs",
        "a/a1.rs",
        "other/b_impl.rs",
        "other/b1.rs",
        "c/d.rs",
        "x/mod.rs",
        "x/y.rs",
    ]
    .iter()
    .map(|p| tree.path(p))
    .collect();
    assert_eq!(files, expected);
    assert_eq!(sh.stats().files, 8);
    assert_eq!(sh.counts(), (0, 0, 8, 0));
    assert_hit(sh, EraseGhost::Keep, None, "fn fb1() {}");
    assert_hit(sh, EraseGhost::Keep, None, "mod y; fn fx() {}");
}

#[test]
fn discovery_pauses_over_memory_cap() {
    let _g = setup();
    let tree = TempTree::new(
        "pause",
        &[("lib.rs", "mod a;\nverus! { fn root() {} }\n"), ("a.rs", "verus! { fn fa() {} }\n")],
    );
    let sh = fresh(1);
    let root = tree.path("lib.rs");
    let walker = std::thread::spawn(move || discover(sh, key(EraseGhost::Keep), vec![root]));
    let deadline = Instant::now() + Duration::from_secs(30);
    while sh.stats().files < 1 {
        assert!(Instant::now() < deadline, "first file never scanned");
        std::thread::sleep(Duration::from_millis(5));
    }
    std::thread::sleep(Duration::from_millis(100));
    assert_eq!(sh.stats().files, 1, "discovery must pause over the cap");
    // Consuming the only (still pending) entry frees memory and resumes discovery.
    assert_miss(sh, EraseGhost::Keep, None, "fn root() {}", "still pending");
    walker.join().unwrap();
    assert_eq!(sh.stats().files, 2);
    assert_miss(sh, EraseGhost::Keep, None, "fn fa() {}", "still pending");
    assert_eq!(sh.mem(), 0);
}

#[test]
fn scan_skip_rules() {
    let _g = setup();
    let text = "macro_rules! m { ($x:ident) => { verus! { fn $x() {} } }; }\n\
                verus! { fn outer() {} verus! { fn nested() {} } }\n\
                verus! { fn meta() { $x } }\n\
                verus! { fn café() {} }\n\
                verus! {}\n\
                verus! { #[auto_spec] fn c(x: u64) -> u64 { x } }\n\
                verus! { fn _verus_external_fn_specification_PARUID_0_0_() {} }\n\
                mod inner { verus! { fn in_mod() {} } }\n\
                fn body() { verus! { fn in_fn() {} } }\n";
    let file = lex(text);
    let found = scan_lexed(&file);
    let reasons: Vec<Option<String>> =
        found.blocks.iter().map(|r| block_skip_reason(&file, r.clone())).collect();
    let short: Vec<&str> = reasons
        .iter()
        .map(|r| match r.as_deref() {
            None => "ok",
            Some(r) if r.contains("metavariable") => "meta",
            Some(r) if r.contains("non-ASCII") => "ascii",
            Some(r) if r.contains("empty") => "empty",
            Some(r) if r.contains("contrib") => "contrib",
            Some(r) if r.contains("placeholder") => "marker",
            Some(r) => panic!("unexpected reason {}", r),
        })
        .collect();
    // The nested block and the macro_rules body are never collected.
    assert_eq!(short, ["ok", "meta", "ascii", "empty", "contrib", "marker", "ok", "ok"]);
    assert!(found.mods.is_empty());
}

#[test]
fn scan_module_declarations() {
    let _g = setup();
    let text = "#![allow(unused)]\nmod a;\n#[path = r\"p/q.rs\"] mod b;\n#[cfg(x)] pub(crate) mod r#type;\n\
                #[path = \"io\"] mod inl { mod c; #[path = \"z.rs\"] mod d; }\n\
                verus! { mod e; }\nfn f() {}\nmod g;\n";
    let found = scan_lexed(&lex(text));
    let decl = |name: &str, path: Option<&str>, inline: Vec<DirStep>| ModDecl {
        name: name.to_string(),
        path: path.map(str::to_string),
        inline,
    };
    let io = || vec![DirStep::Path("io".to_string())];
    assert_eq!(
        found.mods,
        vec![
            decl("a", None, vec![]),
            decl("b", Some("p/q.rs"), vec![]),
            decl("type", None, vec![]),
            decl("c", None, io()),
            decl("d", Some("z.rs"), io()),
            decl("e", None, vec![]),
            decl("g", None, vec![]),
        ]
    );
    // Non-mod-rs files own `<dir>/<stem>/`; path attributes are file-relative.
    let tree = TempTree::new("resolve", &[("src/m/a.rs", ""), ("src/m/io/c/mod.rs", "")]);
    let m = tree.path("src/m.rs");
    let out = resolve_mods(&m, false, &found.mods[..5]);
    assert_eq!(
        out,
        vec![
            (tree.path("src/m/a.rs"), false),
            (tree.path("src/p/q.rs"), true),
            (tree.path("src/m/io/c/mod.rs"), true),
            (tree.path("src/m/io/z.rs"), true),
        ]
    );
}

#[test]
fn line_index_positions() {
    let text = "a\nbé c\n\nd";
    let idx = LineIndex::new(text);
    assert_eq!(idx.pos(0), (1, 1));
    assert_eq!(idx.pos(2), (2, 1));
    assert_eq!(idx.pos(6), (2, 4));
    assert_eq!(idx.pos(8), (3, 1));
    assert_eq!(idx.pos(9), (4, 1));
}

#[test]
fn config_parsing() {
    // Unset or empty: on by default.
    assert_eq!(parse_mode(None), Mode::On);
    assert_eq!(parse_mode(Some("")), Mode::On);
    // Opt-outs.
    assert_eq!(parse_mode(Some("0")), Mode::Off);
    assert_eq!(parse_mode(Some(" off ")), Mode::Off);
    assert_eq!(parse_mode(Some("false")), Mode::Off);
    assert_eq!(parse_mode(Some(" 1 ")), Mode::On);
    assert_eq!(parse_mode(Some("on")), Mode::On);
    assert_eq!(parse_mode(Some("true")), Mode::On);
    assert_eq!(parse_mode(Some("check")), Mode::Check);
    // Unknown explicit values disable prefetch.
    assert_eq!(parse_mode(Some("yes")), Mode::Off);
    assert_eq!(parse_mem_cap(None), 1 << 30);
    assert_eq!(parse_mem_cap(Some("4096")), 4096);
    assert_eq!(parse_mem_cap(Some("bogus")), 1 << 30);
}

#[test]
fn read_source_limits() {
    let tree = TempTree::new(
        "read",
        &[("ok.rs", "fn f() {}\n"), ("dir.rs/inner.rs", ""), ("bad.rs", ""), ("big.rs", "")],
    );
    assert_eq!(read_source(&tree.path("ok.rs")).as_deref(), Ok("fn f() {}\n"));
    assert_eq!(read_source(&tree.path("dir.rs")), Err("not a regular file"));
    assert_eq!(read_source(&tree.path("missing.rs")), Err("not a regular file"));
    std::fs::write(tree.path("bad.rs"), [0x66u8, 0xff, 0xfe]).unwrap();
    assert_eq!(read_source(&tree.path("bad.rs")), Err("not UTF-8"));
    // A sparse file one byte over the limit; exactly at the limit is read.
    let big = std::fs::OpenOptions::new().write(true).open(tree.path("big.rs")).unwrap();
    big.set_len(MAX_FILE_SIZE + 1).unwrap();
    assert_eq!(read_source(&tree.path("big.rs")), Err("file too large"));
    big.set_len(MAX_FILE_SIZE).unwrap();
    assert_eq!(read_source(&tree.path("big.rs")).map(|t| t.len() as u64), Ok(MAX_FILE_SIZE));
    // A FIFO is rejected before it is opened (opening it would block).
    let fifo = tree.path("fifo.rs");
    let made =
        std::process::Command::new("mkfifo").arg(&fifo).status().map_or(false, |s| s.success());
    if made {
        assert_eq!(read_source(&fifo), Err("not a regular file"));
    }
}

#[test]
fn discovery_skips_non_regular_module_files() {
    let _g = setup();
    let tree = TempTree::new(
        "nonregular",
        &[
            ("lib.rs", "#[path = \"d\"] mod d;\nmod a;\nverus! { fn root() {} }\n"),
            ("d/x.rs", ""),
            ("a.rs", "verus! { fn fa() {} }\n"),
        ],
    );
    let sh = fresh(DEFAULT_MEM_CAP);
    discover(sh, key(EraseGhost::Keep), vec![tree.path("lib.rs")]);
    sh.settle();
    let files: Vec<PathBuf> = sh.locs().into_iter().map(|l| l.file).collect();
    assert_eq!(files, vec![tree.path("lib.rs"), tree.path("a.rs")]);
    let s = sh.stats();
    assert_eq!((s.files, s.skips), (2, 1), "{:?}", s);
}

/// `_perm_tupN` ids (empty atomic perm tuple names) in `ts`, in order.
fn perm_tup_ids(ts: &TokenStream, out: &mut Vec<u64>) {
    for tt in ts.clone() {
        match tt {
            proc_macro2::TokenTree::Group(g) => perm_tup_ids(&g.stream(), out),
            proc_macro2::TokenTree::Ident(id) => {
                if let Some(n) = id.to_string().strip_prefix("_perm_tup") {
                    out.push(n.parse().expect("perm tuple id"));
                }
            }
            _ => {}
        }
    }
}

#[test]
fn empty_perm_tuple_counter_untouched_by_workers() {
    // The process-global empty perm tuple counter only advances in serial
    // order: parallel and speculative runs of such input fall back before
    // naming a tuple. All counter users run under `setup()`.
    let _g = setup();
    let src = with_uid_items("pub fn atom(x: u8) atomically (au) {} { }");
    let serial_ids = |src: &str| {
        let mut ids = Vec::new();
        perm_tup_ids(&serial(tokens(src), EraseGhost::Keep).tokens, &mut ids);
        assert!(!ids.is_empty(), "serial output names no empty perm tuple");
        // Each name is used by several generated functions.
        ids.sort();
        ids.dedup();
        assert!(ids.windows(2).all(|w| w[1] == w[0] + 1), "{:?}", ids);
        ids
    };
    let first = serial_ids(&src);
    // Parallel (n-way) runs.
    for eg in ALL_MODES {
        match crate::par_items::tests::parallel(tokens(&src), eg, crate::par_items::tests::THREADS)
        {
            Ok(_) => panic!("empty perm tuple must fall back"),
            Err(e) => assert!(e.contains("empty atomic perm tuple"), "{}", e),
        }
    }
    // Speculative runs, from a frozen file block.
    let sh = fresh(DEFAULT_MEM_CAP);
    for eg in ALL_MODES {
        speculate(sh, key(eg), "/virtual/lib.rs", block(&src));
    }
    assert_eq!(sh.counts(), (0, 0, 0, 3), "speculative runs must fail");
    let second = serial_ids(&src);
    assert_eq!(second[0], first.last().unwrap() + 1, "a worker advanced the counter");
    // A worker job that reaches the counter directly fails instead.
    let (tx, rx) = std::sync::mpsc::channel();
    let _ = wt::freeze_rejoin_main(TokenStream::new());
    assert!(pool().submit(
        Box::new(move || {
            let _job = wt::begin_job();
            let r = catch_unwind(AssertUnwindSafe(|| {
                let mut ts = TokenStream::new();
                verus_syn::PermTuple::default().to_pattern_tokens(&mut ts);
            }));
            tx.send(r.is_err()).unwrap();
        }),
        false
    ));
    assert!(rx.recv().unwrap(), "to_pattern_tokens must panic inside a worker job");
}
