//! Unit tests for the parallel `verus!` item rewrite.
//!
//! These run outside the compiler, on fallback tokens. The serial reference is
//! the serial kernel (`rewrite_items_inner2`) applied to the input parsed by the
//! production rejoin (`verus_syn::rejoin_tokens`, no freeze/thaw), and
//! the parallel side runs the real pool/freeze/thaw/replay pipeline in check mode
//! (no counter consumption); results are compared token by token, span by span.

use super::*;
use crate::syntax::{EX_IDENT_UID, Items, rewrite_items_inner2};
use std::str::FromStr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, MutexGuard, Once};

pub(crate) const THREADS: usize = 4;
pub(crate) const ALL_MODES: [EraseGhost; 3] =
    [EraseGhost::Keep, EraseGhost::Erase, EraseGhost::EraseAll];

/// Serializes the tests (shared UID counter and diagnostic recording) and sizes the
/// persistent pool before any test can create it with fewer threads.
pub(crate) fn setup() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        std::env::set_var("VSTD_KIND", "Imported");
        let _ = crate::vstd_kind();
        assert_eq!(pool(THREADS).size, THREADS, "test pool size");
    });
    LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

pub(crate) fn tokens(src: &str) -> TokenStream {
    TokenStream::from_str(src).expect("lex test input")
}

pub(crate) struct Serial {
    pub(crate) tokens: TokenStream,
    pub(crate) diags: Vec<DiagRecord>,
    pub(crate) uid_count: u64,
}

/// Serial reference. `parse_macro_input_rejoin!` needs compiler tokens, and
/// `parse2_rejoin` is crate-private to verus_syn, so this uses the same rejoin
/// buffer as two public steps: `rejoin_tokens` (`rejoin_level` at every level)
/// and the prejoined buffer (`new2_rejoin` minus `rejoin_level`).
pub(crate) fn serial(input: TokenStream, eg: EraseGhost) -> Serial {
    let mut items: Items =
        wt::parse2_prejoined(verus_syn::rejoin_tokens(input)).expect("serial parse");
    let base = EX_IDENT_UID.load(Ordering::Relaxed);
    let _record = MainRecord::start();
    let tokens = rewrite_items_inner2(&mut items.items, eg, true, false);
    let diags = MAIN_RECORD.with(|r| r.borrow_mut().take()).unwrap_or_default();
    Serial { tokens, diags, uid_count: EX_IDENT_UID.load(Ordering::Relaxed) - base }
}

pub(crate) fn parallel(
    input: TokenStream,
    eg: EraseGhost,
    threads: usize,
) -> Result<ParResult, String> {
    let _silent = SilentPanics::new();
    run_parallel_core(input, eg, true, threads, false).map(|p| commit(p, false))
}

/// Runs parallel (check mode, first, so it simulates UIDs from the current
/// counter) and serial on the same tokens and asserts identity.
fn assert_identity(src: &str, eg: EraseGhost) -> Serial {
    let input = tokens(src);
    let par = parallel(input.clone(), eg, THREADS).expect("parallel path must not fall back");
    assert!(par.tasks >= 2, "expected several tasks, got {}", par.tasks);
    let ser = serial(input, eg);
    if let Err(e) = compare_streams("", &par.tokens, &ser.tokens) {
        panic!("token mismatch: {}\nparallel: {}\nserial: {}", e, par.tokens, ser.tokens);
    }
    assert_eq!(par.tokens.to_string(), ser.tokens.to_string());
    assert_eq!(par.diags, ser.diags, "diagnostics differ");
    assert_eq!(par.uid_count, ser.uid_count, "UID allocations differ");
    ser
}

pub(crate) fn corpus(n: usize, block: impl Fn(usize) -> String) -> String {
    (0..n).map(block).collect::<Vec<_>>().join("\n")
}

pub(crate) fn general_block(i: usize) -> String {
    format!(
        r#"
        pub struct S{i} {{ pub a: u64 }}
        pub enum E{i} {{ A {{ x: u64 }}, B {{ x: u64, y: bool }} }}
        pub open spec fn f{i}(x: int) -> int {{ x + {i} }}
        proof fn p{i}(x: int) requires x > 0 ensures f{i}(x) > {i} {{ }}
        fn e{i}(x: u64) -> (r: u64) requires x < 100 ensures r == x + 1 {{
            proof {{ assert(x < 100); }}
            x + 1
        }}
        pub const C{i}: u64 = 5;
        spec const SC{i}: int = 3;
        impl S{i} {{
            pub fn get(&self) -> u64 {{ self.a }}
            pub open spec fn view(&self) -> int {{ self.a as int }}
        }}
        pub trait T{i} {{ fn m(&self) -> (r: u64) ensures r > 0; }}
        mod m{i} {{ pub fn g() {{}} spec fn h() -> bool {{ true }} }}
        pub broadcast proof fn bp{i}(x: int) ensures #[trigger] f{i}(x) == x + {i} {{ }}
        pub broadcast group grp{i} {{ bp{i} }}
        broadcast use grp{i};
        fn arith{i}(a: u8) -> (r: u8) ensures r <= 3 {{ a & 3 }}
        #[verifier::external_body]
        fn ext{i}(v: &mut Vec<u64>) {{ v.push({i}); }}
        "#
    )
}

pub(crate) fn src_general_items() -> String {
    corpus(8, general_block)
}

pub(crate) fn src_enum_synthesis_and_extension_traits() -> String {
    corpus(6, |i| {
        format!(
            r#"
        pub trait Tr{i} {{ fn f(&self) -> usize; }}
        #[verifier::external_trait_extension(TSpec{i} via TSpecImpl{i})]
        pub trait Ex{i} {{
            type ExternalTraitSpecificationFor: Tr{i};
            fn f(&self) -> (r: usize) ensures r > 7;
            spec fn s(&self) -> bool;
        }}
        pub enum En{i} {{ A {{ v: u64, w: bool }}, B {{ v: u64 }}, C(u8) }}
        fn after{i}() {{ }}
        "#
        )
    })
}

pub(crate) fn src_assume_specification_uids_and_extra_impl() -> String {
    corpus(6, |i| {
        format!(
            r#"
        pub assume_specification<T>[ core::mem::swap::<T> ](a: &mut T, b: &mut T)
            ensures *a == *old(b), *b == *old(a);
        fn user{i}(x: u64) -> u64 {{ x }}
        pub assume_specification[ core::hint::spin_loop ]();
        "#
        )
    })
}

pub(crate) fn src_deferred_diagnostics_in_serial_order() -> String {
    corpus(6, |i| {
        format!(
            r#"
        spec fn uninterp_warning{i}(x: int) -> int;
        spec fn fnspec{i}(f: FnSpec(int) -> int) -> int {{ f({i}) }}
        fn plain{i}() {{ }}
        "#
        )
    })
}

pub(crate) fn src_worker_inner_trigger_lists() -> String {
    corpus(8, |i| {
        format!(
            r#"
        pub uninterp spec fn f{i}(x: int) -> bool;
        pub uninterp spec fn g{i}(x: int) -> bool;
        proof fn t{i}()
            requires forall|x: int| #![trigger f{i}(x)] #![trigger f{i}(x), g{i}(x + 1)]
                f{i}(x) && g{i}(x + 1)
        {{
            assert(forall|x: int, y: int| #![trigger f{i}(x), g{i}(y)] f{i}(x) ==> g{i}(y));
        }}
        spec fn q{i}() -> bool {{ exists|x: int| #![trigger g{i}(x)] g{i}(x) }}
        fn e{i}() {{ }}
        "#
        )
    })
}

pub(crate) fn src_additional_items_levels() -> String {
    corpus(8, |i| {
        format!(
            r#"
        pub fn atom{i}(x: u8, y: i32) atomically (au) {{ (old: u64) -> (new: u64), }} {{ }}
        fn no_impl{i}(&self) atomically (au) {{ (o: u8) -> (n: u8), }} {{ }}
        mod am{i} {{
            pub fn inner{i}(y: u64) atomically (au) {{ (o: u8) -> (n: u8), ensures n == o, }}
            {{ }}
        }}
        pub struct S{i} {{ a: u64 }}
        "#
        )
    })
}

pub(crate) fn src_proxy_redo_discards_speculative_events() -> String {
    corpus(8, |i| {
        format!(
            r#"
        spec const SF{i}: FnSpec(int) -> int = |x: int| x + {i};
        pub const K{i}: u64 = {i};
        spec fn uses{i}(f: FnSpec(int) -> int) -> int {{ f({i}) }}
        fn plain{i}() {{ }}
        "#
        )
    })
}

pub(crate) fn src_nested_module_uids() -> String {
    corpus(6, |i| {
        format!(
            r#"
        pub assume_specification[ core::hint::spin_loop ]();
        mod um{i} {{
            pub assume_specification<T>[ core::mem::swap::<T> ](a: &mut T, b: &mut T);
            mod deep{i} {{ pub assume_specification[ core::hint::spin_loop ](); }}
            fn local{i}() {{ }}
        }}
        fn user{i}(x: u64) -> u64 {{ x }}
        "#
        )
    })
}

pub(crate) fn src_outdated_broadcast_use_warning() -> String {
    corpus(6, |i| {
        format!(
            r#"
        pub uninterp spec fn f{i}(x: int) -> int;
        pub broadcast proof fn ba{i}(x: int) ensures #[trigger] f{i}(x) == x {{ admit(); }}
        pub broadcast proof fn bb{i}(x: int) ensures #[trigger] f{i}(x) >= x {{ admit(); }}
        broadcast use ba{i}, bb{i};
        fn after{i}() {{ }}
        "#
        )
    })
}

/// Every identity corpus above (all take the parallel path in every mode).
pub(crate) const IDENTITY_CORPORA: &[(&str, fn() -> String)] = &[
    ("src_general_items", src_general_items),
    ("src_enum_synthesis_and_extension_traits", src_enum_synthesis_and_extension_traits),
    ("src_assume_specification_uids_and_extra_impl", src_assume_specification_uids_and_extra_impl),
    ("src_deferred_diagnostics_in_serial_order", src_deferred_diagnostics_in_serial_order),
    ("src_worker_inner_trigger_lists", src_worker_inner_trigger_lists),
    ("src_additional_items_levels", src_additional_items_levels),
    ("src_proxy_redo_discards_speculative_events", src_proxy_redo_discards_speculative_events),
    ("src_nested_module_uids", src_nested_module_uids),
    ("src_outdated_broadcast_use_warning", src_outdated_broadcast_use_warning),
    ("src_uid_items", src_uid_items),
];

pub(crate) fn src_uid_items() -> String {
    with_uid_items("")
}

#[test]
fn identity_general_items_all_modes() {
    let _g = setup();
    let src = src_general_items();
    for eg in ALL_MODES {
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_enum_synthesis_and_extension_traits() {
    let _g = setup();
    let src = src_enum_synthesis_and_extension_traits();
    for eg in ALL_MODES {
        // Identity also covers the serial position of the appended extension items.
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_assume_specification_uids_and_extra_impl() {
    let _g = setup();
    let src = src_assume_specification_uids_and_extra_impl();
    let ser = assert_identity(&src, EraseGhost::Keep);
    assert_eq!(ser.uid_count, 12, "one UID per assume_specification in serial order");
    for eg in [EraseGhost::Erase, EraseGhost::EraseAll] {
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_deferred_diagnostics_in_serial_order() {
    let _g = setup();
    let src = src_deferred_diagnostics_in_serial_order();
    let ser = assert_identity(&src, EraseGhost::Keep);
    assert_eq!(ser.diags.len(), 12, "two warnings per block: {:?}", ser.diags);
}

#[test]
fn single_segment_check_mode_identity() {
    let _g = setup();
    let input = tokens(&general_block(0));
    let par = parallel(input.clone(), EraseGhost::Keep, 1).expect("one task");
    assert_eq!(par.tasks, 1);
    let ser = serial(input, EraseGhost::Keep);
    compare_streams("", &par.tokens, &ser.tokens).unwrap();
}

fn assert_fallback(src: &str, eg: EraseGhost, reason: &str) {
    let base = EX_IDENT_UID.load(Ordering::Relaxed);
    match parallel(tokens(src), eg, THREADS) {
        Ok(_) => panic!("expected fallback ({})", reason),
        Err(e) => assert!(e.contains(reason), "fallback reason {:?} lacks {:?}", e, reason),
    }
    assert_eq!(EX_IDENT_UID.load(Ordering::Relaxed), base, "fallback consumed UIDs");
}

/// UID-allocating input without unerased-proxy items (whose leaked serial state
/// would make the assume_specification transform fall back first).
pub(crate) fn with_uid_items(extra: &str) -> String {
    let mut src = corpus(8, |i| {
        format!(
            "pub assume_specification[ core::hint::spin_loop ](); fn u{i}(x: u64) -> (r: u64) \
             ensures r == x {{ x }} pub struct S{i} {{ a: u64 }}"
        )
    });
    src.push_str(extra);
    src
}

#[test]
fn identity_uid_items_baseline() {
    let _g = setup();
    assert_identity(&with_uid_items(""), EraseGhost::Keep);
}

#[test]
fn fallback_prefilter_state_change_after_leaked_const_state() {
    // The serial unerased-proxy pass leaves `inside_ghost == 1` and `inside_const`
    // set after a spec const item; the assume_specification transform then changes
    // that state for later items, so the parallel path must not be used.
    let _g = setup();
    let src = format!("spec const SC: int = 3;\n{}", with_uid_items(""));
    assert_fallback(&src, EraseGhost::Keep, "changed visitor state");
}

#[test]
fn fallback_contrib_preprocessing() {
    // Every dispatched contrib preprocessor name forces serial fallback, in any
    // attribute path form `collect_attrs` accepts, on items and impl items.
    let _g = setup();
    assert!(!crate::contrib::PREPROCESSORS.is_empty());
    for (name, _, _) in crate::contrib::PREPROCESSORS {
        for attr in [name.to_string(), format!("contrib::{}", name)] {
            let item = format!("#[{attr}] fn auto(x: u64) -> u64 {{ x }}");
            assert_fallback(&with_uid_items(&item), EraseGhost::Keep, "contrib");
            let imp = format!("impl S0 {{ #[{attr}] fn auto(&self) -> u64 {{ 0 }} }}");
            assert_fallback(&with_uid_items(&imp), EraseGhost::Keep, "contrib");
        }
    }
}

#[test]
fn fallback_global_layout_item() {
    let _g = setup();
    let src = with_uid_items("global size_of usize == 8;");
    assert_fallback(&src, EraseGhost::Keep, "global layout");
}

#[test]
fn fallback_segment_parse_failure() {
    let _g = setup();
    let src = with_uid_items("fn broken() -> { }");
    assert_fallback(&src, EraseGhost::Keep, "parse");
}

#[test]
fn fallback_placeholder_marker_text() {
    let _g = setup();
    let src = with_uid_items("fn _verus_external_fn_specification_PARUID_0_0_() { }");
    assert_fallback(&src, EraseGhost::Keep, "placeholder");
}

#[test]
fn split_segments_cuts_only_at_item_boundaries() {
    let _g = setup();
    let input = tokens(&corpus(8, general_block));
    let tts: Vec<TokenTree> = input.clone().into_iter().collect();
    let segments = split_segments(&tts, 4);
    assert!(segments.len() >= 2 && segments.len() <= 4, "{} segments", segments.len());
    let mut joined = TokenStream::new();
    let mut pos = 0;
    for seg in &segments {
        assert!(!seg.is_empty());
        assert_eq!(seg.start, pos, "contiguous");
        pos = seg.end;
        joined.extend(tts[seg.clone()].iter().cloned());
    }
    assert_eq!(pos, tts.len());
    compare_streams("", &joined, &input).unwrap();
    for seg in &segments[1..] {
        assert!(is_boundary(&tts, seg.start));
        match &tts[seg.start] {
            TokenTree::Ident(id) => assert!(STARTERS.contains(&id.to_string().as_str())),
            TokenTree::Punct(p) => assert_eq!(p.as_char(), '#'),
            other => panic!("segment starts with {:?}", other),
        }
    }
    assert_eq!(split_segments(&tts, 1), vec![0..tts.len()]);
    // Balanced by source offsets: no segment holds more than half of the source.
    let base = tts[0].span().byte_range().start;
    let total = tts[tts.len() - 1].span().byte_range().end - base;
    for seg in &segments {
        let lo = tts[seg.start].span().byte_range().start;
        let hi = tts[seg.end - 1].span().byte_range().end;
        assert!((hi - lo) * 2 <= total, "unbalanced segment {:?}", seg);
    }
}

#[test]
fn split_segments_token_index_fallback_without_offsets() {
    let _g = setup();
    // Call-site spans carry no source range: balance by token index instead.
    let tts: Vec<TokenTree> = tokens(&corpus(8, general_block))
        .into_iter()
        .map(|mut tt| {
            tt.set_span(Span::call_site());
            tt
        })
        .collect();
    assert_eq!(tts[0].span().byte_range(), 0..0);
    let segments = split_segments(&tts, 4);
    assert!(segments.len() >= 2 && segments.len() <= 4, "{} segments", segments.len());
    for seg in &segments[1..] {
        assert!(is_boundary(&tts, seg.start));
        assert!(seg.start * 4 >= tts.len(), "cut {} before the first quarter", seg.start);
    }
}

#[test]
fn segment_freeze_from_trees_equals_freeze_of_segment_stream() {
    let _g = setup();
    let input = tokens(&src_general_items());
    let tts: Vec<TokenTree> = input.into_iter().collect();
    for seg in split_segments(&tts, THREADS) {
        let list = &tts[seg];
        let (a, meta_a) = wt::freeze_rejoin_main(list.iter().cloned().collect());
        let (b, meta_b) = wt::freeze_rejoin_main_trees(list);
        assert!(a.same_input(&b));
        assert_eq!(meta_a.origin_count(), meta_b.origin_count());
        compare_streams("", &meta_b.thaw(&b), &meta_a.thaw(&a)).unwrap();
    }
}

#[test]
fn config_parsing() {
    // Unset or empty: parallel by default.
    assert_eq!(parse_config(None, None, 16), (ParMode::On, 8));
    assert_eq!(parse_config(Some(""), None, 16), (ParMode::On, 8));
    assert_eq!(parse_config(Some(" "), None, 16), (ParMode::On, 8));
    // Opt-outs.
    assert_eq!(parse_config(Some("0"), None, 4), (ParMode::Off, 3));
    assert_eq!(parse_config(Some("off"), Some("5"), 4), (ParMode::Off, 5));
    assert_eq!(parse_config(Some("false"), None, 4), (ParMode::Off, 3));
    assert_eq!(parse_config(Some("1"), None, 1), (ParMode::On, 0));
    assert_eq!(parse_config(Some(" on "), Some("bogus"), 3), (ParMode::On, 2));
    assert_eq!(parse_config(Some("true"), None, 3), (ParMode::On, 2));
    assert_eq!(parse_config(Some("check"), Some("1000"), 3), (ParMode::Check, MAX_THREADS));
    // Unknown explicit values stay serial.
    assert_eq!(parse_config(Some("yes"), Some("2"), 3), (ParMode::Off, 2));
}

#[test]
fn compare_streams_detects_differences() {
    let a = tokens("fn f() { x + 1 }");
    let b = tokens("fn f() { x + 1 }");
    // Same text, different spans (second lexing has later positions).
    assert!(compare_streams("", &a, &b).is_err());
    assert!(compare_streams("", &a, &a.clone()).is_ok());
    let c: TokenStream = a.clone().into_iter().take(2).collect();
    assert!(compare_streams("", &a, &c).is_err());
}

pub(super) static INJECT_WORKER_PANIC: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

#[test]
fn fallback_worker_panic_has_no_side_effects_and_pool_survives() {
    let _g = setup();
    let src = with_uid_items("");
    INJECT_WORKER_PANIC.store(true, Ordering::SeqCst);
    let base = EX_IDENT_UID.load(Ordering::Relaxed);
    let result = parallel(tokens(&src), EraseGhost::Keep, THREADS);
    INJECT_WORKER_PANIC.store(false, Ordering::SeqCst);
    match result {
        Ok(_) => panic!("expected fallback after worker panic"),
        Err(e) => assert!(e.contains("worker panic"), "{}", e),
    }
    assert_eq!(EX_IDENT_UID.load(Ordering::Relaxed), base);
    // The persistent pool is still usable afterwards.
    assert_identity(&src, EraseGhost::Keep);
}

#[test]
fn identity_worker_inner_trigger_lists() {
    let _g = setup();
    let src = src_worker_inner_trigger_lists();
    for eg in ALL_MODES {
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_additional_items_levels() {
    // Visits append additional items (also from items nested in modules) after the
    // whole current list; they are visited as later levels in serial list order.
    let _g = setup();
    let src = src_additional_items_levels();
    for eg in ALL_MODES {
        let ser = assert_identity(&src, eg);
        let out = ser.tokens.to_string();
        assert!(out.contains("Atom0AtomicUpdatePredicate"), "{}", out);
        assert!(out.contains("_FAILED_TO_RESOLVE_SELF"), "{}", out);
    }
}

#[test]
fn fallback_empty_atomic_perm_tuple() {
    // Empty perm tuples are named from a process-global verus_syn counter.
    let _g = setup();
    let src = with_uid_items("pub fn atom(x: u8) atomically (au) {} { }");
    assert_fallback(&src, EraseGhost::Keep, "empty atomic perm tuple");
}

pub(super) static REDOS: AtomicUsize = AtomicUsize::new(0);

#[test]
fn identity_proxy_redo_discards_speculative_events() {
    // Each spec const leaves serial proxy-pass state, so every later task with
    // proxy items redoes its pass; the speculative pass's diagnostics must be
    // replaced, not replayed twice.
    let _g = setup();
    let src = src_proxy_redo_discards_speculative_events();
    let before = REDOS.load(Ordering::SeqCst);
    let ser = assert_identity(&src, EraseGhost::Keep);
    assert!(REDOS.load(Ordering::SeqCst) > before, "no proxy redo happened");
    let fnspec = ser.diags.iter().filter(|d| d.msg.contains("FnSpec")).count();
    assert!(fnspec >= 16, "FnSpec warnings: {:?}", ser.diags);
    for eg in [EraseGhost::Erase, EraseGhost::EraseAll] {
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_nested_module_uids() {
    // Top-level UIDs are requested in the prefilter, nested ones while visiting
    // the module; serial order is all top-level requests first.
    let _g = setup();
    let src = src_nested_module_uids();
    let ser = assert_identity(&src, EraseGhost::Keep);
    assert_eq!(ser.uid_count, 18, "three UIDs per block");
    for eg in [EraseGhost::Erase, EraseGhost::EraseAll] {
        assert_identity(&src, eg);
    }
}

#[test]
fn identity_outdated_broadcast_use_warning() {
    let _g = setup();
    let src = src_outdated_broadcast_use_warning();
    for eg in ALL_MODES {
        let ser = assert_identity(&src, eg);
        let warnings = ser.diags.iter().filter(|d| d.msg.contains("Outdated syntax")).count();
        let expected = if eg.erase() { 6 } else { 0 };
        assert_eq!(warnings, expected, "{:?}", ser.diags);
    }
}
