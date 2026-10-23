//! Thread-transferable token IR for parallel Verus macro expansion.
//!
//! The main thread freezes its compiler-backed input with
//! [`freeze_rejoin_main`], applying Verus operator rejoining once. A worker
//! thread inside a `proc_macro2` worker job melts the frozen IR into fallback
//! tokens, parses them with [`parse2_prejoined`], and freezes its output with
//! [`freeze_worker`]. The main thread finally thaws the worker output with
//! [`ThawMetadata::thaw`], reusing the original compiler tokens wherever the
//! worker kept them unchanged.
//!
//! Every [`freeze_rejoin_main`] call draws a fresh segment nonce shared by its
//! [`FrozenTokens`] and [`ThawMetadata`]. [`melt_worker`] binds the worker job
//! to that nonce and [`freeze_worker`] stamps it on the worker output, so
//! [`ThawMetadata::thaw`] rejects (panics on) frozen tokens of another segment
//! before building any span.
//!
//! Prefetch: a scheduler may lex a source file inside a worker job with
//! [`lex_positional`] (after [`normalize_rustc_source`]) and freeze a token
//! range of it with [`freeze_rejoin_text`] before the compiler delivers that
//! macro input. Text freezing mirrors [`freeze_rejoin_main`] exactly (traversal,
//! origin numbering, Verus operator rejoining by offset adjacency), so when the
//! real input arrives, [`ThawMetadata::adopt`] checks that both freezes agree
//! ([`FrozenTokens::same_input`]) and the returned [`Adopted`] thaws worker
//! output of the speculative segment against the real compiler tokens.
//!
//! Worker jobs need the vendored proc-macro2 (cfg `verus_proc_macro2_worker`,
//! set by build.rs). With a stock proc-macro2 this module still compiles, but
//! [`begin_job`] always panics, so callers that turn worker panics into serial
//! fallback keep working.

#[cfg(feature = "parsing")]
use crate::buffer::TokenBuffer;
#[cfg(feature = "parsing")]
use crate::parse::{Parse, ParseStream};
#[cfg(feature = "parsing")]
use crate::Result;
use alloc::string::String;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::ops::Range;
use core::sync::atomic::{AtomicU64, Ordering};
use proc_macro2::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};
use std::collections::HashMap;
pub(crate) use substrate::compiler_end_eq_start;
use substrate::{
    bind_job_nonce, ident_sym_raw, ident_unchecked, input_span, job_nonce, literal_from_repr,
    literal_repr, prepare_main_thread, release_group, span_id, span_recipe, SpanRecipe,
    WorkerSpanId,
};

pub use substrate::{
    begin_job, in_worker_job, lex_positional, normalize_rustc_source, LexError, LexedFile,
    LexedKind, LexedTok, WorkerJob,
};

/// Whether worker jobs can run (the vendored proc-macro2 is in use).
pub const WORKER_JOBS_AVAILABLE: bool = cfg!(verus_proc_macro2_worker);

#[cfg(verus_proc_macro2_worker)]
mod substrate {
    pub use proc_macro2::__verus_worker::*;
}

// Degraded substrate for a stock proc-macro2: no job can ever start, so every
// job-only operation is unreachable.
#[cfg(not(verus_proc_macro2_worker))]
#[allow(dead_code, missing_docs, clippy::needless_pass_by_value)]
mod substrate {
    use alloc::string::String;
    use alloc::vec::Vec;
    use core::marker::PhantomData;
    use core::ops::Range;
    use proc_macro2::{Delimiter, Ident, Literal, Spacing, Span};

    // Same plain data as `proc_macro2::__verus_worker`'s positional lexer.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub enum LexedKind {
        Group { delim: Delimiter, len: u32 },
        Ident { text: String, raw: bool },
        Punct { ch: char, spacing: Spacing },
        Literal { repr: String },
    }
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct LexedTok {
        pub kind: LexedKind,
        pub lo: u32,
        pub hi: u32,
    }
    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct LexedFile {
        pub toks: Vec<LexedTok>,
        pub non_ascii_idents: Vec<u32>,
    }
    impl LexedFile {
        pub fn has_non_ascii_ident_in(&self, range: Range<usize>) -> bool {
            self.non_ascii_idents
                .iter()
                .any(|&i| range.contains(&(i as usize)))
        }
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub struct LexError {
        pub offset: u32,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct WorkerSpanId(u32);

    impl WorkerSpanId {
        pub const CALL_SITE: WorkerSpanId = WorkerSpanId(0);
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum SpanRecipe {
        CallSite,
        MixedSite,
        Input(u32),
        ResolvedAt {
            span: WorkerSpanId,
            at: WorkerSpanId,
        },
        LocatedAt {
            span: WorkerSpanId,
            at: WorkerSpanId,
        },
        JoinOrFirst {
            first: WorkerSpanId,
            second: WorkerSpanId,
        },
    }

    #[must_use]
    pub struct WorkerJob {
        _not_send_sync: PhantomData<*const ()>,
    }

    impl WorkerJob {
        pub fn end(self) {}
    }

    #[track_caller]
    fn unavailable() -> ! {
        panic!("verus_syn::worker_tokens: worker jobs need the Verus-vendored proc-macro2")
    }

    pub fn begin_job() -> WorkerJob {
        unavailable()
    }
    pub fn in_worker_job() -> bool {
        false
    }
    pub fn prepare_main_thread() -> bool {
        false
    }
    pub fn bind_job_nonce(_: u64) {
        unavailable()
    }
    pub fn job_nonce() -> Option<u64> {
        unavailable()
    }
    pub fn input_span(_: u32) -> Span {
        unavailable()
    }
    pub fn span_id(_: Span) -> WorkerSpanId {
        unavailable()
    }
    pub fn span_recipe(_: WorkerSpanId) -> SpanRecipe {
        unavailable()
    }
    pub fn ident_unchecked(_: &str, _: bool, _: Span) -> Ident {
        unavailable()
    }
    pub fn ident_sym_raw(_: &Ident) -> (&str, bool) {
        unavailable()
    }
    pub fn literal_from_repr(_: &str, _: Span) -> Literal {
        unavailable()
    }
    pub fn literal_repr(_: &Literal) -> &str {
        unavailable()
    }
    pub fn lex_positional(_: &str) -> Result<LexedFile, LexError> {
        unavailable()
    }
    pub fn normalize_rustc_source(_: &str) -> String {
        unavailable()
    }
    pub fn release_group(group: proc_macro2::Group) {
        drop(group);
    }
    pub fn compiler_end_eq_start(_: Span, _: Span) -> bool {
        false
    }
}

/// Source of nonzero, process-unique segment nonces.
static NEXT_NONCE: AtomicU64 = AtomicU64::new(1);

fn fresh_nonce() -> u64 {
    loop {
        let nonce = NEXT_NONCE.fetch_add(1, Ordering::Relaxed);
        if nonce != 0 {
            return nonce;
        }
    }
}

// A compact span reference. Values below `RECIPE_TAG` are direct main-thread
// input span ids; values with `RECIPE_TAG` set index the recipe table, except
// `CALL_SITE_REF`, which denotes `Span::call_site()`.
type SpanRef = u32;
const RECIPE_TAG: u32 = 1 << 31;
const CALL_SITE_REF: SpanRef = u32::MAX;

fn input_ref(id: u32) -> SpanRef {
    assert!(id < RECIPE_TAG, "worker_tokens: input span id overflow");
    id
}

fn recipe_ref(index: usize) -> SpanRef {
    assert!(
        index < (RECIPE_TAG - 1) as usize,
        "worker_tokens: span recipe table overflow"
    );
    index as u32 | RECIPE_TAG
}

// Derived span recipe; children are input refs, `CALL_SITE_REF`, or earlier recipes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum FrozenRecipe {
    MixedSite,
    ResolvedAt { span: SpanRef, at: SpanRef },
    LocatedAt { span: SpanRef, at: SpanRef },
    JoinOrFirst { first: SpanRef, second: SpanRef },
}

// One preorder token node. `Group::len` counts the nodes of its subtree, excluding
// the group node itself. Text ranges index `FrozenTokens::text`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Node {
    Group {
        delimiter: Delimiter,
        span: SpanRef,
        len: u32,
    },
    Ident {
        start: u32,
        end: u32,
        raw: bool,
        span: SpanRef,
    },
    Punct {
        ch: char,
        spacing: Spacing,
        span: SpanRef,
    },
    Literal {
        start: u32,
        end: u32,
        span: SpanRef,
    },
}

/// Compact, thread-transferable token trees without compiler handles.
#[derive(Clone, Debug)]
pub struct FrozenTokens {
    nodes: Arc<[Node]>,
    text: Arc<str>,
    recipes: Arc<[FrozenRecipe]>,
    // Segment nonce; 0 only for tokens without input span references.
    nonce: u64,
    // Whether any node or recipe references a main-thread input span id.
    has_input: bool,
    // Number of input origins of an input freeze (one per node); 0 for worker output.
    origin_count: u32,
}

impl Default for FrozenTokens {
    fn default() -> Self {
        FrozenTokens {
            nodes: Arc::from(Vec::new()),
            text: Arc::from(""),
            recipes: Arc::from(Vec::new()),
            nonce: 0,
            has_input: false,
            origin_count: 0,
        }
    }
}

impl FrozenTokens {
    /// Returns true if the frozen stream has no tokens.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Returns the number of token nodes, counting every nested token.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Approximate heap footprint in bytes: the node table, the text arena,
    /// and the span recipe table.
    pub fn heap_bytes(&self) -> usize {
        core::mem::size_of::<Node>() * self.nodes.len()
            + self.text.len()
            + core::mem::size_of::<FrozenRecipe>() * self.recipes.len()
    }

    fn text_at(&self, start: u32, end: u32) -> &str {
        &self.text[start as usize..end as usize]
    }

    /// Whether both freezes have the same token IR (nodes, text, recipes),
    /// ignoring their segment nonces.
    pub fn same_input(&self, other: &FrozenTokens) -> bool {
        self.has_input == other.has_input
            && *self.nodes == *other.nodes
            && *self.text == *other.text
            && *self.recipes == *other.recipes
    }

    /// Deterministic hash of the IR compared by [`FrozenTokens::same_input`]
    /// (equal for same-input freezes, stable across threads and processes).
    pub fn input_hash(&self) -> u64 {
        let mut h = WordHash::new();
        h.write_u64(self.has_input as u64);
        h.write_u64(self.nodes.len() as u64);
        for node in self.nodes.iter() {
            let (head, tail) = match *node {
                Node::Group {
                    delimiter,
                    span,
                    len,
                } => (
                    delimiter_code(delimiter) << 8,
                    (span as u64) | (len as u64) << 32,
                ),
                Node::Ident {
                    start,
                    end,
                    raw,
                    span,
                } => (
                    1 | (raw as u64) << 8 | (span as u64) << 32,
                    (start as u64) | (end as u64) << 32,
                ),
                Node::Punct { ch, spacing, span } => (
                    2 | ((spacing == Spacing::Joint) as u64) << 8 | (span as u64) << 32,
                    ch as u64,
                ),
                Node::Literal { start, end, span } => {
                    (3 | (span as u64) << 32, (start as u64) | (end as u64) << 32)
                }
            };
            h.write_u64(head);
            h.write_u64(tail);
        }
        h.write_u64(self.text.len() as u64);
        h.write_bytes(self.text.as_bytes());
        h.write_u64(self.recipes.len() as u64);
        for recipe in self.recipes.iter() {
            let (tag, a, b) = match *recipe {
                FrozenRecipe::MixedSite => (0, 0, 0),
                FrozenRecipe::ResolvedAt { span, at } => (1, span, at),
                FrozenRecipe::LocatedAt { span, at } => (2, span, at),
                FrozenRecipe::JoinOrFirst { first, second } => (3, first, second),
            };
            h.write_u64(tag);
            h.write_u64((a as u64) | (b as u64) << 32);
        }
        h.0
    }
}

fn delimiter_code(delimiter: Delimiter) -> u64 {
    match delimiter {
        Delimiter::Parenthesis => 0,
        Delimiter::Brace => 1,
        Delimiter::Bracket => 2,
        Delimiter::None => 3,
    }
}

// Deterministic word-at-a-time multiplicative hash (no per-process seed).
struct WordHash(u64);

impl WordHash {
    fn new() -> Self {
        WordHash(0xcbf2_9ce4_8422_2325)
    }

    fn write_u64(&mut self, v: u64) {
        self.0 = (self.0.rotate_left(5) ^ v).wrapping_mul(0x517c_c1b7_2722_0a95);
    }

    // Callers write the length first, so zero padding of the tail is unambiguous.
    fn write_bytes(&mut self, bytes: &[u8]) {
        let mut chunks = bytes.chunks_exact(8);
        for chunk in &mut chunks {
            let mut word = [0u8; 8];
            word.copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(word));
        }
        let rest = chunks.remainder();
        if !rest.is_empty() {
            let mut word = [0u8; 8];
            word[..rest.len()].copy_from_slice(rest);
            self.write_u64(u64::from_le_bytes(word));
        }
    }
}

#[allow(dead_code)]
fn assert_frozen_tokens_send_sync() {
    fn check<T: Send + Sync>() {}
    check::<FrozenTokens>();
}

// Original compiler token for one main-thread input span id.
enum OriginToken {
    Other,
    Ident {
        ident: Ident,
        start: u32,
        end: u32,
        raw: bool,
    },
    Literal {
        literal: Literal,
        start: u32,
        end: u32,
    },
}

struct Origin {
    span: Span,
    token: OriginToken,
}

/// Main-thread metadata mapping frozen input span ids back to compiler tokens.
pub struct ThawMetadata {
    origins: Vec<Origin>,
    text: Arc<str>,
    nonce: u64,
}

struct Builder {
    nodes: Vec<Node>,
    text: String,
    recipes: Vec<FrozenRecipe>,
    has_input: bool,
}

impl Builder {
    fn new() -> Self {
        Builder {
            nodes: Vec::new(),
            text: String::new(),
            recipes: Vec::new(),
            has_input: false,
        }
    }

    // Records the use of `span`; returns it unchanged.
    fn use_span(&mut self, span: SpanRef) -> SpanRef {
        if span & RECIPE_TAG == 0 {
            self.has_input = true;
        }
        span
    }

    fn push_text(&mut self, s: &str) -> (u32, u32) {
        let start = self.text.len();
        self.text.push_str(s);
        let end = self.text.len();
        assert!(
            end <= u32::MAX as usize,
            "worker_tokens: text arena overflow"
        );
        (start as u32, end as u32)
    }

    // Writes the `Display` text of `value` into the arena.
    fn push_display(&mut self, value: &dyn core::fmt::Display) -> (u32, u32) {
        use core::fmt::Write as _;
        let start = self.text.len();
        write!(self.text, "{}", value).expect("worker_tokens: Display failed");
        let end = self.text.len();
        assert!(
            end <= u32::MAX as usize,
            "worker_tokens: text arena overflow"
        );
        (start as u32, end as u32)
    }

    // Writes an identifier's symbol (its `Display` text without `r#`) into the
    // arena; returns its range and rawness.
    fn push_ident_display(&mut self, ident: &Ident) -> (u32, u32, bool) {
        let (start, end) = self.push_display(ident);
        let raw = self.text[start as usize..].starts_with("r#");
        if raw {
            self.text
                .replace_range(start as usize..start as usize + 2, "");
            (start, end - 2, true)
        } else {
            (start, end, false)
        }
    }

    fn begin_group(&mut self, delimiter: Delimiter, span: SpanRef) -> usize {
        let span = self.use_span(span);
        let index = self.nodes.len();
        self.nodes.push(Node::Group {
            delimiter,
            span,
            len: 0,
        });
        index
    }

    fn end_group(&mut self, index: usize) {
        let subtree = self.nodes.len() - index - 1;
        assert!(subtree <= u32::MAX as usize, "worker_tokens: node overflow");
        if let Node::Group { len, .. } = &mut self.nodes[index] {
            *len = subtree as u32;
        }
    }

    fn finish(self, nonce: u64, origin_count: usize) -> FrozenTokens {
        let origin_count =
            u32::try_from(origin_count).expect("worker_tokens: origin count overflow");
        FrozenTokens {
            nodes: Arc::from(self.nodes),
            text: Arc::from(self.text),
            recipes: Arc::from(self.recipes),
            nonce,
            has_input: self.has_input,
            origin_count,
        }
    }
}

/// Rejoins Verus operators like `rejoin_tokens` and freezes the result.
///
/// Must be called on the main thread outside a worker job. It also runs
/// proc-macro2's backend detection on this thread, before any worker job.
pub fn freeze_rejoin_main(stream: TokenStream) -> (FrozenTokens, ThawMetadata) {
    let mut freezer = MainFreezer::start("freeze_rejoin_main");
    freezer.freeze_level(stream);
    freezer.finish()
}

/// [`freeze_rejoin_main`] of the stream of `trees`, without building that
/// stream: the result equals `freeze_rejoin_main(trees.iter().cloned().collect())`
/// on fallback tokens, and freezes exactly the given compiler trees (no
/// re-lowering of a rebuilt stream) on compiler tokens.
pub fn freeze_rejoin_main_trees(trees: &[TokenTree]) -> (FrozenTokens, ThawMetadata) {
    let mut freezer = MainFreezer::start("freeze_rejoin_main_trees");
    let mut tokens: Vec<MainTok> = trees.iter().map(MainTok::Borrowed).collect();
    crate::verus::rejoin_core(&mut tokens);
    freezer.builder.nodes.reserve(tokens.len());
    for tok in &tokens {
        let tree = match tok {
            MainTok::Borrowed(tree) => tree,
            MainTok::Owned(tree) => tree,
        };
        freezer.freeze_tree(tree);
    }
    freezer.finish()
}

/// Releases main-thread trees whose freeze is done, skipping the compiler
/// bridge's per-group drop requests (see [`freeze_rejoin_main`]).
pub fn release_main_trees(trees: Vec<TokenTree>) {
    for tree in trees {
        if let TokenTree::Group(group) = tree {
            release_group(group);
        }
    }
}

// A top-level token of `freeze_rejoin_main_trees`: an input tree, or a token
// replaced by rejoining (a joint punct or a folded `isnt`/`hasnt`).
enum MainTok<'a> {
    Borrowed(&'a TokenTree),
    Owned(TokenTree),
}

impl MainTok<'_> {
    fn tree(&self) -> &TokenTree {
        match self {
            MainTok::Borrowed(tree) => tree,
            MainTok::Owned(tree) => tree,
        }
    }
}

// Delegates to the `TokenTree` adapter, so rejoining is the same as on owned trees.
impl crate::verus::RejoinTok for MainTok<'_> {
    fn punct(&self) -> Option<(char, Spacing)> {
        self.tree().punct()
    }
    fn fold_target(&self) -> Option<&'static str> {
        self.tree().fold_target()
    }
    fn adjacent(&self, next: &Self) -> bool {
        self.tree().adjacent(next.tree())
    }
    fn make_joint(&mut self) {
        if let TokenTree::Punct(_) = self.tree() {
            let mut tree = self.tree().clone();
            tree.make_joint();
            *self = MainTok::Owned(tree);
        }
    }
    fn folded(&self, next: &Self, joined: &'static str) -> Self {
        MainTok::Owned(self.tree().folded(next.tree(), joined))
    }
}

struct MainFreezer {
    builder: Builder,
    origins: Vec<Origin>,
    // Reusable per-level token buffers.
    scratch: Vec<Vec<TokenTree>>,
}

impl MainFreezer {
    fn start(what: &str) -> MainFreezer {
        assert!(!in_worker_job(), "{} called inside a worker job", what);
        let _ = prepare_main_thread();
        MainFreezer {
            builder: Builder::new(),
            origins: Vec::new(),
            scratch: Vec::new(),
        }
    }

    fn finish(self) -> (FrozenTokens, ThawMetadata) {
        let nonce = fresh_nonce();
        let frozen = self.builder.finish(nonce, self.origins.len());
        let metadata = ThawMetadata {
            origins: self.origins,
            text: frozen.text.clone(),
            nonce,
        };
        (frozen, metadata)
    }

    fn push_origin(&mut self, span: Span, token: OriginToken) -> SpanRef {
        let id = u32::try_from(self.origins.len()).unwrap_or(RECIPE_TAG);
        let span_ref = input_ref(id);
        self.origins.push(Origin { span, token });
        span_ref
    }

    fn freeze_level(&mut self, stream: TokenStream) {
        let mut tokens = self.scratch.pop().unwrap_or_default();
        tokens.extend(stream);
        crate::verus::rejoin_level(&mut tokens);
        self.builder.nodes.reserve(tokens.len());
        for tt in tokens.drain(..) {
            self.freeze_tree(&tt);
            // The group's subtree is frozen; its compiler handle is not needed.
            if let TokenTree::Group(group) = tt {
                release_group(group);
            }
        }
        self.scratch.push(tokens);
    }

    fn freeze_tree(&mut self, tt: &TokenTree) {
        match tt {
            TokenTree::Group(group) => {
                // The serial path normalizes open/close spans to the whole span.
                let span = self.push_origin(group.span(), OriginToken::Other);
                let index = self.builder.begin_group(group.delimiter(), span);
                self.freeze_level(group.stream());
                self.builder.end_group(index);
            }
            TokenTree::Ident(ident) => {
                let (start, end, raw) = self.builder.push_ident_display(ident);
                let token = OriginToken::Ident {
                    ident: ident.clone(),
                    start,
                    end,
                    raw,
                };
                let span = self.push_origin(ident.span(), token);
                let span = self.builder.use_span(span);
                self.builder.nodes.push(Node::Ident {
                    start,
                    end,
                    raw,
                    span,
                });
            }
            TokenTree::Punct(punct) => {
                let span = self.push_origin(punct.span(), OriginToken::Other);
                let span = self.builder.use_span(span);
                self.builder.nodes.push(Node::Punct {
                    ch: punct.as_char(),
                    spacing: punct.spacing(),
                    span,
                });
            }
            TokenTree::Literal(literal) => {
                let (start, end) = self.builder.push_display(literal);
                let token = OriginToken::Literal {
                    literal: literal.clone(),
                    start,
                    end,
                };
                let span = self.push_origin(literal.span(), token);
                let span = self.builder.use_span(span);
                self.builder.nodes.push(Node::Literal { start, end, span });
            }
        }
    }
}

/// Freezes the lexed tokens `file.toks[range]` like [`freeze_rejoin_main`]
/// freezes the compiler tokens of the same text, under a fresh segment nonce.
///
/// `range` must consist of whole sibling subtrees (for example `0..len`, or
/// the contents `i + 1..i + 1 + len` of a group at `i`); otherwise this panics.
/// Verus operators are rejoined with byte-offset adjacency in place of span
/// adjacency. Origin numbering is the same preorder as `freeze_rejoin_main`,
/// so an equal input gives an IR that [`FrozenTokens::same_input`] accepts.
/// Callers should skip ranges with non-ASCII identifiers
/// ([`LexedFile::has_non_ascii_ident_in`]), whose rustc text is NFC-normalized.
///
/// Touches no `Span` and may run on any thread, inside or outside a job.
pub fn freeze_rejoin_text(file: &LexedFile, range: Range<usize>) -> FrozenTokens {
    assert!(
        range.start <= range.end && range.end <= file.toks.len(),
        "freeze_rejoin_text: range {:?} out of bounds for {} tokens",
        range,
        file.toks.len()
    );
    let mut builder = Builder::new();
    let mut origins = 0usize;
    freeze_text_level(&mut builder, &mut origins, file, range);
    builder.finish(fresh_nonce(), origins)
}

// One lexed token of a level during offset-adjacency rejoining.
#[derive(Clone, Copy)]
struct TextTok {
    // Index into `LexedFile::toks`.
    index: usize,
    lo: u32,
    hi: u32,
    // Current char and spacing of a punct; `None` otherwise.
    punct: Option<(char, Spacing)>,
    // `isnt`/`hasnt` for a non-raw `is`/`has` identifier.
    fold_target: Option<&'static str>,
    // Text of an identifier folded from `!is`/`!has`.
    folded: Option<&'static str>,
}

impl crate::verus::RejoinTok for TextTok {
    fn punct(&self) -> Option<(char, Spacing)> {
        self.punct
    }
    fn fold_target(&self) -> Option<&'static str> {
        self.fold_target
    }
    fn adjacent(&self, next: &Self) -> bool {
        self.hi == next.lo
    }
    fn make_joint(&mut self) {
        if let Some((_, spacing)) = &mut self.punct {
            *spacing = Spacing::Joint;
        }
    }
    fn folded(&self, next: &Self, joined: &'static str) -> Self {
        TextTok {
            index: self.index,
            lo: self.lo,
            hi: next.hi,
            punct: None,
            fold_target: None,
            folded: Some(joined),
        }
    }
}

fn subtree_end(file: &LexedFile, index: usize) -> usize {
    match file.toks[index].kind {
        LexedKind::Group { len, .. } => index + 1 + len as usize,
        _ => index + 1,
    }
}

// Mirrors `freeze_main_level`: rejoin one level, then push one origin per token
// in preorder.
fn freeze_text_level(
    builder: &mut Builder,
    origins: &mut usize,
    file: &LexedFile,
    range: Range<usize>,
) {
    let mut tokens: Vec<TextTok> = Vec::new();
    let mut i = range.start;
    while i < range.end {
        let tok = &file.toks[i];
        let (punct, fold_target) = match &tok.kind {
            LexedKind::Punct { ch, spacing } => (Some((*ch, *spacing)), None),
            LexedKind::Ident { text, raw: false } if text == "is" => (None, Some("isnt")),
            LexedKind::Ident { text, raw: false } if text == "has" => (None, Some("hasnt")),
            _ => (None, None),
        };
        tokens.push(TextTok {
            index: i,
            lo: tok.lo,
            hi: tok.hi,
            punct,
            fold_target,
            folded: None,
        });
        i = subtree_end(file, i);
    }
    assert!(
        i == range.end,
        "freeze_rejoin_text: range {:?} splits a group",
        range
    );
    crate::verus::rejoin_core(&mut tokens);
    builder.nodes.reserve(tokens.len());
    for tt in tokens {
        let span = input_ref(u32::try_from(*origins).unwrap_or(RECIPE_TAG));
        *origins += 1;
        let span = builder.use_span(span);
        if let Some(joined) = tt.folded {
            let (start, end) = builder.push_text(joined);
            builder.nodes.push(Node::Ident {
                start,
                end,
                raw: false,
                span,
            });
            continue;
        }
        match &file.toks[tt.index].kind {
            LexedKind::Group { delim, len } => {
                let index = builder.begin_group(*delim, span);
                let inner = tt.index + 1..tt.index + 1 + *len as usize;
                freeze_text_level(builder, origins, file, inner);
                builder.end_group(index);
            }
            LexedKind::Ident { text, raw } => {
                let (start, end) = builder.push_text(text);
                builder.nodes.push(Node::Ident {
                    start,
                    end,
                    raw: *raw,
                    span,
                });
            }
            LexedKind::Punct { .. } => {
                let (ch, spacing) = tt.punct.unwrap();
                builder.nodes.push(Node::Punct { ch, spacing, span });
            }
            LexedKind::Literal { repr } => {
                let (start, end) = builder.push_text(repr);
                builder.nodes.push(Node::Literal { start, end, span });
            }
        }
    }
}

/// Rebuilds fallback tokens from frozen IR inside a worker job, binding the job
/// to the segment of `frozen` (a job serves exactly one segment).
pub fn melt_worker(frozen: &FrozenTokens) -> TokenStream {
    assert!(in_worker_job(), "melt_worker called outside a worker job");
    if frozen.has_input {
        assert!(
            frozen.nonce != 0,
            "melt_worker: frozen tokens reference input spans without a segment"
        );
        bind_job_nonce(frozen.nonce);
    }
    let mut spans: Vec<Span> = Vec::with_capacity(frozen.recipes.len());
    for recipe in frozen.recipes.iter() {
        let span = match *recipe {
            FrozenRecipe::MixedSite => Span::mixed_site(),
            FrozenRecipe::ResolvedAt { span, at } => {
                melt_span(&spans, span).resolved_at(melt_span(&spans, at))
            }
            FrozenRecipe::LocatedAt { span, at } => {
                melt_span(&spans, span).located_at(melt_span(&spans, at))
            }
            FrozenRecipe::JoinOrFirst { first, second } => {
                let first = melt_span(&spans, first);
                first.join(melt_span(&spans, second)).unwrap_or(first)
            }
        };
        spans.push(span);
    }
    melt_range(frozen, &spans, 0, frozen.nodes.len())
}

fn melt_span(recipe_spans: &[Span], span: SpanRef) -> Span {
    if span == CALL_SITE_REF {
        Span::call_site()
    } else if span & RECIPE_TAG != 0 {
        recipe_spans[(span & !RECIPE_TAG) as usize]
    } else {
        input_span(span)
    }
}

fn melt_range(frozen: &FrozenTokens, spans: &[Span], mut i: usize, end: usize) -> TokenStream {
    let mut trees: Vec<TokenTree> = Vec::new();
    while i < end {
        match frozen.nodes[i] {
            Node::Group {
                delimiter,
                span,
                len,
            } => {
                let inner_end = i + 1 + len as usize;
                let stream = melt_range(frozen, spans, i + 1, inner_end);
                let mut group = Group::new(delimiter, stream);
                group.set_span(melt_span(spans, span));
                trees.push(TokenTree::Group(group));
                i = inner_end;
            }
            Node::Ident {
                start,
                end,
                raw,
                span,
            } => {
                let sym = frozen.text_at(start, end);
                trees.push(TokenTree::Ident(ident_unchecked(
                    sym,
                    raw,
                    melt_span(spans, span),
                )));
                i += 1;
            }
            Node::Punct { ch, spacing, span } => {
                let mut punct = Punct::new(ch, spacing);
                punct.set_span(melt_span(spans, span));
                trees.push(TokenTree::Punct(punct));
                i += 1;
            }
            Node::Literal { start, end, span } => {
                let repr = frozen.text_at(start, end);
                trees.push(TokenTree::Literal(literal_from_repr(
                    repr,
                    melt_span(spans, span),
                )));
                i += 1;
            }
        }
    }
    TokenStream::from_iter(trees)
}

/// Freezes fallback tokens produced inside a worker job, stamping them with the
/// segment nonce bound by [`melt_worker`].
pub fn freeze_worker(stream: TokenStream) -> FrozenTokens {
    assert!(in_worker_job(), "freeze_worker called outside a worker job");
    let mut freezer = WorkerFreezer {
        builder: Builder::new(),
        memo: HashMap::new(),
        recipe_refs: HashMap::new(),
    };
    freezer.freeze_level(stream);
    let nonce = job_nonce().unwrap_or(0);
    assert!(
        nonce != 0 || !freezer.builder.has_input,
        "freeze_worker: output references input spans but the job melted no segment"
    );
    freezer.builder.finish(nonce, 0)
}

struct WorkerFreezer {
    builder: Builder,
    memo: HashMap<WorkerSpanId, SpanRef>,
    // Structural dedupe: equal recipes thaw to equal spans, so each is stored once.
    recipe_refs: HashMap<FrozenRecipe, SpanRef>,
}

impl WorkerFreezer {
    fn lookup(&self, id: WorkerSpanId) -> Option<SpanRef> {
        if id == WorkerSpanId::CALL_SITE {
            Some(CALL_SITE_REF)
        } else {
            self.memo.get(&id).copied()
        }
    }

    fn push_recipe(&mut self, recipe: FrozenRecipe) -> SpanRef {
        if let Some(&span) = self.recipe_refs.get(&recipe) {
            return span;
        }
        match recipe {
            FrozenRecipe::MixedSite => {}
            FrozenRecipe::ResolvedAt { span: a, at: b }
            | FrozenRecipe::LocatedAt { span: a, at: b }
            | FrozenRecipe::JoinOrFirst {
                first: a,
                second: b,
            } => {
                self.builder.use_span(a);
                self.builder.use_span(b);
            }
        }
        let span = recipe_ref(self.builder.recipes.len());
        self.builder.recipes.push(recipe);
        self.recipe_refs.insert(recipe, span);
        span
    }

    // Exports the recipe DAG of one span iteratively; children have smaller ids.
    fn export_span(&mut self, span: Span) -> SpanRef {
        let root = span_id(span);
        if let Some(span) = self.lookup(root) {
            return span;
        }
        let mut stack = alloc::vec![root];
        while let Some(&top) = stack.last() {
            if self.lookup(top).is_some() {
                stack.pop();
                continue;
            }
            let (a, b) = match span_recipe(top) {
                SpanRecipe::CallSite => {
                    self.memo.insert(top, CALL_SITE_REF);
                    stack.pop();
                    continue;
                }
                SpanRecipe::Input(id) => {
                    self.memo.insert(top, input_ref(id));
                    stack.pop();
                    continue;
                }
                SpanRecipe::MixedSite => {
                    let span = self.push_recipe(FrozenRecipe::MixedSite);
                    self.memo.insert(top, span);
                    stack.pop();
                    continue;
                }
                SpanRecipe::ResolvedAt { span, at } | SpanRecipe::LocatedAt { span, at } => {
                    (span, at)
                }
                SpanRecipe::JoinOrFirst { first, second } => (first, second),
            };
            match (self.lookup(a), self.lookup(b)) {
                (Some(a), Some(b)) => {
                    let recipe = match span_recipe(top) {
                        SpanRecipe::ResolvedAt { .. } => {
                            FrozenRecipe::ResolvedAt { span: a, at: b }
                        }
                        SpanRecipe::LocatedAt { .. } => FrozenRecipe::LocatedAt { span: a, at: b },
                        _ => FrozenRecipe::JoinOrFirst {
                            first: a,
                            second: b,
                        },
                    };
                    let span = self.push_recipe(recipe);
                    self.memo.insert(top, span);
                    stack.pop();
                }
                (a_ref, b_ref) => {
                    if a_ref.is_none() {
                        stack.push(a);
                    }
                    if b_ref.is_none() {
                        stack.push(b);
                    }
                }
            }
        }
        self.lookup(root).unwrap()
    }

    fn freeze_level(&mut self, stream: TokenStream) {
        for tt in stream {
            match tt {
                TokenTree::Group(group) => {
                    let span = self.export_span(group.span());
                    let index = self.builder.begin_group(group.delimiter(), span);
                    self.freeze_level(group.stream());
                    self.builder.end_group(index);
                }
                TokenTree::Ident(ident) => {
                    let span = self.export_span(ident.span());
                    let span = self.builder.use_span(span);
                    let (sym, raw) = ident_sym_raw(&ident);
                    let (start, end) = self.builder.push_text(sym);
                    self.builder.nodes.push(Node::Ident {
                        start,
                        end,
                        raw,
                        span,
                    });
                }
                TokenTree::Punct(punct) => {
                    let span = self.export_span(punct.span());
                    let span = self.builder.use_span(span);
                    self.builder.nodes.push(Node::Punct {
                        ch: punct.as_char(),
                        spacing: punct.spacing(),
                        span,
                    });
                }
                TokenTree::Literal(literal) => {
                    let span = self.export_span(literal.span());
                    let span = self.builder.use_span(span);
                    let (start, end) = self.builder.push_text(literal_repr(&literal));
                    self.builder.nodes.push(Node::Literal { start, end, span });
                }
            }
        }
    }
}

/// Real thaw metadata adopted for the worker output of a speculative segment
/// (see [`ThawMetadata::adopt`]).
pub struct Adopted<'a> {
    meta: &'a ThawMetadata,
    spec_nonce: u64,
}

impl Adopted<'_> {
    /// Nonce of the adopted speculative segment.
    pub fn spec_nonce(&self) -> u64 {
        self.spec_nonce
    }

    /// Like [`ThawMetadata::thaw`], but also accepts frozen tokens stamped with
    /// the speculative segment's nonce, resolving their input span ids to the
    /// real compiler tokens.
    pub fn thaw(&self, frozen: &FrozenTokens) -> TokenStream {
        self.meta.thaw_accepting(frozen, Some(self.spec_nonce))
    }
}

impl ThawMetadata {
    /// Number of input origins (frozen input span ids).
    pub fn origin_count(&self) -> usize {
        self.origins.len()
    }

    /// Span of the first input origin: the span of the first input token (for a
    /// folded leading `!is`/`!has`, its join, which starts at the same place).
    pub fn first_span(&self) -> Option<Span> {
        self.origins.first().map(|origin| origin.span)
    }

    /// Adopts the speculative freeze `spec` (from [`freeze_rejoin_text`]) for
    /// this real metadata, given the real frozen tokens `real` returned with
    /// it by [`freeze_rejoin_main`].
    ///
    /// Returns `None` unless `real` belongs to this metadata's segment, `spec`
    /// has a segment, both have the same IR ([`FrozenTokens::same_input`]), and
    /// both have this metadata's origin count. Main thread only.
    pub fn adopt(&self, real: &FrozenTokens, spec: &FrozenTokens) -> Option<Adopted<'_>> {
        assert!(
            !in_worker_job(),
            "ThawMetadata::adopt called inside a worker job"
        );
        let origins = self.origins.len();
        let adoptable = real.nonce == self.nonce
            && spec.nonce != 0
            && real.origin_count as usize == origins
            && spec.origin_count as usize == origins
            && real.same_input(spec);
        if adoptable {
            Some(Adopted {
                meta: self,
                spec_nonce: spec.nonce,
            })
        } else {
            None
        }
    }

    /// Rebuilds main-thread tokens from frozen IR, reusing unchanged originals.
    ///
    /// Panics, before building any token, unless `frozen` comes from this
    /// metadata's segment (or references no input span and has no segment).
    pub fn thaw(&self, frozen: &FrozenTokens) -> TokenStream {
        self.thaw_accepting(frozen, None)
    }

    fn thaw_accepting(&self, frozen: &FrozenTokens, spec_nonce: Option<u64>) -> TokenStream {
        assert!(
            !in_worker_job(),
            "ThawMetadata::thaw called inside a worker job"
        );
        let accepted = frozen.nonce == self.nonce
            || Some(frozen.nonce) == spec_nonce
            || (frozen.nonce == 0 && !frozen.has_input);
        if !accepted {
            match spec_nonce {
                None => panic!(
                    "ThawMetadata::thaw: frozen tokens of segment {} do not belong to segment {}",
                    frozen.nonce, self.nonce
                ),
                Some(spec) => panic!(
                    "Adopted::thaw: frozen tokens of segment {} do not belong to segment {} (adopted {})",
                    frozen.nonce, self.nonce, spec
                ),
            }
        }
        let mut spans: Vec<Span> = Vec::with_capacity(frozen.recipes.len());
        for recipe in frozen.recipes.iter() {
            let span = match *recipe {
                FrozenRecipe::MixedSite => Span::mixed_site(),
                FrozenRecipe::ResolvedAt { span, at } => {
                    self.span(&spans, span).resolved_at(self.span(&spans, at))
                }
                FrozenRecipe::LocatedAt { span, at } => {
                    self.span(&spans, span).located_at(self.span(&spans, at))
                }
                FrozenRecipe::JoinOrFirst { first, second } => {
                    let first = self.span(&spans, first);
                    first.join(self.span(&spans, second)).unwrap_or(first)
                }
            };
            spans.push(span);
        }
        let mut parsed = HashMap::new();
        self.thaw_range(frozen, &spans, &mut parsed, 0, frozen.nodes.len())
    }

    fn span(&self, recipe_spans: &[Span], span: SpanRef) -> Span {
        if span == CALL_SITE_REF {
            Span::call_site()
        } else if span & RECIPE_TAG != 0 {
            recipe_spans[(span & !RECIPE_TAG) as usize]
        } else {
            match self.origins.get(span as usize) {
                Some(origin) => origin.span,
                None => panic!("worker_tokens: input span id {} out of range", span),
            }
        }
    }

    fn origin_text(&self, start: u32, end: u32) -> &str {
        &self.text[start as usize..end as usize]
    }

    // `parsed` caches the parse of each literal repr that is not an origin reuse.
    fn thaw_range<'f>(
        &self,
        frozen: &'f FrozenTokens,
        spans: &[Span],
        parsed: &mut HashMap<&'f str, Literal>,
        mut i: usize,
        end: usize,
    ) -> TokenStream {
        let mut trees: Vec<TokenTree> = Vec::new();
        while i < end {
            match frozen.nodes[i] {
                Node::Group {
                    delimiter,
                    span,
                    len,
                } => {
                    let inner_end = i + 1 + len as usize;
                    let stream = self.thaw_range(frozen, spans, parsed, i + 1, inner_end);
                    let mut group = Group::new(delimiter, stream);
                    group.set_span(self.span(spans, span));
                    trees.push(TokenTree::Group(group));
                    i = inner_end;
                }
                Node::Ident {
                    start,
                    end,
                    raw,
                    span,
                } => {
                    let sym = frozen.text_at(start, end);
                    let reused = match self.origins.get(span as usize) {
                        Some(Origin {
                            token:
                                OriginToken::Ident {
                                    ident,
                                    start: s,
                                    end: e,
                                    raw: r,
                                },
                            ..
                        }) if span & RECIPE_TAG == 0
                            && *r == raw
                            && self.origin_text(*s, *e) == sym =>
                        {
                            Some(ident.clone())
                        }
                        _ => None,
                    };
                    let ident = match reused {
                        Some(ident) => ident,
                        None if raw => Ident::new_raw(sym, self.span(spans, span)),
                        None => Ident::new(sym, self.span(spans, span)),
                    };
                    trees.push(TokenTree::Ident(ident));
                    i += 1;
                }
                Node::Punct { ch, spacing, span } => {
                    let mut punct = Punct::new(ch, spacing);
                    punct.set_span(self.span(spans, span));
                    trees.push(TokenTree::Punct(punct));
                    i += 1;
                }
                Node::Literal { start, end, span } => {
                    let repr = frozen.text_at(start, end);
                    let reused = match self.origins.get(span as usize) {
                        Some(Origin {
                            token:
                                OriginToken::Literal {
                                    literal,
                                    start: s,
                                    end: e,
                                },
                            ..
                        }) if span & RECIPE_TAG == 0 && self.origin_text(*s, *e) == repr => {
                            Some(literal.clone())
                        }
                        _ => None,
                    };
                    let literal = match reused {
                        Some(literal) => literal,
                        None => {
                            let mut literal = match parsed.get(repr) {
                                Some(literal) => literal.clone(),
                                None => {
                                    let literal: Literal = match repr.parse() {
                                        Ok(literal) => literal,
                                        Err(_) => {
                                            panic!("worker_tokens: invalid literal repr {:?}", repr)
                                        }
                                    };
                                    parsed.insert(repr, literal.clone());
                                    literal
                                }
                            };
                            literal.set_span(self.span(spans, span));
                            literal
                        }
                    };
                    trees.push(TokenTree::Literal(literal));
                    i += 1;
                }
            }
        }
        TokenStream::from_iter(trees)
    }
}

/// Parses tokens whose Verus operators were already rejoined by `freeze_rejoin_main`.
#[cfg(feature = "parsing")]
pub fn parse2_prejoined<T: Parse>(tokens: TokenStream) -> Result<T> {
    parse_prejoined_with(T::parse, tokens)
}

/// Runs a parser over prejoined tokens, enforcing that the input is fully parsed.
#[cfg(feature = "parsing")]
pub fn parse_prejoined_with<T>(
    f: impl FnOnce(ParseStream) -> Result<T>,
    tokens: TokenStream,
) -> Result<T> {
    let buf = TokenBuffer::new2_prejoined(tokens);
    crate::parse::parse_token_buffer(f, &buf)
}

#[cfg(all(test, not(verus_proc_macro2_worker)))]
mod stub_tests {
    use super::*;
    use alloc::string::ToString;
    use std::panic::catch_unwind;

    #[test]
    fn stock_proc_macro2_degrades_to_main_only() {
        assert!(!WORKER_JOBS_AVAILABLE);
        assert!(!in_worker_job());
        assert!(catch_unwind(begin_job).is_err());
        let input: TokenStream = "a ==> b".parse().unwrap();
        let (frozen, meta) = freeze_rejoin_main(input.clone());
        let thawed = meta.thaw(&frozen);
        assert_eq!(thawed.to_string(), crate::rejoin_tokens(input).to_string());
        let _: crate::Expr = parse2_prejoined(thawed).unwrap();
    }
}

#[cfg(all(test, verus_proc_macro2_worker))]
mod tests {
    use super::*;
    use crate::buffer::TokenBuffer;
    use alloc::boxed::Box;
    use alloc::format;
    use alloc::string::{String, ToString};
    use alloc::vec;
    use alloc::vec::Vec;
    use core::ops::Range;
    use proc_macro2::{
        Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree,
    };
    use quote::ToTokens;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    type SpanSig = (String, Range<usize>, (usize, usize), (usize, usize));

    fn span_sig(span: Span) -> SpanSig {
        let start = span.start();
        let end = span.end();
        (
            format!("{:?}", span),
            span.byte_range(),
            (start.line, start.column),
            (end.line, end.column),
        )
    }

    fn assert_same_span(path: &str, what: &str, a: Span, b: Span) {
        assert_eq!(span_sig(a), span_sig(b), "{}: {} span mismatch", path, what);
    }

    fn assert_same_tree(path: &str, a: &TokenTree, b: &TokenTree) {
        match (a, b) {
            (TokenTree::Group(x), TokenTree::Group(y)) => {
                assert_eq!(x.delimiter(), y.delimiter(), "{}: delimiter mismatch", path);
                assert_same_span(path, "group", x.span(), y.span());
                assert_same_span(path, "group open", x.span_open(), y.span_open());
                assert_same_span(path, "group close", x.span_close(), y.span_close());
                assert_same_stream(
                    &format!("{}/{:?}", path, x.delimiter()),
                    &x.stream(),
                    &y.stream(),
                );
            }
            (TokenTree::Ident(x), TokenTree::Ident(y)) => {
                assert_eq!(x.to_string(), y.to_string(), "{}: ident mismatch", path);
                assert_same_span(path, "ident", x.span(), y.span());
            }
            (TokenTree::Punct(x), TokenTree::Punct(y)) => {
                assert_eq!(x.as_char(), y.as_char(), "{}: punct char mismatch", path);
                assert_eq!(x.spacing(), y.spacing(), "{}: punct spacing mismatch", path);
                assert_same_span(path, "punct", x.span(), y.span());
            }
            (TokenTree::Literal(x), TokenTree::Literal(y)) => {
                assert_eq!(x.to_string(), y.to_string(), "{}: literal mismatch", path);
                assert_same_span(path, "literal", x.span(), y.span());
            }
            _ => panic!("{}: token kind mismatch: {:?} vs {:?}", path, a, b),
        }
    }

    fn assert_same_stream(path: &str, a: &TokenStream, b: &TokenStream) {
        let a: Vec<TokenTree> = a.clone().into_iter().collect();
        let b: Vec<TokenTree> = b.clone().into_iter().collect();
        assert_eq!(
            a.len(),
            b.len(),
            "{}: token count mismatch: {:?} vs {:?}",
            path,
            a,
            b
        );
        for (i, (x, y)) in a.iter().zip(b.iter()).enumerate() {
            assert_same_tree(&format!("{}[{}]", path, i), x, y);
        }
    }

    fn parse_ts(src: &str) -> TokenStream {
        src.parse().unwrap()
    }

    fn trees(stream: &TokenStream) -> Vec<TokenTree> {
        stream.clone().into_iter().collect()
    }

    fn count_nodes(stream: &TokenStream) -> usize {
        stream
            .clone()
            .into_iter()
            .map(|tt| match tt {
                TokenTree::Group(g) => 1 + count_nodes(&g.stream()),
                _ => 1,
            })
            .sum()
    }

    fn for_each_span(stream: &TokenStream, f: &mut dyn FnMut(Span)) {
        for tt in stream.clone() {
            f(tt.span());
            if let TokenTree::Group(g) = tt {
                for_each_span(&g.stream(), f);
            }
        }
    }

    fn expr_string(expr: &crate::Expr) -> String {
        expr.to_token_stream().to_string()
    }

    fn serial_expr(input: &TokenStream) -> String {
        let expr =
            crate::parse::parse2_rejoin(<crate::Expr as crate::parse::Parse>::parse, input.clone())
                .unwrap_or_else(|e| panic!("serial parse of {} failed: {}", input, e));
        expr_string(&expr)
    }

    fn assert_thaw_matches_rejoin(input: TokenStream) {
        let expected = crate::rejoin_tokens(input.clone());
        let (frozen, meta) = freeze_rejoin_main(input.clone());
        assert_eq!(
            frozen.node_count(),
            count_nodes(&expected),
            "node count for {}",
            input
        );
        assert_eq!(frozen.is_empty(), expected.is_empty());
        let thawed = meta.thaw(&frozen);
        assert_same_stream(&format!("<{}>", input), &thawed, &expected);
    }

    #[test]
    fn thaw_of_main_freeze_equals_rejoin_tokens() {
        let sources = [
            "a ==> b && c <==> d",
            "x !is Foo",
            "x !has y",
            "y =~= z",
            "x !~~= y",
            "x =~~= y",
            "x !~= y",
            "a === b",
            "a !== b",
            "a &&& b ||| c",
            "r#match r#type + r#fn",
            "( [ { a ==> b } ] )",
            "f(x !is Foo, [y =~= z], { a <==> b })",
            "a += b; c - -d; x::y => z |a| a",
            "\"s\" 'c' b'x' b\"y\" 1.5 2u8 0x1fi64 r\"raw\" 1e10f32",
            "",
        ];
        for src in sources {
            assert_thaw_matches_rejoin(parse_ts(src));
        }

        // Manual None-delimited groups, nested and next to rejoinable tokens.
        let inner = Group::new(Delimiter::None, parse_ts("a ==> b"));
        let nested = Group::new(
            Delimiter::None,
            TokenStream::from_iter(vec![
                TokenTree::Group(inner.clone()),
                TokenTree::Punct(Punct::new('+', Spacing::Alone)),
                TokenTree::Group(Group::new(Delimiter::Parenthesis, parse_ts("x !is Foo"))),
            ]),
        );
        let mut stream = parse_ts("p !has q");
        stream.extend(vec![TokenTree::Group(inner), TokenTree::Group(nested)]);
        stream.extend(parse_ts("y =~= z"));
        assert_thaw_matches_rejoin(stream);

        // Manual punctuation with explicit spacing.
        let manual = TokenStream::from_iter(vec![
            TokenTree::Punct(Punct::new('=', Spacing::Joint)),
            TokenTree::Punct(Punct::new('=', Spacing::Alone)),
            TokenTree::Punct(Punct::new('>', Spacing::Alone)),
            TokenTree::Punct(Punct::new('#', Spacing::Joint)),
        ]);
        assert_thaw_matches_rejoin(manual);
    }

    #[test]
    fn main_freeze_folds_not_is() {
        let input = parse_ts("x !is Foo");
        assert_eq!(count_nodes(&input), 4);
        let (frozen, meta) = freeze_rejoin_main(input.clone());
        assert_eq!(frozen.node_count(), 3);
        assert!(matches!(frozen.nodes[1], Node::Ident { raw: false, .. }));
        let thawed = meta.thaw(&frozen);
        assert_eq!(thawed.to_string(), "x isnt Foo");
        let isnt = &trees(&thawed)[1];
        let orig = trees(&input);
        let joined = orig[1].span().join(orig[2].span()).unwrap();
        assert_same_span("isnt", "joined", isnt.span(), joined);

        let (frozen, meta) = freeze_rejoin_main(parse_ts("x !has y"));
        assert_eq!(frozen.node_count(), 3);
        assert_eq!(meta.thaw(&frozen).to_string(), "x hasnt y");

        let empty = FrozenTokens::default();
        assert!(empty.is_empty());
        assert_eq!(empty.node_count(), 0);
    }

    // Fallback main `TokenStream` construction splits negative literals into `-` and a
    // positive literal (proc-macro2 issue 235), unlike compiler and worker-job streams,
    // so a compiler-style single negative literal token is modeled directly in the
    // frozen IR and its thaw metadata.
    fn negative_literal_fixture() -> (FrozenTokens, ThawMetadata, Literal, Literal, TokenStream) {
        let anchors = trees(&parse_ts("f (p, q)"));
        let group_span = anchors[1].span();
        let inner = match &anchors[1] {
            TokenTree::Group(g) => trees(&g.stream()),
            _ => unreachable!(),
        };
        let f = match &anchors[0] {
            TokenTree::Ident(f) => f.clone(),
            _ => unreachable!(),
        };
        let mut l1 = Literal::i32_suffixed(-1);
        l1.set_span(inner[0].span());
        let mut l2 = Literal::f64_unsuffixed(-2.5);
        l2.set_span(inner[2].span());
        let text: Arc<str> = Arc::from("f-1i32-2.5");
        let nonce = fresh_nonce();
        let frozen = FrozenTokens {
            nodes: Arc::from(vec![
                Node::Ident {
                    start: 0,
                    end: 1,
                    raw: false,
                    span: 0,
                },
                Node::Group {
                    delimiter: Delimiter::Parenthesis,
                    span: 1,
                    len: 3,
                },
                Node::Literal {
                    start: 1,
                    end: 6,
                    span: 2,
                },
                Node::Punct {
                    ch: ',',
                    spacing: Spacing::Alone,
                    span: 3,
                },
                Node::Literal {
                    start: 6,
                    end: 10,
                    span: 4,
                },
            ]),
            text: text.clone(),
            recipes: Arc::from(Vec::new()),
            nonce,
            has_input: true,
            origin_count: 5,
        };
        let meta = ThawMetadata {
            origins: vec![
                Origin {
                    span: f.span(),
                    token: OriginToken::Ident {
                        ident: f,
                        start: 0,
                        end: 1,
                        raw: false,
                    },
                },
                Origin {
                    span: group_span,
                    token: OriginToken::Other,
                },
                Origin {
                    span: l1.span(),
                    token: OriginToken::Literal {
                        literal: l1.clone(),
                        start: 1,
                        end: 6,
                    },
                },
                Origin {
                    span: inner[1].span(),
                    token: OriginToken::Other,
                },
                Origin {
                    span: l2.span(),
                    token: OriginToken::Literal {
                        literal: l2.clone(),
                        start: 6,
                        end: 10,
                    },
                },
            ],
            text,
            nonce,
        };
        // Serial reference: the rejoin buffer splits negative literals the same way.
        let args = TokenStream::from_iter(vec![
            TokenTree::Literal(l1.clone()),
            TokenTree::Punct(Punct::new(',', Spacing::Alone)),
            TokenTree::Literal(l2.clone()),
        ]);
        let serial_input = TokenStream::from_iter(vec![
            anchors[0].clone(),
            TokenTree::Group(Group::new(Delimiter::Parenthesis, args)),
        ]);
        (frozen, meta, l1, l2, serial_input)
    }

    #[test]
    fn negative_literals_prejoined_parse() {
        let (frozen, _meta, _, _, serial_input) = negative_literal_fixture();
        let serial = serial_expr(&serial_input);
        let job = begin_job();
        let melted = melt_worker(&frozen);
        let expr: crate::Expr = parse2_prejoined(melted).unwrap();
        let prejoined = expr_string(&expr);
        job.end();
        assert_eq!(prejoined, serial);
    }

    #[test]
    fn negative_literals_melt_and_thaw_single_token() {
        let (frozen, meta, l1, l2, _) = negative_literal_fixture();
        let job = begin_job();
        let melted = melt_worker(&frozen);
        let inner = match &trees(&melted)[1] {
            TokenTree::Group(g) => trees(&g.stream()),
            other => panic!("expected group, got {:?}", other),
        };
        let reprs: Vec<String> = inner.iter().map(|t| t.to_string()).collect();
        // A worker-created negative literal also stays a single token.
        let mut out = trees(&melted);
        out.push(TokenTree::Literal(Literal::i64_suffixed(-3)));
        let refrozen = freeze_worker(TokenStream::from_iter(out));
        job.end();
        assert!(!in_worker_job());
        // Worker streams keep negative literals as single tokens, like compiler streams.
        assert_eq!(reprs, ["-1i32", ",", "-2.5"]);
        assert_eq!(refrozen.node_count(), 6);
        let literal_reprs: Vec<&str> = refrozen
            .nodes
            .iter()
            .filter_map(|node| match *node {
                Node::Literal { start, end, .. } => Some(refrozen.text_at(start, end)),
                _ => None,
            })
            .collect();
        assert_eq!(literal_reprs, ["-1i32", "-2.5", "-3i64"]);

        // Unchanged negative literals are origin reuses. The fallback main stream used
        // by tests splits them again on assembly, exactly as for the original tokens.
        let thawed = meta.thaw(&refrozen);
        let mut expected = trees(&meta.thaw(&frozen));
        expected.push(TokenTree::Literal(Literal::i64_suffixed(-3)));
        assert_same_stream("neg", &thawed, &TokenStream::from_iter(expected));
        let inner = match &trees(&thawed)[1] {
            TokenTree::Group(g) => trees(&g.stream()),
            other => panic!("expected group, got {:?}", other),
        };
        assert_same_span("neg-1", "literal", inner[1].span(), l1.span());
        assert_same_span("neg-2", "literal", inner[4].span(), l2.span());
    }

    #[test]
    fn worker_thread_roundtrip() {
        let input = parse_ts("a b c 1u8 r#k ( d e )");
        let rejoined = trees(&crate::rejoin_tokens(input.clone()));
        let (frozen, meta) = freeze_rejoin_main(input.clone());
        assert_eq!(frozen.node_count(), 8);
        assert!(!frozen.is_empty());

        let out_frozen: FrozenTokens = std::thread::spawn(move || {
            let job = begin_job();
            assert!(in_worker_job());
            let melted = trees(&melt_worker(&frozen));
            assert_eq!(melted.len(), 6);
            let a = melted[0].span();
            let b = melted[1].span();
            let c = melted[2].span();
            let mut out: Vec<TokenTree> = vec![
                melted[0].clone(),
                melted[3].clone(),
                melted[4].clone(),
                melted[5].clone(),
                TokenTree::Ident(Ident::new("fresh", Span::mixed_site())),
                TokenTree::Ident(Ident::new("res", a.resolved_at(b))),
            ];
            let mut punct = Punct::new('#', Spacing::Joint);
            punct.set_span(a.located_at(b));
            out.push(TokenTree::Punct(punct));
            let mut group = Group::new(Delimiter::Bracket, TokenStream::new());
            group.set_span(a.join(b).unwrap_or(a));
            out.push(TokenTree::Group(group));
            out.push(TokenTree::Literal(Literal::u32_suffixed(7)));
            out.push(TokenTree::Ident(Ident::new_raw("r_ident", b)));
            out.push(TokenTree::Ident(Ident::new("zz", c)));
            out.push(TokenTree::Ident(Ident::new("site", Span::call_site())));
            let frozen = freeze_worker(TokenStream::from_iter(out));
            job.end();
            assert!(!in_worker_job());
            frozen
        })
        .join()
        .unwrap();

        assert_eq!(out_frozen.node_count(), 14);
        assert_eq!(out_frozen.recipes.len(), 4);
        let thawed = trees(&meta.thaw(&out_frozen));
        assert_eq!(thawed.len(), 12);
        let texts: Vec<String> = thawed.iter().map(|t| t.to_string()).collect();
        assert_eq!(
            texts,
            [
                "a",
                "1u8",
                "r#k",
                "(d e)",
                "fresh",
                "res",
                "#",
                "[]",
                "7u32",
                "r#r_ident",
                "zz",
                "site"
            ]
        );

        // Untouched tokens are origin reuses.
        assert_same_tree("out[0]", &thawed[0], &rejoined[0]);
        assert_same_tree("out[1]", &thawed[1], &rejoined[3]);
        assert_same_tree("out[2]", &thawed[2], &rejoined[4]);
        assert_same_tree("out[3]", &thawed[3], &rejoined[5]);

        let a = rejoined[0].span();
        let b = rejoined[1].span();
        let c = rejoined[2].span();
        let call = Span::call_site();
        assert_same_span("fresh", "mixed_site", thawed[4].span(), call);
        assert_same_span("fresh", "mixed_site", thawed[4].span(), Span::mixed_site());
        assert_same_span("res", "resolved_at", thawed[5].span(), a);
        assert_same_span("#", "located_at", thawed[6].span(), b);
        match &thawed[6] {
            TokenTree::Punct(p) => assert_eq!(p.spacing(), Spacing::Joint),
            other => panic!("expected punct, got {:?}", other),
        }
        let joined = a.join(b).unwrap();
        assert_ne!(span_sig(joined), span_sig(a));
        assert_same_span("[]", "join", thawed[7].span(), joined);
        assert_same_span("7u32", "call_site", thawed[8].span(), call);
        assert_same_span("r_ident", "input", thawed[9].span(), b);
        assert_same_span("zz", "input", thawed[10].span(), c);
        assert_same_span("site", "call_site", thawed[11].span(), call);
    }

    #[test]
    fn worker_job_cleanup() {
        assert!(!in_worker_job());
        let _ = prepare_main_thread();
        let job = begin_job();
        assert!(in_worker_job());
        job.end();
        assert!(!in_worker_job());

        let result = catch_unwind(AssertUnwindSafe(|| {
            let _job = begin_job();
            assert!(in_worker_job());
            panic!("intentional panic inside a worker job");
        }));
        assert!(result.is_err());
        assert!(!in_worker_job());

        let job = begin_job();
        assert!(in_worker_job());
        let nested = catch_unwind(AssertUnwindSafe(|| {
            let _second = begin_job();
        }));
        assert!(nested.is_err(), "second begin_job must panic");
        drop(job);
        assert!(!in_worker_job());

        let job = begin_job();
        let melted = melt_worker(&FrozenTokens::default());
        assert!(melted.is_empty());
        assert!(freeze_worker(melted).is_empty());
        job.end();

        let melt = catch_unwind(|| melt_worker(&FrozenTokens::default()));
        assert!(melt.is_err(), "melt_worker outside a job must panic");
        let freeze = catch_unwind(|| freeze_worker(TokenStream::new()));
        assert!(freeze.is_err(), "freeze_worker outside a job must panic");
        assert!(!in_worker_job());
    }

    #[test]
    fn prejoined_parse_equals_serial_rejoin_parse() {
        let sources = [
            "a ==> b",
            "x !is Foo",
            "a <==> b ==> c",
            "s =~= t",
            "f(x !has y) ==> a === b",
        ];
        for src in sources {
            let input = parse_ts(src);
            let serial = serial_expr(&input);
            let (frozen, _meta) = freeze_rejoin_main(input);
            let job = begin_job();
            let melted = melt_worker(&frozen);
            // Worker spans have no source location: querying one inside the job panics.
            for_each_span(&melted, &mut |span| {
                let panics = |f: &dyn Fn()| {
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).is_err()
                };
                assert!(panics(&|| _ = span.start()), "{}: start", src);
                assert!(panics(&|| _ = span.end()), "{}: end", src);
                assert!(panics(&|| _ = span.byte_range()), "{}: byte_range", src);
                assert!(panics(&|| _ = span.local_file()), "{}: local_file", src);
            });
            let expr: crate::Expr = parse2_prejoined(melted)
                .unwrap_or_else(|e| panic!("prejoined parse of {} failed: {}", src, e));
            let prejoined = expr_string(&expr);
            job.end();
            assert_eq!(prejoined, serial, "{}", src);
        }
        let implies = serial_expr(&parse_ts("a ==> b"));
        assert!(implies.contains("==>"), "{}", implies);
    }

    #[test]
    fn prejoined_buffer_does_not_rejoin() {
        // Parsed input has adjacent real spans: the rejoin buffer folds `!is`.
        let parsed = parse_ts("x !is Foo");
        let buffer = TokenBuffer::new2_rejoin(parsed.clone());
        let (x, cursor) = buffer.begin().ident().expect("x");
        assert_eq!(x.to_string(), "x");
        let (isnt, cursor) = cursor.ident().expect("isnt");
        assert_eq!(isnt.to_string(), "isnt");
        let (foo, cursor) = cursor.ident().expect("Foo");
        assert_eq!(foo.to_string(), "Foo");
        assert!(cursor.eof());

        let manual = TokenStream::from_iter(vec![
            TokenTree::Ident(Ident::new("x", Span::call_site())),
            TokenTree::Punct(Punct::new('!', Spacing::Alone)),
            TokenTree::Ident(Ident::new("is", Span::call_site())),
            TokenTree::Ident(Ident::new("Foo", Span::call_site())),
        ]);
        for stream in [parsed, manual] {
            let buffer = TokenBuffer::new2_prejoined(stream);
            let (_, cursor) = buffer.begin().ident().expect("x");
            let (bang, cursor) = cursor.punct().expect("!");
            assert_eq!(bang.as_char(), '!');
            assert_eq!(bang.spacing(), Spacing::Alone);
            let (is, cursor) = cursor.ident().expect("is");
            assert_eq!(is.to_string(), "is");
            let (_, cursor) = cursor.ident().expect("Foo");
            assert!(cursor.eof());
        }
    }

    fn panic_message(f: impl FnOnce()) -> String {
        let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a panic");
        match payload.downcast::<String>() {
            Ok(s) => *s,
            Err(payload) => payload
                .downcast::<&str>()
                .map(|s| s.to_string())
                .unwrap_or_default(),
        }
    }

    #[test]
    fn thaw_rejects_tokens_of_another_segment() {
        let (frozen_a, meta_a) = freeze_rejoin_main(parse_ts("a b"));
        let (frozen_b, meta_b) = freeze_rejoin_main(parse_ts("c d"));
        assert_ne!(meta_a.nonce, meta_b.nonce);
        let msg = panic_message(|| drop(meta_b.thaw(&frozen_a)));
        assert!(msg.contains("do not belong"), "{}", msg);
        assert!(catch_unwind(AssertUnwindSafe(|| meta_a.thaw(&frozen_b))).is_err());

        // Worker output inherits the melted segment's nonce, also when it only
        // references call-site spans (like deferred diagnostics).
        let (out, marks) = std::thread::spawn(move || {
            let _job = begin_job();
            let melted = melt_worker(&frozen_a);
            let out = freeze_worker(melted);
            let marks = freeze_worker(TokenStream::from_iter(vec![TokenTree::Punct(Punct::new(
                '#',
                Spacing::Alone,
            ))]));
            (out, marks)
        })
        .join()
        .unwrap();
        assert!(!marks.has_input);
        assert_eq!(meta_a.thaw(&out).to_string(), "a b");
        assert_eq!(meta_a.thaw(&marks).to_string(), "#");
        assert!(catch_unwind(AssertUnwindSafe(|| meta_b.thaw(&out))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| meta_b.thaw(&marks))).is_err());

        // Unbound, input-free tokens thaw with any metadata.
        assert!(meta_b.thaw(&FrozenTokens::default()).is_empty());
    }

    #[test]
    fn job_serves_one_segment() {
        let (frozen_a, _meta_a) = freeze_rejoin_main(parse_ts("a"));
        let (frozen_b, _meta_b) = freeze_rejoin_main(parse_ts("b"));
        let job = begin_job();
        let _ = melt_worker(&frozen_a);
        let _ = melt_worker(&frozen_a);
        assert!(catch_unwind(AssertUnwindSafe(|| melt_worker(&frozen_b))).is_err());
        job.end();
        // A fresh job may take the other segment.
        let job = begin_job();
        let _ = melt_worker(&frozen_b);
        job.end();

        // Input spans without a melted segment cannot be frozen.
        let job = begin_job();
        let ident = Ident::new("x", input_span(0));
        let msg = panic_message(|| {
            let _ = freeze_worker(TokenStream::from_iter(vec![TokenTree::Ident(ident)]));
        });
        assert!(msg.contains("melted no segment"), "{}", msg);
        job.end();
    }

    #[test]
    fn rejoin_entry_points_fail_inside_worker_job() {
        let input = parse_ts("a ==> b");
        let (frozen, _meta) = freeze_rejoin_main(input.clone());
        let job = begin_job();
        let melted = melt_worker(&frozen);
        let checks: Vec<(&str, Box<dyn FnOnce()>)> = vec![
            ("rejoin_tokens", {
                let m = melted.clone();
                Box::new(move || drop(crate::rejoin_tokens(m)))
            }),
            ("new2_rejoin", {
                let m = melted.clone();
                Box::new(move || drop(TokenBuffer::new2_rejoin(m)))
            }),
            ("parse2_rejoin", {
                let m = melted.clone();
                Box::new(move || {
                    let _ =
                        crate::parse::parse2_rejoin(<crate::Expr as crate::parse::Parse>::parse, m);
                })
            }),
            ("freeze_rejoin_main", {
                let m = melted.clone();
                Box::new(move || drop(freeze_rejoin_main(m)))
            }),
        ];
        for (name, check) in checks {
            let msg = panic_message(check);
            assert!(msg.contains("worker job"), "{}: {}", name, msg);
        }
        // The prejoined parser is the worker entry point.
        let expr: crate::Expr = parse2_prejoined(melted).unwrap();
        job.end();
        assert_eq!(expr_string(&expr), serial_expr(&input));
    }

    #[test]
    fn worker_jobs_available_with_vendored_proc_macro2() {
        assert!(WORKER_JOBS_AVAILABLE);
    }

    // Verbatim copy of `rejoin_level` before its `rejoin_core` refactor.
    fn reference_rejoin_level(tokens: &mut Vec<proc_macro2::TokenTree>) {
        use proc_macro2::{Ident, Punct, Spacing, Spacing::*, Span, TokenTree};
        fn pun(t: &TokenTree) -> Option<(char, Spacing)> {
            match t {
                TokenTree::Punct(p) => Some((p.as_char(), p.spacing())),
                _ => None,
            }
        }
        fn adjacent(s1: Span, s2: Span) -> bool {
            let l1 = s1.end();
            let l2 = s2.start();
            s1.local_file() == s2.local_file() && l1.eq(&l2)
        }
        fn make_joint(t: &mut TokenTree) {
            if let TokenTree::Punct(p) = t {
                let mut punct = Punct::new(p.as_char(), Joint);
                punct.set_span(p.span());
                *t = TokenTree::Punct(punct);
            }
        }
        let len = tokens.len();
        let mut removed: Vec<usize> = Vec::new();
        let till = if len >= 2 { len - 2 } else { 0 };
        let mut j = 0;
        while j < till {
            let t0 = pun(&tokens[j]);
            if t0 == Some(('!', Alone)) {
                if let TokenTree::Ident(id) = &tokens[j + 1] {
                    let joined = match id.to_string().as_str() {
                        "is" => Some("isnt"),
                        "has" => Some("hasnt"),
                        _ => None,
                    };
                    if let Some(joined) = joined {
                        let s1 = tokens[j].span();
                        let s2 = id.span();
                        if adjacent(s1, s2) {
                            tokens[j] =
                                TokenTree::Ident(Ident::new(joined, s1.join(s2).unwrap_or(s1)));
                            removed.push(j + 1);
                            j += 2;
                            continue;
                        }
                    }
                }
            }
            let t1 = pun(&tokens[j + 1]);
            let t2 = pun(&tokens[j + 2]);
            let t3 = if j + 3 < len {
                pun(&tokens[j + 3])
            } else {
                None
            };
            match (t0, t1, t2, t3) {
                (
                    Some(('<', Joint)),
                    Some(('=', Alone)),
                    Some(('=', Joint)),
                    Some(('>', Alone)),
                )
                | (Some(('=', Joint)), Some(('=', Alone)), Some(('=', Alone)), _)
                | (Some(('!', Joint)), Some(('=', Alone)), Some(('=', Alone)), _)
                | (Some(('=', Joint)), Some(('=', Alone)), Some(('>', Alone)), _)
                | (Some(('<', Joint)), Some(('=', Alone)), Some(('=', Alone)), _)
                | (Some(('&', Joint)), Some(('&', Alone)), Some(('&', Alone)), _)
                | (Some(('|', Joint)), Some(('|', Alone)), Some(('|', Alone)), _) => {
                    if adjacent(tokens[j + 1].span(), tokens[j + 2].span()) {
                        make_joint(&mut tokens[j + 1]);
                    }
                }
                (Some(('=', Alone)), Some(('~', Alone)), Some(('=', Alone)), _)
                | (Some(('!', Alone)), Some(('~', Alone)), Some(('=', Alone)), _) => {
                    if adjacent(tokens[j + 1].span(), tokens[j + 2].span()) {
                        make_joint(&mut tokens[j]);
                        make_joint(&mut tokens[j + 1]);
                    }
                }
                (
                    Some(('=', Alone)),
                    Some(('~', Alone)),
                    Some(('~', Alone)),
                    Some(('=', Alone)),
                )
                | (
                    Some(('!', Alone)),
                    Some(('~', Alone)),
                    Some(('~', Alone)),
                    Some(('=', Alone)),
                ) => {
                    if adjacent(tokens[j + 2].span(), tokens[j + 3].span()) {
                        make_joint(&mut tokens[j]);
                        make_joint(&mut tokens[j + 1]);
                        make_joint(&mut tokens[j + 2]);
                    }
                }
                _ => {}
            }
            j += 1;
        }
        if !removed.is_empty() {
            let mut removed = removed.into_iter().peekable();
            let mut k = 0;
            tokens.retain(|_| {
                let keep = removed.peek() != Some(&k);
                if !keep {
                    removed.next();
                }
                k += 1;
                keep
            });
        }
    }

    fn reference_rejoin_tokens(stream: TokenStream) -> TokenStream {
        let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
        reference_rejoin_level(&mut tokens);
        for tt in &mut tokens {
            if let TokenTree::Group(group) = tt {
                let mut new_group =
                    Group::new(group.delimiter(), reference_rejoin_tokens(group.stream()));
                new_group.set_span(group.span());
                *group = new_group;
            }
        }
        TokenStream::from_iter(tokens)
    }

    const VERUS_CORPUS: &[&str] = &[
        "verus! { proof fn f(x: int) ensures a <==> b, c =~= d, e !is Foo, g &&& h ||| i { } }",
        "a ==> b && c <==> d; x === y; x !== y; s =~~= t; u !~= v; w !~~= z; p !~ = q",
        "x !is Foo; x !has y; x ! is y; x !is; !is; a !r#is b; a !hasnt b; !is Foo",
        "&&& a &&& b ||| c &&&& d <==>",
        "f(-1, - 2i32, -3.5e1, x-1, -x, [-0x1f; 2])",
        "/// doc line \"q\" \\ tab\t\n//! inner\n/** block\n doc */ fn g() {}\n/*! ib */ x",
        "fn a() {\r\n    let s = \"x\r\ny\";\r\n    b !is C\r\n}\r\n",
        "fn h<'a, 'b: 'a>(x: &'a u8, y: &'static str) -> char { x=='e' && '\\n' != c; 'o: loop { break 'o; } }",
        "r#match r#type !is r#is x !has y z::r#fn",
        "\u{feff}#!/usr/bin/env run\nfn main() { a <==> b }",
        "0x1f 1u8 1.0f64 1e-3 b\"bytes\" r#\"raw\"# br\"b\" c\"cstr\" b'x' '\\'' 1.",
        "a=~=b a!~=b a==>b a<==>b a!is b x.0.1 m!{ y } #[attr] #![inner] $x ? @ ~",
        "",
    ];

    // The fallback main stream marks a punct before `'` Joint, rustc does not.
    fn rustc_compat_spacing(stream: TokenStream) -> TokenStream {
        let tokens = trees(&stream);
        let mut out = Vec::with_capacity(tokens.len());
        for (i, tt) in tokens.iter().enumerate() {
            let next_quote = tokens
                .get(i + 1)
                .is_some_and(|next| next.to_string().starts_with('\''));
            out.push(match tt {
                TokenTree::Punct(p)
                    if p.as_char() != '\'' && p.spacing() == Spacing::Joint && next_quote =>
                {
                    let mut punct = Punct::new(p.as_char(), Spacing::Alone);
                    punct.set_span(p.span());
                    TokenTree::Punct(punct)
                }
                TokenTree::Group(g) => {
                    let mut group = Group::new(g.delimiter(), rustc_compat_spacing(g.stream()));
                    group.set_span(g.span());
                    TokenTree::Group(group)
                }
                other => other.clone(),
            });
        }
        TokenStream::from_iter(out)
    }

    fn lex_in_job(src: &str) -> LexedFile {
        let _ = prepare_main_thread();
        let job = begin_job();
        let file = lex_positional(src).unwrap_or_else(|e| panic!("lex {:?}: {}", src, e.offset));
        job.end();
        file
    }

    #[test]
    fn rejoin_core_matches_reference_rejoin() {
        let mut streams: Vec<TokenStream> = VERUS_CORPUS
            .iter()
            .map(|src| parse_ts(&normalize_rustc_source(src)))
            .collect();
        // Call-site spans all compare adjacent.
        streams.push(TokenStream::from_iter(vec![
            TokenTree::Punct(Punct::new('!', Spacing::Alone)),
            TokenTree::Ident(Ident::new("is", Span::call_site())),
            TokenTree::Ident(Ident::new("x", Span::call_site())),
            TokenTree::Punct(Punct::new('=', Spacing::Alone)),
            TokenTree::Punct(Punct::new('~', Spacing::Alone)),
            TokenTree::Punct(Punct::new('~', Spacing::Alone)),
            TokenTree::Punct(Punct::new('=', Spacing::Alone)),
            TokenTree::Punct(Punct::new('<', Spacing::Joint)),
            TokenTree::Punct(Punct::new('=', Spacing::Alone)),
            TokenTree::Punct(Punct::new('=', Spacing::Joint)),
            TokenTree::Punct(Punct::new('>', Spacing::Alone)),
        ]));
        for stream in streams {
            let expected = reference_rejoin_tokens(stream.clone());
            let actual = crate::rejoin_tokens(stream.clone());
            assert_same_stream(&format!("<{}>", stream), &actual, &expected);
            let mut level = trees(&stream);
            let mut reference = level.clone();
            crate::verus::rejoin_level(&mut level);
            reference_rejoin_level(&mut reference);
            assert_same_stream(
                "level",
                &TokenStream::from_iter(level),
                &TokenStream::from_iter(reference),
            );
        }
    }

    #[test]
    fn text_freeze_equals_main_freeze_of_fallback_stream() {
        for src in VERUS_CORPUS {
            let text = normalize_rustc_source(src);
            let stream = rustc_compat_spacing(parse_ts(&text));
            let (real, meta) = freeze_rejoin_main(stream.clone());
            let file = lex_in_job(&text);
            assert!(!file.has_non_ascii_ident_in(0..file.toks.len()));
            let spec = freeze_rejoin_text(&file, 0..file.toks.len());
            assert_eq!(*spec.nodes, *real.nodes, "nodes of {:?}", src);
            assert_eq!(*spec.text, *real.text, "text of {:?}", src);
            assert!(spec.same_input(&real), "{:?}", src);
            assert_eq!(spec.input_hash(), real.input_hash(), "{:?}", src);
            assert_eq!(spec.origin_count, real.origin_count);
            assert_eq!(spec.origin_count as usize, meta.origin_count());
            assert_ne!(spec.nonce, real.nonce);
            assert!(meta.adopt(&real, &spec).is_some(), "{:?}", src);
            if src.contains(" !is ") {
                assert!(spec.text.contains("isnt"), "{:?}", src);
            }

            // Every group's contents freezes like the compiler group's stream.
            let mut groups = Vec::new();
            collect_groups(&stream, &mut groups);
            let lexed: Vec<usize> = (0..file.toks.len())
                .filter(|&i| matches!(file.toks[i].kind, LexedKind::Group { .. }))
                .collect();
            assert_eq!(groups.len(), lexed.len(), "{:?}", src);
            for (group, i) in groups.into_iter().zip(lexed) {
                let len = match file.toks[i].kind {
                    LexedKind::Group { len, .. } => len as usize,
                    _ => unreachable!(),
                };
                let (real, meta) = freeze_rejoin_main(group.stream());
                let spec = freeze_rejoin_text(&file, i + 1..i + 1 + len);
                assert!(spec.same_input(&real), "group {} of {:?}", i, src);
                assert!(meta.adopt(&real, &spec).is_some());
            }
        }
    }

    // Groups of `stream` in preorder.
    fn collect_groups(stream: &TokenStream, out: &mut Vec<Group>) {
        for tt in trees(stream) {
            if let TokenTree::Group(g) = tt {
                out.push(g.clone());
                collect_groups(&g.stream(), out);
            }
        }
    }

    #[test]
    fn text_freeze_detects_rustc_differences() {
        // Without the compat rule the fallback stream differs on `&'a`.
        let text = "x: &'a u8";
        let (real, _) = freeze_rejoin_main(parse_ts(text));
        let file = lex_in_job(text);
        assert!(!freeze_rejoin_text(&file, 0..file.toks.len()).same_input(&real));
        // Non-ASCII identifiers are reported.
        let file = lex_in_job("a \u{e9}t\u{e9} (b \u{3b1})");
        assert_eq!(file.non_ascii_idents, [1, 4]);
        assert!(file.has_non_ascii_ident_in(3..5));
        assert!(!file.has_non_ascii_ident_in(2..4));
    }

    #[test]
    fn text_freeze_rejects_bad_ranges() {
        let file = lex_in_job("a (b c) d");
        let msg = panic_message(|| drop(freeze_rejoin_text(&file, 1..3)));
        assert!(msg.contains("splits a group"), "{}", msg);
        let msg = panic_message(|| drop(freeze_rejoin_text(&file, 0..9)));
        assert!(msg.contains("out of bounds"), "{}", msg);
        assert!(freeze_rejoin_text(&file, 2..2).is_empty());
        assert_eq!(freeze_rejoin_text(&file, 1..4).node_count(), 3);
    }

    #[test]
    fn same_input_ignores_nonce() {
        let file = lex_in_job("a <==> b");
        let x = freeze_rejoin_text(&file, 0..file.toks.len());
        let y = freeze_rejoin_text(&file, 0..file.toks.len());
        assert_ne!(x.nonce, y.nonce);
        assert!(x.same_input(&y));
        assert_eq!(x.input_hash(), y.input_hash());
        let other = lex_in_job("a <==> c");
        let z = freeze_rejoin_text(&other, 0..other.toks.len());
        assert!(!x.same_input(&z));
        assert_ne!(x.input_hash(), z.input_hash());
        assert!(FrozenTokens::default().same_input(&FrozenTokens::default()));
    }

    #[test]
    fn adopted_thaw_of_speculative_worker_output() {
        let text = "f(x !is Foo, a <==> b) + r#k";
        let input = parse_ts(text);
        let expected = crate::rejoin_tokens(input.clone());
        let (real, meta) = freeze_rejoin_main(input);
        let file = lex_in_job(text);
        let spec = freeze_rejoin_text(&file, 0..file.toks.len());
        let spec_nonce = spec.nonce;
        let (out, out_real) = std::thread::spawn(move || {
            let job = begin_job();
            let melted = melt_worker(&spec);
            let out = freeze_worker(melted);
            job.end();
            let job = begin_job();
            let out_real = freeze_worker(melt_worker(&real));
            job.end();
            (out, out_real)
        })
        .join()
        .unwrap();
        assert_eq!(out.nonce, spec_nonce);
        let (real, _meta) = freeze_rejoin_main(parse_ts(text));
        // A different real freeze of the same text has another segment.
        assert!(meta.adopt(&real, &out).is_none());
        let msg = panic_message(|| drop(meta.thaw(&out)));
        assert!(msg.contains("do not belong"), "{}", msg);

        let (real, meta) = freeze_rejoin_main(parse_ts(text));
        let spec = freeze_rejoin_text(&file, 0..file.toks.len());
        let adopted = meta.adopt(&real, &spec).expect("same input adopts");
        assert_eq!(adopted.spec_nonce(), spec.nonce);
        // Output of another speculative segment is rejected.
        let msg = panic_message(|| drop(adopted.thaw(&out)));
        assert!(msg.contains("Adopted::thaw"), "{}", msg);
        // Output of an adopted segment thaws to the reused compiler tokens.
        let spec_out = std::thread::spawn(move || {
            let job = begin_job();
            let out = freeze_worker(melt_worker(&spec));
            job.end();
            out
        })
        .join()
        .unwrap();
        let thawed = adopted.thaw(&spec_out);
        let expected_real = meta.thaw(&real);
        assert_same_stream("adopted", &thawed, &expected_real);
        assert_eq!(thawed.to_string(), expected.to_string());
        // Real-segment output and input-free output stay accepted.
        assert_same_stream("real", &adopted.thaw(&real), &expected_real);
        assert!(adopted.thaw(&FrozenTokens::default()).is_empty());
        let msg = panic_message(|| drop(adopted.thaw(&out_real)));
        assert!(msg.contains("do not belong"), "{}", msg);
    }

    #[test]
    fn adopt_rejects_mismatches() {
        let text = "a ==> b";
        let (real, meta) = freeze_rejoin_main(parse_ts(text));
        let file = lex_in_job(text);
        let spec = freeze_rejoin_text(&file, 0..file.toks.len());
        assert!(meta.adopt(&real, &spec).is_some());
        // Different text.
        let other = lex_in_job("a ==> c");
        let other = freeze_rejoin_text(&other, 0..other.toks.len());
        assert!(meta.adopt(&real, &other).is_none());
        // Different spacing (`= =>` is not rejoined).
        let spaced = lex_in_job("a = => b");
        let spaced = freeze_rejoin_text(&spaced, 0..spaced.toks.len());
        assert!(meta.adopt(&real, &spaced).is_none());
        // `real` of another segment.
        let (real_b, _) = freeze_rejoin_main(parse_ts(text));
        assert!(meta.adopt(&real_b, &spec).is_none());
        // Unbound speculative tokens, or a different origin count.
        let mut unbound = spec.clone();
        unbound.nonce = 0;
        assert!(meta.adopt(&real, &unbound).is_none());
        let mut miscounted = spec.clone();
        miscounted.origin_count += 1;
        assert!(miscounted.same_input(&spec));
        assert!(meta.adopt(&real, &miscounted).is_none());
        let mut real_miscounted = real.clone();
        real_miscounted.origin_count += 1;
        assert!(meta.adopt(&real_miscounted, &spec).is_none());
        // Worker output is never an input freeze.
        let out = std::thread::spawn(move || {
            let job = begin_job();
            let out = freeze_worker(melt_worker(&spec));
            job.end();
            out
        })
        .join()
        .unwrap();
        assert!(out.same_input(&real));
        assert!(meta.adopt(&real, &out).is_none());
    }

    fn main_trees_sources() -> Vec<TokenStream> {
        let mut sources: Vec<TokenStream> = [
            "x !is Foo ; y",
            "!is a",
            "a ==> b && c <==> d ; fn f() { x !has y } struct S;",
            "y =~= z x !~~= y a === b !== c &&& d ||| e",
            "r#match r#type \"s\" 1.5 2u8 b'x' [a <==> b] (c =~= d)",
            "",
        ]
        .iter()
        .map(|s| parse_ts(s))
        .collect();
        // Manual punctuation with explicit spacing and a None-delimited group.
        sources.push(TokenStream::from_iter(vec![
            TokenTree::Punct(Punct::new('=', Spacing::Joint)),
            TokenTree::Punct(Punct::new('=', Spacing::Alone)),
            TokenTree::Punct(Punct::new('>', Spacing::Alone)),
            TokenTree::Group(Group::new(Delimiter::None, parse_ts("a ==> b"))),
            TokenTree::Punct(Punct::new('#', Spacing::Joint)),
        ]));
        sources
    }

    #[test]
    fn freeze_of_trees_equals_freeze_of_stream() {
        for input in main_trees_sources() {
            let list = trees(&input);
            let (a, meta_a) = freeze_rejoin_main(TokenStream::from_iter(list.clone()));
            let (b, meta_b) = freeze_rejoin_main_trees(&list);
            assert_ne!(a.nonce, b.nonce);
            assert!(a.same_input(&b), "IR differs for {}", input);
            assert_eq!(a.input_hash(), b.input_hash());
            assert_eq!(a.origin_count, b.origin_count);
            assert_eq!(meta_a.origin_count(), meta_b.origin_count());
            for (x, y) in meta_a.origins.iter().zip(meta_b.origins.iter()) {
                assert_same_span(&format!("<{}>", input), "origin", x.span, y.span);
            }
            match (meta_a.first_span(), list.first()) {
                (Some(first), Some(tree)) => {
                    assert_eq!(first.start(), tree.span().start());
                    assert_eq!(first.local_file(), tree.span().local_file());
                }
                (None, None) => {}
                other => panic!("first span mismatch: {:?}", other),
            }
            let path = format!("<{}>", input);
            assert_same_stream(&path, &meta_b.thaw(&b), &meta_a.thaw(&a));
            assert_same_stream(
                &path,
                &meta_b.thaw(&b),
                &crate::rejoin_tokens(input.clone()),
            );
            release_main_trees(list);
        }
    }

    #[test]
    fn first_span_of_folded_not_is_starts_at_bang() {
        let input = parse_ts("!is a");
        let bang = trees(&input)[0].span();
        let (_, meta) = freeze_rejoin_main(input);
        let first = meta.first_span().unwrap();
        assert_eq!(first.start(), bang.start());
        assert_eq!(first.local_file(), bang.local_file());
        let (_, empty) = freeze_rejoin_main(TokenStream::new());
        assert!(empty.first_span().is_none());
    }

    #[test]
    fn identifier_display_written_into_arena() {
        let (frozen, meta) = freeze_rejoin_main(parse_ts("r#match plain r#type 'a' 1u8"));
        let texts: Vec<(&str, bool)> = frozen
            .nodes
            .iter()
            .filter_map(|node| match *node {
                Node::Ident {
                    start, end, raw, ..
                } => Some((frozen.text_at(start, end), raw)),
                Node::Literal { start, end, .. } => Some((frozen.text_at(start, end), false)),
                _ => None,
            })
            .collect();
        assert_eq!(
            texts,
            [
                ("match", true),
                ("plain", false),
                ("type", true),
                ("'a'", false),
                ("1u8", false)
            ]
        );
        assert_eq!(&*frozen.text, "matchplaintype'a'1u8");
        assert_eq!(
            meta.thaw(&frozen).to_string(),
            "r#match plain r#type 'a' 1u8"
        );
    }

    #[test]
    fn worker_freeze_dedupes_equal_recipes() {
        let input = parse_ts("a b c");
        let orig = trees(&input);
        let (frozen, meta) = freeze_rejoin_main(input);
        let out = std::thread::spawn(move || {
            let job = begin_job();
            let melted = trees(&melt_worker(&frozen));
            let (a, b) = (melted[0].span(), melted[1].span());
            // Each call records a new worker span id with an equal recipe.
            let r1 = a.resolved_at(b);
            let r2 = a.resolved_at(b);
            assert_ne!(span_id(r1), span_id(r2));
            let l1 = a.located_at(Span::mixed_site());
            let l2 = a.located_at(Span::mixed_site());
            let out = TokenStream::from_iter(vec![
                TokenTree::Ident(Ident::new("p", r1)),
                TokenTree::Ident(Ident::new("q", r2)),
                TokenTree::Ident(Ident::new("s", l1)),
                TokenTree::Ident(Ident::new("t", l2)),
                TokenTree::Ident(Ident::new("u", a.resolved_at(a))),
            ]);
            let frozen = freeze_worker(out);
            job.end();
            frozen
        })
        .join()
        .unwrap();
        // resolved_at(a, b), mixed_site, located_at(a, mixed), resolved_at(a, a).
        assert_eq!(out.recipes.len(), 4);
        let thawed = trees(&meta.thaw(&out));
        let (a, b) = (orig[0].span(), orig[1].span());
        let expected = [
            a.resolved_at(b),
            a.resolved_at(b),
            a.located_at(Span::mixed_site()),
            a.located_at(Span::mixed_site()),
            a.resolved_at(a),
        ];
        assert_eq!(thawed.len(), expected.len());
        for (i, (tree, span)) in thawed.iter().zip(expected).enumerate() {
            assert_same_span(&format!("out[{}]", i), "recipe", tree.span(), span);
        }
    }

    #[test]
    fn thaw_reuses_parsed_literals_by_repr() {
        let input = parse_ts("1u8 x");
        let orig = trees(&input);
        let (frozen, meta) = freeze_rejoin_main(input);
        let out = std::thread::spawn(move || {
            let job = begin_job();
            let melted = trees(&melt_worker(&frozen));
            let x = melted[1].span();
            let lit = |text: &str, span: Span| {
                let mut literal: Literal = text.parse().unwrap();
                literal.set_span(span);
                TokenTree::Literal(literal)
            };
            let out = TokenStream::from_iter(vec![
                melted[0].clone(),
                lit("1u8", x),
                lit("\"s\"", x),
                lit("1u8", Span::call_site()),
                lit("\"s\"", Span::call_site()),
                lit("-2i32", x),
                lit("-2i32", x),
            ]);
            let frozen = freeze_worker(out);
            job.end();
            frozen
        })
        .join()
        .unwrap();
        let thawed = trees(&meta.thaw(&out));
        let x = orig[1].span();
        let call = Span::call_site();
        let mut expected = vec![orig[0].clone()];
        for (text, span) in [
            ("1u8", x),
            ("\"s\"", x),
            ("1u8", call),
            ("\"s\"", call),
            ("-2i32", x),
            ("-2i32", x),
        ] {
            let mut literal: Literal = text.parse().unwrap();
            literal.set_span(span);
            expected.push(TokenTree::Literal(literal));
        }
        assert_same_stream(
            "lits",
            &TokenStream::from_iter(thawed),
            &TokenStream::from_iter(expected),
        );
    }

    #[test]
    fn word_hash_separates_inputs_and_matches_text_freeze() {
        let a = lex_in_job("f(x, 1u8) + \"long string literal text\"");
        let b = lex_in_job("f(x, 1u8) + \"long string literal texu\"");
        let fa = freeze_rejoin_text(&a, 0..a.toks.len());
        let fb = freeze_rejoin_text(&b, 0..b.toks.len());
        assert!(!fa.same_input(&fb));
        assert_ne!(fa.input_hash(), fb.input_hash());
        let fa2 = freeze_rejoin_text(&a, 0..a.toks.len());
        assert_eq!(fa.input_hash(), fa2.input_hash());
        // Tail padding cannot alias a longer text: lengths are hashed first.
        let mut h1 = WordHash::new();
        h1.write_u64(1);
        h1.write_bytes(b"a");
        let mut h2 = WordHash::new();
        h2.write_u64(2);
        h2.write_bytes(b"a\0");
        assert_ne!(h1.0, h2.0);
    }
}
