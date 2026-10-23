//! Verus positional lexing (hidden, not part of the upstream proc-macro2 API).
//!
//! [`lex_positional`] runs the fallback lexer over a whole source text inside
//! a worker job and lowers its output to plain preorder data carrying byte
//! offsets, so that a scheduler can speculatively prepare macro inputs before
//! the compiler delivers them. No `Span` value escapes: the lexer runs with a
//! positional cursor that registers nothing in the source map, and every
//! token it builds is dropped before returning.
//!
//! The lowering follows the token shapes rustc 1.98 hands to proc macros for
//! the same text (see `rustc_expand::proc_macro_server`):
//! - a punct directly followed by `'` (a lifetime or char literal, which are
//!   not punct tokens in rustc) is `Alone`;
//! - a doc comment becomes `#` `!`? `[doc = "…"]`, all `Alone`, whose string
//!   literal escapes every character of the comment with `char::escape_debug`;
//! - identifiers with non-ASCII text are listed in
//!   [`LexedFile::non_ascii_idents`], because rustc NFC-normalizes them and
//!   callers must not assume their text matches.
//!
//! [`normalize_rustc_source`] applies rustc's source-file normalization (BOM
//! removal, CRLF to LF) and blanks a shebang line, so that byte offsets of the
//! lexed text equal rustc's file-relative byte positions.

use crate::fallback;
use crate::parse::{token_stream, Cursor};
use crate::{Delimiter, Spacing, TokenStream, TokenTree};
use alloc::borrow::ToOwned as _;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::{self, Display};
use core::ops::Range;

/// Kind of a [`LexedTok`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexedKind {
    /// A delimited group; its `len` descendant tokens follow it in preorder.
    Group {
        delim: Delimiter,
        len: u32,
    },
    /// Identifier text without the `r#` prefix.
    Ident {
        text: String,
        raw: bool,
    },
    Punct {
        ch: char,
        spacing: Spacing,
    },
    /// Literal source representation, as rustc's `Literal::to_string`.
    Literal {
        repr: String,
    },
}

/// One preorder token with its byte range `lo..hi` in the lexed text. A
/// group's range covers both delimiters; the tokens lowered from one doc
/// comment all carry the range of the comment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexedTok {
    pub kind: LexedKind,
    pub lo: u32,
    pub hi: u32,
}

/// Preorder token list of one source text.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LexedFile {
    pub toks: Vec<LexedTok>,
    /// Ascending indices into `toks` of identifiers with non-ASCII text.
    pub non_ascii_idents: Vec<u32>,
}

impl LexedFile {
    /// Whether any token index in `range` is a non-ASCII identifier.
    pub fn has_non_ascii_ident_in(&self, range: Range<usize>) -> bool {
        let first = self
            .non_ascii_idents
            .partition_point(|&i| (i as usize) < range.start);
        self.non_ascii_idents
            .get(first)
            .is_some_and(|&i| (i as usize) < range.end)
    }
}

/// Lexing failure at byte `offset` of the lexed text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LexError {
    pub offset: u32,
}

impl Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "cannot lex source text at byte {}", self.offset)
    }
}

/// Maps fallback cursor offsets (1 + char index) to byte offsets.
struct OffsetMap {
    // Byte offset of every char index, plus the text length; `None` for ASCII.
    bytes: Option<Vec<u32>>,
}

impl OffsetMap {
    fn new(src: &str) -> Self {
        if src.is_ascii() {
            return OffsetMap { bytes: None };
        }
        let mut bytes: Vec<u32> = src.char_indices().map(|(b, _)| b as u32).collect();
        bytes.push(src.len() as u32);
        OffsetMap { bytes: Some(bytes) }
    }

    fn byte(&self, off: u32) -> u32 {
        let index = off.saturating_sub(1);
        match &self.bytes {
            None => index,
            Some(bytes) => bytes[index as usize],
        }
    }
}

/// Lexes `src` with the fallback lexer and returns its tokens in preorder with
/// byte offsets into `src`. Callable only inside a worker job; it neither
/// registers `src` in the source map nor runs backend detection.
#[track_caller]
pub fn lex_positional(src: &str) -> Result<LexedFile, LexError> {
    crate::__verus_worker::require_job("lex_positional");
    // Cursor offsets are 1 + char index and must fit in u32.
    if src.len() >= (u32::MAX - 1) as usize {
        return Err(LexError { offset: 0 });
    }
    let map = OffsetMap::new(src);
    let cursor = Cursor { rest: src, off: 1 };
    let stream = match token_stream(cursor) {
        Ok(stream) => TokenStream::_new_fallback(stream),
        Err(err) => {
            return Err(LexError {
                offset: map.byte(err.span.lo),
            })
        }
    };
    let mut file = LexedFile::default();
    lower_level(src, &map, stream, &mut file);
    Ok(file)
}

fn lower_level(src: &str, map: &OffsetMap, stream: TokenStream, file: &mut LexedFile) {
    for tt in stream {
        let span: fallback::Span =
            crate::__verus_worker::fallback_span(tt.span(), "lex_positional");
        let (lo, hi) = (map.byte(span.lo), map.byte(span.hi));
        let kind = match tt {
            TokenTree::Group(group) => {
                let index = file.toks.len();
                file.toks.push(LexedTok {
                    kind: LexedKind::Group {
                        delim: group.delimiter(),
                        len: 0,
                    },
                    lo,
                    hi,
                });
                lower_level(src, map, group.stream(), file);
                let subtree = u32::try_from(file.toks.len() - index - 1)
                    .expect("lex_positional: token count overflow");
                if let LexedKind::Group { len, .. } = &mut file.toks[index].kind {
                    *len = subtree;
                }
                continue;
            }
            TokenTree::Ident(ident) => {
                let (text, raw) = crate::__verus_worker::ident_sym_raw(&ident);
                if !text.is_ascii() {
                    let index = u32::try_from(file.toks.len())
                        .expect("lex_positional: token count overflow");
                    file.non_ascii_idents.push(index);
                }
                LexedKind::Ident {
                    text: text.to_owned(),
                    raw,
                }
            }
            TokenTree::Punct(punct) => {
                let ch = punct.as_char();
                let mut spacing = punct.spacing();
                if ch != '\'' && spacing == Spacing::Joint && src[hi as usize..].starts_with('\'') {
                    spacing = Spacing::Alone;
                }
                LexedKind::Punct { ch, spacing }
            }
            TokenTree::Literal(literal) => {
                let text = &src[lo as usize..hi as usize];
                // Only a doc comment lowers to a literal whose text starts with `/`.
                let repr = if text.starts_with('/') {
                    rustc_doc_literal(text)
                } else {
                    crate::__verus_worker::literal_repr(&literal).to_owned()
                };
                LexedKind::Literal { repr }
            }
        };
        file.toks.push(LexedTok { kind, lo, hi });
    }
}

/// rustc's string literal for a doc comment's text: every character of the
/// comment body escaped with `char::escape_debug`.
fn rustc_doc_literal(comment: &str) -> String {
    let body = if comment.starts_with("/*") {
        &comment[3..comment.len() - 2]
    } else {
        // A line comment's range includes the `\r` of a `\r\n` terminator.
        let body = &comment[3..];
        body.strip_suffix('\r').unwrap_or(body)
    };
    let mut repr = String::with_capacity(body.len() + 2);
    repr.push('"');
    for ch in body.chars() {
        repr.extend(ch.escape_debug());
    }
    repr.push('"');
    repr
}

/// Applies rustc's source-file normalization: strips a leading BOM, replaces
/// every `\r\n` with `\n`, and blanks (with spaces, keeping byte offsets) a
/// shebang line that rustc's lexer would skip.
pub fn normalize_rustc_source(src: &str) -> String {
    let src = src.strip_prefix('\u{feff}').unwrap_or(src);
    let mut out = if src.contains("\r\n") {
        src.replace("\r\n", "\n")
    } else {
        src.to_owned()
    };
    if let Some(len) = shebang_len(&out) {
        out.replace_range(..len, &" ".repeat(len));
    }
    out
}

/// Byte length of a shebang line, following `rustc_lexer::strip_shebang`.
fn shebang_len(src: &str) -> Option<usize> {
    let tail = src.strip_prefix("#!")?;
    if next_token_is_open_bracket(tail) {
        return None;
    }
    Some(2 + tail.find('\n').unwrap_or(tail.len()))
}

/// rustc_lexer whitespace (`Pattern_White_Space`).
fn is_rustc_whitespace(ch: char) -> bool {
    matches!(
        ch,
        '\t' | '\n'
            | '\u{000B}'
            | '\u{000C}'
            | '\r'
            | ' '
            | '\u{0085}'
            | '\u{200E}'
            | '\u{200F}'
            | '\u{2028}'
            | '\u{2029}'
    )
}

/// Whether the first token of `s` other than whitespace and non-doc comments
/// is `[`.
fn next_token_is_open_bracket(mut s: &str) -> bool {
    loop {
        s = s.trim_start_matches(is_rustc_whitespace);
        if s.starts_with("//") {
            let doc = (s.starts_with("///") && !s.starts_with("////")) || s.starts_with("//!");
            if doc {
                return false;
            }
            s = &s[s.find('\n').unwrap_or(s.len())..];
        } else if s.starts_with("/*") {
            let doc = (s.starts_with("/**") && !s.starts_with("/**/") && !s.starts_with("/***"))
                || s.starts_with("/*!");
            if doc {
                return false;
            }
            s = skip_block_comment(s);
        } else {
            return s.starts_with('[');
        }
    }
}

/// Skips a (nested) block comment starting at `s`; unterminated runs to EOF.
fn skip_block_comment(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut depth = 0usize;
    let mut i = 0;
    while i + 1 < bytes.len() {
        if bytes[i] == b'/' && bytes[i + 1] == b'*' {
            depth += 1;
            i += 2;
        } else if bytes[i] == b'*' && bytes[i + 1] == b'/' {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return &s[i..];
            }
        } else {
            i += 1;
        }
    }
    ""
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::__verus_worker::{begin_job, prepare_main_thread, WorkerJob};

    fn test_job() -> WorkerJob {
        let _ = prepare_main_thread();
        begin_job()
    }

    fn summary(file: &LexedFile) -> Vec<String> {
        file.toks
            .iter()
            .map(|t| match &t.kind {
                LexedKind::Group { delim, len } => {
                    alloc::format!("G{:?}{}@{}..{}", delim, len, t.lo, t.hi)
                }
                LexedKind::Ident { text, raw } => {
                    alloc::format!(
                        "I{}{}@{}..{}",
                        if *raw { "r#" } else { "" },
                        text,
                        t.lo,
                        t.hi
                    )
                }
                LexedKind::Punct { ch, spacing } => alloc::format!(
                    "P{}{}@{}..{}",
                    ch,
                    if *spacing == Spacing::Joint { "j" } else { "" },
                    t.lo,
                    t.hi
                ),
                LexedKind::Literal { repr } => alloc::format!("L{}@{}..{}", repr, t.lo, t.hi),
            })
            .collect()
    }

    #[cfg(not(fuzzing))]
    #[test]
    fn positional_offsets_and_shapes() {
        let before = fallback::source_map_file_count();
        let _job = test_job();
        let file = lex_positional("f(x: &'a u8) -> é { r#type <==> 'c' }").unwrap();
        assert_eq!(
            summary(&file),
            [
                "If@0..1",
                "GParenthesis6@1..12",
                "Ix@2..3",
                "P:@3..4",
                "P&@5..6",
                "P'j@6..7",
                "Ia@7..8",
                "Iu8@9..11",
                "P-j@13..14",
                "P>@14..15",
                "Ié@16..18",
                "GBrace6@19..38",
                "Ir#type@21..27",
                "P<j@28..29",
                "P=j@29..30",
                "P=j@30..31",
                "P>@31..32",
                "L'c'@33..36",
            ]
        );
        assert_eq!(file.non_ascii_idents, [10]);
        assert!(file.has_non_ascii_ident_in(0..11));
        assert!(!file.has_non_ascii_ident_in(11..18));
        assert!(!file.has_non_ascii_ident_in(0..10));
        assert_eq!(fallback::source_map_file_count(), before);
    }

    #[test]
    fn punct_before_quote_is_alone() {
        let _job = test_job();
        let file = lex_positional("&'a x=='b' <'c>").unwrap();
        assert_eq!(
            summary(&file),
            [
                "P&@0..1",
                "P'j@1..2",
                "Ia@2..3",
                "Ix@4..5",
                "P=j@5..6",
                "P=@6..7",
                "L'b'@7..10",
                "P<@11..12",
                "P'j@12..13",
                "Ic@13..14",
                "P>@14..15",
            ]
        );
    }

    #[test]
    fn doc_comments_use_rustc_escaping() {
        let _job = test_job();
        let file = lex_positional("/// it's \"q\" \\ \0 \t é\n//! inner\n/** blk */ x").unwrap();
        let s = summary(&file);
        assert_eq!(
            s,
            [
                "P#@0..21",
                "GBracket3@0..21",
                "Idoc@0..21",
                "P=@0..21",
                "L\" it\\'s \\\"q\\\" \\\\ \\0 \\t é\"@0..21",
                "P#@22..31",
                "P!@22..31",
                "GBracket3@22..31",
                "Idoc@22..31",
                "P=@22..31",
                "L\" inner\"@22..31",
                "P#@32..42",
                "GBracket3@32..42",
                "Idoc@32..42",
                "P=@32..42",
                "L\" blk \"@32..42",
                "Ix@43..44",
            ]
        );
        // Literal text equals what rustc's `escape_debug` lowering produces.
        let mut expected = String::from("\"");
        for ch in " it's \"q\" \\ \0 \t é".chars() {
            expected.extend(ch.escape_debug());
        }
        expected.push('"');
        assert_eq!(file.toks[4].kind, LexedKind::Literal { repr: expected });
    }

    #[test]
    fn lex_error_offsets() {
        let _job = test_job();
        assert_eq!(lex_positional("é ( b"), Err(LexError { offset: 3 }));
        assert_eq!(lex_positional("a ) b"), Err(LexError { offset: 2 }));
        assert_eq!(lex_positional("a \u{1} b"), Err(LexError { offset: 2 }));
        assert_eq!(lex_positional(""), Ok(LexedFile::default()));
    }

    #[test]
    #[should_panic(expected = "outside a worker job")]
    fn requires_job() {
        let _ = lex_positional("a");
    }

    #[test]
    fn negative_literal_is_minus_and_literal() {
        let _job = test_job();
        let file = lex_positional("-1i32 - 2.5").unwrap();
        assert_eq!(
            summary(&file),
            ["P-@0..1", "L1i32@1..5", "P-@6..7", "L2.5@8..11"]
        );
    }

    #[test]
    fn normalize_source() {
        let blank = |n: usize| " ".repeat(n);
        assert_eq!(normalize_rustc_source("\u{feff}a\r\nb\rc\r\n"), "a\nb\rc\n");
        assert_eq!(
            normalize_rustc_source("#!/usr/bin/env \u{e9}\nfn"),
            blank(17) + "\nfn"
        );
        assert_eq!(normalize_rustc_source("#!/bin/sh"), blank(9));
        assert_eq!(normalize_rustc_source("#![attr]\nfn"), "#![attr]\nfn");
        let attr = "#! // c\n /* n /* d */ */ [attr]";
        assert_eq!(normalize_rustc_source(attr), attr);
        assert_eq!(normalize_rustc_source("#! /// d\n[x]"), blank(8) + "\n[x]");
        assert_eq!(normalize_rustc_source("#!/**/[x]"), "#!/**/[x]");
        assert_eq!(normalize_rustc_source("#!/** d */[x]"), blank(13));
        assert_eq!(normalize_rustc_source("\u{feff}#!x\r\ny"), blank(3) + "\ny");
        assert_eq!(normalize_rustc_source("a #!x"), "a #!x");
    }
}
