# Verus modifications

This directory is proc-macro2 1.0.107 (crates.io release, upstream commit
`ed8a5497669cd63db33bf24646f261b012bbbc4a`), licensed under MIT OR Apache-2.0,
modified by the Verus contributors. The Verus source workspace selects it with
`[patch.crates-io]`.

Changes: the hidden worker-job module `src/verus_worker.rs` (new) and its hooks
in `src/lib.rs`, `src/fallback.rs`, `src/parse.rs`, and `src/detection.rs`;
the hidden positional lexer `src/verus_lex.rs` (new, re-exported from
`__verus_worker`); `build.rs` and `links` in `Cargo.toml` advertise that module
to direct dependents. The public upstream API is otherwise unchanged.

Inside a worker job, span location queries (`start`, `end`, `byte_range`,
`file`, `local_file`, `source_text`) panic instead of returning dummy values,
so the job fails and is rerun serially.

Positional lexing (`__verus_worker::lex_positional`, worker jobs only) runs
the unchanged fallback lexer with a positional cursor (`off: 1`) that registers
nothing in the source map, and lowers the result to plain preorder data
(`LexedFile`/`LexedTok`, byte offsets) so no `Span` escapes. It applies the
token shapes rustc 1.98 gives proc macros where the fallback lexer differs: a
punct directly followed by `'` is `Alone`, and doc-comment literals escape
every character with `char::escape_debug`; identifiers with non-ASCII text are
reported (rustc NFC-normalizes them). `normalize_rustc_source` strips a BOM,
replaces `\r\n` with `\n`, and blanks a shebang line as `rustc_lexer` would
skip it, keeping rustc's byte offsets. Its consumer is `verus_syn`'s
`worker_tokens::freeze_rejoin_text`, which freezes a lexed range exactly like
`freeze_rejoin_main` (with offset-adjacency rejoining through the shared
`verus::rejoin_core`), and `ThawMetadata::adopt`, which accepts such a
speculative freeze when its IR equals the real one.
