//! A stably addressed token buffer supporting efficient traversal based on a
//! cheaply copyable cursor.

// This module is heavily commented as it contains most of the unsafe code in
// Syn, and caution should be used when editing it. The public-facing interface
// is 100% safe but the implementation is fragile internally.

use crate::ext::TokenStreamExt as _;
use crate::Lifetime;
use alloc::boxed::Box;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::cell::OnceCell;
use core::cmp::Ordering;
use core::fmt::{self, Write as _};
use core::marker::PhantomData;
use core::ptr;
use proc_macro2::extra::DelimSpan;
use proc_macro2::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

/// Internal type which is used instead of `TokenTree` to represent a token tree
/// within a `TokenBuffer`.
enum Entry {
    // Mimicking types from proc-macro.
    // Group entries may cache a lazily rebuilt rejoined stream.
    Group(Group, usize, Option<Box<OnceCell<Group>>>),
    // Identifier and lazily cached text.
    Ident(Ident, OnceCell<Box<str>>),
    Punct(Punct),
    // Rejoined buffers retain the original form of split negative literals.
    Literal(Literal, Option<Box<Literal>>),
    // End entries contain the offset (negative) to the start of the buffer, and
    // offset (negative) to the matching Group entry.
    End(isize, isize),
}

/// A buffer that can be efficiently traversed multiple times, unlike
/// `TokenStream` which requires a deep copy in order to traverse more than
/// once.
pub struct TokenBuffer {
    // NOTE: Do not implement clone on this - while the current design could be
    // cloned, other designs which could be desirable may not be cloneable.
    entries: Box<[Entry]>,
}

impl TokenBuffer {
    fn recursive_new(entries: &mut Vec<Entry>, stream: TokenStream) {
        for tt in stream {
            match tt {
                TokenTree::Ident(ident) => entries.push(Entry::Ident(ident, OnceCell::new())),
                TokenTree::Punct(punct) => entries.push(Entry::Punct(punct)),
                TokenTree::Literal(literal) => entries.push(Entry::Literal(literal, None)),
                TokenTree::Group(group) => {
                    let group_start_index = entries.len();
                    entries.push(Entry::End(0, 0)); // we replace this below
                    Self::recursive_new(entries, group.stream());
                    let group_end_index = entries.len();
                    let group_offset = group_end_index - group_start_index;
                    entries.push(Entry::End(
                        -(group_end_index as isize),
                        -(group_offset as isize),
                    ));
                    entries[group_start_index] = Entry::Group(group, group_offset, None);
                }
            }
        }
    }

    // Builds the buffer from rejoined levels while preserving bridge normalization of
    // group spans and negative numeric literals.
    // `rejoin` is false when the stream was already rejoined at every level.
    fn recursive_new_rejoin(entries: &mut Vec<Entry>, stream: TokenStream, rejoin: bool) {
        let mut tokens: Vec<TokenTree> = stream.into_iter().collect();
        if rejoin {
            crate::verus::rejoin_level(&mut tokens);
        }
        entries.reserve(tokens.len() + 1);
        for tt in tokens {
            match tt {
                TokenTree::Ident(ident) => entries.push(Entry::Ident(ident, OnceCell::new())),
                TokenTree::Punct(punct) => entries.push(Entry::Punct(punct)),
                TokenTree::Literal(literal) => {
                    if let Some(positive) = split_negative_literal(&literal) {
                        let mut minus = Punct::new('-', Spacing::Alone);
                        minus.set_span(literal.span());
                        entries.push(Entry::Punct(minus));
                        entries.push(Entry::Literal(positive, Some(Box::new(literal))));
                    } else {
                        entries.push(Entry::Literal(literal, None));
                    }
                }
                TokenTree::Group(mut group) => {
                    group.set_span(group.span());
                    let group_start_index = entries.len();
                    entries.push(Entry::End(0, 0)); // we replace this below
                    Self::recursive_new_rejoin(entries, group.stream(), rejoin);
                    let group_end_index = entries.len();
                    let group_offset = group_end_index - group_start_index;
                    entries.push(Entry::End(
                        -(group_end_index as isize),
                        -(group_offset as isize),
                    ));
                    entries[group_start_index] =
                        Entry::Group(group, group_offset, Some(Box::new(OnceCell::new())));
                }
            }
        }
    }

    /// Creates a token buffer with Verus operators rejoined during construction.
    pub(crate) fn new2_rejoin(stream: TokenStream) -> Self {
        Self::new2_rejoin_with(stream, true)
    }

    /// Creates a rejoin-style token buffer from a stream already rejoined at every level.
    #[doc(hidden)]
    pub fn new2_prejoined(stream: TokenStream) -> Self {
        Self::new2_rejoin_with(stream, false)
    }

    fn new2_rejoin_with(stream: TokenStream, rejoin: bool) -> Self {
        let mut entries = Vec::new();
        Self::recursive_new_rejoin(&mut entries, stream, rejoin);
        entries.push(Entry::End(-(entries.len() as isize), 0));
        Self {
            entries: entries.into_boxed_slice(),
        }
    }

    /// Creates a `TokenBuffer` containing all the tokens from the input
    /// `proc_macro::TokenStream`.
    #[cfg(feature = "proc-macro")]
    #[cfg_attr(docsrs, doc(cfg(feature = "proc-macro")))]
    pub fn new(stream: proc_macro::TokenStream) -> Self {
        Self::new2(stream.into())
    }

    /// Creates a `TokenBuffer` containing all the tokens from the input
    /// `proc_macro2::TokenStream`.
    pub fn new2(stream: TokenStream) -> Self {
        let mut entries = Vec::new();
        Self::recursive_new(&mut entries, stream);
        entries.push(Entry::End(-(entries.len() as isize), 0));
        Self {
            entries: entries.into_boxed_slice(),
        }
    }

    /// Creates a cursor referencing the first token in the buffer and able to
    /// traverse until the end of the buffer.
    pub fn begin(&self) -> Cursor {
        let ptr = self.entries.as_ptr();
        unsafe { Cursor::create(ptr, ptr.add(self.entries.len() - 1)) }
    }
}

/// A cheaply copyable cursor into a `TokenBuffer`.
///
/// This cursor holds a shared reference into the immutable data which is used
/// internally to represent a `TokenStream`, and can be efficiently manipulated
/// and copied around.
///
/// An empty `Cursor` can be created directly, or one may create a `TokenBuffer`
/// object and get a cursor to its first token with `begin()`.
pub struct Cursor<'a> {
    // The current entry which the `Cursor` is pointing at.
    ptr: *const Entry,
    // This is the only `Entry::End` object which this cursor is allowed to
    // point at. All other `End` objects are skipped over in `Cursor::create`.
    scope: *const Entry,
    // Cursor is covariant in 'a. This field ensures that our pointers are still
    // valid.
    marker: PhantomData<&'a Entry>,
}

impl<'a> Cursor<'a> {
    /// Creates a cursor referencing a static empty TokenStream.
    pub fn empty() -> Self {
        // It's safe in this situation for us to put an `Entry` object in global
        // storage, despite it not actually being safe to send across threads
        // (`Ident` is a reference into a thread-local table). This is because
        // this entry never includes a `Ident` object.
        //
        // This wrapper struct allows us to break the rules and put a `Sync`
        // object in global storage.
        struct UnsafeSyncEntry(Entry);
        unsafe impl Sync for UnsafeSyncEntry {}
        static EMPTY_ENTRY: UnsafeSyncEntry = UnsafeSyncEntry(Entry::End(0, 0));

        Cursor {
            ptr: &EMPTY_ENTRY.0,
            scope: &EMPTY_ENTRY.0,
            marker: PhantomData,
        }
    }

    /// This create method intelligently exits non-explicitly-entered
    /// `None`-delimited scopes when the cursor reaches the end of them,
    /// allowing for them to be treated transparently.
    unsafe fn create(mut ptr: *const Entry, scope: *const Entry) -> Self {
        // NOTE: If we're looking at a `End`, we want to advance the cursor
        // past it, unless `ptr == scope`, which means that we're at the edge of
        // our cursor's scope. We should only have `ptr != scope` at the exit
        // from None-delimited groups entered with `ignore_none`.
        while let Entry::End(..) = unsafe { &*ptr } {
            if ptr::eq(ptr, scope) {
                break;
            }
            ptr = unsafe { ptr.add(1) };
        }

        Cursor {
            ptr,
            scope,
            marker: PhantomData,
        }
    }

    /// Get the current entry.
    fn entry(self) -> &'a Entry {
        unsafe { &*self.ptr }
    }

    /// Bump the cursor to point at the next token after the current one. This
    /// is undefined behavior if the cursor is currently looking at an
    /// `Entry::End`.
    ///
    /// If the cursor is looking at an `Entry::Group`, the bumped cursor will
    /// point at the first token in the group (with the same scope end).
    unsafe fn bump_ignore_group(self) -> Cursor<'a> {
        unsafe { Cursor::create(self.ptr.add(1), self.scope) }
    }

    /// While the cursor is looking at a `None`-delimited group, move it to look
    /// at the first token inside instead. If the group is empty, this will move
    /// the cursor past the `None`-delimited group.
    ///
    /// WARNING: This mutates its argument.
    fn ignore_none(&mut self) {
        while let Entry::Group(group, _, _) = self.entry() {
            if group.delimiter() == Delimiter::None {
                unsafe { *self = self.bump_ignore_group() };
            } else {
                break;
            }
        }
    }

    /// Checks whether the cursor is currently pointing at the end of its valid
    /// scope.
    pub fn eof(self) -> bool {
        // We're at eof if we're at the end of our scope.
        ptr::eq(self.ptr, self.scope)
    }

    /// If the cursor is pointing at a `Ident`, returns it along with a cursor
    /// pointing at the next `TokenTree`.
    pub fn ident(mut self) -> Option<(Ident, Cursor<'a>)> {
        self.ignore_none();
        match self.entry() {
            Entry::Ident(ident, _) => Some((ident.clone(), unsafe { self.bump_ignore_group() })),
            _ => None,
        }
    }

    /// Returns the identifier, its cached text, and the next cursor.
    pub(crate) fn ident_str(mut self) -> Option<(&'a Ident, &'a str, Cursor<'a>)> {
        self.ignore_none();
        match self.entry() {
            Entry::Ident(ident, text) => {
                let text = text.get_or_init(|| ident.to_string().into_boxed_str());
                Some((ident, text, unsafe { self.bump_ignore_group() }))
            }
            _ => None,
        }
    }

    /// If the cursor is pointing at a `Punct`, returns it along with a cursor
    /// pointing at the next `TokenTree`.
    pub fn punct(mut self) -> Option<(Punct, Cursor<'a>)> {
        self.ignore_none();
        match self.entry() {
            Entry::Punct(punct) if punct.as_char() != '\'' => {
                Some((punct.clone(), unsafe { self.bump_ignore_group() }))
            }
            _ => None,
        }
    }

    /// If the cursor is pointing at a `Literal`, return it along with a cursor
    /// pointing at the next `TokenTree`.
    pub fn literal(mut self) -> Option<(Literal, Cursor<'a>)> {
        self.ignore_none();
        match self.entry() {
            Entry::Literal(literal, _) => {
                Some((literal.clone(), unsafe { self.bump_ignore_group() }))
            }
            _ => None,
        }
    }

    /// If the cursor is pointing at a `Lifetime`, returns it along with a
    /// cursor pointing at the next `TokenTree`.
    pub fn lifetime(mut self) -> Option<(Lifetime, Cursor<'a>)> {
        self.ignore_none();
        match self.entry() {
            Entry::Punct(punct) if punct.as_char() == '\'' && punct.spacing() == Spacing::Joint => {
                let next = unsafe { self.bump_ignore_group() };
                let (ident, rest) = next.ident()?;
                let lifetime = Lifetime {
                    apostrophe: punct.span(),
                    ident,
                };
                Some((lifetime, rest))
            }
            _ => None,
        }
    }

    /// If the cursor is pointing at a `Group` with the given delimiter, returns
    /// a cursor into that group and one pointing to the next `TokenTree`.
    pub fn group(mut self, delim: Delimiter) -> Option<(Cursor<'a>, DelimSpan, Cursor<'a>)> {
        // If we're not trying to enter a none-delimited group, we want to
        // ignore them. We have to make sure to _not_ ignore them when we want
        // to enter them, of course. For obvious reasons.
        if delim != Delimiter::None {
            self.ignore_none();
        }

        if let Entry::Group(group, end_offset, _) = self.entry() {
            if group.delimiter() == delim {
                let span = group.delim_span();
                let end_of_group = unsafe { self.ptr.add(*end_offset) };
                let inside_of_group = unsafe { Cursor::create(self.ptr.add(1), end_of_group) };
                let after_group = unsafe { Cursor::create(end_of_group, self.scope) };
                return Some((inside_of_group, span, after_group));
            }
        }

        None
    }

    /// If the cursor is pointing at a `Group`, returns a cursor into the group
    /// and one pointing to the next `TokenTree`.
    pub fn any_group(self) -> Option<(Cursor<'a>, Delimiter, DelimSpan, Cursor<'a>)> {
        if let Entry::Group(group, end_offset, _) = self.entry() {
            let delimiter = group.delimiter();
            let span = group.delim_span();
            let end_of_group = unsafe { self.ptr.add(*end_offset) };
            let inside_of_group = unsafe { Cursor::create(self.ptr.add(1), end_of_group) };
            let after_group = unsafe { Cursor::create(end_of_group, self.scope) };
            return Some((inside_of_group, delimiter, span, after_group));
        }

        None
    }

    pub(crate) fn any_group_token(self) -> Option<(Group, Cursor<'a>)> {
        if let Entry::Group(_, end_offset, _) = self.entry() {
            let end_of_group = unsafe { self.ptr.add(*end_offset) };
            let after_group = unsafe { Cursor::create(end_of_group, self.scope) };
            return Some((self.group_token(), after_group));
        }

        None
    }

    // Returns the stored group or its cached rejoined form.
    fn group_token(self) -> Group {
        match self.entry() {
            Entry::Group(group, _, None) => group.clone(),
            Entry::Group(group, end_offset, Some(cell)) => cell
                .get_or_init(|| {
                    let mut rebuilt = Group::new(group.delimiter(), unsafe {
                        self.rebuilt_stream(*end_offset)
                    });
                    rebuilt.set_span(group.span());
                    rebuilt
                })
                .clone(),
            _ => unreachable!(),
        }
    }

    // Reconstructs a rejoined group stream, restoring negative literal tokens.
    unsafe fn rebuilt_stream(self, end_offset: usize) -> TokenStream {
        let end = unsafe { self.ptr.add(end_offset) };
        let mut trees: Vec<TokenTree> = Vec::new();
        let mut ptr = unsafe { self.ptr.add(1) };
        while ptr < end {
            let cursor = Cursor {
                ptr,
                scope: end,
                marker: PhantomData,
            };
            let len = match unsafe { &*ptr } {
                Entry::Group(_, end_offset, _) => {
                    trees.push(TokenTree::Group(cursor.group_token()));
                    *end_offset + 1
                }
                Entry::Ident(ident, _) => {
                    trees.push(TokenTree::Ident(ident.clone()));
                    1
                }
                Entry::Punct(punct) => match unsafe { &*ptr.add(1) } {
                    Entry::Literal(_, Some(negative)) => {
                        trees.push(TokenTree::Literal((**negative).clone()));
                        2
                    }
                    _ => {
                        trees.push(TokenTree::Punct(punct.clone()));
                        1
                    }
                },
                Entry::Literal(literal, _) => {
                    trees.push(TokenTree::Literal(literal.clone()));
                    1
                }
                Entry::End(..) => unreachable!(),
            };
            ptr = unsafe { ptr.add(len) };
        }
        TokenStream::from_iter(trees)
    }

    /// Copies all remaining tokens visible from this cursor into a
    /// `TokenStream`.
    pub fn token_stream(self) -> TokenStream {
        let mut tokens = TokenStream::new();
        let mut cursor = self;
        while let Some((tt, rest)) = cursor.token_tree() {
            tokens.append(tt);
            cursor = rest;
        }
        tokens
    }

    /// If the cursor is pointing at a `TokenTree`, returns it along with a
    /// cursor pointing at the next `TokenTree`.
    ///
    /// Returns `None` if the cursor has reached the end of its stream.
    ///
    /// This method does not treat `None`-delimited groups as transparent, and
    /// will return a `Group(None, ..)` if the cursor is looking at one.
    pub fn token_tree(self) -> Option<(TokenTree, Cursor<'a>)> {
        let (tree, len) = match self.entry() {
            Entry::Group(_, end_offset, _) => (self.group_token().into(), *end_offset),
            Entry::Literal(literal, _) => (literal.clone().into(), 1),
            Entry::Ident(ident, _) => (ident.clone().into(), 1),
            Entry::Punct(punct) => (punct.clone().into(), 1),
            Entry::End(..) => return None,
        };

        let rest = unsafe { Cursor::create(self.ptr.add(len), self.scope) };
        Some((tree, rest))
    }

    /// Returns the `Span` of the current token, or `Span::call_site()` if this
    /// cursor points to eof.
    pub fn span(mut self) -> Span {
        match self.entry() {
            Entry::Group(group, _, _) => group.span(),
            Entry::Literal(literal, _) => literal.span(),
            Entry::Ident(ident, _) => ident.span(),
            Entry::Punct(punct) => punct.span(),
            Entry::End(_, offset) => {
                self.ptr = unsafe { self.ptr.offset(*offset) };
                if let Entry::Group(group, _, _) = self.entry() {
                    group.span_close()
                } else {
                    Span::call_site()
                }
            }
        }
    }

    /// Returns the `Span` of the token immediately prior to the position of
    /// this cursor, or of the current token if there is no previous one.
    #[cfg(any(feature = "full", feature = "derive"))]
    pub(crate) fn prev_span(mut self) -> Span {
        if start_of_buffer(self) < self.ptr {
            self.ptr = unsafe { self.ptr.sub(1) };
        }
        self.span()
    }

    /// Skip over the next token that is not a None-delimited group, without
    /// cloning it. Returns `None` if this cursor points to eof.
    ///
    /// This method treats `'lifetimes` as a single token.
    pub(crate) fn skip(mut self) -> Option<Cursor<'a>> {
        self.ignore_none();

        let len = match self.entry() {
            Entry::End(..) => return None,

            // Treat lifetimes as a single tt for the purposes of 'skip'.
            Entry::Punct(punct) if punct.as_char() == '\'' && punct.spacing() == Spacing::Joint => {
                match unsafe { &*self.ptr.add(1) } {
                    Entry::Ident(..) => 2,
                    _ => 1,
                }
            }

            Entry::Group(_, end_offset, _) => *end_offset,
            _ => 1,
        };

        Some(unsafe { Cursor::create(self.ptr.add(len), self.scope) })
    }

    pub(crate) fn scope_delimiter(self) -> Delimiter {
        match unsafe { &*self.scope } {
            Entry::End(_, offset) => match unsafe { &*self.scope.offset(*offset) } {
                Entry::Group(group, _, _) => group.delimiter(),
                _ => Delimiter::None,
            },
            _ => unreachable!(),
        }
    }
}

impl<'a> Copy for Cursor<'a> {}

impl<'a> Clone for Cursor<'a> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<'a> Eq for Cursor<'a> {}

impl<'a> PartialEq for Cursor<'a> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.ptr, other.ptr)
    }
}

impl<'a> PartialOrd for Cursor<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if same_buffer(*self, *other) {
            Some(cmp_assuming_same_buffer(*self, *other))
        } else {
            None
        }
    }
}

pub(crate) fn same_scope(a: Cursor, b: Cursor) -> bool {
    ptr::eq(a.scope, b.scope)
}

pub(crate) fn same_buffer(a: Cursor, b: Cursor) -> bool {
    ptr::eq(start_of_buffer(a), start_of_buffer(b))
}

fn start_of_buffer(cursor: Cursor) -> *const Entry {
    unsafe {
        match &*cursor.scope {
            Entry::End(offset, _) => cursor.scope.offset(*offset),
            _ => unreachable!(),
        }
    }
}

pub(crate) fn cmp_assuming_same_buffer(a: Cursor, b: Cursor) -> Ordering {
    a.ptr.cmp(&b.ptr)
}

pub(crate) fn open_span_of_group(cursor: Cursor) -> Span {
    match cursor.entry() {
        Entry::Group(group, _, _) => group.span_open(),
        _ => cursor.span(),
    }
}

// Splits a proc-macro-created negative numeric literal using its original span.
fn split_negative_literal(literal: &Literal) -> Option<Literal> {
    struct FirstByte(Option<u8>);
    impl fmt::Write for FirstByte {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            match s.as_bytes().first() {
                Some(&b) => {
                    self.0 = Some(b);
                    Err(fmt::Error)
                }
                None => Ok(()),
            }
        }
    }
    let mut first = FirstByte(None);
    let _ = write!(first, "{}", literal);
    if first.0 != Some(b'-') {
        return None;
    }
    let text = literal.to_string();
    let mut positive: Literal = text[1..]
        .parse()
        .expect("negative literal without a number");
    positive.set_span(literal.span());
    Some(positive)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejoin_buffer_splits_negative_literal() {
        let literal = Literal::i64_unsuffixed(-1);
        let positive = split_negative_literal(&literal).expect("negative literal");
        assert_eq!(positive.to_string(), "1");
        assert_eq!(
            alloc::format!("{:?}", positive.span()),
            alloc::format!("{:?}", literal.span())
        );

        let input = TokenStream::from(TokenTree::Literal(literal));
        let buffer = TokenBuffer::new2_rejoin(input);
        let cursor = buffer.begin();
        let (minus, cursor) = cursor.punct().expect("minus token");
        assert_eq!(minus.as_char(), '-');
        let (positive, cursor) = cursor.literal().expect("positive literal");
        assert_eq!(positive.to_string(), "1");
        assert!(cursor.eof());
    }
}
