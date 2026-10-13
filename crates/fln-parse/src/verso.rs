//! Verso doc comments: where `doc.verso` is set, a doc comment's body is not one atom but a Verso
//! document (`Lean/DocString/Parser.lean`, run by `versoCommentBodyFn` in `Lean/Parser/Term.lean`):
//! paragraphs, lists, headers and code blocks of text, code, roles, emphasis and links. Ported
//! combinator by combinator, with the pin's positions. A body the pin's parser fails on, or
//! recovers in, is its `parseFailure`, as at the pin. A body holding what this port does not read
//! (a directive, a metadata block, a link or footnote definition, a description list, a numeral or
//! a string escape outside the plain ones) is `None`, and the caller keeps the plain body.

use crate::null_node;
use fln_core::name::Name;
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::token::{is_id_first, is_id_rest};
use fln_syntax::tree::Syntax;

/// A doc comment's Verso body: its blocks, or the pin's `parseFailure`.
pub(crate) enum Body {
    Blocks(Syntax),
    Failure,
}

/// Why a parser stopped.
enum Stop {
    /// An error with the parser state at this position: an alternative is tried only where the
    /// failed one started (`<|>` backtracks only an error that consumed nothing).
    Fail(usize),
    /// An error inside a `recover…` combinator. The pin's parse goes on past it, but any recovered
    /// error makes the whole body a `parseFailure`, so nothing after it can change the result.
    Recovered,
    /// Syntax this port does not read.
    Unsupported,
}

type Parsed<T> = Result<T, Stop>;

/// `recover…`: an error here is recovered from, which fails the document.
fn recovered(stop: Stop) -> Stop {
    match stop {
        Stop::Fail(_) => Stop::Recovered,
        other => other,
    }
}

/// `p <|> q`: `q` only where `p` failed without moving.
fn first_of<T>(at: usize, parsers: &[&dyn Fn() -> Parsed<T>]) -> Parsed<T> {
    for parser in parsers {
        match parser() {
            Err(Stop::Fail(stopped)) if stopped == at => {}
            other => return other,
        }
    }
    Err(Stop::Fail(at))
}

/// `manyFn` (`many1Fn` when `one`): repeat `parse` until it fails without moving. A success that
/// moves nothing after the first is the pin's "did not consume anything" error.
fn many<T>(
    at: usize,
    one: bool,
    mut parse: impl FnMut(usize) -> Parsed<(T, usize)>,
) -> Parsed<(Vec<T>, usize)> {
    let mut items = Vec::new();
    let mut pos = at;
    loop {
        let first = one && items.is_empty();
        match parse(pos) {
            Ok((_, next)) if next == pos && !first => return Err(Stop::Fail(pos)),
            Ok((item, next)) => {
                items.push(item);
                pos = next;
            }
            Err(Stop::Fail(stopped)) if stopped == pos && !first => return Ok((items, pos)),
            Err(stop) => return Err(stop),
        }
    }
}

/// `String.quote`.
fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for c in text.chars() {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            c if u32::from(c) <= 31 || c == '\x7f' => {
                out.push_str(&format!("\\x{:02x}", u32::from(c)));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `unescapeStr`: each backslash stands for the character after it.
fn unescape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            out.extend(chars.next());
        } else {
            out.push(c);
        }
    }
    out
}

/// `Char.isWhitespace`.
fn is_whitespace(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\r' | '\n')
}

fn kind(name: &str) -> Name {
    Name::from_components(["Lean", "Doc", "Syntax", name])
}

fn syntax(name: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(kind(name), args)
}

/// An atom over `start..end` (`asStringFn`, `chFn`), or zero-width at `start` (`fakeAtomHere`).
fn atom(start: usize, end: usize, val: impl Into<String>) -> Syntax {
    Syntax::atom(
        SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(start)),
            pos: BytePos(start),
            trailing: ByteSpan::empty_at(BytePos(end)),
            end_pos: BytePos(end),
        },
        val,
    )
}

/// `fakeAtom` with no source information.
fn fake(val: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, val)
}

/// A literal node (`str`, `num`) over one atom.
fn literal(kind: &str, atom: Syntax) -> Syntax {
    Syntax::node(Name::str(Name::anonymous(), kind), vec![atom])
}

/// Where a list item's indicator is: its column and its kind (the bullet, or the character after
/// an ordered item's number).
#[derive(Clone, Copy)]
enum List {
    Unordered(char, usize),
    Ordered(char, usize),
}

/// `BlockCtxt`'s per-block fields; the document-wide ones are on [`Doc`].
#[derive(Clone, Default)]
struct Blocks {
    min_indent: usize,
    lists: Vec<List>,
}

/// `InlineCtxt`.
#[derive(Clone, Copy)]
struct Inlines {
    newlines: bool,
    bold: Option<usize>,
    emph: Option<usize>,
    in_link: bool,
}

const TEXT_LINE: Inlines = Inlines {
    newlines: true,
    bold: None,
    emph: None,
    in_link: false,
};

struct Doc<'a> {
    text: &'a str,
    /// `c'.endPos`: the `-` of the closing `-/`.
    end: usize,
    /// `BlockCtxt.baseColumn`.
    base: usize,
    /// `BlockCtxt.docStartPosition` where `forDocString` sets one: its line's start, its column.
    doc_start: Option<(usize, usize)>,
}

/// The Verso document between `start` (where the opener's whitespace ends) and `close` (the `-`
/// of the closing `-/`) in `text`, the command's source, whose first byte is taken to be a line's
/// first column. `None` where it holds syntax this port does not read.
#[inline(never)]
pub(crate) fn body(text: &str, start: usize, close: usize) -> Option<Body> {
    let doc = Doc::for_doc_string(text, start, close);
    // `document`: spaces, blank lines, then blocks.
    let at = doc.blank_lines(doc.spaces(start));
    match doc.blocks(&Blocks::default(), at, false) {
        Ok((blocks, end)) if end >= close => Some(Body::Blocks(blocks)),
        Ok(_) | Err(Stop::Fail(_) | Stop::Recovered) => Some(Body::Failure),
        Err(Stop::Unsupported) => None,
    }
}

impl Doc<'_> {
    /// `BlockCtxt.forDocString`: the base column is the least of the opener's (counted, as the pin
    /// counts it, three bytes before `start`), the closer's and every content line's indentation.
    fn for_doc_string(text: &str, start: usize, close: usize) -> Doc<'_> {
        let mut doc = Doc {
            text,
            end: close,
            base: 0,
            doc_start: None,
        };
        let mut base = doc.column(start.saturating_sub(3)).min(doc.column(close));
        // `minContentIndent`.
        let (mut after_newline, mut column) = (false, 0);
        for c in text[start..close].chars() {
            if c == '\n' {
                after_newline = true;
                column = 0;
            } else if after_newline && c != ' ' {
                base = base.min(column);
                after_newline = false;
            } else {
                column += 1;
            }
        }
        doc.base = base;
        let column = doc.column(start);
        if column > base {
            let first = doc.spaces(start);
            doc.doc_start = Some((doc.line_start(first), doc.column(first)));
        }
        doc
    }

    fn peek(&self, at: usize) -> Option<char> {
        self.text.get(at..self.end)?.chars().next()
    }

    fn starts(&self, at: usize, prefix: &str) -> bool {
        self.text
            .get(at..self.end)
            .is_some_and(|rest| rest.starts_with(prefix))
    }

    fn line_start(&self, at: usize) -> usize {
        self.text[..at].rfind('\n').map_or(0, |newline| newline + 1)
    }

    /// `FileMap.toPosition`'s column: characters since the line's start.
    fn column(&self, at: usize) -> usize {
        self.text[self.line_start(at)..at].chars().count()
    }

    /// The end of the run of `c` from `at`.
    fn run(&self, at: usize, c: char) -> usize {
        let mut pos = at;
        while self.peek(pos) == Some(c) {
            pos += c.len_utf8();
        }
        pos
    }

    fn spaces(&self, at: usize) -> usize {
        self.run(at, ' ')
    }

    /// `manyFn blankLine`: lines holding only spaces.
    fn blank_lines(&self, at: usize) -> usize {
        let mut pos = at;
        loop {
            let after = self.spaces(pos);
            if self.peek(after) != Some('\n') {
                return pos;
            }
            pos = after + 1;
        }
    }

    /// `bol`: at or before the base column, or on the document's first line before its start.
    fn bol(&self, at: usize) -> bool {
        let column = self.column(at);
        column <= self.base
            || self
                .doc_start
                .is_some_and(|(line, start)| column <= start && self.line_start(at) == line)
    }

    /// `onlyBlockOpeners`: whether the line holds only list and quote openers before `at`.
    fn only_block_openers(&self, at: usize) -> bool {
        let bytes = self.text.as_bytes();
        let mut pos = self.line_start(at);
        while pos < at && pos < self.end {
            if bytes[pos].is_ascii_digit() {
                while pos < bytes.len() && bytes[pos].is_ascii_digit() && pos < at {
                    pos += 1;
                }
                if pos >= bytes.len() {
                    return false;
                }
                if matches!(bytes[pos], b'.' | b')') {
                    pos += 1;
                }
            } else if matches!(bytes[pos], b' ' | b'>' | b'*' | b'+' | b'-') {
                pos += 1;
            } else {
                return false;
            }
        }
        true
    }

    /// `blockOpener`, as a lookahead: escaped characters and spaces, then a list item's indicator
    /// and a space, `: `, `:::`, a code fence, `%%%` or `>`.
    fn block_opener(&self, at: usize) -> bool {
        let mut pos = at;
        loop {
            match self.peek(pos) {
                Some('\\') => match self.peek(pos + 1) {
                    Some(next) => pos += 1 + next.len_utf8(),
                    None => return false,
                },
                Some(' ') => pos += 1,
                _ => break,
            }
        }
        let rest = &self.text[pos..self.end];
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        ["* ", "- ", "+ ", ": ", ":::", "```", "%%%", ">"]
            .iter()
            .any(|opener| rest.starts_with(opener))
            || (digits > 0
                && (rest[digits..].starts_with(". ") || rest[digits..].starts_with(") ")))
    }

    /// `rawIdentFn (includeWhitespace := false)`: a possibly dotted name, `«»` escapes allowed.
    fn ident(&self, at: usize) -> Parsed<(Syntax, usize)> {
        let mut name = Name::anonymous();
        let mut pos = at;
        loop {
            let component = match self.peek(pos) {
                Some('«') => {
                    let start = pos + '«'.len_utf8();
                    let Some(length) = self.text[start..self.end].find('»') else {
                        return Err(Stop::Fail(start));
                    };
                    pos = start + length + '»'.len_utf8();
                    &self.text[start..start + length]
                }
                Some(c) if is_id_first(c) => {
                    let start = pos;
                    pos += c.len_utf8();
                    while let Some(c) = self.peek(pos).filter(|&c| is_id_rest(c)) {
                        pos += c.len_utf8();
                    }
                    &self.text[start..pos]
                }
                _ => return Err(Stop::Fail(at)),
            };
            name = Name::str(name, component);
            let continues = self.peek(pos) == Some('.')
                && self
                    .peek(pos + 1)
                    .is_some_and(|c| is_id_first(c) || c == '«');
            if !continues {
                break;
            }
            pos += 1;
        }
        let ident = Syntax::Ident {
            info: SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(at)),
                pos: BytePos(at),
                trailing: ByteSpan::empty_at(BytePos(pos)),
                end_pos: BytePos(pos),
            },
            raw_val: ByteSpan::new(BytePos(at), BytePos(pos))
                .unwrap_or_else(|| ByteSpan::empty_at(BytePos(at))),
            val: name,
            preresolved: Vec::new(),
        };
        Ok((ident, pos))
    }

    /// `val`: a string literal, a name or a decimal numeral, each without the whitespace after it.
    fn value(&self, at: usize) -> Parsed<(Syntax, usize)> {
        match self.peek(at) {
            Some('"') => {
                let mut pos = at + 1;
                loop {
                    match self.peek(pos) {
                        None => return Err(Stop::Fail(at)),
                        Some('"') => break,
                        Some('\\') => match self.peek(pos + 1) {
                            Some('\\' | '"' | '\'' | 'n' | 't' | 'r') => pos += 2,
                            _ => return Err(Stop::Unsupported),
                        },
                        Some(c) => pos += c.len_utf8(),
                    }
                }
                let end = pos + 1;
                let string = literal("str", atom(at, end, &self.text[at..end]));
                Ok((syntax("arg_str", vec![string]), end))
            }
            Some(c) if is_id_first(c) || c == '«' => {
                let (name, end) = self.ident(at)?;
                Ok((syntax("arg_ident", vec![name]), end))
            }
            Some(c) if c.is_ascii_digit() => {
                let end = at
                    + self.text[at..self.end]
                        .bytes()
                        .take_while(u8::is_ascii_digit)
                        .count();
                let radix = self.starts(at, "0") && end == at + 1;
                if matches!(self.peek(end), Some('.' | 'e' | 'E' | '_'))
                    || (radix && matches!(self.peek(end), Some('b' | 'B' | 'o' | 'O' | 'x' | 'X')))
                {
                    return Err(Stop::Unsupported);
                }
                let numeral = literal("num", atom(at, end, &self.text[at..end]));
                Ok((syntax("arg_num", vec![numeral]), end))
            }
            _ => Err(Stop::Fail(at)),
        }
    }

    /// `arg`: a flag, a parenthesized named argument, a name with or without `:=`, or a value.
    fn arg(&self, at: usize) -> Parsed<(Syntax, usize)> {
        match self.peek(at) {
            Some(sign @ ('+' | '-')) => {
                if self.peek(at + 1) == Some(' ') {
                    return Err(Stop::Recovered);
                }
                let (name, end) = self.ident(at + 1).map_err(recovered)?;
                let flag = if sign == '+' { "flag_on" } else { "flag_off" };
                Ok((syntax(flag, vec![atom(at, at + 1, sign), name]), end))
            }
            Some('(') => {
                let (name, pos) = self.ident(self.spaces(at + 1)).map_err(recovered)?;
                let assign = self.spaces(pos);
                if !self.starts(assign, ":=") {
                    return Err(Stop::Recovered);
                }
                let (value, pos) = self.value(self.spaces(assign + 2)).map_err(recovered)?;
                let close = self.spaces(pos);
                if self.peek(close) != Some(')') {
                    return Err(Stop::Recovered);
                }
                let named = syntax(
                    "named",
                    vec![
                        atom(at, at + 1, "("),
                        name,
                        atom(assign, assign + 2, ":="),
                        value,
                        atom(close, close + 1, ")"),
                    ],
                );
                Ok((named, self.spaces(close + 1)))
            }
            _ => match self.ident(at) {
                Ok((name, pos)) => {
                    let assign = self.spaces(pos);
                    if !self.starts(assign, ":=") {
                        let ident = syntax("arg_ident", vec![name]);
                        return Ok((syntax("anon", vec![ident]), assign));
                    }
                    let (value, pos) = self.value(self.spaces(assign + 2))?;
                    let named = syntax(
                        "named_no_paren",
                        vec![name, atom(assign, assign + 2, ":="), value],
                    );
                    Ok((named, self.spaces(pos)))
                }
                Err(Stop::Fail(_)) => {
                    let (value, end) = self.value(at)?;
                    Ok((syntax("anon", vec![value]), end))
                }
                Err(stop) => Err(stop),
            },
        }
    }

    /// `nameAndArgs` on one line: a name, then arguments separated by spaces.
    fn name_and_args(&self, at: usize) -> Parsed<(Syntax, Syntax, usize)> {
        let (name, pos) = self.ident(self.spaces(at))?;
        let mut pos = self.spaces(pos);
        let mut args = Vec::new();
        loop {
            match self.arg(pos) {
                Ok((arg, next)) => {
                    args.push(arg);
                    pos = self.spaces(next);
                }
                Err(Stop::Fail(stopped)) if stopped == pos => break,
                Err(stop) => return Err(stop),
            }
        }
        Ok((name, null_node(args), pos))
    }

    /// `inlineTextChar`: one character of text, an escaped one included; `None` at the characters
    /// that open another inline.
    fn text_char(&self, at: usize) -> Parsed<usize> {
        match self.peek(at) {
            None => Err(Stop::Fail(at)),
            Some('\\') => match self.peek(at + 1) {
                Some(next) => Ok(at + 1 + next.len_utf8()),
                None => Err(Stop::Fail(at + 1)),
            },
            Some('\n' | '*' | '_' | '[' | ']' | '{' | '}' | '`') => Err(Stop::Fail(at)),
            Some('!') if self.peek(at + 1) == Some('[') => Err(Stop::Fail(at)),
            Some('$') => match (self.peek(at + 1), self.peek(at + 2)) {
                (Some('`'), _) | (Some('$'), Some('`')) => Err(Stop::Fail(at)),
                (Some('$'), _) => Ok(at + 2),
                _ => Ok(at + 1),
            },
            Some(c) => Ok(at + c.len_utf8()),
        }
    }

    /// `text`: a run of text characters, unescaped and quoted.
    fn text(&self, at: usize) -> Parsed<(Syntax, usize)> {
        let mut end = self.text_char(at)?;
        loop {
            match self.text_char(end) {
                Ok(next) => end = next,
                Err(Stop::Fail(stopped)) if stopped == end => break,
                Err(stop) => return Err(stop),
            }
        }
        let val = quote(&unescape(&self.text[at..end]));
        Ok((
            syntax("text", vec![literal("str", atom(at, end, val))]),
            end,
        ))
    }

    /// `linebreak`: a newline the paragraph goes on after (not a blank line, not a block opener).
    fn linebreak(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        if !ctxt.newlines || self.peek(at) != Some('\n') {
            return Err(Stop::Fail(at));
        }
        let next = self.spaces(at + 1);
        if self.peek(next) == Some('\n') || self.block_opener(next) {
            return Err(Stop::Fail(at));
        }
        let newline = literal("str", atom(at, at + 1, "\"\\n\""));
        Ok((
            syntax("linebreak", vec![atom(at, at, "line!"), newline]),
            at + 1,
        ))
    }

    /// `inline`: text, a line break, or a delimited inline.
    fn inline(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        first_of(
            at,
            &[&|| self.text(at), &|| self.linebreak(ctxt, at), &|| {
                self.delimited(ctxt, at)
            }],
        )
    }

    fn inlines(&self, ctxt: Inlines, at: usize, one: bool) -> Parsed<(Vec<Syntax>, usize)> {
        many(at, one, |pos| self.inline(ctxt, pos))
    }

    /// `delimitedInline`.
    fn delimited(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        first_of(
            at,
            &[
                &|| self.emphasis(ctxt, at, '_'),
                &|| self.emphasis(ctxt, at, '*'),
                &|| self.code(at),
                &|| self.math(at),
                &|| self.role(ctxt, at),
                &|| self.image(at),
                &|| self.link(ctxt, at),
                &|| self.footnote(ctxt, at),
            ],
        )
    }

    /// `emph` (`_`) and `bold` (`*`), `emphLike`: an opener of one or more marks (fewer than the
    /// enclosing one's inside it), inlines, and as many marks after a non-space.
    fn emphasis(&self, ctxt: Inlines, at: usize, mark: char) -> Parsed<(Syntax, usize)> {
        let (depth, name) = if mark == '*' {
            (ctxt.bold, "bold")
        } else {
            (ctxt.emph, "emph")
        };
        let opened = match depth {
            None if self.peek(at) == Some(mark) => self.run(at, mark),
            None | Some(0 | 1) => return Err(Stop::Fail(at)),
            Some(depth) => {
                // `atMostFn (depth - 1)`, which refuses a further mark after taking them all.
                let mut pos = at;
                while pos - at < depth - 1 && self.peek(pos) == Some(mark) {
                    pos += 1;
                }
                if pos - at == depth - 1 && self.peek(pos) == Some(mark) {
                    return Err(Stop::Fail(at));
                }
                pos
            }
        };
        if matches!(self.peek(opened), Some(' ' | '\n')) {
            return Err(Stop::Fail(at));
        }
        let count = opened - at;
        let inner = if mark == '*' {
            Inlines {
                bold: Some(count),
                ..ctxt
            }
        } else {
            Inlines {
                emph: Some(count),
                ..ctxt
            }
        };
        let (inlines, close) = self.inlines(inner, opened, false).map_err(recovered)?;
        let after_space = self.text[..close]
            .chars()
            .next_back()
            .is_some_and(is_whitespace);
        let closed = close + count;
        let closes = self
            .text
            .get(close..closed)
            .is_some_and(|marks| closed <= self.end && marks.chars().all(|c| c == mark));
        if after_space || !closes {
            return Err(Stop::Recovered);
        }
        let node = syntax(
            name,
            vec![
                atom(at, opened, &self.text[at..opened]),
                null_node(inlines),
                atom(close, closed, &self.text[close..closed]),
            ],
        );
        Ok((node, closed))
    }

    /// `code`: a run of backticks, content holding only shorter runs, and the same run. The
    /// content is quoted as written and, between a space at each end, trimmed of them (`normFn`).
    fn code(&self, at: usize) -> Parsed<(Syntax, usize)> {
        let opened = self.run(at, '`');
        if opened == at {
            return Err(Stop::Fail(at));
        }
        let count = opened - at;
        let mut close = opened;
        while let Some(c) = self.peek(close) {
            if c == '`' {
                let run = self.run(close, '`');
                if run - close >= count {
                    break;
                }
                close = run;
            } else {
                close += c.len_utf8();
            }
        }
        if close == opened || self.run(close, '`') - close != count {
            return Err(Stop::Recovered);
        }
        let quoted = quote(&self.text[opened..close]);
        let trimmed = quoted
            .get(2..quoted.len().saturating_sub(2))
            .filter(|core| {
                quoted.len() >= 4
                    && quoted.starts_with("\" ")
                    && quoted.ends_with(" \"")
                    && core.chars().any(|c| c != ' ')
            })
            .map(|core| format!("\"{core}\""));
        let content = match trimmed {
            Some(val) => atom(opened + 1, close - 1, val),
            None => atom(opened, close, quoted),
        };
        let closed = close + count;
        let node = syntax(
            "code",
            vec![
                atom(at, opened, &self.text[at..opened]),
                literal("str", content),
                atom(close, closed, &self.text[close..closed]),
            ],
        );
        Ok((node, closed))
    }

    /// `math`: `$$` or `$` before inline code.
    fn math(&self, at: usize) -> Parsed<(Syntax, usize)> {
        for (opener, name) in [("$$", "display_math"), ("$", "inline_math")] {
            if !self.starts(at, opener) {
                continue;
            }
            match self.code(at + opener.len()) {
                Ok((code, end)) => {
                    let opener = atom(at, at + opener.len(), opener);
                    return Ok((syntax(name, vec![opener, code]), end));
                }
                Err(Stop::Fail(_)) => {}
                Err(stop) => return Err(stop),
            }
        }
        Err(Stop::Fail(at))
    }

    /// `role`: `{name args}`, then bracketed inlines or one delimited inline (between fake
    /// brackets).
    fn role(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        if self.peek(at) != Some('{') {
            return Err(Stop::Fail(at));
        }
        let (name, args, pos) = self.name_and_args(self.spaces(at + 1)).map_err(recovered)?;
        let close = self.spaces(pos);
        if self.peek(close) != Some('}') {
            return Err(Stop::Recovered);
        }
        let mut parts = vec![
            atom(at, at + 1, "{"),
            name,
            args,
            atom(close, close + 1, "}"),
        ];
        let open = close + 1;
        if self.peek(open) == Some('[') {
            let (inlines, bracket) = self.inlines(ctxt, open + 1, false).map_err(recovered)?;
            if self.peek(bracket) != Some(']') {
                return Err(Stop::Recovered);
            }
            parts.extend([
                atom(open, open + 1, "["),
                null_node(inlines),
                atom(bracket, bracket + 1, "]"),
            ]);
            return Ok((syntax("role", parts), bracket + 1));
        }
        match self.delimited(ctxt, open) {
            Ok((inline, end)) => {
                parts.extend([fake("["), null_node(vec![inline]), fake("]")]);
                Ok((syntax("role", parts), end))
            }
            Err(Stop::Fail(_)) => Err(Stop::Fail(open)),
            Err(stop) => Err(stop),
        }
    }

    /// `takeUntilEscFn`: characters up to one of `stops`, a backslash escaping the next.
    fn until_escaped(&self, at: usize, stops: &[char]) -> Parsed<usize> {
        let mut pos = at;
        loop {
            match self.peek(pos) {
                None => return Ok(pos),
                Some('\\') => match self.peek(pos + 1) {
                    Some(next) => pos += 1 + next.len_utf8(),
                    None => return Err(Stop::Fail(pos + 1)),
                },
                Some(c) if stops.contains(&c) => return Ok(pos),
                Some(c) => pos += c.len_utf8(),
            }
        }
    }

    /// A quoted string literal over `start..end`, as written.
    fn written(&self, start: usize, end: usize) -> Syntax {
        literal("str", atom(start, end, quote(&self.text[start..end])))
    }

    /// `linkTarget`: `[ref]` or `(url)`, at least one character inside.
    fn link_target(&self, at: usize) -> Parsed<(Syntax, usize)> {
        let (name, open, close) = match self.peek(at) {
            Some('[') => ("ref", "[", ']'),
            Some('(') => ("url", "(", ')'),
            _ => return Err(Stop::Fail(at)),
        };
        let start = at + 1;
        // At least one character, an escaped one included.
        let end = match self.peek(start) {
            Some(c) if c != close && c != '\n' => self
                .until_escaped(start, &[close, '\n'])
                .map_err(recovered)?,
            _ => return Err(Stop::Recovered),
        };
        if self.peek(end) != Some(close) {
            return Err(Stop::Recovered);
        }
        let node = syntax(
            name,
            vec![
                atom(at, start, open),
                self.written(start, end),
                atom(end, end + 1, close),
            ],
        );
        Ok((node, end + 1))
    }

    /// `image`: `![alt]` and a link target.
    fn image(&self, at: usize) -> Parsed<(Syntax, usize)> {
        if !self.starts(at, "![") {
            return Err(Stop::Fail(at));
        }
        let end = self
            .until_escaped(at + 2, &[']', '\n'])
            .map_err(recovered)?;
        if self.peek(end) != Some(']') {
            return Err(Stop::Recovered);
        }
        let (target, after) = self.link_target(end + 1).map_err(recovered)?;
        let node = syntax(
            "image",
            vec![
                atom(at, at + 2, "!["),
                self.written(at + 2, end),
                atom(end, end + 1, "]"),
                target,
            ],
        );
        Ok((node, after))
    }

    /// `link`: `[inlines]` and a link target, not inside another link.
    fn link(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        if ctxt.in_link || self.peek(at) != Some('[') || self.peek(at + 1) == Some('^') {
            return Err(Stop::Fail(at));
        }
        let inner = Inlines {
            in_link: true,
            ..ctxt
        };
        let (inlines, end) = self.inlines(inner, at + 1, true).map_err(recovered)?;
        if self.peek(end) != Some(']') {
            return Err(Stop::Recovered);
        }
        let (target, after) = self.link_target(end + 1).map_err(recovered)?;
        let node = syntax(
            "link",
            vec![
                atom(at, at + 1, "["),
                null_node(inlines),
                atom(end, end + 1, "]"),
                target,
            ],
        );
        Ok((node, after))
    }

    /// `footnote`: `[^name]`, not inside a link.
    fn footnote(&self, ctxt: Inlines, at: usize) -> Parsed<(Syntax, usize)> {
        if ctxt.in_link || !self.starts(at, "[^") {
            return Err(Stop::Fail(at));
        }
        let start = at + 2;
        let end = self.until_escaped(start, &[']', '\n']).map_err(recovered)?;
        if end == start || self.peek(end) != Some(']') {
            return Err(Stop::Recovered);
        }
        let node = syntax(
            "footnote",
            vec![
                atom(at, start, "[^"),
                self.written(start, end),
                atom(end, end + 1, "]"),
            ],
        );
        Ok((node, end + 1))
    }

    /// `blocks` (`blocks1` when `one`): blocks, blank lines between them.
    fn blocks(&self, ctxt: &Blocks, at: usize, one: bool) -> Parsed<(Syntax, usize)> {
        let mut items = Vec::new();
        let mut pos = at;
        loop {
            match self.block(ctxt, pos) {
                Ok((block, next)) => {
                    items.push(block);
                    pos = next;
                }
                Err(Stop::Fail(stopped)) if stopped == pos && !(one && items.is_empty()) => {
                    return Ok((null_node(items), pos));
                }
                Err(stop) => return Err(stop),
            }
            // `blockSep`: blank lines, then spaces at the end of the document.
            pos = self.blank_lines(pos);
            let last = self.spaces(pos);
            if last >= self.end {
                pos = last;
            }
        }
    }

    /// `block`: the first of the openers that reads here, else a paragraph.
    fn block(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        self.unread_block(ctxt, at)?;
        first_of(
            at,
            &[
                &|| self.block_command(ctxt, at),
                &|| self.list(ctxt, at, false),
                &|| self.list(ctxt, at, true),
                &|| self.header(ctxt, at),
                &|| self.code_block(ctxt, at),
                &|| self.blockquote(ctxt, at),
                &|| self.para(ctxt, at),
            ],
        )
    }

    /// The blocks this port does not read, where their openers would commit the pin's parse: a
    /// description list, a directive, a link or footnote definition, a metadata block. Each is
    /// tried only after openers that cannot start where it does, so checking first is the same.
    fn unread_block(&self, ctxt: &Blocks, at: usize) -> Parsed<()> {
        let pos = self.spaces(at);
        let indented = self.column(pos) >= ctxt.min_indent;
        let description = self.only_block_openers(at) && self.starts(pos, ": ") && indented;
        let directive = indented && self.starts(pos, ":::");
        let metadata = self.bol(at) && self.starts(pos, "%%%");
        let definition = self.bol(at) && indented && self.definition(pos);
        if description || directive || metadata || definition {
            return Err(Stop::Unsupported);
        }
        Ok(())
    }

    /// Whether a link (`[name]:`) or footnote (`[^name]:`) definition starts at `at`.
    fn definition(&self, at: usize) -> bool {
        if self.peek(at) != Some('[') {
            return false;
        }
        let footnote = self.peek(at + 1) == Some('^');
        let start = at + 1 + usize::from(footnote);
        if !footnote && matches!(self.peek(start), None | Some(']' | '^')) {
            return false;
        }
        let Ok(end) = self.until_escaped(start, &[']']) else {
            return false;
        };
        end > start && self.starts(end, "]:")
    }

    /// `block_command`: `{name args}` alone on a line.
    fn block_command(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        let open = self.spaces(at);
        if self.column(open) < ctxt.min_indent || self.peek(open) != Some('{') {
            return Err(Stop::Fail(at));
        }
        let (name, args, pos) = match self.name_and_args(open + 1) {
            Ok(read) => read,
            Err(Stop::Fail(_)) => return Err(Stop::Fail(at)),
            Err(stop) => return Err(stop),
        };
        let close = self.spaces(pos);
        if self.peek(close) != Some('}') {
            return Err(Stop::Fail(at));
        }
        let after = self.spaces(close + 1);
        let end = match self.peek(after) {
            Some('\n') => after + 1,
            None => after,
            Some(_) => return Err(Stop::Fail(at)),
        };
        let parts = vec![
            atom(open, open + 1, "{"),
            name,
            args,
            atom(close, close + 1, "}"),
        ];
        Ok((syntax("command", parts), end))
    }

    /// `unorderedList` and `orderedList`: items whose indicators share one column and kind.
    fn list(&self, ctxt: &Blocks, at: usize, ordered: bool) -> Parsed<(Syntax, usize)> {
        let fail = Err(Stop::Fail(at));
        if !self.only_block_openers(at) {
            return fail;
        }
        let start = self.spaces(at);
        let column = self.column(start);
        if column < ctxt.min_indent {
            return fail;
        }
        let digits = self.text[start..self.end]
            .bytes()
            .take_while(u8::is_ascii_digit)
            .count();
        let (indicator, after) = if ordered {
            if digits == 0 {
                return fail;
            }
            (self.peek(start + digits), start + digits + 1)
        } else {
            (self.peek(start), start + 1)
        };
        let item = match indicator {
            Some(c @ ('.' | ')')) if ordered => List::Ordered(c, column),
            Some(c @ ('*' | '-' | '+')) if !ordered => List::Unordered(c, column),
            _ => return fail,
        };
        if !matches!(self.peek(after), Some(' ' | '\n')) {
            return fail;
        }
        let mut lists = ctxt.lists.clone();
        lists.push(item);
        let inner = Blocks {
            min_indent: column + 1,
            lists,
        };
        let (items, end) = many(start, true, |pos| self.list_item(&inner, pos))?;
        let items = null_node(items);
        let node = if ordered {
            let number = literal(
                "num",
                atom(start, start + digits, &self.text[start..start + digits]),
            );
            syntax(
                "ol",
                vec![
                    atom(at, at, "ol("),
                    number,
                    atom(start, start, ")"),
                    atom(start, start, "{"),
                    items,
                    atom(end, end, "}"),
                ],
            )
        } else {
            syntax(
                "ul",
                vec![atom(start, start, "ul{"), items, atom(end, end, "}")],
            )
        };
        Ok((node, end))
    }

    /// `listItem`: the innermost list's indicator at its column, then blocks indented past it.
    fn list_item(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        let start = self.spaces(at);
        let indicator_end = match ctxt.lists.last() {
            Some(&List::Unordered(bullet, column))
                if self.column(start) == column && self.peek(start) == Some(bullet) =>
            {
                start + 1
            }
            Some(&List::Ordered(after, column)) if self.column(start) == column => {
                let digits = self.text[start..self.end]
                    .bytes()
                    .take_while(u8::is_ascii_digit)
                    .count();
                if digits == 0 || self.peek(start + digits) != Some(after) {
                    return Err(Stop::Fail(at));
                }
                start + digits + 1
            }
            _ => return Err(Stop::Fail(at)),
        };
        if !matches!(self.peek(indicator_end), Some(' ' | '\n')) {
            return Err(Stop::Fail(at));
        }
        let inner = Blocks {
            min_indent: self.column(indicator_end),
            lists: ctxt.lists.clone(),
        };
        let mut pos = indicator_end;
        while matches!(self.peek(pos), Some(' ' | '\n')) {
            pos += 1;
        }
        let (blocks, end) = self.blocks(&inner, pos, true)?;
        let indicator = atom(start, indicator_end, &self.text[start..indicator_end]);
        Ok((syntax("li", vec![indicator, blocks]), end))
    }

    /// `header`: `#`s at the line's start, a space, and a line of inlines.
    fn header(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        if self.column(at) < ctxt.min_indent || !self.bol(at) {
            return Err(Stop::Fail(at));
        }
        let start = self.spaces(at);
        if self.peek(start) != Some('#') {
            return Err(Stop::Fail(at));
        }
        if !self.bol(start) {
            return Err(Stop::Fail(start));
        }
        let marks = self.run(start, '#');
        if self.peek(marks) != Some(' ') {
            return Err(Stop::Fail(marks));
        }
        let text = self.spaces(marks + 1);
        if matches!(self.peek(text), None | Some('\n')) {
            return Err(Stop::Fail(text));
        }
        let line = Inlines {
            newlines: false,
            ..TEXT_LINE
        };
        let (inlines, end) = self.inlines(line, text, true)?;
        let level = (marks - start - 1).to_string();
        let parts = vec![
            atom(start, marks, "header("),
            literal("num", Syntax::atom(SourceInfo::None, level)),
            fake(")"),
            fake("{"),
            null_node(inlines),
            atom(end, end, "}"),
        ];
        Ok((syntax("header", parts), end))
    }

    /// `codeBlock`: a fence of three or more backticks, an optional name and arguments, the lines
    /// up to a fence as wide at the same column, quoted with the fence's indentation dropped.
    fn code_block(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        let start = self.spaces(at);
        let column = self.column(start);
        let opened = self.run(start, '`');
        if column < ctxt.min_indent || opened - start < 3 {
            return Err(Stop::Fail(at));
        }
        let width = opened - start;
        let pos = self.spaces(opened);
        let (info, pos) = match self.name_and_args(pos) {
            Ok((name, args, end)) => (null_node(vec![name, args]), end),
            Err(Stop::Fail(stopped)) if stopped == pos => (null_node(Vec::new()), pos),
            Err(stop) => return Err(recovered(stop)),
        };
        if self.peek(pos) != Some('\n') {
            return Err(Stop::Recovered);
        }
        let content = pos + 1;
        let mut line = content;
        loop {
            let indent = self.spaces(line);
            if self.peek(indent) == Some('\n') {
                line = indent + 1;
                continue;
            }
            let fence = self.run(indent, '`') - indent >= width;
            if !self.bol(line) || self.column(indent) < column || fence {
                break;
            }
            let newline = self.text[indent..self.end]
                .find('\n')
                .map(|offset| indent + offset);
            match newline {
                Some(newline) => line = newline + 1,
                None if self.end == line => break,
                None => return Err(Stop::Recovered),
            }
        }
        let close = self.spaces(line);
        let closed = close + width;
        let fenced =
            self.bol(line) && self.column(close) == column && self.run(close, '`') == closed;
        let after = self.spaces(closed);
        let end = match self.peek(after) {
            Some('\n') if fenced => after + 1,
            None if fenced => after,
            _ => return Err(Stop::Recovered),
        };
        let code = de_indent(column, &self.text[content..line]);
        let parts = vec![
            atom(start, opened, &self.text[start..opened]),
            info,
            atom(pos, pos + 1, "\n"),
            literal("str", atom(content, line, quote(&code))),
            atom(close, closed, &self.text[close..closed]),
        ];
        Ok((syntax("codeblock", parts), end))
    }

    /// `blockquote`: `>` and blocks indented past it.
    fn blockquote(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        let mark = self.spaces(at);
        if self.column(mark) < ctxt.min_indent || self.peek(mark) != Some('>') {
            return Err(Stop::Fail(at));
        }
        let inner = Blocks {
            min_indent: self.column(mark + 1),
            lists: ctxt.lists.clone(),
        };
        match self.blocks(&inner, mark + 1, false) {
            Ok((blocks, end)) => Ok((
                syntax("blockquote", vec![atom(mark, mark + 1, ">"), blocks]),
                end,
            )),
            Err(Stop::Fail(_)) => Err(Stop::Fail(at)),
            Err(stop) => Err(stop),
        }
    }

    /// `para`: a line that opens no other block, indented enough, and its inlines.
    fn para(&self, ctxt: &Blocks, at: usize) -> Parsed<(Syntax, usize)> {
        let start = self.spaces(at);
        if self.block_opener(start) || self.column(start) < ctxt.min_indent {
            return Err(Stop::Fail(at));
        }
        let (inlines, end) = self.inlines(TEXT_LINE, start, true)?;
        let parts = vec![
            atom(start, start, "para{"),
            null_node(inlines),
            atom(end, end, "}"),
        ];
        Ok((syntax("para", parts), end))
    }
}

/// `codeBlock`'s `deIndent`: without a final newline, every line less its first `column`
/// characters, each ended by a newline.
fn de_indent(column: usize, code: &str) -> String {
    let code = code.strip_suffix('\n').unwrap_or(code);
    let mut out = String::with_capacity(code.len() + 1);
    for line in code.split('\n') {
        out.extend(line.chars().skip(column));
        out.push('\n');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{de_indent, quote, unescape};

    #[test]
    fn quoting_and_unescaping_follow_the_pins_string_functions() {
        assert_eq!(quote("a \"b\"\n\\"), "\"a \\\"b\\\"\\n\\\\\"");
        assert_eq!(quote("\u{1}"), "\"\\x01\"");
        assert_eq!(unescape("\\{x\\*"), "{x*");
        assert_eq!(de_indent(2, "  a\n    b\n"), "a\n  b\n");
        assert_eq!(de_indent(0, ""), "\n");
    }
}
