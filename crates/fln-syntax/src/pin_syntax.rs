//! The pin syntax corpus (bead `fln-pin-syntax-corpus-7b5b`): Vellum's reader and printer for
//! `fln.pin-syntax/1`, the lossless form in which `scripts/extract/dump_command_syntax.lean
//! --lossless` prints every command tree the pinned frontend produced for a file.
//!
//! The pin's trees are the expected output of FrankenLean's parser and the input its macro
//! executor and elaborator can be measured on before that parser exists. Neither use is
//! possible on a lossy form, so the round trip `print(read(dump)) == dump` is asserted over the
//! whole corpus: anything [`read`] keeps, [`print`] writes back byte for byte.
//!
//! An identifier's raw value is a span into the file (see [`Syntax::Ident`]), so reading needs
//! the file: [`read`] refuses a dump whose raw text is not exactly the bytes its span names.
//! Over the pinned Init and Std sources every identifier is original syntax whose raw value is
//! a slice of its file (measured 2026-10-07: 1,377,773 identifiers).
//!
//! Both directions use an explicit stack: command trees nest deeply and Vellum runs on small
//! host stacks.

use crate::source::{BytePos, ByteSpan, SourceInfo};
use crate::tree::{Preresolved, Syntax};
use fln_core::name::{LeafView, Name};
use std::fmt::Write as _;

/// The schema line every dump begins with.
pub const SCHEMA: &str = "fln.pin-syntax/1";

/// The corpus's digest: FNV-1a 64, the manifest's and the cache key's. It guards against
/// drift, not against an adversary.
pub fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// Where dumps are cached, outside the repository: `$FLN_PIN_SYNTAX_CACHE`, else
/// `$XDG_CACHE_HOME/fln/pin-syntax`, else `$HOME/.cache/fln/pin-syntax`. A dump lives at
/// `<root>/<pin commit>/<producer digest>/<source digest>.dump`, digests as 16 hex digits.
pub fn cache_root() -> Option<std::path::PathBuf> {
    let from = |key: &str| std::env::var_os(key).filter(|value| !value.is_empty());
    from("FLN_PIN_SYNTAX_CACHE")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            from("XDG_CACHE_HOME").map(|cache| std::path::Path::new(&cache).join("fln/pin-syntax"))
        })
        .or_else(|| {
            from("HOME").map(|home| std::path::Path::new(&home).join(".cache/fln/pin-syntax"))
        })
}

/// One message the pin logged while processing the file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinMessage {
    /// `info`, `warning` or `error`.
    pub severity: String,
    pub line: u64,
    pub column: u64,
    pub text: String,
}

/// Everything one dump holds: the header's tree, each command's tree, and the messages.
#[derive(Debug, Clone, PartialEq)]
pub struct PinTrees {
    pub header: Syntax,
    pub commands: Vec<Syntax>,
    pub messages: Vec<PinMessage>,
}

/// Why a dump was refused: the 1-based line and what was wrong there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinSyntaxError {
    pub line: usize,
    pub reason: String,
}

impl std::fmt::Display for PinSyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "pin syntax dump line {}: {}", self.line, self.reason)
    }
}

impl std::error::Error for PinSyntaxError {}

/// The dump's lines, numbered from 1, each required to end with a newline.
struct Lines<'a> {
    inner: std::iter::Enumerate<std::str::SplitInclusive<'a, char>>,
    /// The line after a tree: a tree ends where its root's arity is met.
    pending: Option<(usize, &'a str)>,
}

impl<'a> Lines<'a> {
    fn next(&mut self, want: &str) -> Result<(usize, &'a str), PinSyntaxError> {
        if let Some(line) = self.pending.take() {
            return Ok(line);
        }
        match self.inner.next() {
            Some((index, line)) => match line.strip_suffix('\n') {
                Some(line) => Ok((index + 1, line)),
                None => Err(error(index + 1, "the dump does not end with a newline")),
            },
            None => Err(error(0, &format!("the dump ends before {want}"))),
        }
    }
}

/// Read a `fln.pin-syntax/1` dump of the file whose bytes are `source`.
pub fn read(dump: &str, source: &[u8]) -> Result<PinTrees, PinSyntaxError> {
    let mut lines = Lines {
        inner: dump.split_inclusive('\n').enumerate(),
        pending: None,
    };
    let (n, schema) = lines.next("the schema line")?;
    if schema != SCHEMA {
        return Err(error(n, &format!("expected the schema line `{SCHEMA}`")));
    }
    let (n, header) = lines.next("HEADER")?;
    if header != "HEADER" {
        return Err(error(n, "expected `HEADER`"));
    }
    let header = read_tree(&mut lines, source)?;
    let mut commands = Vec::new();
    let mut messages = Vec::new();
    loop {
        let (n, line) = lines.next("END")?;
        if let Some(index) = line.strip_prefix("COMMAND ") {
            if !messages.is_empty() || index != commands.len().to_string() {
                return Err(error(
                    n,
                    "commands must be numbered from 0 and precede messages",
                ));
            }
            commands.push(read_tree(&mut lines, source)?);
        } else if let Some(rest) = line.strip_prefix("MESSAGE ") {
            messages.push(read_message(rest).map_err(|reason| error(n, &reason))?);
        } else if let Some(rest) = line.strip_prefix("END ") {
            if rest != format!("{} {}", commands.len(), messages.len()) {
                return Err(error(n, "END does not count what the dump holds"));
            }
            if let Some((index, _)) = lines.inner.next() {
                return Err(error(index + 1, "text after END"));
            }
            return Ok(PinTrees {
                header,
                commands,
                messages,
            });
        } else {
            return Err(error(n, "expected COMMAND, MESSAGE or END"));
        }
    }
}

/// Print `trees` as the dump of the file whose bytes are `source`; the inverse of [`read`].
pub fn print(trees: &PinTrees, source: &[u8]) -> Result<String, PinSyntaxError> {
    let mut out = String::new();
    out.push_str(SCHEMA);
    out.push_str("\nHEADER\n");
    print_tree(&trees.header, source, &mut out)?;
    for (index, command) in trees.commands.iter().enumerate() {
        let _ = writeln!(out, "COMMAND {index}");
        print_tree(command, source, &mut out)?;
    }
    for message in &trees.messages {
        let _ = write!(
            out,
            "MESSAGE {} {} {} ",
            message.severity, message.line, message.column
        );
        json_string(&message.text, &mut out);
        out.push('\n');
    }
    let _ = writeln!(out, "END {} {}", trees.commands.len(), trees.messages.len());
    Ok(out)
}

fn error(line: usize, reason: &str) -> PinSyntaxError {
    PinSyntaxError {
        line,
        reason: reason.to_owned(),
    }
}

/// A node still collecting its children.
struct Open {
    depth: usize,
    info: SourceInfo,
    kind: Name,
    arity: usize,
    args: Vec<Syntax>,
}

/// One tree in pre-order, each line `<depth> <tag> ...`. The line after the tree is handed back
/// through `lines.pending`.
fn read_tree(lines: &mut Lines<'_>, source: &[u8]) -> Result<Syntax, PinSyntaxError> {
    let mut stack: Vec<Open> = Vec::new();
    loop {
        let (n, line) = lines.next("a tree line")?;
        let mut cursor = Cursor::new(line);
        let depth = cursor.number().map_err(|reason| error(n, &reason))? as usize;
        let expected = stack.last().map_or(0, |open| open.depth + 1);
        if depth != expected {
            return Err(error(
                n,
                &format!("depth {depth} where {expected} was expected"),
            ));
        }
        let tag = cursor.word().map_err(|reason| error(n, &reason))?;
        let leaf = match tag {
            "N" => {
                let info = cursor.info().map_err(|reason| error(n, &reason))?;
                let kind = cursor.name().map_err(|reason| error(n, &reason))?;
                let arity = cursor.number().map_err(|reason| error(n, &reason))? as usize;
                cursor.end().map_err(|reason| error(n, &reason))?;
                if arity > 0 {
                    stack.push(Open {
                        depth,
                        info,
                        kind,
                        arity,
                        args: Vec::with_capacity(arity.min(1 << 16)),
                    });
                    continue;
                }
                Syntax::Node {
                    info,
                    kind,
                    args: Vec::new(),
                }
            }
            "A" => {
                let info = cursor.info().map_err(|reason| error(n, &reason))?;
                let val = cursor.string().map_err(|reason| error(n, &reason))?;
                cursor.end().map_err(|reason| error(n, &reason))?;
                Syntax::Atom { info, val }
            }
            "I" => {
                let info = cursor.info().map_err(|reason| error(n, &reason))?;
                let raw = cursor.span().map_err(|reason| error(n, &reason))?;
                let text = cursor.string().map_err(|reason| error(n, &reason))?;
                if source.get(raw.start().0..raw.end().0) != Some(text.as_bytes()) {
                    return Err(error(
                        n,
                        "the identifier's raw text is not the bytes its span names",
                    ));
                }
                let val = cursor.name().map_err(|reason| error(n, &reason))?;
                let preresolved = cursor.preresolved().map_err(|reason| error(n, &reason))?;
                cursor.end().map_err(|reason| error(n, &reason))?;
                Syntax::Ident {
                    info,
                    raw_val: raw,
                    val,
                    preresolved,
                }
            }
            "M" => {
                cursor.end().map_err(|reason| error(n, &reason))?;
                Syntax::Missing
            }
            _ => return Err(error(n, "expected a node, atom, identifier or missing tag")),
        };
        // Attach the finished subtree, closing every node its arrival completes.
        let mut done = leaf;
        loop {
            let Some(open) = stack.last_mut() else {
                // The root finished; the next line belongs to whatever follows the tree.
                lines.pending = Some(lines.next("the line after a tree")?);
                return Ok(done);
            };
            open.args.push(done);
            if open.args.len() < open.arity {
                break;
            }
            let open = stack.pop().expect("an open node");
            done = Syntax::Node {
                info: open.info,
                kind: open.kind,
                args: open.args,
            };
        }
    }
}

fn read_message(rest: &str) -> Result<PinMessage, String> {
    let mut cursor = Cursor::new(rest);
    let severity = cursor.word()?.to_owned();
    if !matches!(severity.as_str(), "info" | "warning" | "error") {
        return Err(format!("unknown severity `{severity}`"));
    }
    let line = cursor.number()?;
    let column = cursor.number()?;
    let text = cursor.string()?;
    cursor.end()?;
    Ok(PinMessage {
        severity,
        line,
        column,
        text,
    })
}

fn print_tree(root: &Syntax, source: &[u8], out: &mut String) -> Result<(), PinSyntaxError> {
    let mut stack = vec![(0usize, root)];
    while let Some((depth, syntax)) = stack.pop() {
        let _ = write!(out, "{depth} ");
        match syntax {
            Syntax::Missing => out.push('M'),
            Syntax::Node { info, kind, args } => {
                out.push_str("N ");
                print_info(info, out);
                out.push(' ');
                json_name(kind, out);
                let _ = write!(out, " {}", args.len());
                stack.extend(args.iter().rev().map(|arg| (depth + 1, arg)));
            }
            Syntax::Atom { info, val } => {
                out.push_str("A ");
                print_info(info, out);
                out.push(' ');
                json_string(val, out);
            }
            Syntax::Ident {
                info,
                raw_val,
                val,
                preresolved,
            } => {
                let text = source
                    .get(raw_val.start().0..raw_val.end().0)
                    .and_then(|bytes| std::str::from_utf8(bytes).ok())
                    .ok_or_else(|| error(0, "an identifier's span is not text of the source"))?;
                out.push_str("I ");
                print_info(info, out);
                let _ = write!(out, " {} {} ", raw_val.start().0, raw_val.end().0);
                json_string(text, out);
                out.push(' ');
                json_name(val, out);
                out.push(' ');
                json_preresolved(preresolved, out);
            }
        }
        out.push('\n');
    }
    Ok(())
}

fn print_info(info: &SourceInfo, out: &mut String) {
    match info {
        SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } => {
            let _ = write!(
                out,
                "o {} {} {} {} {} {}",
                leading.start().0,
                leading.end().0,
                pos.0,
                end_pos.0,
                trailing.start().0,
                trailing.end().0
            );
        }
        SourceInfo::Synthetic {
            pos,
            end_pos,
            canonical,
        } => {
            let _ = write!(out, "s {} {} {}", pos.0, end_pos.0, u8::from(*canonical));
        }
        SourceInfo::None => out.push('n'),
    }
}

/// `Lean.Json.compress` of a string: `"` and `\` escaped, `\n` and `\r` by name, every other
/// character below U+0020 as `\u` with four lowercase hex digits, everything else verbatim
/// (vendored `src/Lean/Data/Json/Printer.lean`, `escapeAux`).
fn json_string(text: &str, out: &mut String) {
    out.push('"');
    for c in text.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// A name as the JSON array of its components from the root: strings, and numbers for
/// numeric components.
fn json_name(name: &Name, out: &mut String) {
    let mut components = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        components.push(cursor.clone());
        cursor = cursor.parent();
    }
    out.push('[');
    for (index, component) in components.iter().rev().enumerate() {
        if index != 0 {
            out.push(',');
        }
        match component.leaf_view() {
            LeafView::Str(text) => json_string(text, out),
            LeafView::Num(value) => {
                let _ = write!(out, "{value}");
            }
            LeafView::Anonymous => {}
        }
    }
    out.push(']');
}

/// The pre-resolved list as `Lean.Json.compress` prints it: object keys in sorted order.
fn json_preresolved(preresolved: &[Preresolved], out: &mut String) {
    out.push('[');
    for (index, entry) in preresolved.iter().enumerate() {
        if index != 0 {
            out.push(',');
        }
        match entry {
            Preresolved::Namespace { ns } => {
                out.push_str("{\"namespace\":");
                json_name(ns, out);
                out.push('}');
            }
            Preresolved::Decl { name, fields } => {
                out.push_str("{\"decl\":");
                json_name(name, out);
                out.push_str(",\"fields\":[");
                for (index, field) in fields.iter().enumerate() {
                    if index != 0 {
                        out.push(',');
                    }
                    json_string(field, out);
                }
                out.push_str("]}");
            }
        }
    }
    out.push(']');
}

/// A cursor over one line: fields separated by single spaces.
struct Cursor<'a> {
    text: &'a str,
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(text: &'a str) -> Self {
        Self { text, at: 0 }
    }

    fn rest(&self) -> &'a str {
        &self.text[self.at..]
    }

    /// Skip the single space before a field (none before the first).
    fn field(&mut self) -> Result<(), String> {
        if self.at == 0 {
            return Ok(());
        }
        if self.rest().starts_with(' ') {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("expected a space at column {}", self.at))
        }
    }

    fn word(&mut self) -> Result<&'a str, String> {
        self.field()?;
        let rest = self.rest();
        let len = rest.find(' ').unwrap_or(rest.len());
        if len == 0 {
            return Err(format!("expected a field at column {}", self.at));
        }
        self.at += len;
        Ok(&rest[..len])
    }

    fn number(&mut self) -> Result<u64, String> {
        let word = self.word()?;
        if word.len() > 1 && word.starts_with('0') {
            return Err(format!("`{word}` is not a canonical number"));
        }
        word.parse()
            .map_err(|_| format!("`{word}` is not a number"))
    }

    fn position(&mut self) -> Result<BytePos, String> {
        usize::try_from(self.number()?)
            .map(BytePos)
            .map_err(|_| "a position does not fit this host".to_owned())
    }

    fn span(&mut self) -> Result<ByteSpan, String> {
        let start = self.position()?;
        let end = self.position()?;
        ByteSpan::new(start, end)
            .ok_or_else(|| format!("span {}..{} runs backwards", start.0, end.0))
    }

    fn info(&mut self) -> Result<SourceInfo, String> {
        match self.word()? {
            "o" => {
                let leading = self.span()?;
                let pos = self.position()?;
                let end_pos = self.position()?;
                if end_pos.0 < pos.0 {
                    return Err(format!(
                        "a token ending at {} before its start {}",
                        end_pos.0, pos.0
                    ));
                }
                let trailing = self.span()?;
                Ok(SourceInfo::Original {
                    leading,
                    pos,
                    trailing,
                    end_pos,
                })
            }
            "s" => {
                let pos = self.position()?;
                let end_pos = self.position()?;
                if end_pos.0 < pos.0 {
                    return Err(format!(
                        "a span ending at {} before its start {}",
                        end_pos.0, pos.0
                    ));
                }
                let canonical = match self.word()? {
                    "0" => false,
                    "1" => true,
                    other => return Err(format!("`{other}` is not a canonical flag")),
                };
                Ok(SourceInfo::Synthetic {
                    pos,
                    end_pos,
                    canonical,
                })
            }
            "n" => Ok(SourceInfo::None),
            other => Err(format!("`{other}` is not a source info tag")),
        }
    }

    fn end(&self) -> Result<(), String> {
        if self.rest().is_empty() {
            Ok(())
        } else {
            Err(format!("unexpected text at column {}", self.at))
        }
    }

    fn eat(&mut self, byte: u8) -> Result<(), String> {
        if self.rest().as_bytes().first() == Some(&byte) {
            self.at += 1;
            Ok(())
        } else {
            Err(format!("expected `{}` at column {}", byte as char, self.at))
        }
    }

    fn json_string(&mut self) -> Result<String, String> {
        self.eat(b'"')?;
        let mut value = String::new();
        let mut chars = self.rest().char_indices();
        while let Some((offset, c)) = chars.next() {
            match c {
                '"' => {
                    self.at += offset + 1;
                    return Ok(value);
                }
                '\\' => match chars.next().map(|(_, c)| c) {
                    Some('"') => value.push('"'),
                    Some('\\') => value.push('\\'),
                    Some('n') => value.push('\n'),
                    Some('r') => value.push('\r'),
                    Some('u') => {
                        let hex: String = chars.by_ref().take(4).map(|(_, c)| c).collect();
                        let code = u32::from_str_radix(&hex, 16)
                            .ok()
                            .filter(|_| hex.len() == 4)
                            .and_then(char::from_u32)
                            .ok_or_else(|| format!("bad \\u escape `{hex}`"))?;
                        value.push(code);
                    }
                    _ => return Err("an escape Lean's JSON printer does not write".to_owned()),
                },
                c => value.push(c),
            }
        }
        Err("an unterminated JSON string".to_owned())
    }

    fn string(&mut self) -> Result<String, String> {
        self.field()?;
        self.json_string()
    }

    fn json_name_value(&mut self) -> Result<Name, String> {
        self.eat(b'[')?;
        let mut name = Name::default();
        if self.rest().starts_with(']') {
            self.at += 1;
            return Ok(name);
        }
        loop {
            if self.rest().starts_with('"') {
                name = Name::str(name, self.json_string()?);
            } else {
                let rest = self.rest();
                let len = rest
                    .find(|c: char| !c.is_ascii_digit())
                    .unwrap_or(rest.len());
                let digits = &rest[..len];
                if digits.is_empty() || (digits.len() > 1 && digits.starts_with('0')) {
                    return Err(format!("a bad name component at column {}", self.at));
                }
                let value: u64 = digits
                    .parse()
                    .map_err(|_| "a numeric name component beyond u64".to_owned())?;
                self.at += len;
                name = Name::num(name, value);
            }
            if self.rest().starts_with(',') {
                self.at += 1;
            } else {
                self.eat(b']')?;
                return Ok(name);
            }
        }
    }

    fn name(&mut self) -> Result<Name, String> {
        self.field()?;
        self.json_name_value()
    }

    fn preresolved(&mut self) -> Result<Vec<Preresolved>, String> {
        self.field()?;
        self.eat(b'[')?;
        let mut entries = Vec::new();
        if self.rest().starts_with(']') {
            self.at += 1;
            return Ok(entries);
        }
        loop {
            if let Some(rest) = self.rest().strip_prefix("{\"namespace\":") {
                self.at = self.text.len() - rest.len();
                let ns = self.json_name_value()?;
                self.eat(b'}')?;
                entries.push(Preresolved::Namespace { ns });
            } else if let Some(rest) = self.rest().strip_prefix("{\"decl\":") {
                self.at = self.text.len() - rest.len();
                let name = self.json_name_value()?;
                let Some(rest) = self.rest().strip_prefix(",\"fields\":[") else {
                    return Err("a decl entry without its fields".to_owned());
                };
                self.at = self.text.len() - rest.len();
                let mut fields = Vec::new();
                if self.rest().starts_with(']') {
                    self.at += 1;
                } else {
                    loop {
                        fields.push(self.json_string()?);
                        if self.rest().starts_with(',') {
                            self.at += 1;
                        } else {
                            self.eat(b']')?;
                            break;
                        }
                    }
                }
                self.eat(b'}')?;
                entries.push(Preresolved::Decl { name, fields });
            } else {
                return Err(format!("a bad pre-resolved entry at column {}", self.at));
            }
            if self.rest().starts_with(',') {
                self.at += 1;
            } else {
                self.eat(b']')?;
                return Ok(entries);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const SOURCE: &str = "def «a b».x := y\n";

    fn dump() -> String {
        [
            SCHEMA,
            "HEADER",
            "0 N n [\"Lean\",\"Parser\",\"Module\",\"header\"] 0",
            "COMMAND 0",
            "0 N n [\"Lean\",\"Parser\",\"Command\",\"declaration\"] 3",
            "1 A o 0 0 0 3 3 4 \"def\"",
            "1 I o 4 4 4 13 13 14 4 13 \"«a b».x\" [\"a b\",\"x\"] []",
            "1 N s 14 16 1 [\"x\",\"_@\",\"M\",\"_hyg\",3] 2",
            "2 M",
            "2 I o 17 17 17 18 18 19 17 18 \"y\" [\"y\"] [{\"decl\":[\"y\"],\"fields\":[\"f\",\"q\\\"\"]},{\"namespace\":[\"y\"]}]",
            "MESSAGE warning 1 4 \"tab\\u0009here\\u0001\"",
            "END 1 1",
            "",
        ]
        .join("\n")
    }

    #[test]
    fn a_dump_round_trips_byte_for_byte_with_scopes_escapes_and_preresolution() {
        let dump = dump();
        let trees = read(&dump, SOURCE.as_bytes()).unwrap();
        assert_eq!(trees.commands.len(), 1);
        assert_eq!(trees.messages[0].text, "tab\there\u{1}");
        let Syntax::Node { args, .. } = &trees.commands[0] else {
            panic!("a node root");
        };
        let Syntax::Node { kind, info, .. } = &args[2] else {
            panic!("the synthetic node");
        };
        assert_eq!(kind.to_display_string(), "x._@.M._hyg.3");
        assert!(matches!(
            info,
            SourceInfo::Synthetic {
                canonical: true,
                ..
            }
        ));
        assert_eq!(print(&trees, SOURCE.as_bytes()).unwrap(), dump);
    }

    #[test]
    fn a_dump_that_misstates_its_tree_its_counts_or_its_file_is_refused() {
        let good = dump();
        for (from, to) in [
            ("2 M", "3 M"),
            ("END 1 1", "END 1 0"),
            ("\"«a b».x\"", "\"«a b».z\""),
            ("COMMAND 0", "COMMAND 1"),
            ("1 A o 0 0 0 3 3 4", "1 A o 0 0 3 0 3 4"),
            ("MESSAGE warning", "MESSAGE notice"),
            (
                "[\"x\",\"_@\",\"M\",\"_hyg\",3]",
                "[\"x\",\"_@\",\"M\",\"_hyg\",03]",
            ),
        ] {
            let bad = good.replacen(from, to, 1);
            assert_ne!(bad, good, "{from}");
            assert!(read(&bad, SOURCE.as_bytes()).is_err(), "{to}");
        }
        assert!(read(good.trim_end(), SOURCE.as_bytes()).is_err());
        assert!(read(&format!("{good}extra\n"), SOURCE.as_bytes()).is_err());
    }

    #[test]
    fn deep_trees_read_and_print_without_host_recursion() {
        let depth = 20_000;
        let mut lines = vec![SCHEMA.to_owned(), "HEADER".to_owned()];
        for level in 0..depth {
            lines.push(format!("{level} N n [\"k\"] 1"));
        }
        lines.push(format!("{depth} M"));
        lines.push("END 0 0".to_owned());
        lines.push(String::new());
        let dump = lines.join("\n");
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let trees = read(&dump, b"").unwrap();
                assert_eq!(print(&trees, b"").unwrap(), dump);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
