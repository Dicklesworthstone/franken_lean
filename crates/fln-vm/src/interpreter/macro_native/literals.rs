//! Pinned `Init.Meta.Defs` literal APIs. These decode syntax supplied by user
//! macros, which need not be a spelling accepted by the source lexer.

use super::super::scalar_code_point;
use super::{
    IntrinsicFailure, Name, NameBudget, Obj, SyntaxKind, VmRefusal, child, expansion_layout,
    inject_name, layout, limit, name, source_info, string, syntax_kind,
};

const MAX_LITERAL_BYTES: u64 = 16 * 1024 * 1024;

pub(super) fn mk_lit(kind: &Obj, text: &Obj, info: &Obj) -> Result<Obj, IntrinsicFailure> {
    let native_kind = name(kind)?;
    source_info(info)?;
    let spelling = literal_text(text)?;
    // Charge the entire new literal before allocating its node, atom or array.
    // The shared SourceInfo and String carriers are retained without rewriting.
    let mut budget = NameBudget::new("literal constructor nodes", "literal constructor bytes");
    budget.nodes(2)?;
    budget.name(&native_kind)?;
    budget.text(spelling)?;
    Ok(literal(
        kind.clone_ref(),
        text.clone_ref(),
        info.clone_ref(),
    ))
}

pub(super) fn mk_str_lit(value: &Obj, info: &Obj) -> Result<Obj, IntrinsicFailure> {
    source_info(info)?;
    let value = literal_text(value)?;
    // `str` contributes three bytes to the complete constructor budget. The
    // output has exactly two syntax nodes and a two-node, fixed-size Name.
    let spelling = quote(value, MAX_LITERAL_BYTES - 3)?;
    Ok(literal(
        inject_name(&str_kind()),
        Obj::mk_string(&spelling),
        info.clone_ref(),
    ))
}

pub(super) fn is_lit(kind: &Obj, value: &Obj) -> Result<Obj, IntrinsicFailure> {
    Ok(option(literal_value(&name(kind)?, value)?))
}

pub(super) fn is_str_lit(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    Ok(option(decoded_value(value)?))
}

pub(super) fn get_string(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    Ok(decoded_value(value)?.unwrap_or_else(|| Obj::mk_string("")))
}

pub(super) fn mk_char_lit(value: &Obj, info: &Obj) -> Result<Obj, IntrinsicFailure> {
    const OPERATION: &str = "Lean.Syntax.mkCharLit";
    source_info(info)?;
    let scalar = scalar_code_point(value, OPERATION, 0)?;
    let character = char::from_u32(scalar).ok_or(VmRefusal::NatOverflow {
        operation: OPERATION,
    })?;
    // A character spelling occupies at most six bytes, including delimiters.
    let mut spelling = String::with_capacity(6);
    spelling.push('\'');
    match character {
        '\n' => spelling.push_str("\\n"),
        '\t' => spelling.push_str("\\t"),
        '\\' => spelling.push_str("\\\\"),
        '"' => spelling.push_str("\\\""),
        '\'' => spelling.push_str("\\'"),
        character if character <= '\u{1f}' || character == '\u{7f}' => {
            let byte = character as u8;
            let hex = b"0123456789abcdef";
            spelling.push_str("\\x");
            spelling.push(char::from(hex[usize::from(byte >> 4)]));
            spelling.push(char::from(hex[usize::from(byte & 15)]));
        }
        character => spelling.push(character),
    }
    spelling.push('\'');
    Ok(literal(
        inject_name(&char_kind()),
        Obj::mk_string(&spelling),
        info.clone_ref(),
    ))
}

pub(super) fn is_char_lit(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    Ok(option(
        decoded_char(value)?.map(|character| Obj::mk_nat(character as usize)),
    ))
}

pub(super) fn get_char(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    // The pin's Inhabited Char instance uses 'A', including for invalid literals.
    Ok(Obj::mk_nat(decoded_char(value)?.unwrap_or('A') as usize))
}

fn str_kind() -> Name {
    Name::str(Name::anonymous(), "str")
}

fn char_kind() -> Name {
    Name::str(Name::anonymous(), "char")
}

fn literal(kind: Obj, text: Obj, info: Obj) -> Obj {
    let atom = Obj::mk_ctor(layout::SYNTAX_ATOM.tag, vec![info, text], &[]);
    // `mkLit` calls `mkNode` with its default info. Only the atom receives the
    // caller's SourceInfo; copying it to the node changes getHeadInfo behavior.
    Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            kind,
            Obj::mk_array(vec![atom]),
        ],
        &[],
    )
}

fn option(value: Option<Obj>) -> Obj {
    value.map_or_else(
        || Obj::mk_nat(expansion_layout::OPTION_NONE_TAG),
        |value| Obj::mk_ctor(expansion_layout::OPTION_SOME.tag, vec![value], &[]),
    )
}

pub(super) fn literal_value(kind: &Name, value: &Obj) -> Result<Option<Obj>, IntrinsicFailure> {
    if !matches!(syntax_kind(value)?, SyntaxKind::Node) || name(&child(value, 1)?)? != *kind {
        return Ok(None);
    }
    let args = child(value, 2)?;
    let (size, _) = args.try_array_view().ok_or(VmRefusal::InvalidArrayObject)?;
    if size != 1 {
        return Ok(None);
    }
    let atom = args.array_child(0);
    if !matches!(syntax_kind(&atom)?, SyntaxKind::Atom) {
        return Ok(None);
    }
    let value = child(&atom, 1)?;
    literal_text(&value)?;
    Ok(Some(value))
}

fn decoded_value(value: &Obj) -> Result<Option<Obj>, IntrinsicFailure> {
    let Some(text) = literal_value(&str_kind(), value)? else {
        return Ok(None);
    };
    Ok(decode(literal_text(&text)?)?.map(|decoded| Obj::mk_string(&decoded)))
}

fn decoded_char(value: &Obj) -> Result<Option<char>, IntrinsicFailure> {
    let Some(text) = literal_value(&char_kind(), value)? else {
        return Ok(None);
    };
    // `decodeCharLit` reads byte position one without checking either quote
    // or the tail. Invalid raw positions yield the default Char, just as in
    // the string decoder; unknown escapes remain Option.none.
    let mut cursor = Cursor {
        text: literal_text(&text)?,
        position: 1,
    };
    let character = cursor.read();
    Ok(if character == '\\' {
        quoted_char(cursor).map(|(character, _)| character)
    } else {
        Some(character)
    })
}

pub(super) fn literal_text(value: &Obj) -> Result<&str, IntrinsicFailure> {
    let (_, _, _, bytes) = value
        .try_borrow_string_view()
        .ok_or(VmRefusal::InvalidStringObject)?;
    // Bound work before UTF-8/count validation scans the borrowed carrier.
    limit(
        "literal input bytes",
        MAX_LITERAL_BYTES,
        bytes.len().saturating_sub(1) as u64,
    )?;
    Ok(string(value)?)
}

/// `String.quote` uses `Char.quoteCore` with `inString = true`: CR is `\x0d`,
/// single quotes are literal, and only ASCII controls/DEL use hex escaping.
fn quote(value: &str, allowed: u64) -> Result<String, IntrinsicFailure> {
    let mut bytes = 2u64;
    for character in value.chars() {
        bytes = bytes.saturating_add(match character {
            '\n' | '\t' | '\\' | '"' => 2,
            character if character <= '\u{1f}' || character == '\u{7f}' => 4,
            character => character.len_utf8() as u64,
        });
        limit("literal constructor bytes", allowed, bytes)?;
    }
    limit("literal constructor bytes", allowed, bytes)?;
    let mut result = String::with_capacity(bytes as usize);
    result.push('"');
    for character in value.chars() {
        match character {
            '\n' => result.push_str("\\n"),
            '\t' => result.push_str("\\t"),
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            character if character <= '\u{1f}' || character == '\u{7f}' => {
                let byte = character as u8;
                let hex = b"0123456789abcdef";
                result.push_str("\\x");
                result.push(char::from(hex[usize::from(byte >> 4)]));
                result.push(char::from(hex[usize::from(byte & 15)]));
            }
            character => result.push(character),
        }
    }
    result.push('"');
    Ok(result)
}

/// Raw byte positions are observable on malformed spellings. The pin's
/// `String.Internal.get` returns default Char ('A') at an invalid position;
/// `next` then advances by that character's one-byte width.
#[derive(Clone, Copy)]
struct Cursor<'a> {
    text: &'a str,
    position: usize,
}

impl Cursor<'_> {
    fn get(self) -> char {
        self.text
            .get(self.position..)
            .and_then(|text| text.chars().next())
            .unwrap_or('A')
    }

    fn read(&mut self) -> char {
        let character = self.get();
        self.position = self.position.saturating_add(character.len_utf8());
        character
    }

    fn at_end(self) -> bool {
        self.position >= self.text.len()
    }
}

fn quoted_char(mut cursor: Cursor<'_>) -> Option<(char, Cursor<'_>)> {
    let character = match cursor.read() {
        '\\' => '\\',
        '"' => '"',
        '\'' => '\'',
        'r' => '\r',
        'n' => '\n',
        't' => '\t',
        escape @ ('x' | 'u') => {
            let mut scalar = 0;
            for _ in 0..if escape == 'x' { 2 } else { 4 } {
                scalar = scalar * 16 + cursor.read().to_digit(16)?;
            }
            // `Char.ofNat` maps UTF-16 surrogate values to NUL.
            char::from_u32(scalar).unwrap_or('\0')
        }
        _ => return None,
    };
    Some((character, cursor))
}

fn whitespace(character: char) -> bool {
    matches!(character, ' ' | '\t' | '\r' | '\n')
}

/// Unlike the lexer, the public API intentionally does not validate opening
/// quotes, trailing characters, raw delimiters, or a newline-only string gap.
fn decode(value: &str) -> Result<Option<String>, IntrinsicFailure> {
    limit("literal input bytes", MAX_LITERAL_BYTES, value.len() as u64)?;
    let mut cursor = Cursor {
        text: value,
        position: 1,
    };
    if value.starts_with('r') {
        let mut hashes = 0usize;
        while cursor.read() == '#' {
            hashes += 1;
        }
        let start = cursor.position;
        let end = value.len().saturating_sub(hashes + 1);
        if start >= end {
            return Ok(Some(String::new()));
        }
        // `Pos.Raw.extract` scans for an exact end position. If the requested
        // end is inside a UTF-8 character, it keeps the complete remaining tail.
        let end = if value.is_char_boundary(end) {
            end
        } else {
            value.len()
        };
        return Ok(Some(value.get(start..end).unwrap_or("").to_owned()));
    }
    let mut result = String::new();
    loop {
        let character = cursor.read();
        if character == '"' {
            return Ok(Some(result));
        }
        if cursor.at_end() {
            return Ok(None);
        }
        let character = if character == '\\' {
            if let Some((character, next)) = quoted_char(cursor) {
                cursor = next;
                character
            } else if whitespace(cursor.get()) {
                while whitespace(cursor.get()) {
                    cursor.read();
                }
                continue;
            } else {
                return Ok(None);
            }
        } else {
            character
        };
        limit(
            "literal decoded bytes",
            MAX_LITERAL_BYTES,
            (result.len() as u64).saturating_add(character.len_utf8() as u64),
        )?;
        result.push(character);
    }
}
