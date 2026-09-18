//! Failure-atomic LSP content changes over the exact retained source snapshot.
//!
//! Changes are ordered, not a set of edits against the original document. Each
//! range addresses the result of its predecessors in UTF-16 code units. No
//! document/version/publication state is mutated here. The caller may publish
//! only the complete result, and must invalidate its source on refusal.

use std::borrow::Cow;

use super::{
    DecodedField, RawField, VersionField, decoded_integer_field, decoded_string_field,
    object_field, params_object, parse_array_end, parse_value_end, skip_ws,
};

const MAX_CHANGES: usize = 4096;
const MAX_CHANGE_INPUT_BYTES: usize = 64 * 1024 * 1024;
const MAX_SOURCE_BYTES: usize = super::super::session::MAX_RETAINED_SOURCE_BYTES;
const MAX_EDIT_WORK_BYTES: usize = MAX_SOURCE_BYTES * 8;

#[derive(Clone, Copy)]
struct Limits {
    changes: usize,
    source_bytes: usize,
    work_bytes: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Position {
    line: u32,
    character: u32,
}

type Refusal = &'static str;

fn position(raw: RawField<'_>) -> Result<Position, Refusal> {
    fn coordinate(raw: RawField<'_>, key: &str) -> Result<u32, Refusal> {
        match decoded_integer_field(raw, key) {
            VersionField::Valid(value) if (0..=i64::from(i32::MAX)).contains(&value) => {
                Ok(value as u32)
            }
            _ => Err("LSP edit positions require unambiguous nonnegative integer coordinates"),
        }
    }
    Ok(Position {
        line: coordinate(raw, "line")?,
        character: coordinate(raw, "character")?,
    })
}

/// LSP clamps positions beyond the document/line to its end. An offset inside
/// a surrogate pair has no UTF-8 scalar boundary and is refused, not rounded.
fn byte_offset(text: &str, position: Position) -> Result<usize, Refusal> {
    let bytes = text.as_bytes();
    let mut start = 0;
    let mut line = 0;
    while line < position.line && start < bytes.len() {
        match bytes[start] {
            b'\r' => {
                start += 1;
                if bytes.get(start) == Some(&b'\n') {
                    start += 1;
                }
                line += 1;
            }
            b'\n' => {
                start += 1;
                line += 1;
            }
            _ => start += 1,
        }
    }
    if line < position.line {
        return Ok(text.len());
    }
    let mut end = start;
    while end < bytes.len() && !matches!(bytes[end], b'\r' | b'\n') {
        end += 1;
    }
    let mut units = 0u64;
    let wanted = u64::from(position.character);
    for (offset, scalar) in text[start..end].char_indices() {
        if units == wanted {
            return Ok(start + offset);
        }
        units += scalar.len_utf16() as u64;
        if units > wanted {
            return Err("LSP edit position splits a UTF-16 surrogate pair");
        }
    }
    Ok(end)
}

fn charge(work: &mut usize, bytes: usize) -> Result<(), Refusal> {
    *work = work
        .checked_sub(bytes)
        .ok_or("FrankenLean incremental-edit work budget is exhausted")?;
    Ok(())
}

fn copied(text: &str) -> Result<String, Refusal> {
    let mut result = String::new();
    result
        .try_reserve_exact(text.len())
        .map_err(|_| "FrankenLean could not allocate the edited source snapshot")?;
    result.push_str(text);
    Ok(result)
}

fn apply_one<'a>(
    current: Option<Cow<'a, str>>,
    change: &str,
    limits: Limits,
    work: &mut usize,
) -> Result<Cow<'a, str>, Refusal> {
    let text = match decoded_string_field(RawField::Value(change), "text") {
        DecodedField::Valid(text) => text,
        _ => return Err("LSP content change requires one unambiguous text string"),
    };
    if text.len() > limits.source_bytes {
        return Err("FrankenLean edited source exceeds the bounded source-byte limit");
    }
    let range = object_field(change, "range");
    let length = decoded_integer_field(RawField::Value(change), "rangeLength");
    let range = match range {
        RawField::Missing if length == VersionField::Missing => {
            charge(work, text.len())?;
            return Ok(Cow::Owned(text));
        }
        RawField::Value(range) => range,
        _ => return Err("LSP full replacements must omit range and rangeLength"),
    };
    let current = current.ok_or("LSP incremental change requires a retained source snapshot")?;
    let start = position(object_field(range, "start"))?;
    let end = position(object_field(range, "end"))?;
    if start > end {
        return Err("LSP content change has a reversed range");
    }
    // Charge before scanning the source. This covers both coordinate scans,
    // rangeLength validation, and copying/moving the surviving source bytes.
    let cost = current
        .len()
        .checked_mul(4)
        .and_then(|cost| cost.checked_add(text.len()))
        .ok_or("FrankenLean incremental-edit work accounting overflowed")?;
    charge(work, cost)?;
    let start = byte_offset(&current, start)?;
    let end = byte_offset(&current, end)?;
    if start > end {
        return Err("LSP content change has a reversed range");
    }
    match length {
        VersionField::Missing => {}
        VersionField::Valid(length)
            if (0..=i64::from(i32::MAX)).contains(&length)
                && current[start..end].encode_utf16().count() as u64 == length as u64 => {}
        _ => return Err("LSP rangeLength disagrees with the UTF-16 replacement range"),
    }
    let size = current
        .len()
        .checked_sub(end - start)
        .and_then(|size| size.checked_add(text.len()))
        .filter(|size| *size <= limits.source_bytes)
        .ok_or("FrankenLean edited source exceeds the bounded source-byte limit")?;
    let mut result = String::new();
    result
        .try_reserve_exact(size)
        .map_err(|_| "FrankenLean could not allocate the edited source snapshot")?;
    result.push_str(&current[..start]);
    result.push_str(&text);
    result.push_str(&current[end..]);
    Ok(Cow::Owned(result))
}

/// Decode and apply a complete didChange batch. Full replacements also work
/// without a retained snapshot; a later range then addresses that replacement.
/// A malformed earlier change is never excused by a later full replacement.
pub(in crate::dispatch) fn content_changes_text_from(
    params: RawField<'_>,
    source: Option<&str>,
) -> Result<String, Refusal> {
    apply_with_limits(
        params,
        source,
        Limits {
            changes: MAX_CHANGES,
            source_bytes: MAX_SOURCE_BYTES,
            work_bytes: MAX_EDIT_WORK_BYTES,
        },
    )
}

fn apply_with_limits(
    params: RawField<'_>,
    source: Option<&str>,
    limits: Limits,
) -> Result<String, Refusal> {
    let RawField::Value(params) = params_object(params) else {
        return Err("LSP didChange requires an unambiguous parameter object");
    };
    let RawField::Value(changes) = object_field(params, "contentChanges") else {
        return Err("LSP didChange requires one unambiguous contentChanges array");
    };
    if changes.len() > MAX_CHANGE_INPUT_BYTES {
        return Err("FrankenLean contentChanges input exceeds its byte limit");
    }
    let bytes = changes.as_bytes();
    let begin = skip_ws(bytes, 0);
    if bytes.get(begin) != Some(&b'[') {
        return Err("LSP contentChanges must be an array");
    }
    let end = parse_array_end(changes, begin, 0)
        .filter(|end| skip_ws(bytes, *end) == bytes.len())
        .ok_or("LSP contentChanges array is malformed")?;
    let mut index = skip_ws(bytes, begin + 1);
    let mut current = source.map(Cow::Borrowed);
    let mut count = 0;
    let mut work = limits.work_bytes;
    while index < end && bytes.get(index) != Some(&b']') {
        if count >= limits.changes {
            return Err("FrankenLean contentChanges exceeds the bounded change-count limit");
        }
        count += 1;
        let next = parse_value_end(changes, index, 0)
            .ok_or("LSP contentChanges contains a malformed change")?;
        current = Some(apply_one(current, &changes[index..next], limits, &mut work)?);
        index = skip_ws(bytes, next);
        if bytes.get(index) == Some(&b',') {
            index = skip_ws(bytes, index + 1);
        }
    }
    let current = current.ok_or("LSP incremental change requires a retained source snapshot")?;
    if current.len() > limits.source_bytes {
        return Err("FrankenLean edited source exceeds the bounded source-byte limit");
    }
    match current {
        Cow::Owned(text) => Ok(text),
        Cow::Borrowed(text) => {
            charge(&mut work, text.len())?;
            copied(text)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn apply(source: Option<&str>, changes: &str) -> Result<String, Refusal> {
        let params = format!("{{\"contentChanges\":{changes}}}");
        content_changes_text_from(RawField::Value(&params), source)
    }

    #[test]
    fn ranges_address_each_preceding_result() {
        assert_eq!(
            apply(Some("abc"), r#"[
                {"range":{"start":{"line":0,"character":1},"end":{"line":0,"character":1}},"text":"\n"},
                {"range":{"start":{"line":1,"character":0},"end":{"line":1,"character":1}},"text":"B"}
            ]"#),
            Ok("a\nBc".to_string())
        );
    }

    #[test]
    fn utf16_offsets_and_lengths_are_not_utf8_bytes_or_scalar_counts() {
        let valid = r#"[{"range":{"start":{"line":0,"character":1},"end":{"line":0,"character":3}},"rangeLength":2,"text":"X"}]"#;
        assert_eq!(apply(Some("a🤖b"), valid), Ok("aXb".to_string()));
        assert!(apply(Some("a🤖b"), &valid.replace("\"rangeLength\":2", "\"rangeLength\":1")).is_err());
        for (start, end) in [(1, 2), (2, 3), (2, 2)] {
            let changes = format!(r#"[{{"range":{{"start":{{"line":0,"character":{start}}},"end":{{"line":0,"character":{end}}}}},"text":"X"}}]"#);
            assert!(apply(Some("a🤖b"), &changes).is_err());
        }
    }

    #[test]
    fn crlf_cr_lf_and_trailing_empty_line_are_addressable() {
        assert_eq!(
            apply(Some("a\r\nβ\rc\n"), r#"[{"range":{"start":{"line":0,"character":1},"end":{"line":2,"character":1}},"rangeLength":5,"text":"Q"}]"#),
            Ok("aQ\n".to_string())
        );
        assert_eq!(
            apply(Some("x\r\n"), r#"[{"range":{"start":{"line":1,"character":0},"end":{"line":1,"character":0}},"text":"z"}]"#),
            Ok("x\r\nz".to_string())
        );
    }

    #[test]
    fn oversized_positions_clamp_without_consuming_a_line_ending() {
        assert_eq!(
            apply(Some("a\nb"), r#"[{"range":{"start":{"line":0,"character":99},"end":{"line":0,"character":99}},"text":"!"}]"#),
            Ok("a!\nb".to_string())
        );
        assert_eq!(
            apply(Some("a\nb"), r#"[{"range":{"start":{"line":99,"character":99},"end":{"line":99,"character":99}},"text":"!"}]"#),
            Ok("a\nb!".to_string())
        );
    }

    #[test]
    fn a_full_replacement_can_recover_missing_source_before_a_range() {
        let changes = r#"[{"text":"abc"},{"range":{"start":{"line":0,"character":1},"end":{"line":0,"character":2}},"text":"X"}]"#;
        assert_eq!(apply(None, changes), Ok("aXc".to_string()));
        let changes = r#"[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"text":"X"},{"text":"recovery"}]"#;
        assert!(apply(None, changes).is_err());
    }

    #[test]
    fn empty_changes_are_a_noop_only_with_an_existing_snapshot() {
        assert_eq!(apply(Some("abc"), "[]"), Ok("abc".to_string()));
        assert_eq!(apply(Some(""), "[]"), Ok(String::new()));
        assert!(apply(None, "[]").is_err());
    }

    #[test]
    fn malformed_or_ambiguous_changes_never_return_a_partial_result() {
        let original = "unchanged".to_string();
        for changes in [
            r#"[{"text":"new"},{"text":null}]"#,
            r#"[{"text":"new","\u0074ext":"forged"}]"#,
            r#"[{"text":"new","range":null}]"#,
            r#"[{"text":"new","rangeLength":1}]"#,
            r#"[{"range":{"start":{"line":0,"character":2},"end":{"line":0,"character":1}},"text":"x"}]"#,
            r#"[{"range":{"start":{"line":-1,"character":0},"end":{"line":0,"character":0}},"text":"x"}]"#,
            r#"[{"range":{"start":{"line":0.0,"character":0},"end":{"line":0,"character":0}},"text":"x"}]"#,
            r#"[{"range":{"start":{"line":2147483648,"character":0},"end":{"line":0,"character":0}},"text":"x"}]"#,
            r#"[{"range":{"start":{"line":0,"line":1,"character":0},"end":{"line":0,"character":0}},"text":"x"}]"#,
            r#"[{"range":{"start":{"line":0,"character":0},"start":{"line":0,"character":1},"end":{"line":0,"character":0}},"text":"x"}]"#,
            r#"[{"text":"\ud800"}]"#,
            r#"[{"text":"x"},]"#,
            r#"[{"metadata":{"text":"forged"}}]"#,
            r#"[true]"#,
            r#"{}"#,
        ] {
            assert!(apply(Some(&original), changes).is_err(), "accepted {changes}");
            assert_eq!(original, "unchanged");
        }
        let params = RawField::Value(r#"{"contentChanges":[{"text":"x"}],"\u0063ontentChanges":[{"text":"y"}]}"#);
        assert!(content_changes_text_from(params, Some(&original)).is_err());
    }

    #[test]
    fn intermediate_size_change_count_and_work_are_bounded() {
        let limits = Limits { changes: 2, source_bytes: 8, work_bytes: 128 };
        for changes in [
            r#"[{"text":"123456789"},{"text":"ok"}]"#,
            r#"[{"text":"1"},{"text":"2"},{"text":"3"}]"#,
            r#"[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"text":"123456789"}]"#,
        ] {
            let params = format!("{{\"contentChanges\":{changes}}}");
            assert!(apply_with_limits(RawField::Value(&params), Some("a"), limits).is_err());
        }
        let params = RawField::Value(r#"{"contentChanges":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},"text":""}]}"#);
        assert!(apply_with_limits(params, Some("12345678"), Limits { work_bytes: 31, ..limits }).is_err());
        assert_eq!(apply_with_limits(params, Some("12345678"), Limits { work_bytes: 32, ..limits }), Ok("12345678".to_string()));
    }
}
