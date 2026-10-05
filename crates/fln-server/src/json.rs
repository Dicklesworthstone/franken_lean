//! Binary-facing façade for Lantern's strict JSON-RPC parser.
//!
//! Transcript tools are separate binary crates, so they cannot name the private
//! `dispatch::json` module through the library API. They include this façade as
//! their local `json` module; the implementation itself remains single-source at
//! `dispatch/json/core.rs`. Live document edits depend on dispatch session state
//! and must not be pulled into these standalone transcript binaries.

#![allow(dead_code)]
// `include!` splices the decoder (which ends in a `#[cfg(test)] mod tests)
// above the façade functions below, so the parser's own items legitimately follow
// a test module whenever this façade is compiled as a test target.
#![allow(clippy::items_after_test_module)]

include!("dispatch/json/core.rs");

pub(super) fn object_member<'a>(object: RawField<'a>, key: &str) -> RawField<'a> {
    match object_value(object) {
        RawField::Value(value) => object_field(value, key),
        RawField::Missing => RawField::Missing,
        RawField::Invalid => RawField::Invalid,
    }
}

pub(super) fn object_string_member(object: RawField<'_>, key: &str) -> DecodedField {
    decoded_string(object_member(object, key))
}

pub(super) fn object_integer_member(object: RawField<'_>, key: &str) -> VersionField {
    match object_member(object, key) {
        RawField::Missing => VersionField::Missing,
        RawField::Invalid => VersionField::Invalid,
        RawField::Value(value) => value
            .trim()
            .parse::<i64>()
            .map(VersionField::Valid)
            .unwrap_or(VersionField::Invalid),
    }
}

pub(super) fn object_boolean_member(object: RawField<'_>, key: &str) -> BooleanField {
    decoded_boolean_field(object_value(object), key)
}

pub(super) fn response_result(json: &str) -> RawField<'_> {
    object_field(json, "result")
}

pub(super) fn response_error(json: &str) -> RawField<'_> {
    object_field(json, "error")
}

fn object_value(raw: RawField<'_>) -> RawField<'_> {
    match raw {
        RawField::Value(value) if value.trim_start().starts_with('{') => RawField::Value(value),
        RawField::Missing => RawField::Missing,
        RawField::Value(_) | RawField::Invalid => RawField::Invalid,
    }
}

pub(super) fn response_error_code(error: RawField<'_>) -> VersionField {
    decoded_integer_field(object_value(error), "code")
}

pub(super) fn response_error_message(error: RawField<'_>) -> DecodedField {
    decoded_string_field(object_value(error), "message")
}

// Native semantic result profiles. Correlation validates their payload, not
// merely the JSON object's outer shape; it still makes no theorem verdict.
pub(super) fn plain_goal_result(value: &str) -> bool {
    if value.len() > 1024 * 1024 {
        return false;
    }
    let root = RawField::Value(value);
    if !matches!(
        object_string_member(root, "rendered"),
        DecodedField::Valid(_)
    ) {
        return false;
    }
    let RawField::Value(goals) = object_member(root, "goals") else {
        return false;
    };
    let bytes = goals.as_bytes();
    let mut i = skip_ws(bytes, 0);
    if bytes.get(i) != Some(&b'[') {
        return false;
    }
    i += 1;
    let mut count = 0;
    loop {
        i = skip_ws(bytes, i);
        if bytes.get(i) == Some(&b']') {
            return skip_ws(bytes, i + 1) == bytes.len();
        }
        if count >= 256 || bytes.get(i) != Some(&b'"') {
            return false;
        }
        let Some(end) = parse_value_end(goals, i, 0) else {
            return false;
        };
        if !matches!(
            decoded_string(RawField::Value(&goals[i..end])),
            DecodedField::Valid(_)
        ) {
            return false;
        }
        count += 1;
        i = skip_ws(bytes, end);
        if bytes.get(i) == Some(&b',') {
            i += 1;
            if bytes.get(skip_ws(bytes, i)) == Some(&b']') {
                return false;
            }
        } else if bytes.get(i) != Some(&b']') {
            return false;
        }
    }
}
pub(super) fn hover_result(value: &str) -> bool {
    if value.len() > 1024 * 1024 {
        return false;
    }
    let root = RawField::Value(value);
    let contents = object_member(root, "contents");
    if !matches!(object_string_member(contents, "kind"), DecodedField::Valid(kind) if kind == "plaintext")
        || !matches!(
            object_string_member(contents, "value"),
            DecodedField::Valid(_)
        )
    {
        return false;
    }
    matches!(range_points(object_member(root, "range")), Some((start, end)) if start <= end)
}

/// One LSP `Range` as ordered `(line, character)` pairs, each a non-negative i32.
fn range_points(range: RawField<'_>) -> Option<((i64, i64), (i64, i64))> {
    let point = |key| {
        let point = object_member(range, key);
        match (
            object_integer_member(point, "line"),
            object_integer_member(point, "character"),
        ) {
            (VersionField::Valid(line), VersionField::Valid(character))
                if (0..=i64::from(i32::MAX)).contains(&line)
                    && (0..=i64::from(i32::MAX)).contains(&character) =>
            {
                Some((line, character))
            }
            _ => None,
        }
    };
    Some((point("start")?, point("end")?))
}

/// A nonempty string with no control characters, as the native server emits.
fn plain_string_member(object: RawField<'_>, key: &str) -> bool {
    matches!(
        object_string_member(object, key),
        DecodedField::Valid(text) if !text.is_empty() && !text.chars().any(char::is_control)
    )
}

/// The elements of a JSON array, each as raw text; `None` if it is not one, if an element is
/// malformed, or if it holds more than `limit` elements.
fn array_elements(value: &str, limit: usize) -> Option<Vec<&str>> {
    let bytes = value.as_bytes();
    let mut i = skip_ws(bytes, 0);
    if bytes.get(i) != Some(&b'[') {
        return None;
    }
    i += 1;
    let mut elements = Vec::new();
    loop {
        i = skip_ws(bytes, i);
        if bytes.get(i) == Some(&b']') {
            return (skip_ws(bytes, i + 1) == bytes.len()).then_some(elements);
        }
        if elements.len() >= limit {
            return None;
        }
        let end = parse_value_end(value, i, 0)?;
        elements.push(value.get(i..end)?);
        i = skip_ws(bytes, end);
        if bytes.get(i) == Some(&b',') {
            i += 1;
            if bytes.get(skip_ws(bytes, i)) == Some(&b']') {
                return None;
            }
        } else if bytes.get(i) != Some(&b']') {
            return None;
        }
    }
}

/// The native completion profile (`dispatch/semantic/completion.rs`): a `CompletionList`
/// with a boolean `isIncomplete` and at most 256 plaintext items. Each item has a nonempty
/// label, kind 1..=25, `insertTextFormat` 1 (plaintext; the server never sends snippets),
/// an optional string `filterText`, and a `textEdit` whose range is ordered and on one
/// line, with nonempty `newText`.
pub(super) fn completion_result(value: &str) -> bool {
    if value.len() > 1024 * 1024 {
        return false;
    }
    let root = RawField::Value(value);
    if !matches!(
        object_boolean_member(root, "isIncomplete"),
        BooleanField::Valid(_)
    ) {
        return false;
    }
    let RawField::Value(items) = object_member(root, "items") else {
        return false;
    };
    let Some(items) = array_elements(items, 256) else {
        return false;
    };
    items.into_iter().all(|item| {
        let item = RawField::Value(item);
        let edit = object_member(item, "textEdit");
        let filter_text = match object_member(item, "filterText") {
            RawField::Missing => true,
            field => matches!(decoded_string(field), DecodedField::Valid(_)),
        };
        plain_string_member(item, "label")
            && matches!(object_integer_member(item, "kind"), VersionField::Valid(kind) if (1..=25).contains(&kind))
            && matches!(
                object_integer_member(item, "insertTextFormat"),
                VersionField::Valid(1)
            )
            && filter_text
            && plain_string_member(edit, "newText")
            && matches!(
                range_points(object_member(edit, "range")),
                Some((start, end)) if start <= end && start.0 == end.0
            )
    })
}

/// The native definition profile: one LSP `Location` whose URI is a nonempty string without
/// control characters and whose range is nonempty, as `dispatch/semantic.rs` refuses an
/// empty or inverted target range rather than sending one.
pub(super) fn definition_result(value: &str) -> bool {
    if value.len() > 1024 * 1024 {
        return false;
    }
    let root = RawField::Value(value);
    plain_string_member(root, "uri")
        && matches!(range_points(object_member(root, "range")), Some((start, end)) if start < end)
}
