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
    let range = object_member(root, "range");
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
    matches!((point("start"),point("end")),(Some(start),Some(end)) if start <= end)
}
