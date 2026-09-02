//! Binary-facing façade for Lantern's strict JSON-RPC parser.
//!
//! Transcript tools are separate binary crates, so they cannot name the private
//! `dispatch::json` module through the library API. They include this façade as
//! their local `json` module; the implementation itself remains single-source at
//! `dispatch/json.rs`.

#![allow(dead_code)]

include!("dispatch/json.rs");

pub(super) fn object_member(object: RawField<'_>, key: &str) -> RawField<'_> {
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
