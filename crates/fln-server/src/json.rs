//! Binary-facing façade for Lantern's strict JSON-RPC parser.
//!
//! Transcript tools are separate binary crates, so they cannot name the private
//! `dispatch::json` module through the library API. They include this façade as
//! their local `json` module; the implementation itself remains single-source at
//! `dispatch/json.rs`.

#![allow(dead_code)]

include!("dispatch/json.rs");

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
