//! Structural, failure-atomic decoding of client filesystem observations.
use super::*;
use std::collections::BTreeSet;

const MAX_FILE_EVENTS: usize = 4096;
const MAX_FILE_EVENT_BYTES: usize = 1024 * 1024;

pub(in crate::dispatch) fn watched_file_uris(params: RawField<'_>) -> Result<Vec<String>, &'static str> {
    decode_events(params, MAX_FILE_EVENTS, MAX_FILE_EVENT_BYTES)
}

fn decode_events(params: RawField<'_>, max_events: usize, max_bytes: usize) -> Result<Vec<String>, &'static str> {
    let RawField::Value(params) = params_object(params) else {
        return Err("watched-file changes require an unambiguous parameter object");
    };
    if params.len() > max_bytes { return Err("watched-file changes exceed their byte limit"); }
    let RawField::Value(changes) = object_field(params, "changes") else {
        return Err("watched-file changes require one unambiguous changes array");
    };
    let bytes = changes.as_bytes();
    let begin = skip_ws(bytes, 0);
    let end = parse_array_end(changes, begin, 0)
        .filter(|end| skip_ws(bytes, *end) == bytes.len())
        .ok_or("watched-file changes must be a valid array")?;
    let mut index = skip_ws(bytes, begin + 1);
    let mut count = 0usize;
    let mut total = 0usize;
    let mut uris = BTreeSet::new();
    while index < end && bytes.get(index) != Some(&b']') {
        count += 1;
        if count > max_events { return Err("watched-file changes exceed their event limit"); }
        let next = parse_value_end(changes, index, 0).ok_or("malformed watched-file event")?;
        let event = RawField::Value(&changes[index..next]);
        let uri = match decoded_string_field(event, "uri") {
            DecodedField::Valid(uri) if !uri.is_empty() && !uri.chars().any(char::is_control) => uri,
            _ => return Err("watched-file events require one nonempty URI string"),
        };
        if !matches!(decoded_integer_field(event, "type"), VersionField::Valid(1..=3)) {
            return Err("watched-file event type must be Created(1), Changed(2), or Deleted(3)");
        }
        total = total.checked_add(uri.len()).filter(|n| *n <= max_bytes)
            .ok_or("watched-file URI bytes exceed their limit")?;
        uris.insert(uri);
        index = skip_ws(bytes, next);
        if bytes.get(index) == Some(&b',') { index = skip_ws(bytes, index + 1); }
    }
    // Event kinds are invalidation hints, not source authority. Recheck against
    // the final disk snapshot and current editor overlays once per consumer.
    Ok(uris.into_iter().collect())
}

pub(in crate::dispatch) fn supports_file_registration(mut params: RawField<'_>) -> bool {
    for key in ["capabilities", "workspace", "didChangeWatchedFiles"] {
        params = match params {
            RawField::Value(object) => object_field(object, key),
            _ => return false,
        };
    }
    decoded_boolean_field(params, "dynamicRegistration") == BooleanField::Valid(true)
}

#[derive(Debug, PartialEq, Eq)]
pub(in crate::dispatch) enum RegistrationReply { Accepted, Rejected, Malformed }

/// Used only after envelope/JSON-RPC/id validation of a method-less response.
pub(in crate::dispatch) fn registration_reply(message: &str) -> RegistrationReply {
    if object_field(message, "params") != RawField::Missing { return RegistrationReply::Malformed; }
    match (object_field(message, "result"), object_field(message, "error")) {
        (RawField::Value("null"), RawField::Missing) => RegistrationReply::Accepted,
        (RawField::Missing, RawField::Value(error))
            if matches!(decoded_integer_field(RawField::Value(error), "code"),
                VersionField::Valid(n) if i32::try_from(n).is_ok())
                && matches!(decoded_string_field(RawField::Value(error), "message"), DecodedField::Valid(_)) => RegistrationReply::Rejected,
        _ => RegistrationReply::Malformed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn decode(params: &str) -> Result<Vec<String>, &'static str> { watched_file_uris(RawField::Value(params)) }
    #[test]
    fn all_event_kinds_and_escaped_uris_deduplicate_in_stable_order() {
        assert_eq!(decode(r#"{"changes":[{"uri":"file:///b","type":3},{"uri":"file:///a","type":1},{"uri":"file:///\u0061","type":2}]}"#).unwrap(), ["file:///a", "file:///b"]);
        assert!(decode(r#"{"changes":[]}"#).unwrap().is_empty());
    }
    #[test]
    fn a_malformed_late_event_never_returns_the_valid_prefix() {
        for bad in ["null", "{}", r#"{"uri":"file:///b","type":4}"#, r#"{"uri":"file:///b","type":"2"}"#, r#"{"uri":"file:///b","type":2.0}"#, r#"{"uri":"file:///b","type":2,"type":2}"#, r#"{"uri":"a","uri":"b","type":2}"#, r#"{"uri":"\ud800","type":2}"#] {
            let params = format!(r#"{{"changes":[{{"uri":"file:///a","type":2}},{bad}]}}"#);
            assert!(decode(&params).is_err(), "{params}");
        }
        for bad in ["{}", r#"{"changes":false}"#, r#"{"changes":[],"changes":[]}"#, r#"{"changes":[{"uri":"","type":1}]}"#, r#"{"changes":[{"uri":"file:///\n","type":1}]}"#] {
            assert!(decode(bad).is_err(), "{bad}");
        }
    }
    #[test]
    fn repeated_events_still_consume_count_and_byte_budgets() {
        let params = r#"{"changes":[{"uri":"file:///a","type":1},{"uri":"file:///a","type":2}]}"#;
        assert!(decode_events(RawField::Value(params), 1, 1024).is_err());
        assert!(decode_events(RawField::Value(params), 2, params.len() - 1).is_err());
        assert_eq!(decode_events(RawField::Value(params), 2, params.len()).unwrap(), ["file:///a"]);
    }
    #[test]
    fn capability_is_exact_and_nested_decoys_or_duplicates_cannot_enable_it() {
        let yes = r#"{"capabilities":{"workspace":{"didChangeWatchedFiles":{"dynamicRegistration":true}}}}"#;
        assert!(supports_file_registration(RawField::Value(yes)));
        for no in ["{}", r#"{"dynamicRegistration":true}"#, r#"{"capabilities":{"workspace":{"didChangeWatchedFiles":{"other":{"dynamicRegistration":true}}}}}"#, r#"{"capabilities":{},"capabilities":{"workspace":{"didChangeWatchedFiles":{"dynamicRegistration":true}}}}"#] {
            assert!(!supports_file_registration(RawField::Value(no)), "{no}");
        }
        for value in ["false", "null", "1", "\"true\""] {
            assert!(!supports_file_registration(RawField::Value(&yes.replace("true", value))));
        }
    }
    #[test]
    fn registration_responses_require_an_exclusive_null_result_or_typed_error() {
        assert_eq!(registration_reply(r#"{"result":null}"#), RegistrationReply::Accepted);
        assert_eq!(registration_reply(r#"{"error":{"code":-32601,"message":"unsupported"}}"#), RegistrationReply::Rejected);
        for bad in ["{}", r#"{"result":{}}"#, r#"{"result":null,"result":null}"#, r#"{"result":null,"params":{}}"#, r#"{"result":null,"error":{"code":1,"message":"bad"}}"#, r#"{"error":{"code":2147483648,"message":"bad"}}"#, r#"{"error":{"code":1,"message":false}}"#] {
            assert_eq!(registration_reply(bad), RegistrationReply::Malformed, "{bad}");
        }
    }
}
