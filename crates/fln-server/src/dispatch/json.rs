use fln_core::diag::DIAGNOSTIC_PROJECTION_SCHEMA;

use crate::json_string;

const MAX_JSON_NESTING: usize = 256;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RequestId {
    Number(String),
    Text(String),
    Null,
}

impl RequestId {
    pub(super) fn as_json(&self) -> String {
        match self {
            Self::Number(value) => value.clone(),
            Self::Text(value) => json_string(value),
            Self::Null => "null".to_string(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum RequestIdField {
    Absent,
    Valid(RequestId),
    Invalid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RawField<'a> {
    Missing,
    Value(&'a str),
    Invalid,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum DecodedField {
    Missing,
    Valid(String),
    Invalid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VersionField {
    Missing,
    Valid(i64),
    Invalid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BooleanField {
    Missing,
    Valid(bool),
    Invalid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum EnvelopeError {
    MalformedJson,
    NotObject,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Envelope<'a> {
    pub(super) jsonrpc: DecodedField,
    pub(super) id: RequestIdField,
    pub(super) method: DecodedField,
    pub(super) params: RawField<'a>,
}

fn skip_ws(bytes: &[u8], mut index: usize) -> usize {
    while matches!(
        bytes.get(index).copied(),
        Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
    ) {
        index += 1;
    }
    index
}

fn scan_string_end(bytes: &[u8], start: usize) -> Option<usize> {
    if bytes.get(start).copied()? != b'"' {
        return None;
    }
    let mut index = start.checked_add(1)?;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return index.checked_add(1),
            b'\\' => {
                let escape = *bytes.get(index.checked_add(1)?)?;
                match escape {
                    b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => {
                        index = index.checked_add(2)?;
                    }
                    b'u' => {
                        let end = index.checked_add(6)?;
                        let digits = bytes.get(index + 2..end)?;
                        if !digits.iter().all(u8::is_ascii_hexdigit) {
                            return None;
                        }
                        index = end;
                    }
                    _ => return None,
                }
            }
            0x00..=0x1f => return None,
            _ => index += 1,
        }
    }
    None
}

fn scan_number_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start;
    if bytes.get(index).copied() == Some(b'-') {
        index = index.checked_add(1)?;
    }

    match bytes.get(index).copied()? {
        b'0' => {
            index += 1;
            if bytes.get(index).is_some_and(u8::is_ascii_digit) {
                return None;
            }
        }
        b'1'..=b'9' => {
            index += 1;
            while bytes.get(index).is_some_and(u8::is_ascii_digit) {
                index += 1;
            }
        }
        _ => return None,
    }

    if bytes.get(index).copied() == Some(b'.') {
        index += 1;
        let first = *bytes.get(index)?;
        if !first.is_ascii_digit() {
            return None;
        }
        index += 1;
        while bytes.get(index).is_some_and(u8::is_ascii_digit) {
            index += 1;
        }
    }

    if matches!(bytes.get(index).copied(), Some(b'e' | b'E')) {
        index += 1;
        if matches!(bytes.get(index).copied(), Some(b'+' | b'-')) {
            index += 1;
        }
        let first = *bytes.get(index)?;
        if !first.is_ascii_digit() {
            return None;
        }
        index += 1;
        while bytes.get(index).is_some_and(u8::is_ascii_digit) {
            index += 1;
        }
    }

    Some(index)
}

fn scan_literal_end(bytes: &[u8], start: usize, literal: &[u8]) -> Option<usize> {
    let end = start.checked_add(literal.len())?;
    (bytes.get(start..end)? == literal).then_some(end)
}

fn parse_value_end(json: &str, start: usize, depth: usize) -> Option<usize> {
    if depth > MAX_JSON_NESTING {
        return None;
    }
    let bytes = json.as_bytes();
    let start = skip_ws(bytes, start);
    match bytes.get(start).copied()? {
        b'"' => scan_string_end(bytes, start),
        b'{' => parse_object_end(json, start, depth),
        b'[' => parse_array_end(json, start, depth),
        b't' => scan_literal_end(bytes, start, b"true"),
        b'f' => scan_literal_end(bytes, start, b"false"),
        b'n' => scan_literal_end(bytes, start, b"null"),
        b'-' | b'0'..=b'9' => scan_number_end(bytes, start),
        _ => None,
    }
}

fn parse_object_end(json: &str, start: usize, depth: usize) -> Option<usize> {
    if depth == MAX_JSON_NESTING {
        return None;
    }
    let bytes = json.as_bytes();
    let mut index = start.checked_add(1)?;
    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b'}') {
        return index.checked_add(1);
    }

    loop {
        let key_end = scan_string_end(bytes, index)?;
        index = skip_ws(bytes, key_end);
        if bytes.get(index).copied() != Some(b':') {
            return None;
        }
        index = skip_ws(bytes, index.checked_add(1)?);
        index = parse_value_end(json, index, depth + 1)?;
        index = skip_ws(bytes, index);
        match bytes.get(index).copied()? {
            b',' => {
                index = skip_ws(bytes, index.checked_add(1)?);
                if bytes.get(index).copied() == Some(b'}') {
                    return None;
                }
            }
            b'}' => return index.checked_add(1),
            _ => return None,
        }
    }
}

fn parse_array_end(json: &str, start: usize, depth: usize) -> Option<usize> {
    if depth == MAX_JSON_NESTING {
        return None;
    }
    let bytes = json.as_bytes();
    let mut index = start.checked_add(1)?;
    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b']') {
        return index.checked_add(1);
    }

    loop {
        index = parse_value_end(json, index, depth + 1)?;
        index = skip_ws(bytes, index);
        match bytes.get(index).copied()? {
            b',' => {
                index = skip_ws(bytes, index.checked_add(1)?);
                if bytes.get(index).copied() == Some(b']') {
                    return None;
                }
            }
            b']' => return index.checked_add(1),
            _ => return None,
        }
    }
}

fn decode_json_string_value(value: &str) -> Option<String> {
    fn hex_quad(chars: &mut std::str::Chars<'_>) -> Option<u16> {
        let mut value = 0u16;
        for _ in 0..4 {
            value = value.checked_mul(16)?;
            value = value.checked_add(u16::try_from(chars.next()?.to_digit(16)?).ok()?)?;
        }
        Some(value)
    }

    fn unicode_escape(chars: &mut std::str::Chars<'_>) -> Option<char> {
        let first = hex_quad(chars)?;
        match first {
            0xd800..=0xdbff => {
                if chars.next()? != '\\' || chars.next()? != 'u' {
                    return None;
                }
                let second = hex_quad(chars)?;
                if !(0xdc00..=0xdfff).contains(&second) {
                    return None;
                }
                let high = u32::from(first) - 0xd800;
                let low = u32::from(second) - 0xdc00;
                char::from_u32(0x1_0000 + (high << 10) + low)
            }
            0xdc00..=0xdfff => None,
            scalar => char::from_u32(u32::from(scalar)),
        }
    }

    let value = value.trim();
    let end = scan_string_end(value.as_bytes(), 0)?;
    if end != value.len() {
        return None;
    }
    let mut chars = value.strip_prefix('"')?.chars();
    let mut result = String::new();
    loop {
        match chars.next()? {
            '"' => return chars.next().is_none().then_some(result),
            '\\' => {
                let escaped = chars.next()?;
                result.push(match escaped {
                    '"' => '"',
                    '\\' => '\\',
                    '/' => '/',
                    'b' => '\u{0008}',
                    'f' => '\u{000c}',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    'u' => unicode_escape(&mut chars)?,
                    _ => return None,
                });
            }
            control if control <= '\u{001f}' => return None,
            other => result.push(other),
        }
    }
}

fn decoded_string(raw: RawField<'_>) -> DecodedField {
    match raw {
        RawField::Missing => DecodedField::Missing,
        RawField::Invalid => DecodedField::Invalid,
        RawField::Value(value) => decode_json_string_value(value)
            .map(DecodedField::Valid)
            .unwrap_or(DecodedField::Invalid),
    }
}

fn request_id(raw: RawField<'_>) -> RequestIdField {
    match raw {
        RawField::Missing => RequestIdField::Absent,
        RawField::Invalid => RequestIdField::Invalid,
        RawField::Value(value) => {
            let value = value.trim();
            if value == "null" {
                RequestIdField::Valid(RequestId::Null)
            } else if value.starts_with('"') {
                decode_json_string_value(value)
                    .map(RequestId::Text)
                    .map_or(RequestIdField::Invalid, RequestIdField::Valid)
            } else {
                let bytes = value.as_bytes();
                match scan_number_end(bytes, 0) {
                    Some(end) if end == bytes.len() => {
                        RequestIdField::Valid(RequestId::Number(value.to_string()))
                    }
                    _ => RequestIdField::Invalid,
                }
            }
        }
    }
}

pub(super) fn parse_envelope(json: &str) -> Result<Envelope<'_>, EnvelopeError> {
    let bytes = json.as_bytes();
    let mut index = skip_ws(bytes, 0);
    let value_end = parse_value_end(json, index, 0).ok_or(EnvelopeError::MalformedJson)?;
    if skip_ws(bytes, value_end) != bytes.len() {
        return Err(EnvelopeError::MalformedJson);
    }
    if bytes.get(index).copied() != Some(b'{') {
        return Err(EnvelopeError::NotObject);
    }
    index += 1;

    let mut jsonrpc = RawField::Missing;
    let mut id = RawField::Missing;
    let mut method = RawField::Missing;
    let mut params = RawField::Missing;

    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b'}') {
        index += 1;
    } else {
        loop {
            let key_start = index;
            let key_end =
                scan_string_end(bytes, key_start).ok_or(EnvelopeError::MalformedJson)?;
            let key_value = json
                .get(key_start..key_end)
                .ok_or(EnvelopeError::MalformedJson)?;
            let key =
                decode_json_string_value(key_value).ok_or(EnvelopeError::MalformedJson)?;
            index = skip_ws(bytes, key_end);
            if bytes.get(index).copied() != Some(b':') {
                return Err(EnvelopeError::MalformedJson);
            }
            index = skip_ws(
                bytes,
                index.checked_add(1).ok_or(EnvelopeError::MalformedJson)?,
            );
            let value_start = index;
            let value_end =
                parse_value_end(json, value_start, 0).ok_or(EnvelopeError::MalformedJson)?;
            let value = json
                .get(value_start..value_end)
                .ok_or(EnvelopeError::MalformedJson)?;

            let slot = match key.as_str() {
                "jsonrpc" => Some(&mut jsonrpc),
                "id" => Some(&mut id),
                "method" => Some(&mut method),
                "params" => Some(&mut params),
                _ => None,
            };
            if let Some(slot) = slot {
                if !matches!(*slot, RawField::Missing) {
                    *slot = RawField::Invalid;
                } else {
                    *slot = RawField::Value(value);
                }
            }

            index = skip_ws(bytes, value_end);
            match bytes
                .get(index)
                .copied()
                .ok_or(EnvelopeError::MalformedJson)?
            {
                b',' => {
                    index = skip_ws(
                        bytes,
                        index.checked_add(1).ok_or(EnvelopeError::MalformedJson)?,
                    );
                    if bytes.get(index).copied() == Some(b'}') {
                        return Err(EnvelopeError::MalformedJson);
                    }
                }
                b'}' => {
                    index += 1;
                    break;
                }
                _ => return Err(EnvelopeError::MalformedJson),
            }
        }
    }

    if skip_ws(bytes, index) != bytes.len() {
        return Err(EnvelopeError::MalformedJson);
    }

    Ok(Envelope {
        jsonrpc: decoded_string(jsonrpc),
        id: request_id(id),
        method: decoded_string(method),
        params,
    })
}

fn object_field<'a>(json: &'a str, wanted: &str) -> RawField<'a> {
    let bytes = json.as_bytes();
    let mut index = skip_ws(bytes, 0);
    if bytes.get(index).copied() != Some(b'{') {
        return RawField::Invalid;
    }
    index += 1;
    let mut found = RawField::Missing;

    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b'}') {
        index += 1;
    } else {
        loop {
            let key_start = index;
            let Some(key_end) = scan_string_end(bytes, key_start) else {
                return RawField::Invalid;
            };
            let Some(key) = json
                .get(key_start..key_end)
                .and_then(decode_json_string_value)
            else {
                return RawField::Invalid;
            };
            index = skip_ws(bytes, key_end);
            if bytes.get(index).copied() != Some(b':') {
                return RawField::Invalid;
            }
            index = skip_ws(bytes, index + 1);
            let value_start = index;
            let Some(value_end) = parse_value_end(json, value_start, 0) else {
                return RawField::Invalid;
            };
            let Some(value) = json.get(value_start..value_end) else {
                return RawField::Invalid;
            };
            if key == wanted {
                if !matches!(found, RawField::Missing) {
                    return RawField::Invalid;
                }
                found = RawField::Value(value);
            }

            index = skip_ws(bytes, value_end);
            match bytes.get(index).copied() {
                Some(b',') => {
                    index = skip_ws(bytes, index + 1);
                    if bytes.get(index).copied() == Some(b'}') {
                        return RawField::Invalid;
                    }
                }
                Some(b'}') => {
                    index += 1;
                    break;
                }
                _ => return RawField::Invalid,
            }
        }
    }

    if skip_ws(bytes, index) == bytes.len() {
        found
    } else {
        RawField::Invalid
    }
}

fn params_object(params: RawField<'_>) -> RawField<'_> {
    match params {
        RawField::Value(value) if value.trim_start().starts_with('{') => RawField::Value(value),
        RawField::Missing => RawField::Missing,
        RawField::Value(_) | RawField::Invalid => RawField::Invalid,
    }
}

fn text_document_object(params: RawField<'_>) -> RawField<'_> {
    match params_object(params) {
        RawField::Value(value) => match object_field(value, "textDocument") {
            RawField::Value(document) if document.trim_start().starts_with('{') => {
                RawField::Value(document)
            }
            RawField::Missing => RawField::Missing,
            RawField::Value(_) | RawField::Invalid => RawField::Invalid,
        },
        other => other,
    }
}

fn decoded_string_field(object: RawField<'_>, key: &str) -> DecodedField {
    match object {
        RawField::Value(value) => decoded_string(object_field(value, key)),
        RawField::Missing => DecodedField::Missing,
        RawField::Invalid => DecodedField::Invalid,
    }
}

fn decoded_integer_field(object: RawField<'_>, key: &str) -> VersionField {
    let raw = match object {
        RawField::Value(value) => object_field(value, key),
        RawField::Missing => RawField::Missing,
        RawField::Invalid => RawField::Invalid,
    };
    match raw {
        RawField::Missing => VersionField::Missing,
        RawField::Invalid => VersionField::Invalid,
        RawField::Value(value) => {
            let value = value.trim();
            let bytes = value.as_bytes();
            match scan_number_end(bytes, 0) {
                Some(end)
                    if end == bytes.len()
                        && !value
                            .bytes()
                            .any(|byte| matches!(byte, b'.' | b'e' | b'E')) =>
                {
                    value
                        .parse::<i64>()
                        .map(VersionField::Valid)
                        .unwrap_or(VersionField::Invalid)
                }
                _ => VersionField::Invalid,
            }
        }
    }
}

fn decoded_boolean_field(object: RawField<'_>, key: &str) -> BooleanField {
    let raw = match object {
        RawField::Value(value) => object_field(value, key),
        RawField::Missing => RawField::Missing,
        RawField::Invalid => RawField::Invalid,
    };
    match raw {
        RawField::Missing => BooleanField::Missing,
        RawField::Invalid => BooleanField::Invalid,
        RawField::Value(value) => match value.trim() {
            "true" => BooleanField::Valid(true),
            "false" => BooleanField::Valid(false),
            _ => BooleanField::Invalid,
        },
    }
}

pub(super) fn text_document_uri(params: RawField<'_>) -> DecodedField {
    decoded_string_field(text_document_object(params), "uri")
}

pub(super) fn text_document_version(params: RawField<'_>) -> VersionField {
    decoded_integer_field(text_document_object(params), "version")
}

pub(super) fn text_document_text(params: RawField<'_>) -> DecodedField {
    decoded_string_field(text_document_object(params), "text")
}

pub(super) fn save_text(params: RawField<'_>) -> DecodedField {
    decoded_string_field(params_object(params), "text")
}

pub(super) fn direct_uri(params: RawField<'_>) -> DecodedField {
    decoded_string_field(params_object(params), "uri")
}

pub(super) fn direct_version(params: RawField<'_>) -> VersionField {
    decoded_integer_field(params_object(params), "version")
}

/// Validate the canonical diagnostic-outcome tuple and return its authority.
///
/// This intentionally does more than read a boolean: the schema, outcome kind,
/// and authority bit are one typed contract. Unknown schemas, missing fields,
/// duplicate decoded keys, and contradictory outcome/authority pairs are invalid.
pub(super) fn direct_authority(params: RawField<'_>) -> BooleanField {
    let params = params_object(params);
    let schema = decoded_string_field(params, "schema");
    let outcome = decoded_string_field(params, "outcome");
    let authority = decoded_boolean_field(params, "authority");
    match (schema, outcome, authority) {
        (
            DecodedField::Valid(schema),
            DecodedField::Valid(outcome),
            BooleanField::Valid(authority),
        ) if schema == DIAGNOSTIC_PROJECTION_SCHEMA => match (outcome.as_str(), authority) {
            ("complete", true)
            | ("inconclusive", false)
            | ("internal_fault", false) => BooleanField::Valid(authority),
            _ => BooleanField::Invalid,
        },
        _ => BooleanField::Invalid,
    }
}

pub(super) fn direct_request_id(params: RawField<'_>) -> RequestIdField {
    match params_object(params) {
        RawField::Value(value) => request_id(object_field(value, "id")),
        RawField::Missing => RequestIdField::Absent,
        RawField::Invalid => RequestIdField::Invalid,
    }
}

fn single_array_element(value: &str) -> Option<&str> {
    let bytes = value.as_bytes();
    let mut index = skip_ws(bytes, 0);
    if bytes.get(index).copied() != Some(b'[') {
        return None;
    }
    index += 1;
    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b']') {
        return None;
    }
    let start = index;
    let end = parse_value_end(value, start, 0)?;
    index = skip_ws(bytes, end);
    if bytes.get(index).copied() != Some(b']') {
        return None;
    }
    index += 1;
    if skip_ws(bytes, index) != bytes.len() {
        return None;
    }
    value.get(start..end)
}

pub(super) fn content_changes_text(params: RawField<'_>) -> DecodedField {
    let params = params_object(params);
    let changes = match params {
        RawField::Value(value) => object_field(value, "contentChanges"),
        RawField::Missing => RawField::Missing,
        RawField::Invalid => RawField::Invalid,
    };
    let RawField::Value(changes) = changes else {
        return match changes {
            RawField::Missing => DecodedField::Missing,
            RawField::Invalid => DecodedField::Invalid,
            RawField::Value(_) => unreachable!(),
        };
    };
    let Some(change) = single_array_element(changes) else {
        return DecodedField::Invalid;
    };
    if !matches!(object_field(change, "range"), RawField::Missing)
        || !matches!(object_field(change, "rangeLength"), RawField::Missing)
    {
        return DecodedField::Invalid;
    }
    decoded_string_field(RawField::Value(change), "text")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn envelope_preserves_every_json_rpc_id_kind() {
        for (json, expected) in [
            (
                r#"{"jsonrpc":"2.0","id":42,"method":"x"}"#,
                RequestId::Number("42".to_string()),
            ),
            (
                r#"{"jsonrpc":"2.0","id":-1.25e+2,"method":"x"}"#,
                RequestId::Number("-1.25e+2".to_string()),
            ),
            (
                r#"{"jsonrpc":"2.0","id":"req-\ud83e\udd16","method":"x"}"#,
                RequestId::Text("req-🤖".to_string()),
            ),
            (
                r#"{"jsonrpc":"2.0","id":null,"method":"x"}"#,
                RequestId::Null,
            ),
        ] {
            let envelope = parse_envelope(json).expect("valid envelope");
            assert_eq!(envelope.id, RequestIdField::Valid(expected));
        }
    }

    #[test]
    fn malformed_nested_json_is_rejected_even_when_selected_fields_are_valid() {
        for json in [
            r#"{"jsonrpc":"2.0","method":"x","params":{"bad":tru}}"#,
            r#"{"jsonrpc":"2.0","method":"x","params":[1,]}"#,
            r#"{"jsonrpc":"2.0","method":"x","params":{"a" 1}}"#,
            r#"{"jsonrpc":"2.0","method":"x"} trailing"#,
        ] {
            assert!(parse_envelope(json).is_err(), "accepted malformed JSON: {json}");
        }
    }

    #[test]
    fn selected_duplicate_fields_are_typed_invalid() {
        let envelope =
            parse_envelope(r#"{"jsonrpc":"2.0","id":1,"id":2,"method":"x","params":{}}"#)
                .expect("structurally valid JSON");
        assert_eq!(envelope.id, RequestIdField::Invalid);
    }

    #[test]
    fn document_fields_are_read_only_from_their_exact_containers() {
        let envelope = parse_envelope(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","textDocument":{"uri":"file:///wrong"},"params":{"metadata":{"textDocument":{"uri":"file:///also-wrong"}},"textDocument":{"uri":"file:///right","version":3,"text":"ok"}}}"#,
        )
        .expect("valid envelope");
        assert_eq!(
            text_document_uri(envelope.params),
            DecodedField::Valid("file:///right".to_string())
        );
        assert_eq!(text_document_version(envelope.params), VersionField::Valid(3));
        assert_eq!(
            text_document_text(envelope.params),
            DecodedField::Valid("ok".to_string())
        );
    }

    #[test]
    fn direct_params_fields_are_exact_and_ambiguity_safe() {
        let params = RawField::Value(
            r#"{"uri":"file:///x","version":3,"id":"wait","schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true}"#,
        );
        assert_eq!(
            direct_uri(params),
            DecodedField::Valid("file:///x".to_string())
        );
        assert_eq!(direct_version(params), VersionField::Valid(3));
        assert_eq!(direct_authority(params), BooleanField::Valid(true));
        assert_eq!(
            direct_request_id(params),
            RequestIdField::Valid(RequestId::Text("wait".to_string()))
        );

        let duplicate = RawField::Value(
            r#"{"uri":"a","uri":"b","version":1,"id":1,"id":2,"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"\u0061uthority":false}"#,
        );
        assert_eq!(direct_uri(duplicate), DecodedField::Invalid);
        assert_eq!(direct_request_id(duplicate), RequestIdField::Invalid);
        assert_eq!(direct_authority(duplicate), BooleanField::Invalid);
    }

    #[test]
    fn diagnostic_outcome_tuple_is_structural_and_coherent() {
        for (params, expected) in [
            (
                r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true}"#,
                BooleanField::Valid(true),
            ),
            (
                r#"{"schema":"fln.diagnostic-projection/1","outcome":"inconclusive","authority":false,"detail":{"authority":true,"outcome":"complete"}}"#,
                BooleanField::Valid(false),
            ),
            (
                r#"{"schema":"fln.diagnostic-projection/1","outcome":"internal_fault","authority":false,"message":"\"authority\":true"}"#,
                BooleanField::Valid(false),
            ),
        ] {
            assert_eq!(direct_authority(RawField::Value(params)), expected);
        }

        for params in [
            r#"{"schema":"wrong","outcome":"complete","authority":true}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"inconclusive","authority":true}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":false}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"future","authority":true}"#,
            r#"{"outcome":"complete","authority":true}"#,
            r#"{"schema":"fln.diagnostic-projection/1","authority":true}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":"true"}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"\u0061uthority":false}"#,
        ] {
            assert_eq!(
                direct_authority(RawField::Value(params)),
                BooleanField::Invalid,
                "accepted incoherent diagnostic outcome: {params}"
            );
        }
        assert_eq!(direct_authority(RawField::Missing), BooleanField::Invalid);
        assert_eq!(direct_authority(RawField::Invalid), BooleanField::Invalid);
    }

    #[test]
    fn full_sync_requires_exactly_one_unranged_text_change() {
        for params in [
            r#"{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[]}"#,
            r#"{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"text":"a"},{"text":"b"}]}"#,
            r#"{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"range":{},"text":"a"}]}"#,
            r#"{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"rangeLength":1,"text":"a"}]}"#,
        ] {
            assert_eq!(
                content_changes_text(RawField::Value(params)),
                DecodedField::Invalid
            );
        }
        assert_eq!(
            content_changes_text(RawField::Value(
                r#"{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"text":"whole"}]}"#,
            )),
            DecodedField::Valid("whole".to_string())
        );
    }

    #[test]
    fn string_decoder_rejects_lone_surrogates_and_unknown_escapes() {
        for value in [r#""\ud83e""#, r#""\udd16""#, r#""\q""#] {
            assert!(decode_json_string_value(value).is_none());
        }
    }
}
