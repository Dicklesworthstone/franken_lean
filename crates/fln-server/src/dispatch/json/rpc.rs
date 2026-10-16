//! The pinned Lean RPC envelopes, with strict decoded-key duplicate checks.
//! UInt64/USize identifiers are JSON strings, preserving all 64 bits in clients.
use super::*;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(in crate::dispatch) enum WireFormat {
    #[default]
    V0,
    V1,
}
impl WireFormat {
    pub(in crate::dispatch) fn key(self) -> &'static str {
        match self {
            Self::V0 => "p",
            Self::V1 => "__rpcref",
        }
    }
    pub(in crate::dispatch) fn reference(self, id: u64) -> String {
        format!("{{\"{}\":\"{id}\"}}", self.key())
    }
}

pub(in crate::dispatch) struct Call<'a> {
    pub uri: String,
    pub session: u64,
    pub position: Position,
    pub method: String,
    pub params: RawField<'a>,
}
fn object(value: RawField<'_>) -> Result<&str, &'static str> {
    match params_object(value) {
        RawField::Value(value) => Ok(value),
        _ => Err("RPC parameters require an object"),
    }
}
fn string(value: RawField<'_>, key: &str) -> Result<String, &'static str> {
    match decoded_string_field(value, key) {
        DecodedField::Valid(text) if text.len() <= 16 * 1024 => Ok(text),
        _ => Err("RPC string field is missing, invalid, duplicated or too large"),
    }
}
fn integer(value: RawField<'_>) -> Result<u64, &'static str> {
    let DecodedField::Valid(value) = decoded_string(value) else {
        return Err("RPC identifiers must be string-encoded UInt64 values");
    };
    if value.is_empty() || value.len() > 20 || !value.bytes().all(|c| c.is_ascii_digit()) {
        return Err("RPC identifier is not a decimal UInt64 string");
    }
    value.parse().map_err(|_| "RPC identifier exceeds UInt64")
}
fn uri(value: String) -> Result<String, &'static str> {
    if value.is_empty() || value.chars().any(char::is_control) {
        Err("RPC URI is empty or contains control characters")
    } else {
        Ok(value)
    }
}
pub(in crate::dispatch) fn connect(value: RawField<'_>) -> Result<String, &'static str> {
    object(value)?;
    uri(string(value, "uri")?)
}
pub(in crate::dispatch) fn notification(
    value: RawField<'_>,
) -> Result<(String, u64), &'static str> {
    let raw = object(value)?;
    Ok((connect(value)?, integer(object_field(raw, "sessionId"))?))
}
pub(in crate::dispatch) fn call(value: RawField<'_>) -> Result<Call<'_>, &'static str> {
    let raw = object(value)?;
    let DecodedField::Valid(document) = text_document_uri(value) else {
        return Err("RPC call requires one textDocument URI");
    };
    if document.len() > 16 * 1024 {
        return Err("RPC URI exceeds its limit");
    }
    let method = string(value, "method")?;
    if method.is_empty() {
        return Err("RPC method is empty");
    }
    let params = object_field(raw, "params");
    if !matches!(params, RawField::Value(_)) {
        return Err("RPC call requires one params field");
    }
    Ok(Call {
        uri: uri(document)?,
        session: integer(object_field(raw, "sessionId"))?,
        position: query_position(value)?,
        method,
        params,
    })
}
pub(in crate::dispatch) fn goal_position(
    value: RawField<'_>,
    outer_uri: &str,
) -> Result<Position, &'static str> {
    if !matches!(text_document_uri(value), DecodedField::Valid(ref uri) if uri == outer_uri) {
        return Err("RPC procedure parameters must name the session document");
    }
    query_position(value)
}
pub(in crate::dispatch) fn wire_format(value: RawField<'_>) -> Result<WireFormat, &'static str> {
    let mut current = value;
    for key in ["capabilities", "lean", "rpcWireFormat"] {
        current = match current {
            RawField::Missing | RawField::Value("null") => return Ok(WireFormat::V0),
            _ => object_field(object(current)?, key),
        };
    }
    match current {
        RawField::Missing | RawField::Value("null") => Ok(WireFormat::V0),
        _ => match decoded_string(current) {
            DecodedField::Valid(value) if value == "v0" => Ok(WireFormat::V0),
            DecodedField::Valid(value) if value == "v1" => Ok(WireFormat::V1),
            _ => Err("unsupported or ambiguous Lean RPC wire format"),
        },
    }
}
pub(in crate::dispatch) fn references(
    value: RawField<'_>,
    format: WireFormat,
) -> Result<Vec<u64>, &'static str> {
    let RawField::Value(array) = object_field(object(value)?, "refs") else {
        return Err("RPC release requires one refs array");
    };
    let array = array.trim();
    let bytes = array.as_bytes();
    if bytes.first() != Some(&b'[') {
        return Err("RPC release refs must be an array");
    }
    let mut cursor = skip_ws(bytes, 1);
    let mut result = Vec::new();
    if bytes.get(cursor) == Some(&b']') && skip_ws(bytes, cursor + 1) == bytes.len() {
        return Ok(result);
    }
    loop {
        if result.len() >= 4096 {
            return Err("RPC release exceeds its reference limit");
        }
        let end = parse_value_end(array, cursor, 0).ok_or("malformed RPC release reference")?;
        let reference = &array[cursor..end];
        result.push(integer(object_field(reference, format.key()))?);
        cursor = skip_ws(bytes, end);
        match bytes.get(cursor) {
            Some(b']') if skip_ws(bytes, cursor + 1) == bytes.len() => return Ok(result),
            Some(b',') => cursor = skip_ws(bytes, cursor + 1),
            _ => return Err("malformed RPC reference array"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn identifiers_preserve_all_bits_and_reject_numbers_or_ambiguous_fields() {
        let value = r#"{"uri":"x","sessionId":"18446744073709551615"}"#;
        assert_eq!(
            notification(RawField::Value(value)),
            Ok(("x".into(), u64::MAX))
        );
        for id in [
            "1",
            "null",
            "true",
            "\"-1\"",
            "\"18446744073709551616\"",
            "\"1.0\"",
        ] {
            let value = format!(r#"{{"uri":"x","sessionId":{id}}}"#);
            assert!(notification(RawField::Value(&value)).is_err());
        }
        assert!(
            notification(RawField::Value(
                r#"{"uri":"x","sessionId":"1","session\u0049d":"2"}"#
            ))
            .is_err()
        );
    }
    #[test]
    fn release_decodes_the_entire_array_before_returning_any_ids() {
        for format in [WireFormat::V0, WireFormat::V1] {
            let value = format!(r#"{{"refs":[{0},{0}]}}"#, format.reference(17));
            assert_eq!(
                references(RawField::Value(&value), format),
                Ok(vec![17, 17])
            );
            for suffix in ["1", "null", "{}", "{\"p\":\"2\",\"p\":\"3\"}"] {
                let value = format!(r#"{{"refs":[{},{suffix}]}}"#, format.reference(17));
                assert!(references(RawField::Value(&value), format).is_err());
            }
        }
        assert!(references(RawField::Value(r#"{"refs":[{"p":"0"},]}"#), WireFormat::V0).is_err());
    }
    #[test]
    fn wire_negotiation_defaults_and_rejects_duplicate_decoded_keys() {
        assert_eq!(wire_format(RawField::Value("{}")), Ok(WireFormat::V0));
        assert_eq!(
            wire_format(RawField::Value(
                r#"{"capabilities":{"lean":{"rpcWireFormat":"v1"}}}"#
            )),
            Ok(WireFormat::V1)
        );
        assert!(
            wire_format(RawField::Value(
                r#"{"capabilities":{"lean":{"rpcWireFormat":"v1","rpcWire\u0046ormat":"v0"}}}"#
            ))
            .is_err()
        );
    }
}
