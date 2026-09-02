use fln_core::diag::DIAGNOSTIC_PROJECTION_SCHEMA;

use super::DiagnosticCompletion;
use super::json::RawField;

const MAX_OUTCOME_NESTING: usize = 256;

#[derive(Debug, Default)]
struct OutcomeFields {
    schema: Option<String>,
    outcome: Option<String>,
    authority: Option<bool>,
    diagnostic_count: Option<u64>,
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
                index = index.checked_add(2)?;
                if index > bytes.len() {
                    return None;
                }
            }
            0x00..=0x1f => return None,
            _ => index += 1,
        }
    }
    None
}

fn scan_value_end(bytes: &[u8], start: usize) -> Option<usize> {
    let start = skip_ws(bytes, start);
    match bytes.get(start).copied()? {
        b'"' => scan_string_end(bytes, start),
        b'{' | b'[' => {
            let mut stack = Vec::with_capacity(8);
            stack.push(if bytes[start] == b'{' { b'}' } else { b']' });
            let mut index = start.checked_add(1)?;
            while index < bytes.len() {
                match bytes[index] {
                    b'"' => index = scan_string_end(bytes, index)?,
                    b'{' => {
                        if stack.len() >= MAX_OUTCOME_NESTING {
                            return None;
                        }
                        stack.push(b'}');
                        index += 1;
                    }
                    b'[' => {
                        if stack.len() >= MAX_OUTCOME_NESTING {
                            return None;
                        }
                        stack.push(b']');
                        index += 1;
                    }
                    b'}' | b']' => {
                        if stack.pop()? != bytes[index] {
                            return None;
                        }
                        index += 1;
                        if stack.is_empty() {
                            return Some(index);
                        }
                    }
                    _ => index += 1,
                }
            }
            None
        }
        _ => {
            let mut index = start;
            while let Some(byte) = bytes.get(index).copied() {
                if matches!(byte, b',' | b'}' | b']' | b' ' | b'\t' | b'\r' | b'\n') {
                    break;
                }
                index += 1;
            }
            (index > start).then_some(index)
        }
    }
}

fn decode_json_string(value: &str) -> Option<String> {
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

fn decode_json_u64(value: &str) -> Option<u64> {
    let value = value.trim();
    if value.is_empty() || value.bytes().any(|byte| !byte.is_ascii_digit()) {
        return None;
    }
    if value.len() > 1 && value.starts_with('0') {
        return None;
    }
    value.parse().ok()
}

fn set_once<T>(slot: &mut Option<T>, value: T) -> Option<()> {
    if slot.is_some() {
        return None;
    }
    *slot = Some(value);
    Some(())
}

fn parse_fields(value: &str) -> Option<OutcomeFields> {
    let bytes = value.as_bytes();
    let mut index = skip_ws(bytes, 0);
    if bytes.get(index).copied()? != b'{' {
        return None;
    }
    index += 1;
    let mut fields = OutcomeFields::default();
    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b'}') {
        index += 1;
    } else {
        loop {
            let key_start = index;
            let key_end = scan_string_end(bytes, key_start)?;
            let key = decode_json_string(value.get(key_start..key_end)?)?;
            index = skip_ws(bytes, key_end);
            if bytes.get(index).copied()? != b':' {
                return None;
            }
            index = skip_ws(bytes, index.checked_add(1)?);
            let value_start = index;
            let value_end = scan_value_end(bytes, value_start)?;
            let raw_value = value.get(value_start..value_end)?.trim();
            match key.as_str() {
                "schema" => set_once(&mut fields.schema, decode_json_string(raw_value)?)?,
                "outcome" => set_once(&mut fields.outcome, decode_json_string(raw_value)?)?,
                "authority" => {
                    let authority = match raw_value {
                        "true" => true,
                        "false" => false,
                        _ => return None,
                    };
                    set_once(&mut fields.authority, authority)?;
                }
                "diagnosticCount" => {
                    set_once(&mut fields.diagnostic_count, decode_json_u64(raw_value)?)?;
                }
                _ => {}
            }
            index = skip_ws(bytes, value_end);
            match bytes.get(index).copied()? {
                b',' => {
                    index = skip_ws(bytes, index.checked_add(1)?);
                    if bytes.get(index).copied() == Some(b'}') {
                        return None;
                    }
                }
                b'}' => {
                    index += 1;
                    break;
                }
                _ => return None,
            }
        }
    }
    (skip_ws(bytes, index) == bytes.len()).then_some(fields)
}

pub(super) fn diagnostic_outcome_completion(
    params: RawField<'_>,
) -> Option<DiagnosticCompletion> {
    let RawField::Value(value) = params else {
        return None;
    };
    let fields = parse_fields(value)?;
    if fields.schema.as_deref()? != DIAGNOSTIC_PROJECTION_SCHEMA {
        return None;
    }
    match (
        fields.outcome.as_deref()?,
        fields.authority?,
        fields.diagnostic_count,
    ) {
        ("complete", true, Some(0)) => Some(DiagnosticCompletion::Complete),
        ("inconclusive" | "internal_fault", false, None) => {
            Some(DiagnosticCompletion::Failed)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(value: &str) -> Option<DiagnosticCompletion> {
        diagnostic_outcome_completion(RawField::Value(value))
    }

    #[test]
    fn canonical_outcome_classes_are_typed() {
        assert_eq!(
            parse(r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0}"#),
            Some(DiagnosticCompletion::Complete)
        );
        for outcome in ["inconclusive", "internal_fault"] {
            let value = format!(
                "{{\"schema\":\"fln.diagnostic-projection/1\",\"outcome\":\"{outcome}\",\"authority\":false,\"detail\":{{\"authority\":true,\"diagnosticCount\":99}}}}"
            );
            assert_eq!(parse(&value), Some(DiagnosticCompletion::Failed));
        }
    }

    #[test]
    fn complete_authority_requires_exact_zero_diagnostic_accounting() {
        for value in [
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":1}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":-0}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0.0}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":"0"}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":18446744073709551616}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0,"\u0064iagnosticCount":0}"#,
        ] {
            assert_eq!(parse(value), None, "accepted {value}");
        }
    }

    #[test]
    fn non_authoritative_outcomes_cannot_carry_complete_only_accounting() {
        for outcome in ["inconclusive", "internal_fault"] {
            let value = format!(
                "{{\"schema\":\"fln.diagnostic-projection/1\",\"outcome\":\"{outcome}\",\"authority\":false,\"diagnosticCount\":0}}"
            );
            assert_eq!(parse(&value), None);
        }
    }

    #[test]
    fn nested_or_textual_authority_cannot_spoof_the_top_level_grade() {
        for value in [
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","diagnosticCount":0,"detail":{"authority":true}}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","diagnosticCount":0,"detail":"authority:true"}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":"true","diagnosticCount":0}"#,
        ] {
            assert_eq!(parse(value), None);
        }
    }

    #[test]
    fn duplicate_decoded_keys_and_inconsistent_claims_are_refused() {
        for value in [
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"\u0061uthority":false,"diagnosticCount":0}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":false,"diagnosticCount":0}"#,
            r#"{"schema":"fln.diagnostic-projection/1","outcome":"internal_fault","authority":true}"#,
            r#"{"schema":"other","outcome":"complete","authority":true,"diagnosticCount":0}"#,
            r#"{"outcome":"complete","authority":true,"diagnosticCount":0}"#,
        ] {
            assert_eq!(parse(value), None);
        }
    }
}
