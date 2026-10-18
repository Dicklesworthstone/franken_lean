//! Native diagnostic presentations for Lean.Widget.getInteractiveDiagnostics.
//! The pin uses DiagnosticWith (TaggedText MsgEmbed). Plain text is a valid
//! TaggedText; it must not be advertised as a retained proof or widget reference.
use super::*;
use crate::dispatch::{CallbackMessageClass, DiagnosticCompletion, classify_callback_message};
use std::collections::BTreeSet;

const MAX_CALLBACK_BYTES: usize = 4 * 1024 * 1024;
const MAX_DIAGNOSTICS: usize = 4096;
const MAX_FIELDS: usize = 64;
type Refusal = &'static str;
pub(in crate::dispatch) type LineRange = (u64, u64);

#[derive(Debug)]
struct Diagnostic {
    wire: String,
    start_line: u64,
    end_line: u64,
}

#[derive(Debug, Default)]
pub(in crate::dispatch) struct Batch {
    diagnostics: Vec<Diagnostic>,
}

fn natural(raw: RawField<'_>) -> Result<u64, Refusal> {
    let RawField::Value(value) = raw else {
        return Err("diagnostic line range requires unambiguous natural numbers");
    };
    if value.is_empty()
        || value.len() > 20
        || !value.bytes().all(|byte| byte.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err("diagnostic line range requires unambiguous natural numbers");
    }
    value.parse().map_err(|_| "diagnostic line range exceeds UInt64")
}

pub(in crate::dispatch) fn line_range(value: RawField<'_>) -> Result<Option<LineRange>, Refusal> {
    let raw = object(value)?;
    match object_field(raw, "lineRange") {
        RawField::Missing | RawField::Value("null") => Ok(None),
        RawField::Value(range) => Ok(Some((
            natural(object_field(range, "start"))?,
            natural(object_field(range, "end"))?,
        ))),
        RawField::Invalid => Err("diagnostic line range is malformed or duplicated"),
    }
}

/// Decode all keys once and refuse duplicates even when their spelling differs
/// through JSON escapes. Unknown diagnostic fields are preserved, not interpreted.
fn members(value: &str) -> Result<Vec<(String, &str)>, Refusal> {
    let bytes = value.as_bytes();
    let start = skip_ws(bytes, 0);
    let end = parse_value_end(value, start, 0).ok_or("malformed diagnostic object")?;
    if bytes.get(start) != Some(&b'{') || skip_ws(bytes, end) != bytes.len() {
        return Err("diagnostic must be an object");
    }
    let mut cursor = skip_ws(bytes, start + 1);
    let mut result = Vec::new();
    let mut seen = BTreeSet::new();
    if bytes.get(cursor) == Some(&b'}') {
        return Ok(result);
    }
    loop {
        if result.len() >= MAX_FIELDS {
            return Err("diagnostic has too many fields");
        }
        let key_end = scan_string_end(bytes, cursor).ok_or("malformed diagnostic key")?;
        let key = decode_json_string_value(&value[cursor..key_end])
            .ok_or("invalid diagnostic key")?;
        if !seen.insert(key.clone()) {
            return Err("diagnostic contains duplicate decoded keys");
        }
        cursor = skip_ws(bytes, key_end);
        if bytes.get(cursor) != Some(&b':') {
            return Err("malformed diagnostic object");
        }
        cursor = skip_ws(bytes, cursor + 1);
        let end = parse_value_end(value, cursor, 0).ok_or("malformed diagnostic field")?;
        result.push((key, &value[cursor..end]));
        cursor = skip_ws(bytes, end);
        match bytes.get(cursor) {
            Some(b'}') => return Ok(result),
            Some(b',') => cursor = skip_ws(bytes, cursor + 1),
            _ => return Err("malformed diagnostic object"),
        }
    }
}

fn range(value: &str) -> Result<(Position, Position), Refusal> {
    let start = super::super::edits::position(object_field(value, "start"))?;
    let end = super::super::edits::position(object_field(value, "end"))?;
    if start > end {
        return Err("diagnostic has a reversed range");
    }
    Ok((start, end))
}

impl Diagnostic {
    fn decode(value: &str) -> Result<Self, Refusal> {
        let fields = members(value)?;
        let get = |key: &str| {
            fields.iter().find(|(name, _)| name == key).map(|(_, value)| *value)
        };
        let ordinary_range = range(get("range").ok_or("diagnostic has no range")?)?;
        let full_range = match get("fullRange") {
            None | Some("null") => ordinary_range,
            Some(value) => range(value)?,
        };
        let message = get("message").ok_or("diagnostic has no message")?;
        if decode_json_string_value(message).is_none() {
            return Err("native diagnostic message is not a valid string");
        }
        if let Some(severity) = get("severity").filter(|value| *value != "null") {
            if !matches!(natural(RawField::Value(severity)), Ok(1..=4)) {
                return Err("diagnostic severity is invalid");
            }
        }
        let mut wire = String::from("{");
        for (index, (key, value)) in fields.iter().enumerate() {
            if index != 0 {
                wire.push(',');
            }
            wire.push_str(&crate::json_string(key));
            wire.push(':');
            if key == "message" {
                wire.push_str("{\"text\":");
                wire.push_str(value);
                wire.push('}');
            } else {
                wire.push_str(value);
            }
        }
        wire.push('}');
        // FileWorker.handleGetInteractiveDiagnosticsRequest uses fullRange,
        // excludes a following line reached only at column zero, and includes
        // a zero-width diagnostic when its start line is in the requested range.
        let start_line = u64::from(full_range.0.line);
        let end_line = u64::from(full_range.1.line)
            + u64::from(full_range.1.character != 0);
        Ok(Self { wire, start_line, end_line })
    }

    fn selected(&self, range: Option<LineRange>) -> bool {
        range.is_none_or(|(start, end)| {
            (start <= self.start_line && self.start_line < end)
                || (self.start_line <= start && start < self.end_line)
        })
    }
}

impl Batch {
    /// Observe the same terminal classes as normal publication. A callback
    /// failure, contradictory terminals, or stale version is not an empty list.
    pub(in crate::dispatch) fn from_notifications(
        notifications: &[String],
        uri: &str,
        version: i64,
    ) -> Result<Self, Refusal> {
        if notifications.len() > MAX_DIAGNOSTICS {
            return Err("diagnostic callback exceeds its message limit");
        }
        let total = notifications.iter().try_fold(0usize, |bytes, notification| {
            bytes.checked_add(notification.len())
        });
        if total.is_none_or(|bytes| bytes > MAX_CALLBACK_BYTES) {
            return Err("diagnostic callback exceeds its byte budget");
        }
        let mut diagnostics = None;
        let mut outcome = None;
        for notification in notifications {
            match classify_callback_message(notification, uri) {
                CallbackMessageClass::Invalid => return Err("invalid diagnostic callback output"),
                CallbackMessageClass::Auxiliary => {}
                CallbackMessageClass::DiagnosticOutcome(completion) => {
                    if outcome.replace(completion).is_some() {
                        return Err("duplicate diagnostic completion outcomes");
                    }
                }
                CallbackMessageClass::CurrentDiagnostics => {
                    let envelope = parse_envelope(notification)
                        .map_err(|_| "invalid diagnostic notification")?;
                    match direct_version(envelope.params) {
                        VersionField::Missing => {}
                        VersionField::Valid(current) if current == version => {}
                        _ => return Err("diagnostics do not belong to the current document version"),
                    }
                    let raw = object(envelope.params)?;
                    let RawField::Value(array) = object_field(raw, "diagnostics") else {
                        return Err("diagnostic notification requires one diagnostics array");
                    };
                    if diagnostics.replace(Self::decode_array(array)?).is_some() {
                        return Err("duplicate current-document diagnostic notifications");
                    }
                }
            }
        }
        if outcome == Some(DiagnosticCompletion::Failed) {
            return Err("diagnostic processing reached a non-authoritative terminal outcome");
        }
        match (diagnostics, outcome) {
            (Some(batch), Some(DiagnosticCompletion::Complete))
                if !batch.diagnostics.is_empty() =>
            {
                Err("zero-diagnostic outcome contradicts the diagnostic payload")
            }
            (Some(batch), _) => Ok(batch),
            (None, Some(DiagnosticCompletion::Complete)) => Ok(Self::default()),
            _ => Err("current diagnostic processing has no authoritative result"),
        }
    }

    fn decode_array(array: &str) -> Result<Self, Refusal> {
        let bytes = array.as_bytes();
        let start = skip_ws(bytes, 0);
        let end = parse_value_end(array, start, 0).ok_or("malformed diagnostics array")?;
        if bytes.get(start) != Some(&b'[') || skip_ws(bytes, end) != bytes.len() {
            return Err("diagnostics must be an array");
        }
        let mut cursor = skip_ws(bytes, start + 1);
        let mut batch = Self::default();
        if bytes.get(cursor) == Some(&b']') {
            return Ok(batch);
        }
        loop {
            if batch.diagnostics.len() >= MAX_DIAGNOSTICS {
                return Err("diagnostic count exceeds its limit");
            }
            let end = parse_value_end(array, cursor, 0).ok_or("malformed diagnostic")?;
            batch.diagnostics.push(Diagnostic::decode(&array[cursor..end])?);
            cursor = skip_ws(bytes, end);
            match bytes.get(cursor) {
                Some(b']') => return Ok(batch),
                Some(b',') => cursor = skip_ws(bytes, cursor + 1),
                _ => return Err("malformed diagnostics array"),
            }
        }
    }

    pub(in crate::dispatch) fn retained_bytes(&self) -> Option<usize> {
        let storage = self.diagnostics.capacity().checked_mul(std::mem::size_of::<Diagnostic>())?;
        self.diagnostics.iter().try_fold(storage, |bytes, diagnostic| {
            bytes.checked_add(diagnostic.wire.capacity())
        })
    }

    pub(in crate::dispatch) fn response(
        &self,
        range: Option<LineRange>,
        max_bytes: usize,
    ) -> Result<String, Refusal> {
        if max_bytes < 2 {
            return Err("diagnostic response exceeds its wire budget");
        }
        let mut result = String::from("[");
        let mut first = true;
        for diagnostic in self.diagnostics.iter().filter(|diagnostic| diagnostic.selected(range)) {
            let separator = usize::from(!first);
            let size = result.len().checked_add(separator)
                .and_then(|size| size.checked_add(diagnostic.wire.len()))
                .and_then(|size| size.checked_add(1))
                .ok_or("diagnostic response accounting overflow")?;
            if size > max_bytes {
                return Err("diagnostic response exceeds its wire budget");
            }
            if !first {
                result.push(',');
            }
            first = false;
            result.push_str(&diagnostic.wire);
        }
        result.push(']');
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const URI: &str = "file:///Diagnostics.lean";
    fn diagnostic(start: u32, end: u32, column: u32, message: &str) -> String {
        format!(
            r#"{{"range":{{"start":{{"line":{start},"character":0}},"end":{{"line":{end},"character":{column}}}}},"message":{},"severity":1,"code":"lean.error","leanTags":[1]}}"#,
            crate::json_string(message)
        )
    }
    fn notification(diagnostics: &str, version: &str) -> String {
        format!(
            r#"{{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{{"uri":"{URI}"{version},"diagnostics":{diagnostics}}}}}"#
        )
    }
    fn batch(rows: &[String]) -> Batch {
        Batch::from_notifications(&[notification(&format!("[{}]", rows.join(",")), "")], URI, 1)
            .unwrap()
    }
    #[test]
    fn optional_line_ranges_use_decoded_unambiguous_natural_numbers() {
        assert_eq!(line_range(RawField::Value("{}")), Ok(None));
        assert_eq!(line_range(RawField::Value(r#"{"lineRange":null}"#)), Ok(None));
        assert_eq!(line_range(RawField::Value(r#"{"lineRange":{"start":2,"end":5}}"#)), Ok(Some((2, 5))));
        for value in [
            r#"{"lineRange":[],"line\u0052ange":null}"#,
            r#"{"lineRange":{"start":0,"start":1,"end":2}}"#,
            r#"{"lineRange":{"start":-1,"end":2}}"#,
            r#"{"lineRange":{"start":"0","end":2}}"#,
            r#"{"lineRange":{"start":0.0,"end":2}}"#,
            r#"{"lineRange":{"start":0,"end":18446744073709551616}}"#,
        ] {
            assert!(line_range(RawField::Value(value)).is_err(), "{value}");
        }
    }
    #[test]
    fn messages_are_tagged_text_and_existing_diagnostic_fields_survive() {
        let result = batch(&[diagnostic(0, 0, 2, "β \"quoted\"\nnext")]).response(None, 4096).unwrap();
        assert!(result.contains(r#""message":{"text":"β \"quoted\"\nnext"}"#), "{result}");
        assert!(result.contains(r#""code":"lean.error","leanTags":[1]"#));
        assert!(!result.contains("__rpcref"));
    }
    #[test]
    fn full_range_and_exclusive_end_line_match_the_pin() {
        let ordinary = diagnostic(2, 4, 0, "multiline");
        let extended = ordinary.replacen("{", r#"{"fullRange":{"start":{"line":1,"character":0},"end":{"line":6,"character":0}},"#, 1);
        let data = batch(&[ordinary, extended]);
        assert!(data.response(Some((1, 2)), 4096).unwrap().contains("multiline"));
        assert_eq!(data.response(Some((4, 5)), 4096).unwrap().matches("multiline").count(), 1);
        assert_eq!(data.response(Some((6, 7)), 4096).unwrap(), "[]");
        assert!(batch(&[diagnostic(4, 4, 0, "point")]).response(Some((4, 5)), 4096).unwrap().contains("point"));
        assert!(batch(&[diagnostic(2, 4, 1, "column")]).response(Some((4, 5)), 4096).unwrap().contains("column"));
    }
    #[test]
    fn stale_or_duplicate_notifications_never_become_current_results() {
        let valid = notification("[]", ",\"version\":1");
        assert!(Batch::from_notifications(&[valid.clone()], URI, 1).is_ok());
        assert!(Batch::from_notifications(&[valid.clone()], URI, 2).is_err());
        assert!(Batch::from_notifications(&[valid.clone(), valid], URI, 1).is_err());
        assert!(Batch::from_notifications(&[notification("[]", ",\"version\":1,\"version\":1")], URI, 1).is_err());
    }
    #[test]
    fn failed_missing_and_contradictory_terminals_are_not_empty_diagnostics() {
        use crate::dispatch::wire::{clear_diagnostics_notification, diagnostic_callback_failure_notification};
        let clear = clear_diagnostics_notification(URI);
        let failed = diagnostic_callback_failure_notification(URI);
        assert!(Batch::from_notifications(&[clear.clone()], URI, 1).is_ok());
        assert!(Batch::from_notifications(&[clear, failed], URI, 1).is_err());
        assert!(Batch::from_notifications(&[], URI, 1).is_err());
        assert!(Batch::from_notifications(&[clear_diagnostics_notification("other")], URI, 1).is_err());
        let complete = r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0}}"#.to_owned();
        assert_eq!(Batch::from_notifications(&[complete.clone()], URI, 1).unwrap().response(None, 2).unwrap(), "[]");
        let message = notification(&format!("[{}]", diagnostic(0, 0, 1, "error")), "");
        assert!(Batch::from_notifications(&[message, complete], URI, 1).is_err());
    }
    #[test]
    fn excluded_diagnostics_are_still_validated_and_output_limits_do_not_truncate() {
        let valid = diagnostic(0, 0, 1, "valid");
        let duplicate = valid.replacen(r#""message":"valid""#, r#""message":"valid","mess\u0061ge":"other""#, 1);
        for invalid in [duplicate, valid.replace(r#""severity":1"#, r#""severity":9"#), valid.replace(r#""message":"valid""#, r#""message":{}"#)] {
            assert!(Batch::from_notifications(&[notification(&format!("[{invalid}]"), "")], URI, 1).is_err());
        }
        let data = batch(&[valid]);
        assert!(data.response(None, 2).is_err());
        assert_eq!(data.response(Some((10, 11)), 2).unwrap(), "[]");
        assert!(data.response(Some((10, 11)), 1).is_err());
    }
}
