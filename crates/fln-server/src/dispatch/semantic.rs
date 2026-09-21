//! Typed, read-only editor queries over the dispatcher's accepted source snapshot.
//! Providers cannot supply raw JSON, replace source, or publish diagnostics here.
use super::*;
use std::ops::Range;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryKind {
    Goals,
    Hover,
}

#[derive(Debug, Clone, Copy)]
pub struct Query<'a> {
    pub kind: QueryKind,
    pub uri: &'a str,
    pub version: i64,
    pub text: &'a str,
    /// Original UTF-8 source bytes, converted from the client's UTF-16 position.
    pub offset: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Answer {
    /// Provisional tactic obligations, not evidence of declaration admission.
    Goals { goals: Vec<String> },
    Hover {
        contents: String,
        range: Range<usize>,
    },
}

const MAX_RESULT_BYTES: usize = 1024 * 1024;
const MAX_GOALS: usize = 256;

pub(super) fn initialize_response(id: &RequestId) -> String {
    // Both constructors share the ordinary lifecycle/synchronization contract.
    let response = wire::initialize_response(id);
    response.replacen(
        "\"capabilities\":{",
        "\"capabilities\":{\"hoverProvider\":true,",
        1,
    )
}

/// Convert a verified UTF-8 byte boundary to an LSP position. CRLF is one newline.
fn position(text: &str, offset: usize) -> Result<json::Position, &'static str> {
    if offset > text.len() || !text.is_char_boundary(offset) {
        return Err("semantic range is outside the accepted source");
    }
    let mut line = 0u32;
    let mut character = 0u32;
    let mut chars = text[..offset].chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\r' || c == '\n' {
            if c == '\r' && chars.peek() == Some(&'\n') {
                chars.next();
            }
            line = line.checked_add(1).ok_or("semantic line overflow")?;
            character = 0;
        } else {
            character = character
                .checked_add(c.len_utf16() as u32)
                .ok_or("semantic column overflow")?;
        }
    }
    Ok(json::Position { line, character })
}

fn result_json(answer: Answer, query: Query<'_>) -> Result<String, &'static str> {
    let result = match (query.kind, answer) {
        (QueryKind::Goals, Answer::Goals { goals }) => {
            let size = goals
                .iter()
                .try_fold(0usize, |size, goal| size.checked_add(goal.len()));
            if goals.len() > MAX_GOALS || size.is_none_or(|size| size > MAX_RESULT_BYTES / 16) {
                return Err("semantic goal response exceeds its output budget");
            }
            let rendered = if goals.is_empty() {
                "no goals".to_owned()
            } else {
                goals.join("\n\n")
            };
            let items = goals
                .iter()
                .map(|goal| crate::json_string(goal))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                "{{\"rendered\":{},\"goals\":[{}]}}",
                crate::json_string(&rendered),
                items
            )
        }
        (QueryKind::Hover, Answer::Hover { contents, range }) => {
            if contents.len() > MAX_RESULT_BYTES / 8 || range.start > range.end {
                return Err("semantic hover response exceeds its bounds");
            }
            let start = position(query.text, range.start)?;
            let end = position(query.text, range.end)?;
            format!(
                "{{\"contents\":{{\"kind\":\"plaintext\",\"value\":{}}},\"range\":{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}}}",
                crate::json_string(&contents),
                start.line,
                start.character,
                end.line,
                end.character
            )
        }
        _ => return Err("semantic provider returned a different query kind"),
    };
    if result.len() > MAX_RESULT_BYTES {
        return Err("semantic response exceeds its wire budget");
    }
    Ok(result)
}

pub(super) fn handle(
    output: &mut dyn Write,
    session: &DocumentSession,
    checker: &mut dyn CheckSource,
    id: &RequestId,
    method: &str,
    params: RawField<'_>,
) -> io::Result<()> {
    // Legacy embedders retain the old no-information behavior.
    if !checker.semantic_queries() {
        return write_protocol_message(output, null_response(id));
    }
    let kind = if method == "$/lean/plainGoal" {
        QueryKind::Goals
    } else {
        QueryKind::Hover
    };
    let parsed = (|| {
        let DecodedField::Valid(uri) = text_document_uri(params) else {
            return Err("semantic query requires one document URI");
        };
        if uri.is_empty() {
            return Err("semantic query URI is empty");
        }
        Ok((uri, json::query_position(params)?))
    })();
    let (uri, at) = match parsed {
        Ok(parsed) => parsed,
        Err(error) => return write_protocol_message(output, error_response(id, -32602, error)),
    };
    let sources = session.sources();
    let Some(document) = sources.iter().find(|d| d.uri == uri) else {
        return write_protocol_message(output, null_response(id));
    };
    let Some(text) = document.text else {
        return write_protocol_message(
            output,
            error_response(
                id,
                REQUEST_FAILED_CODE,
                "accepted editor source is unavailable",
            ),
        );
    };
    let offset = match json::byte_offset(text, at) {
        Ok(offset) => offset,
        Err(error) => return write_protocol_message(output, error_response(id, -32602, error)),
    };
    let query = Query {
        kind,
        uri: &uri,
        version: document.version,
        text,
        offset,
    };
    let response = match checker.query(query, &sources) {
        Ok(None) => null_response(id),
        Ok(Some(answer)) => match result_json(answer, query) {
            Ok(result) => format!(
                "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{result}}}",
                id.as_json()
            ),
            Err(error) => error_response(id, REQUEST_FAILED_CODE, error),
        },
        Err(error) => {
            // A provider's unbounded error cannot become an unbounded wire write.
            let message = if error.len() <= 16 * 1024 {
                &error
            } else {
                "semantic query failed (provider detail exceeded its limit)"
            };
            error_response(id, REQUEST_FAILED_CODE, message)
        }
    };
    write_protocol_message(output, response)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ranges_share_utf16_crlf_and_unicode_boundary_rules() {
        let text = "α😀\r\nx";
        let p = position(text, "α😀".len()).unwrap();
        assert_eq!((p.line, p.character), (0, 3));
        let p = position(text, text.len() - 1).unwrap();
        assert_eq!((p.line, p.character), (1, 0));
        assert_eq!(json::byte_offset(text, p).unwrap(), text.len() - 1);
        assert!(position(text, 1).is_err());
        assert!(
            json::byte_offset(
                text,
                json::Position {
                    line: 0,
                    character: 2
                }
            )
            .is_err()
        );
    }
    #[test]
    fn output_is_typed_bounded_and_json_escaped() {
        let q = Query {
            kind: QueryKind::Goals,
            uri: "x",
            version: 1,
            text: "x",
            offset: 0,
        };
        let json = result_json(
            Answer::Goals {
                goals: vec!["h : \"P\"\n⊢ P".to_owned()],
            },
            q,
        )
        .unwrap();
        assert!(json.contains("\\\"P\\\"\\n"));
        assert!(
            result_json(
                Answer::Hover {
                    contents: "x".to_owned(),
                    range: 0..1
                },
                q
            )
            .is_err()
        );
        assert!(
            result_json(
                Answer::Goals {
                    goals: vec!["x".repeat(MAX_RESULT_BYTES)]
                },
                q
            )
            .is_err()
        );
        let q = Query {
            kind: QueryKind::Hover,
            ..q
        };
        assert!(
            result_json(
                Answer::Hover {
                    contents: "x".to_owned(),
                    range: 0..2
                },
                q
            )
            .is_err()
        );
    }
}
