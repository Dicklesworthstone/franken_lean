//! Pinned LSP semantic-token legend and bounded UTF-16 delta encoding.
use std::fmt::Write;
use std::ops::Range;

/// Indices are the exact order of Lean.Data.Lsp.LanguageFeatures at the pin.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenKind {
    Keyword,
    Variable,
    Property,
    Function,
    SorryLike,
}

impl SemanticTokenKind {
    fn index(self) -> u32 {
        match self {
            Self::Keyword => 0,
            Self::Variable => 1,
            Self::Property => 2,
            Self::Function => 3,
            Self::SorryLike => 23,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticToken {
    pub range: Range<usize>,
    pub kind: SemanticTokenKind,
}

const MAX_TOKENS: usize = 32_768;

pub(super) fn capability() -> &'static str {
    r#"{"legend":{"tokenTypes":["keyword","variable","property","function","namespace","type","class","enum","interface","struct","typeParameter","parameter","enumMember","event","method","macro","modifier","comment","string","number","regexp","operator","decorator","leanSorryLike"],"tokenModifiers":["declaration","definition","readonly","static","deprecated","abstract","async","modification","documentation","defaultLibrary"]},"range":true,"full":true}"#
}

pub(super) fn payload_bytes(tokens: &[SemanticToken]) -> Result<usize, &'static str> {
    if tokens.len() > MAX_TOKENS {
        return Err("semantic tokens exceed their count budget");
    }
    Ok(std::mem::size_of_val(tokens))
}

/// Scan monotonically across the source rather than rescanning every token's
/// prefix. Both memory and coordinate-conversion work are linear and bounded.
struct Cursor<'a> {
    text: &'a str,
    offset: usize,
    line: u32,
    character: u32,
}

impl Cursor<'_> {
    fn advance(&mut self, target: usize) -> Result<(u32, u32), &'static str> {
        if target < self.offset || !self.text.is_char_boundary(target) {
            return Err("semantic token range is outside the accepted source");
        }
        if target > 0
            && self.text.as_bytes().get(target - 1) == Some(&b'\r')
            && self.text.as_bytes().get(target) == Some(&b'\n')
        {
            return Err("semantic token range splits CRLF");
        }
        let mut chars = self.text[self.offset..target].chars().peekable();
        while let Some(character) = chars.next() {
            if matches!(character, '\r' | '\n') {
                if character == '\r' && chars.peek() == Some(&'\n') {
                    chars.next();
                }
                self.line = self
                    .line
                    .checked_add(1)
                    .ok_or("semantic token line overflow")?;
                self.character = 0;
            } else {
                self.character = self
                    .character
                    .checked_add(character.len_utf16() as u32)
                    .ok_or("semantic token column overflow")?;
            }
        }
        self.offset = target;
        Ok((self.line, self.character))
    }
}

pub(super) fn result(
    tokens: &[SemanticToken],
    text: &str,
    requested: Option<Range<usize>>,
) -> Result<String, &'static str> {
    payload_bytes(tokens)?;
    if text.len() > super::MAX_RESULT_BYTES {
        return Err("semantic token source exceeds its byte budget");
    }
    let mut cursor = Cursor {
        text,
        offset: 0,
        line: 0,
        character: 0,
    };
    let mut result = String::from("{\"data\":[");
    let mut last = (0, 0);
    let mut emitted = false;
    for token in tokens {
        if token.range.start >= token.range.end {
            return Err("semantic token range is empty or reversed");
        }
        let start = cursor.advance(token.range.start)?;
        let end = cursor.advance(token.range.end)?;
        if start.0 != end.0 {
            return Err("semantic token crosses a line boundary");
        }
        // The pin selects by token start. A token beginning before the request
        // is omitted; one beginning inside it retains its complete source span.
        if requested
            .as_ref()
            .is_some_and(|range| !range.contains(&token.range.start))
        {
            continue;
        }
        let delta_line = start.0 - last.0;
        let delta_start = if delta_line == 0 {
            start.1 - last.1
        } else {
            start.1
        };
        if emitted {
            result.push(',');
        }
        write!(
            &mut result,
            "{delta_line},{delta_start},{},{},0",
            end.1 - start.1,
            token.kind.index()
        )
        .map_err(|_| "semantic token rendering failed")?;
        if result.len() + 2 > super::MAX_RESULT_BYTES {
            return Err("semantic token response exceeds its wire budget");
        }
        last = start;
        emitted = true;
    }
    result.push_str("]}");
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn full_and_range_use_utf16_deltas_and_pin_start_selection() {
        let source = "😀 def x\r\n  x.field";
        let tokens = vec![
            SemanticToken {
                range: 5..8,
                kind: SemanticTokenKind::Keyword,
            },
            SemanticToken {
                range: 16..21,
                kind: SemanticTokenKind::Property,
            },
        ];
        assert_eq!(
            result(&tokens, source, None).unwrap(),
            "{\"data\":[0,3,3,0,0,1,4,5,2,0]}"
        );
        assert_eq!(
            result(&tokens, source, Some(6..17)).unwrap(),
            "{\"data\":[1,4,5,2,0]}"
        );
        assert_eq!(
            result(&tokens, source, Some(8..16)).unwrap(),
            "{\"data\":[]}"
        );
    }

    #[test]
    fn malformed_late_tokens_never_publish_a_partial_result() {
        let source = "def x\r\nby";
        let first = SemanticToken {
            range: 0..3,
            kind: SemanticTokenKind::Keyword,
        };
        for range in [
            1..2,
            5..6,
            6..7,
            7..10,
            7..7,
            std::ops::Range { start: 8, end: 7 },
        ] {
            assert!(
                result(
                    &[
                        first.clone(),
                        SemanticToken {
                            range,
                            kind: SemanticTokenKind::Keyword
                        }
                    ],
                    source,
                    None
                )
                .is_err()
            );
        }
        assert!(
            result(
                &[SemanticToken {
                    range: 0..1,
                    kind: SemanticTokenKind::Keyword
                }],
                "😀",
                None
            )
            .is_err()
        );
        assert!(result(&vec![first; MAX_TOKENS + 1], source, None).is_err());
    }
}
