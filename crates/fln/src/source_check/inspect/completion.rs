//! Global-name completion over the ordinary dual-checked command prefix.
//!
//! The token under the cursor is only a filter. It is never elaborated, installed
//! in an environment, or used to look up a previous successful result. Every
//! replacement is root-qualified, so a local with the same spelling cannot turn
//! a suggested global into another term. Local/field/tactic completion is outside
//! this query's profile.
use super::*;
use fln_core::name::LeafView;
use fln_syntax::source::{BytePos, SourceText};
use fln_syntax::token::{TokenError, TokenKind, TokenTable, is_id_first, is_id_rest, lex_token};
use fln_syntax::trivia::{opens_doc_comment, scan_trivia};
use fln_syntax::view::SourceView;
use std::collections::BTreeMap;
use std::ops::Range;

#[derive(Debug, Clone, Copy)]
pub struct CompletionLookupLimits {
    pub max_source_bytes: usize,
    pub max_modules: usize,
    pub max_commands: usize,
    pub max_tokens: usize,
    pub max_candidates: usize,
    pub max_name_bytes: usize,
    pub max_items: usize,
    pub max_result_bytes: usize,
}
impl Default for CompletionLookupLimits {
    fn default() -> Self {
        Self {
            max_source_bytes: 1024 * 1024,
            max_modules: 256,
            max_commands: 4096,
            max_tokens: 100_000,
            max_candidates: 100_000,
            max_name_bytes: 4096,
            max_items: 256,
            max_result_bytes: 64 * 1024,
        }
    }
}

/// A checked global, not a candidate declaration or an admission certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompletionItem {
    pub label: String,
    pub replacement: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceCompletion {
    /// Replace the whole identifier, including any suffix after the cursor.
    /// These are original UTF-8 byte offsets, never parser-view coordinates.
    pub range: Range<usize>,
    pub items: Vec<SourceCompletionItem>,
    /// More matching names existed than fit the item or output-byte limits.
    pub is_incomplete: bool,
}

impl SourceModuleSession {
    pub fn complete(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        offset: usize,
    ) -> Result<Outcome<Option<SourceCompletion>>, SourceModuleCheckError> {
        self.complete_with_limits(inputs, entry, offset, CompletionLookupLimits::default())
    }

    /// No completion result survives an unsuccessful check of the exact prefix.
    /// The session's checking/retention budgets remain in force independently of
    /// these query limits. No upstream process, VM, or user program is executed.
    pub fn complete_with_limits(
        &mut self,
        inputs: &[SourceModuleInput<'_>],
        entry: &Name,
        offset: usize,
        limits: CompletionLookupLimits,
    ) -> Result<Outcome<Option<SourceCompletion>>, SourceModuleCheckError> {
        if inputs.len() > limits.max_modules {
            return Err(limit("completion modules", limits.max_modules));
        }
        let mut bytes = 0usize;
        for input in inputs {
            bytes = bytes
                .checked_add(input.source.len())
                .filter(|n| *n <= limits.max_source_bytes)
                .ok_or_else(|| limit("completion source bytes", limits.max_source_bytes))?;
        }
        let index = inputs
            .iter()
            .position(|input| input.name == entry)
            .ok_or_else(|| SourceModuleCheckError::MissingModule {
                importer: entry.clone(),
                module: entry.clone(),
            })?;
        let source = inputs[index].source;
        let text = std::str::from_utf8(source)
            .map_err(|_| invalid(entry, offset, "completion source is not UTF-8"))?;
        if offset > text.len() || !text.is_char_boundary(offset) {
            return Err(invalid(
                entry,
                offset,
                "completion position is not a source byte boundary",
            ));
        }
        if offset > 0
            && source.get(offset - 1) == Some(&b'\r')
            && source.get(offset) == Some(&b'\n')
        {
            return Err(invalid(entry, offset, "completion position bisects CRLF"));
        }
        // Lex only as far as the selected token. Later malformed source must
        // not disable a query in an earlier command. Doing this first also
        // avoids treating a cursor inside an unfinished comment as an import
        // or command-partition failure.
        let Some((range, filter)) = completion_token(source, offset, limits)? else {
            return Ok(Outcome::Complete(None));
        };
        let header = modules::parse_source_header(&source[..range.start]).map_err(|error| {
            SourceModuleCheckError::Header {
                module: entry.clone(),
                error,
            }
        })?;
        if range.start < header.body_start.0 {
            return Ok(Outcome::Complete(None));
        }
        // The incomplete identifier need not be valid declaration syntax.
        // Only the already-typed bytes preceding it choose the command prefix;
        // the ordinary checker remains the sole authority over that prefix.
        let commands =
            fln_parse::command_scope::partition(&source[header.body_start.0..range.start])
                .map_err(|error| SourceModuleCheckError::Header {
                    module: entry.clone(),
                    error: error.with_original_offset(header.body_start),
                })?;
        if commands.len() > limits.max_commands {
            return Err(limit("completion commands", limits.max_commands));
        }
        let Some((start, _)) = commands.last() else {
            return Ok(Outcome::Complete(None));
        };
        let prefix_end = header.body_start.0 + start.0;
        if text.get(range.clone()).is_none() {
            return Err(invalid(
                entry,
                offset,
                "completion range is outside the accepted source",
            ));
        }
        let mut prefix_inputs = inputs.to_vec();
        prefix_inputs[index].source = &source[..prefix_end];
        let checked = match self.check(&prefix_inputs, entry)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // Temporary scope commands wrap one declaration without changing its
        // visibility. Read their headers only: a public body under `open … in`
        // or `set_option … in` must not expose the private completion world.
        let mut command_prefix = &source[prefix_end..range.start];
        let mut wrappers = 0usize;
        loop {
            let Some(body) = fln_parse::command_scope::wrapper_body(command_prefix)
                .map_err(|error| invalid(entry, prefix_end, &error.to_string()))?
            else {
                break;
            };
            wrappers += 1;
            if wrappers > limits.max_commands {
                return Err(limit("completion commands", limits.max_commands));
            }
            command_prefix = &command_prefix[body..];
        }
        let scope = checked
            .checked
            .checked
            .scope
            .for_command_prefix(command_prefix)
            .map_err(|error| invalid(entry, prefix_end, &error.to_string()))?;
        // A public theorem's statement is elaborated against public imports,
        // but its proof may use private implementation details. Read only the
        // actual header boundary so a default binder's `:=`, or `let` inside
        // the result type, cannot expose private names in the statement.
        let public_header = scope.exports_declaration()
            && fln_parse::command_scope::modifiers::theorem_body_start(command_prefix)
                .map_err(|error| invalid(entry, prefix_end, &error.to_string()))?
                .is_none();
        let environment = if public_header {
            checked.checked.public_environment.as_ref().ok_or_else(|| {
                invalid(
                    entry,
                    prefix_end,
                    "checked public completion prefix is unavailable",
                )
            })?
        } else {
            checked.checked.checked.engine.environment()
        };
        let absolute_filter = filter.strip_prefix("_root_.");
        let matching = absolute_filter.unwrap_or(&filter);
        let mut names = BTreeMap::new();
        let mut incomplete = false;
        for (index, (name, _)) in environment.constants().enumerate() {
            if index >= limits.max_candidates {
                // Do not expose an arbitrary prefix of an implementation-defined
                // map walk as a complete, schedule-independent answer.
                return Err(limit("completion candidates", limits.max_candidates));
            }
            let Some((label, leaf)) = source_name(name, limits.max_name_bytes, Some(&scope))
                .map_err(|()| limit("completion name bytes", limits.max_name_bytes))?
            else {
                continue;
            };
            if !label.starts_with(matching)
                && !(absolute_filter.is_none() && leaf.starts_with(matching))
            {
                continue;
            }
            let replacement = format!("_root_.{label}");
            names.insert(label.clone(), SourceCompletionItem { label, replacement });
            if names.len() > limits.max_items {
                let _ = names.pop_last();
                incomplete = true;
            }
        }
        let mut result_bytes = 0usize;
        let mut items = Vec::new();
        for item in names.into_values() {
            let size = item
                .label
                .len()
                .checked_add(item.replacement.len())
                .and_then(|size| result_bytes.checked_add(size));
            let Some(size) = size.filter(|size| *size <= limits.max_result_bytes) else {
                incomplete = true;
                break;
            };
            result_bytes = size;
            items.push(item);
        }
        Ok(Outcome::Complete(Some(SourceCompletion {
            range,
            items,
            is_incomplete: incomplete,
        })))
    }
}

fn limit(resource: &'static str, limit: usize) -> SourceModuleCheckError {
    SourceModuleCheckError::Limit { resource, limit }
}
fn invalid(module: &Name, offset: usize, message: &str) -> SourceModuleCheckError {
    SourceModuleCheckError::Source {
        module: module.clone(),
        error: SourceCheckError::Scope {
            file: 0,
            command: 0,
            offset,
            message: message.to_owned(),
        },
    }
}

/// Only ordinary source identifiers are emitted in this first profile. In
/// particular, a numeric/internal component or an escaped dot is never flattened
/// into another global's spelling. Bounds precede component copies.
fn source_name(
    name: &Name,
    max_bytes: usize,
    scope: Option<&fln_elab::source::scope::SourceScope>,
) -> Result<Option<(String, String)>, ()> {
    let mut current = name.clone();
    let mut parts = Vec::new();
    let mut bytes = 0usize;
    while !current.is_anonymous() {
        if parts.len() >= 256 {
            return Ok(None);
        }
        let LeafView::Str(part) = current.leaf_view() else {
            // The exact own-module private prefix may be omitted, after the
            // same component/byte bounds as ordinary names. Calling user_name
            // on this numeric prefix avoids copying an unbounded suffix first.
            if scope.is_some_and(|scope| scope.user_name(&current).is_anonymous()) {
                break;
            }
            return Ok(None);
        };
        bytes = bytes
            .checked_add(part.len())
            .and_then(|n| n.checked_add(usize::from(!parts.is_empty())))
            .filter(|n| *n <= max_bytes)
            .ok_or(())?;
        let mut chars = part.chars();
        if !chars.next().is_some_and(is_id_first) || !chars.all(is_id_rest) {
            return Ok(None);
        }
        parts.push(part.to_owned());
        current = current.parent();
    }
    let Some(leaf) = parts.first().cloned() else {
        return Ok(None);
    };
    parts.reverse();
    Ok(Some((parts.join("."), leaf)))
}

/// A lexical observation, never a repaired program. The ordinary token/trivia
/// primitives handle identifiers, literals, and nested ordinary comments. Doc
/// comment bodies need a separate skip because the reference treats their
/// openers as parser tokens, not whitespace.
fn completion_token(
    source: &[u8],
    offset: usize,
    limits: CompletionLookupLimits,
) -> Result<Option<(Range<usize>, String)>, SourceModuleCheckError> {
    let original = SourceText::from_utf8(source)
        .map_err(|_| limit("completion UTF-8 source", limits.max_source_bytes))?;
    let view = SourceView::of(&original);
    // SourceView maps bytes, whereas an editor cursor denotes a boundary. The
    // valid boundary immediately BEFORE a CRLF maps to the normalized LF; the
    // boundary between CR and LF is not a valid LSP position.
    let bytes = original.as_bytes();
    if offset > 0 && bytes.get(offset - 1) == Some(&b'\r') && bytes.get(offset) == Some(&b'\n') {
        return Ok(None);
    }
    let cursor = view.from_original(BytePos(offset)).or_else(|| {
        (bytes.get(offset) == Some(&b'\r') && bytes.get(offset + 1) == Some(&b'\n'))
            .then(|| view.from_original(BytePos(offset + 1)))
            .flatten()
    });
    let Some(cursor) = cursor else {
        return Ok(None);
    };
    let text = view.normalized();
    let table = TokenTable::new();
    let mut at = BytePos(0);
    let mut tokens = 0usize;
    while at.0 < text.len_bytes() && at.0 <= cursor.0 {
        tokens = tokens
            .checked_add(1)
            .filter(|n| *n <= limits.max_tokens)
            .ok_or_else(|| limit("completion tokens", limits.max_tokens))?;
        let Ok(stop) = scan_trivia(text, at) else {
            return Ok(None);
        };
        if stop.0 > cursor.0 || stop.0 >= text.len_bytes() {
            return Ok(None);
        }
        if opens_doc_comment(text, stop) {
            let Some(end) = doc_comment_end(text.as_bytes(), stop.0) else {
                return Ok(None);
            };
            if cursor.0 < end {
                return Ok(None);
            }
            at = BytePos(end);
            continue;
        }
        match lex_token(text, &table, stop) {
            Ok(token) => {
                let mut end = token.extent.end().0;
                if end <= stop.0 {
                    return Ok(None);
                }
                // The lexer stops before a trailing dot in an unfinished name.
                // Include precisely that dot when the cursor is immediately after it.
                if matches!(&token.kind, TokenKind::Ident(_))
                    && cursor.0 == end + 1
                    && text.as_bytes().get(end) == Some(&b'.')
                {
                    end += 1;
                }
                if stop.0 < cursor.0 && cursor.0 <= end {
                    if !matches!(&token.kind, TokenKind::Ident(_)) {
                        return Ok(None);
                    }
                    let Some(raw) = text.as_str().get(stop.0..cursor.0) else {
                        return Ok(None);
                    };
                    if raw.len() > limits.max_name_bytes {
                        return Err(limit("completion filter bytes", limits.max_name_bytes));
                    }
                    // Incomplete escapes and empty/interior components are not
                    // silently interpreted as ordinary names.
                    if raw.strip_suffix('.').unwrap_or(raw).split('.').any(|part| {
                        let mut chars = part.chars();
                        !chars.next().is_some_and(is_id_first) || !chars.all(is_id_rest)
                    }) {
                        return Ok(None);
                    }
                    let filter = raw.to_owned();
                    return Ok(Some((
                        original_boundary(&view, bytes, stop)
                            ..original_boundary(&view, bytes, BytePos(end)),
                        filter,
                    )));
                }
                at = BytePos(end);
            }
            Err(TokenError::NotAToken { .. }) => {
                // Unknown punctuation is not recovered into authoritative syntax.
                // Advancing a scalar merely lets the lexical query reach a later
                // identifier in the same unfinished command.
                let Some(c) = text.as_str().get(stop.0..).and_then(|s| s.chars().next()) else {
                    return Ok(None);
                };
                at = BytePos(stop.0 + c.len_utf8());
            }
            Err(_) => return Ok(None),
        }
    }
    Ok(None)
}

fn original_boundary(view: &SourceView, original: &[u8], at: BytePos) -> usize {
    let offset = view.to_original(at).0;
    if offset > 0
        && original.get(offset - 1) == Some(&b'\r')
        && original.get(offset) == Some(&b'\n')
    {
        offset - 1
    } else {
        offset
    }
}

fn doc_comment_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut at = start.checked_add(2)?;
    let mut depth = 1usize;
    while at < bytes.len() {
        match (bytes.get(at), bytes.get(at + 1)) {
            (Some(b'/'), Some(b'-')) => {
                depth = depth.checked_add(1)?;
                at += 2;
            }
            (Some(b'-'), Some(b'/')) => {
                depth -= 1;
                at += 2;
                if depth == 0 {
                    return Some(at);
                }
            }
            _ => at += 1,
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn token(source: &str, offset: usize) -> Option<(Range<usize>, String)> {
        completion_token(source.as_bytes(), offset, CompletionLookupLimits::default())
            .expect("bounded lexical query")
    }

    #[test]
    fn partial_and_qualified_names_replace_the_whole_identifier() {
        let source = "def use : Nat := Demo.value";
        let start = source.find("Demo").unwrap();
        assert_eq!(
            token(source, start + 7),
            Some((start..source.len(), "Demo.va".into()))
        );
        let source = "def use : Nat := Demo.";
        let start = source.find("Demo").unwrap();
        assert_eq!(
            token(source, source.len()),
            Some((start..source.len(), "Demo.".into()))
        );
        let source = "def use : Nat := _root_.Demo.va";
        let start = source.find("_root_").unwrap();
        assert_eq!(
            token(source, source.len()),
            Some((start..source.len(), "_root_.Demo.va".into()))
        );
    }

    #[test]
    fn original_unicode_and_crlf_offsets_survive_the_lexical_view() {
        let source = "-- heading\r\ndef use : Nat := αvalue";
        let start = source.find("αvalue").unwrap();
        assert_eq!(
            token(source, start + "αva".len()),
            Some((start..source.len(), "αva".into()))
        );
        let source = "-- heading\r\ndef use : Nat := αvalue\r\n";
        let start = source.find("αvalue").unwrap();
        let end = start + "αvalue".len();
        assert_eq!(token(source, end), Some((start..end, "αvalue".into())));
        assert_eq!(token(source, end + 1), None, "no cursor inside CRLF");
    }

    #[test]
    fn comments_and_literals_never_become_completion_prefixes() {
        for source in [
            "-- value",
            "/- value -/",
            "/-- value -/",
            "/-! value -/",
            "/-- nested /- comment -/ value -/",
            "\"value\"",
            "'v'",
            "/- value",
            "/-- value",
            "\"value",
        ] {
            let offset = source.find('v').unwrap() + 1;
            assert_eq!(token(source, offset), None, "{source}");
        }
        let source = "/-- nested /- comment -/ done -/ def use := value";
        assert!(token(source, source.len()).is_some());
        let source = "def use := \"not a /-- comment\" ++ value";
        assert!(token(source, source.len()).is_some());
    }

    #[test]
    fn malformed_or_escaped_partial_names_are_not_reinterpreted() {
        for source in [
            "def use := Demo..",
            "def use := «a.b»,",
            "def use := «value",
            "def use := 12",
        ] {
            assert_eq!(token(source, source.len()), None, "{source}");
        }
        assert_eq!(
            source_name(&Name::from_components(["a.b"]), 4096, None),
            Ok(None)
        );
        assert_eq!(source_name(&Name::default(), 4096, None), Ok(None));
        assert_eq!(
            source_name(&Name::from_components(["x"]), 1, None),
            Ok(Some(("x".into(), "x".into())))
        );
        assert!(source_name(&Name::from_components(["xx"]), 1, None).is_err());
    }

    #[test]
    fn own_private_aliases_keep_name_limits_and_foreign_names_stay_internal() {
        let scope = fln_elab::source::scope::SourceScope {
            private_module: Some(Name::from_components(["Main"])),
            ..Default::default()
        };
        let private = |module, name: &Name| {
            Name::num(Name::from_components(["_private", module]), 0).append_core(name)
        };
        let name = Name::from_components(["API", "helper"]);
        assert_eq!(
            source_name(&private("Main", &name), 10, Some(&scope)),
            Ok(Some(("API.helper".into(), "helper".into())))
        );
        assert_eq!(
            source_name(&private("Other", &name), 4096, Some(&scope)),
            Ok(None)
        );
        assert!(source_name(&private("Main", &name), 9, Some(&scope)).is_err());
        let deep = Name::from_components(std::iter::repeat_n("x", 257));
        assert_eq!(
            source_name(&private("Main", &deep), 4096, Some(&scope)),
            Ok(None)
        );
    }

    #[test]
    fn lexical_work_and_filter_sizes_are_bounded() {
        let mut limits = CompletionLookupLimits {
            max_tokens: 0,
            ..CompletionLookupLimits::default()
        };
        assert!(matches!(
            completion_token(b"value", 5, limits),
            Err(SourceModuleCheckError::Limit {
                resource: "completion tokens",
                ..
            })
        ));
        limits.max_tokens = 100;
        limits.max_name_bytes = 2;
        assert!(matches!(
            completion_token(b"value", 5, limits),
            Err(SourceModuleCheckError::Limit {
                resource: "completion filter bytes",
                ..
            })
        ));
    }
}
