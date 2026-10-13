//! Native `#guard_msgs` specifications (bead `fln-guard-msgs-lls1`).
//!
//! Mirrors `Lean/Elab/GuardMsgs.lean`: the first filter and first occurrence
//! of an option win. Unmatched severities pass only when a filter is present.
//! Parsing a specification grants no authority to capture unavailable messages.
use super::{tokens, BytePos, DefinitionParseError, NatDefinitionExpectation,
    NatDefinitionParseError, SourceText, SourceView};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action { Check, Drop, Pass }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity { Info, Warning, Error, Trace }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Filter {
    pub action: Action,
    /// `None` is the pin's `all`, including traces.
    pub severity: Option<Severity>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Whitespace { Exact, #[default] Normalized, Lax }

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GuardSpec {
    pub filters: Vec<Filter>,
    pub whitespace: Whitespace,
    pub sorted: bool,
    pub positions: bool,
    pub substring: bool,
}

impl GuardSpec {
    pub fn action(&self, severity: Severity) -> Action {
        self.filters.iter()
            .find(|filter| filter.severity.is_none_or(|selected| selected == severity))
            .map_or_else(
                || if self.filters.is_empty() { Action::Check } else { Action::Pass },
                |filter| filter.action,
            )
    }

    /// Messages already carry their severity and final newline. Sort before
    /// joining, not after normalization; retain duplicate messages.
    pub fn combine(&self, mut messages: Vec<String>) -> String {
        if self.sorted { messages.sort(); }
        messages.join("---\n").trim_ascii().to_owned()
    }

    /// `expected` has already undergone the doc-comment trimming/marker pass.
    pub fn matches(&self, expected: &str, produced: &str) -> bool {
        let expected = self.whitespace.apply(expected);
        let produced = self.whitespace.apply(produced);
        if self.substring { produced.contains(&expected) } else { expected == produced }
    }
}

impl Whitespace {
    pub fn apply(self, text: &str) -> String {
        match self {
            Self::Exact => text.to_owned(),
            Self::Normalized => text.replace('\n', " "),
            // The pin's Char.isWhitespace is NOT Unicode whitespace and does
            // not include vertical tab or form feed (Init/Data/Char/Basic.lean).
            Self::Lax => text.split([' ', '\t', '\r', '\n'])
                .filter(|word| !word.is_empty()).collect::<Vec<_>>().join(" "),
        }
    }
}

/// Read only a wrapper's header, in the same entered grammar as its command.
/// Existing lexer spans preserve comments and CRLF coordinates. Body tokens
/// are not lexed again, so an extension in the guarded command is irrelevant.
pub fn parse(source: &[u8], body: usize) -> Result<GuardSpec, DefinitionParseError> {
    let bad_offset = |at| NatDefinitionParseError::OutsideSeedGrammar {
        at: BytePos(at), expected: NatDefinitionExpectation::EndOfCommand,
    };
    let header = source.get(..body).ok_or_else(|| bad_offset(source.len()))?;
    let original = SourceText::from_utf8(header).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let lexed = tokens(&view)?;
    let mut words = Vec::with_capacity(lexed.len());
    for token in &lexed {
        words.push(view.normalized().as_str()
            .get(token.extent.start().0..token.extent.end().0)
            .ok_or_else(|| bad_offset(view.to_original(token.extent.start()).0))?);
    }
    let mut at = usize::from(words.first().is_some_and(|word| word.starts_with("/--")));
    let result = parse_words(&words, &mut at);
    result.map_err(|index| bad_offset(lexed.get(index)
        .map_or(body, |token| view.to_original(token.extent.start()).0)))
}

fn parse_words(words: &[&str], at: &mut usize) -> Result<GuardSpec, usize> {
    fn take(words: &[&str], at: &mut usize, wanted: &str) -> Result<(), usize> {
        if words.get(*at) != Some(&wanted) { return Err(*at); }
        *at += 1;
        Ok(())
    }
    take(words, at, "#guard_msgs")?;
    let mut spec = GuardSpec::default();
    let mut seen = [false; 4];
    if words.get(*at) == Some(&"(") {
        *at += 1;
        if words.get(*at) != Some(&")") {
            loop {
                let key = *words.get(*at).ok_or(*at)?;
                *at += 1;
                let option = match key {
                    "whitespace" => Some(0), "ordering" => Some(1),
                    "positions" => Some(2), "substring" => Some(3), _ => None,
                };
                if let Some(slot) = option {
                    take(words, at, ":=")?;
                    let value = *words.get(*at).ok_or(*at)?;
                    // Validate duplicates even when the first value wins.
                    match (slot, value) {
                        (0, "exact" | "normalized" | "lax") => {
                            if !seen[slot] {
                                spec.whitespace = match value {
                                    "exact" => Whitespace::Exact,
                                    "lax" => Whitespace::Lax,
                                    _ => Whitespace::Normalized,
                                };
                            }
                        }
                        (1, "exact" | "sorted") => {
                            if !seen[slot] { spec.sorted = value == "sorted"; }
                        }
                        (2 | 3, "true" | "false") => {
                            if !seen[slot] {
                                if slot == 2 { spec.positions = value == "true"; }
                                else { spec.substring = value == "true"; }
                            }
                        }
                        _ => return Err(*at),
                    }
                    seen[slot] = true;
                    *at += 1;
                } else {
                    let action = match key {
                        "check" => Some(Action::Check), "drop" => Some(Action::Drop),
                        "pass" => Some(Action::Pass), _ => None,
                    };
                    let severity = if action.is_some() {
                        let word = *words.get(*at).ok_or(*at)?;
                        *at += 1;
                        word
                    } else { key };
                    let severity = match severity {
                        "all" => None, "info" => Some(Severity::Info),
                        "warning" => Some(Severity::Warning), "error" => Some(Severity::Error),
                        "trace" => Some(Severity::Trace), _ => return Err(*at - 1),
                    };
                    spec.filters.push(Filter { action: action.unwrap_or(Action::Check), severity });
                }
                if words.get(*at) == Some(&")") { break; }
                take(words, at, ",")?;
                // A separator requires another element; no silently skipped tokens.
            }
        }
        take(words, at, ")")?;
    }
    take(words, at, "in")?;
    if *at != words.len() { return Err(*at); }
    Ok(spec)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(words: &[&str]) -> Result<GuardSpec, usize> {
        let mut all = vec!["#guard_msgs", "("];
        all.extend_from_slice(words);
        all.extend_from_slice(&[")", "in"]);
        parse_words(&all, &mut 0)
    }

    #[test]
    fn defaults_and_first_occurrence_are_the_pins() {
        assert_eq!(read(&[]).unwrap(), GuardSpec::default());
        let spec = read(&["whitespace", ":=", "exact", ",", "whitespace", ":=", "lax",
            ",", "ordering", ":=", "sorted", ",", "ordering", ":=", "exact",
            ",", "substring", ":=", "true", ",", "substring", ":=", "false",
            ",", "positions", ":=", "false", ",", "positions", ":=", "true"]).unwrap();
        assert_eq!(spec.whitespace, Whitespace::Exact);
        assert!(spec.sorted && spec.substring && !spec.positions);
        assert_eq!(spec.action(Severity::Warning), Action::Check);
    }

    #[test]
    fn filters_use_first_match_and_unmatched_messages_pass() {
        let spec = read(&["drop", "warning", ",", "info"]).unwrap();
        assert_eq!(spec.action(Severity::Warning), Action::Drop);
        assert_eq!(spec.action(Severity::Info), Action::Check);
        assert_eq!(spec.action(Severity::Error), Action::Pass);
        assert_eq!(spec.action(Severity::Trace), Action::Pass);
        let spec = read(&["pass", "all", ",", "drop", "info"]).unwrap();
        assert_eq!(spec.action(Severity::Info), Action::Pass);
        assert_eq!(spec.action(Severity::Trace), Action::Pass);
    }

    #[test]
    fn modes_sort_whole_messages_and_retain_duplicates() {
        let spec = read(&["ordering", ":=", "sorted"]).unwrap();
        assert_eq!(spec.combine(vec!["info: z\n".into(), "info: a\n".into(), "info: a\n".into()]),
            "info: a\n---\ninfo: a\n---\ninfo: z");
        assert!(spec.matches("info: a b", "info: a\nb"));
        assert!(!spec.matches("info: a b", "info: a  b"));
        let exact = read(&["whitespace", ":=", "exact"]).unwrap();
        assert!(!exact.matches("info: a b", "info: a\nb"));
        let lax = read(&["whitespace", ":=", "lax"]).unwrap();
        assert!(lax.matches("info: a b", "info:\t a\r\n  b"));
        for gap in ['\u{00a0}', '\u{2003}', '\u{000b}', '\u{000c}'] {
            assert!(!lax.matches("a b", &format!("a{gap}b")));
        }
        let substring = read(&["whitespace", ":=", "lax", ",", "substring", ":=", "true"]).unwrap();
        assert!(substring.matches("two words", "info: these are two\n  words!"));
        assert!(!substring.matches("missing", "info: these are two words!"));
    }

    #[test]
    fn malformed_and_unknown_specifications_are_not_defaults() {
        for words in [
            vec!["whitespace", ":=", "other"], vec!["substring", ":=", "1"],
            vec!["unknown", ":=", "true"], vec!["drop"], vec!["drop", "other"],
            vec!["info", "warning"], vec!["info", ","], vec![","],
            vec!["whitespace", ":=", "exact", ",", "whitespace", ":=", "unknown"],
            vec!["(", ")"],
        ] { assert!(read(&words).is_err(), "{words:?}"); }
    }
}
