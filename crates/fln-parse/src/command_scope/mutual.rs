//! Atomic source groups for the native mutual-inductive elaborator.
//!
//! The pin's Command.mutual encloses commands between `mutual` and `end`.
//! This door accepts one to eight inductive declarations; function groups,
//! nested groups and scope changes remain unsupported, never sequentialized.
//! Members use the ordinary declaration parser over their exact source bytes.
use super::*;

fn refusal(view: &SourceView, tokens: &[LexedToken], at: usize) -> DefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::InductiveConstructor,
    }
}
fn word(view: &SourceView, token: &LexedToken, text: &str) -> bool {
    // Escaped identifiers such as «end», and strings/comments containing end,
    // are not delimiters. Structural Name equality alone would lose that fact.
    view.normalized().span_str(token.extent) == Some(text)
}

/// Locate the closing token without parsing or publishing any member. Delimiter
/// validation prevents a malformed telescope from exposing a later declaration
/// as a separate command. No host recursion, including for hostile nesting.
pub(super) fn block_end(
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<usize, DefinitionParseError> {
    let mut delimiters = Vec::new();
    for (index, token) in tokens.iter().enumerate().skip(start + 1) {
        if delimiters.is_empty() {
            if word(view, token, "end") {
                return Ok(index);
            }
            if word(view, token, "mutual") {
                return Err(refusal(view, tokens, index));
            }
        }
        if let TokenKind::Symbol(symbol) = &token.kind {
            match symbol.as_str() {
                "(" => delimiters.push(")"),
                "{" | ".{" => delimiters.push("}"),
                "[" | "@[" => delimiters.push("]"),
                "⦃" => delimiters.push("⦄"),
                ")" | "}" | "]" | "⦄" if delimiters.pop() != Some(symbol.as_str()) => {
                    return Err(refusal(view, tokens, index));
                }
                _ => {}
            }
        }
    }
    Err(refusal(view, tokens, tokens.len()))
}

/// Recognize a complete group and return its untrusted member syntax. The
/// original group's offsets survive parser errors inside every member. None
/// means this is an ordinary command, not an empty or malformed mutual group.
pub fn parse(source: &[u8]) -> Result<Option<Vec<Syntax>>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = super::tokens(&view)?;
    if !tokens
        .first()
        .is_some_and(|token| word(&view, token, "mutual"))
    {
        return Ok(None);
    }
    let end = block_end(&view, &tokens, 0)?;
    if end + 1 != tokens.len() || end == 1 || !word(&view, &tokens[1], "inductive") {
        return Err(refusal(&view, &tokens, end));
    }
    let mut starts = Vec::new();
    let mut depth = 0_usize;
    for (index, token) in tokens.iter().enumerate().take(end).skip(1) {
        if depth == 0 && word(&view, token, "inductive") {
            if starts.len() == 8 {
                return Err(refusal(&view, &tokens, index));
            }
            starts.push(index);
        }
        if let TokenKind::Symbol(symbol) = &token.kind {
            match symbol.as_str() {
                "(" | "{" | ".{" | "[" | "@[" | "⦃" => depth += 1,
                ")" | "}" | "]" | "⦄" => depth -= 1, // block_end checked balance
                _ => {}
            }
        }
    }
    starts.push(end);
    let mut members = Vec::new();
    for pair in starts.windows(2) {
        let start = view.to_original(tokens[pair[0]].extent.start());
        let end = view.to_original(tokens[pair[1]].extent.start());
        let parsed = parse_definition(&source[start.0..end.0])
            .map_err(|error| error.with_original_offset(start))?;
        members.push(parsed.syntax);
    }
    Ok(Some(members))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn groups_keep_member_bytes_and_surrounding_scope_boundaries() {
        let source = "-- mutual fake\r\nnamespace Demo\r\nmutual\r\n  inductive Tree where | node (xs : Forest)\r\n  /- end -/ inductive Forest where | nil | cons (t : Tree)\r\nend\r\ndef t : Tree := Tree.node Forest.nil\r\nend Demo\r\n";
        let commands = super::super::partition(source.as_bytes()).unwrap();
        assert_eq!(commands.len(), 4);
        let mut combined = Vec::new();
        for (offset, command) in &commands {
            assert_eq!(offset.0, combined.len());
            combined.extend_from_slice(command);
        }
        assert_eq!(combined, source.as_bytes());
        assert_eq!(parse(commands[1].1).unwrap().unwrap().len(), 2);
        assert!(parse(commands[2].1).unwrap().is_none());
        assert!(matches!(
            super::super::parse(commands[3].1).unwrap(),
            Some(ScopeCommand::End(Some(_)))
        ));
    }

    #[test]
    fn escaped_delimiters_are_names_and_group_members_are_not_rewritten() {
        let source =
            b"mutual inductive A where | mk (x : B) inductive B where | \xc2\xabend\xc2\xbb end";
        let members = parse(source).unwrap().unwrap();
        assert_eq!(members.len(), 2);
        let single = parse(b"mutual inductive A where | mk end")
            .unwrap()
            .unwrap();
        assert_eq!(single.len(), 1);
    }

    #[test]
    fn malformed_or_unsupported_groups_never_become_partial_commands() {
        for source in [
            "mutual end",
            "mutual inductive A where | mk",
            "mutual inductive A where | mk (x : Nat] end",
            "mutual inductive A where | mk end A",
            "mutual def x := 1 def y := x end",
            "mutual inductive A where | mk def x := 1 end",
            "mutual namespace N inductive A where | mk end end",
            "mutual inductive A where | mk mutual inductive B where end end",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
        let oversized = format!(
            "mutual {} end",
            (0..9)
                .map(|i| format!("inductive A{i} where | mk "))
                .collect::<String>()
        );
        assert!(parse(oversized.as_bytes()).is_err());
    }

    #[test]
    fn member_parse_errors_use_original_group_byte_offsets() {
        let source =
            "-- 🦀\r\nmutual\r\ninductive A where | mk\r\ninductive B where | bad (x : Nat]\r\nend";
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(error.primary_offset().unwrap().0, source.find(']').unwrap());
        let source =
            "mutual\r\ninductive A where | mk\r\ninductive B where | bad deriving Nat\r\nend";
        let error = parse(source.as_bytes()).unwrap_err();
        assert_eq!(
            error.primary_offset().unwrap().0,
            source.find("deriving").unwrap()
        );
    }
}
