//! File-level scope commands. The ordinary declaration parser remains the only
//! declaration parser; this layer partitions original bytes without rewriting.
use super::*;
pub mod attributes;
pub mod imports;
pub mod instances;
pub mod mutual;
pub mod variables;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeCommand {
    Namespace(Name),
    Section(Option<Name>),
    End(Option<Name>),
    Open(Vec<Name>),
    Universe(Vec<Name>),
    Variable(Syntax),
    Simp(attributes::SimpAttribute),
    Instance(instances::InstanceAttribute),
    Trivia,
}

fn table() -> TokenTable {
    let mut table = source_module_token_table();
    for keyword in [
        "prelude",
        "mutual",
        "namespace",
        "section",
        "end",
        "open",
        "universe",
        "scoped",
        "in",
        "hiding",
        "renaming",
        "attribute",
        "variable",
    ] {
        table.insert(keyword);
    }
    table
}
fn tokens(view: &SourceView) -> Result<Vec<LexedToken>, DefinitionParseError> {
    let run = lex_run(view.normalized(), &table());
    let diagnostics: Vec<_> = run
        .diagnostics()
        .into_iter()
        .map(|(message, at)| ParseDiagnostic {
            message,
            at: view.to_original(at),
        })
        .collect();
    if !diagnostics.is_empty() {
        return Err(NatDefinitionParseError::Lexical { diagnostics });
    }
    Ok(run
        .events
        .into_iter()
        .filter_map(|event| match event {
            Event::Token(token) => Some(token),
            _ => None,
        })
        .collect())
}
fn control(s: &str) -> bool {
    matches!(
        s,
        "namespace" | "section" | "end" | "open" | "universe" | "attribute" | "variable"
    )
}
fn declaration(s: &str) -> bool {
    matches!(
        s,
        "def" | "theorem" | "instance" | "structure" | "class" | "inductive" | "#check" | "#eval"
    )
}

/// Recognize complete scope commands, including comments and escaped identifiers.
/// Unsupported `open ... in`, selective opens, and modifiers are never ignored.
pub fn parse(source: &[u8]) -> Result<Option<ScopeCommand>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let Some(first) = tokens.first() else {
        return Ok(Some(ScopeCommand::Trivia));
    };
    let TokenKind::Symbol(keyword) = &first.kind else {
        return Ok(None);
    };
    if keyword == "variable" {
        return variables::parse(&view, &tokens).map(|syntax| Some(ScopeCommand::Variable(syntax)));
    }
    if keyword == "attribute" {
        if let Some(attribute) = instances::parse(&view, &tokens)? {
            return Ok(Some(ScopeCommand::Instance(attribute)));
        }
        return attributes::parse(source).map(|attribute| attribute.map(ScopeCommand::Simp));
    }
    if !control(keyword) {
        return Ok(None);
    }
    let bad = |index: usize| NatDefinitionParseError::OutsideSeedGrammar {
        at: tokens.get(index).map_or(BytePos(source.len()), |t| {
            view.to_original(t.extent.start())
        }),
        expected: NatDefinitionExpectation::EndOfCommand,
    };
    let mut names = Vec::new();
    for (index, token) in tokens.iter().enumerate().skip(1) {
        let TokenKind::Ident(name) = &token.kind else {
            return Err(bad(index));
        };
        names.push(name.clone());
    }
    let command = match keyword.as_str() {
        "namespace" if names.len() == 1 => ScopeCommand::Namespace(names.remove(0)),
        "section" if names.len() <= 1 => ScopeCommand::Section(names.pop()),
        "end" if names.len() <= 1 => ScopeCommand::End(names.pop()),
        "open" if !names.is_empty() => ScopeCommand::Open(names),
        "universe" if !names.is_empty() && names.iter().all(|n| n.parent().is_anonymous()) => {
            ScopeCommand::Universe(names)
        }
        _ => return Err(bad(1)),
    };
    Ok(Some(command))
}

/// Partition both scope commands and declarations, preserving every source byte.
/// Delimiters protect nested terms and explicit universe argument lists; comments
/// and strings are lexer events, not text searched for command-looking words.
/// Scope directives must start a source line. Within a declaration they must
/// also leave its layout block; `end` is still a valid local name in a proof.
pub fn partition(source: &[u8]) -> Result<Vec<(BytePos, &[u8])>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let mut starts = Vec::new();
    let mut depth = 0_usize;
    let source_view = view.normalized();
    let column = |token: &LexedToken| {
        let start = token.extent.start();
        start.0
            - source_view
                .line_start(source_view.line_of(start))
                .expect("token line")
                .0
    };
    let mut declaration_column = None;
    let mut attribute_prefix = false;
    let mut mutual_until = 0;
    for (index, token) in tokens.iter().enumerate() {
        if index < mutual_until {
            continue;
        }
        if let TokenKind::Symbol(symbol) = &token.kind {
            if depth == 0 && symbol == "mutual" {
                // A mutual group is one admission unit. In particular its end
                // cannot close the surrounding namespace or section, and no
                // member may be published before the entire group is checked.
                starts.push(view.to_original(token.extent.start()).0);
                mutual_until = mutual::block_end(&view, &tokens, index)? + 1;
                declaration_column = None;
                attribute_prefix = false;
                continue;
            }
            let command_line = (index == 0
                || source_view.line_of(token.extent.start())
                    > source_view.line_of(tokens[index - 1].extent.end()))
                && declaration_column.is_none_or(|base| column(token) <= base);
            let scope_start = control(symbol) && command_line;
            let inline_start = symbol == "@[" && command_line;
            if depth == 0 && (scope_start || declaration(symbol) || inline_start) {
                if !(attribute_prefix && declaration(symbol)) {
                    starts.push(view.to_original(token.extent.start()).0);
                }
                attribute_prefix = inline_start;
                declaration_column = declaration(symbol).then(|| column(token));
            }
            match symbol.as_str() {
                "(" | "[" | "@[" | "{" | ".{" | "⦃" => depth = depth.saturating_add(1),
                ")" | "]" | "}" | "⦄" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    let mut output = Vec::new();
    let mut start = 0;
    for next in starts.into_iter().skip(1) {
        output.push((BytePos(start), &source[start..next]));
        start = next;
    }
    output.push((BytePos(start), &source[start..]));
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scopes_preserve_structural_names_and_original_offsets() {
        let source = b"-- namespace Fake\r\nnamespace Real\r\n-- end Real\r\ndef x := \"end Real\"\r\nsection\r\nuniverse u v\r\nend\r\nend Real\r\n";
        let commands = partition(source).unwrap();
        assert_eq!(commands.len(), 6);
        let mut joined = Vec::new();
        for (offset, bytes) in &commands {
            assert_eq!(*offset, BytePos(joined.len()));
            joined.extend_from_slice(bytes);
        }
        assert_eq!(joined, source);
        assert_eq!(
            parse(commands[0].1).unwrap(),
            Some(ScopeCommand::Namespace(Name::from_components(["Real"])))
        );
        assert_eq!(
            parse("namespace «A.B»".as_bytes()).unwrap(),
            Some(ScopeCommand::Namespace(Name::from_components(["A.B"])))
        );
        assert_eq!(
            parse(b"section").unwrap(),
            Some(ScopeCommand::Section(None))
        );
        assert_eq!(
            parse(b"/- only trivia -/").unwrap(),
            Some(ScopeCommand::Trivia)
        );
    }
    #[test]
    fn malformed_scope_commands_are_not_partially_accepted() {
        for source in [
            "namespace",
            "namespace A B",
            "end A B",
            "section A B",
            "open",
            "open A (x)",
            "open A in",
            "open scoped A",
            "open A hiding x",
            "open A renaming x -> y",
            "universe A.u",
            "universe u, v",
            "end := 3",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
        assert_eq!(parse(b"def value := 3").unwrap(), None);
    }
    #[test]
    fn universe_commas_and_escaped_command_names_are_not_command_boundaries() {
        let commands = partition(
            "namespace A\ndef «end».{u,v} (x : Sort u) : Sort u := x\ndef q := f.{1,2} Nat\nend A"
                .as_bytes(),
        )
        .unwrap();
        assert_eq!(commands.len(), 4);
        assert!(parse_definition(commands[1].1).is_ok());
    }
    #[test]
    fn scope_words_inside_branch_binders_and_indented_terms_stay_in_the_declaration() {
        for source in [
            "def choose (x : Bool) : Nat := by\n  cases x with\n  | false => exact 0\n  | true => let end := 7; exact end",
            "def choose (x : Nat) : Nat := match x with | Nat.zero => 0 | Nat.succ end => end",
            "def choose (end : Nat) : Nat :=\n  end",
            "def choose (namespace section open universe : Nat) : Nat := open",
        ] {
            let file = format!("namespace Example\n{source}\nend Example");
            let commands = partition(file.as_bytes()).unwrap();
            assert_eq!(commands.len(), 3, "{file}");
            assert!(parse_definition(commands[1].1).is_ok(), "{file}");
            assert_eq!(
                parse(commands[2].1).unwrap(),
                Some(ScopeCommand::End(Some(Name::from_components(["Example"]))))
            );
        }
        let source = include_bytes!("../../../examples/native_index_refinement.lean");
        let commands = partition(source).unwrap();
        assert_eq!(
            commands.len(),
            partition_definition_commands(source).unwrap().len()
        );
        for (_, command) in commands {
            assert!(
                parse_definition(command).is_ok(),
                "{}",
                String::from_utf8_lossy(command)
            );
        }
    }
}
