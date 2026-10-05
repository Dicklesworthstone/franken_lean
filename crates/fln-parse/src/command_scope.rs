//! File-level scope commands. The ordinary declaration parser remains the only
//! declaration parser; this layer partitions original bytes without rewriting.
use super::*;
pub mod attributes;
pub mod imports;
pub mod instances;
pub mod modifiers;
pub mod mutual;
pub mod variables;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeCommand {
    Namespace(Name),
    Section(Option<Name>),
    End(Option<Name>),
    Open(Vec<Name>),
    OpenScoped(Vec<Name>),
    Universe(Vec<Name>),
    Variable(Syntax),
    Include(Vec<Name>),
    Omit(Vec<Name>),
    Simp(attributes::SimpAttribute),
    Instance(instances::InstanceAttribute),
    /// `open A B in <command>` (`Lean.Parser.Command.in`): the pin's macro elaborates it as
    /// `section open A B <command> end`. `body` is the byte offset, within this command's own
    /// source, where the inner command starts.
    OpenIn {
        names: Vec<Name>,
        scoped: bool,
        body: usize,
    },
    Trivia,
}

/// The scope layer's table: the full implicit-Init table, the same one declaration bodies use.
/// Every scope keyword this layer recognises (`namespace`, `end`, `open`, `universe`, `scoped`,
/// `omit`, …) is a token at the pin, so nothing is added by hand; `prelude` is header-only and
/// lives in `imports`' header table.
fn table() -> &'static TokenTable {
    crate::reference_tokens::implicit_init_table()
}
fn tokens(view: &SourceView) -> Result<Vec<LexedToken>, DefinitionParseError> {
    let run = lex_run(view.normalized(), table());
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
        "namespace"
            | "section"
            | "end"
            | "open"
            | "universe"
            | "attribute"
            | "variable"
            | "include"
            | "omit"
    )
}
fn declaration(s: &str) -> bool {
    matches!(
        s,
        "def"
            | "theorem"
            | "example"
            | "instance"
            | "structure"
            | "class"
            | "inductive"
            | "#check"
            | "#eval"
    )
}

/// Recognize complete scope commands, including comments and escaped identifiers.
/// `open A in <command>` is recognized with its body; selective opens (`open A (x)`,
/// `hiding`, `renaming`) are never ignored.
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
    let scoped = keyword == "open"
        && tokens.get(1).is_some_and(
            |token| matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "scoped"),
        );
    let mut names = Vec::new();
    for (index, token) in tokens.iter().enumerate().skip(if scoped { 2 } else { 1 }) {
        let TokenKind::Ident(name) = &token.kind else {
            // `open A B in <command>`: everything after `in` is one more command.
            if keyword == "open"
                && !names.is_empty()
                && matches!(&token.kind, TokenKind::Symbol(symbol) if symbol == "in")
            {
                let Some(body) = tokens.get(index + 1) else {
                    return Err(bad(index + 1));
                };
                return Ok(Some(ScopeCommand::OpenIn {
                    names,
                    scoped,
                    body: view.to_original(body.extent.start()).0,
                }));
            }
            return Err(bad(index));
        };
        names.push(name.clone());
    }
    let command = match keyword.as_str() {
        "namespace" if names.len() == 1 => ScopeCommand::Namespace(names.remove(0)),
        "section" if names.len() <= 1 => ScopeCommand::Section(names.pop()),
        "end" if names.len() <= 1 => ScopeCommand::End(names.pop()),
        "open" if !names.is_empty() && scoped => ScopeCommand::OpenScoped(names),
        "open" if !names.is_empty() => ScopeCommand::Open(names),
        "include" if !names.is_empty() => ScopeCommand::Include(names),
        "omit" if !names.is_empty() => ScopeCommand::Omit(names),
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
    // The column of the attribute or modifier that opened the current declaration, so its
    // body's layout block is measured from the command's first token, not its keyword.
    let mut prefix_column = None;
    // `open A in <command>` is one command: after an `open`'s `in`, the next command that
    // starts belongs to it.
    let mut current_open = false;
    let mut open_in = false;
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
                if !open_in {
                    starts.push(view.to_original(token.extent.start()).0);
                }
                open_in = false;
                current_open = false;
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
            // Attributes and declaration modifiers (`private`, `protected`, `noncomputable`,
            // …) precede the declaration keyword in one command (`declModifiers`).
            let prefix = symbol == "@[" || modifiers::is_modifier(symbol);
            let inline_start = prefix && command_line;
            let continues_prefix = attribute_prefix && (declaration(symbol) || prefix);
            if depth == 0 && current_open && symbol == "in" {
                open_in = true;
                current_open = false;
                continue;
            }
            if depth == 0
                && (scope_start || declaration(symbol) || inline_start || continues_prefix)
            {
                if !continues_prefix {
                    if !open_in {
                        starts.push(view.to_original(token.extent.start()).0);
                    }
                    open_in = false;
                    current_open = scope_start && symbol == "open";
                    prefix_column = inline_start.then(|| column(token));
                }
                attribute_prefix = inline_start || (continues_prefix && !declaration(symbol));
                declaration_column = declaration(symbol)
                    .then(|| prefix_column.map_or(column(token), |base| base.min(column(token))));
            }
            match symbol.as_str() {
                "(" | "[" | "@[" | "{" | ".{" | "⦃" | "⟨" => depth = depth.saturating_add(1),
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
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
    fn scoped_openings_preserve_structural_names_without_becoming_name_opens() {
        let source = "-- 😀\r\nopen scoped A.«B.C» D";
        assert_eq!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenScoped(vec![
                Name::from_components(["A", "B.C"]),
                Name::from_components(["D"]),
            ]))
        );
        assert_eq!(
            parse(b"open A").unwrap(),
            Some(ScopeCommand::Open(vec![Name::from_components(["A"])]))
        );
        for source in [
            "open scoped",
            "open scoped A hiding x",
            "open scoped A in",
            "open scoped A, B",
            "open scoped 4",
        ] {
            assert!(parse(source.as_bytes()).is_err(), "{source}");
        }
    }

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
            "open scoped",
            "open scoped A in",
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
    /// `open A in <command>` (`Lean.Parser.Command.in`) is one command whose body is the next
    /// command; the pin's macro elaborates it as `section open A <command> end`.
    #[test]
    fn open_in_is_one_command_with_its_body() {
        let source = "open A B in\ndef x := 1";
        assert_eq!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenIn {
                names: vec![Name::from_components(["A"]), Name::from_components(["B"])],
                scoped: false,
                body: source.find("def").unwrap(),
            })
        );
        let source = "open scoped A in def x := 1";
        assert!(matches!(
            parse(source.as_bytes()).unwrap(),
            Some(ScopeCommand::OpenIn { scoped: true, body, .. }) if body == source.find("def").unwrap()
        ));

        // The body belongs to the open; the command after it does not.
        let file = "namespace N\nopen A in\ndef x := 1\ndef y := 2\nend N";
        let commands = partition(file.as_bytes()).unwrap();
        let texts: Vec<_> = commands
            .iter()
            .map(|(_, bytes)| std::str::from_utf8(bytes).unwrap())
            .collect();
        assert_eq!(
            texts,
            [
                "namespace N\n",
                "open A in\ndef x := 1\n",
                "def y := 2\n",
                "end N"
            ]
        );

        // Nested opens are one command; each level's body is the rest.
        let file = "open A in\nopen B in\ndef x := 1\ndef y := 2";
        let commands = partition(file.as_bytes()).unwrap();
        assert_eq!(commands.len(), 2);
        let Some(ScopeCommand::OpenIn { body, .. }) = parse(commands[0].1).unwrap() else {
            panic!("open-in");
        };
        let inner = &commands[0].1[body..];
        assert!(matches!(
            parse(inner).unwrap(),
            Some(ScopeCommand::OpenIn { body, .. }) if parse_definition(&inner[body..]).is_ok()
        ));

        // An `in` inside a later declaration does not reach back to an earlier open.
        let file = "open A\ndef f := Id.run do\n  for x in [1] do pure ()\n  pure 0\ndef g := 1";
        assert_eq!(partition(file.as_bytes()).unwrap().len(), 3);
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
        // Each bare scope word is a keyword, so the pinned Reference refuses the declaration;
        // escaped, each is an ordinary name and the Reference accepts it. Captured with the pin
        // (v4.32.0, 2026-10-05) on `namespace Example\n<declaration>\nend Example`:
        //   1. `let end := 7` -> 5:16 unexpected token 'end'; expected '(', ':=', '|' or term
        //   2. `Nat.succ end =>` -> 2:69 unexpected token 'end'; expected '=>'
        //   3. `(end : Nat)` -> 2:12 unexpected token 'end'; expected '_' or identifier
        //   4. `(namespace …` -> 2:12 unexpected token 'namespace'; expected '_' or identifier
        //   5. `«open» universe :` -> 2:40 unexpected token 'universe'; expected ')'
        //   6-9. the same with every word escaped: accepted.
        // Wherever the declaration is refused, the scope words inside it still never split it.
        for (source, accepted) in [
            (
                "def choose (x : Bool) : Nat := by\n  cases x with\n  | false => exact 0\n  | true => let end := 7; exact end",
                false,
            ),
            (
                "def choose (x : Nat) : Nat := match x with | Nat.zero => 0 | Nat.succ end => end",
                false,
            ),
            ("def choose (end : Nat) : Nat :=\n  end", false),
            (
                "def choose (namespace section open universe : Nat) : Nat := open",
                false,
            ),
            (
                "def choose («namespace» «section» «open» universe : Nat) : Nat := «open»",
                false,
            ),
            (
                "def choose (x : Bool) : Nat := by\n  cases x with\n  | false => exact 0\n  | true => let «end» := 7; exact «end»",
                true,
            ),
            (
                "def choose (x : Nat) : Nat := match x with | Nat.zero => 0 | Nat.succ «end» => «end»",
                true,
            ),
            ("def choose («end» : Nat) : Nat :=\n  «end»", true),
            (
                "def choose («namespace» «section» «open» «universe» : Nat) : Nat := «open»",
                true,
            ),
        ] {
            let file = format!("namespace Example\n{source}\nend Example");
            let commands = partition(file.as_bytes()).unwrap();
            assert_eq!(commands.len(), 3, "{file}");
            assert_eq!(parse_definition(commands[1].1).is_ok(), accepted, "{file}");
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
