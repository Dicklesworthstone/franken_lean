//! The pin's command trees for the scope commands (`Lean/Parser/Command.lean`).
//!
//! [`super::parse`] reads what a scope command does to the environment; this module reads how the
//! pin's parser builds it. The two accept the same commands except where the checker does not
//! model what the tree says: `meta` sections retain their trees
//! for explicit refusal. Public, exposure and noncomputable section flags have both a typed
//! command and the original pin-shaped syntax tree.
use super::*;

fn is_scope_command_kind(kind: Option<&Name>) -> bool {
    let Some(kind) = kind else {
        return false;
    };
    *kind == parser_kind(&["Command", "moduleDoc"])
        || *kind == parser_kind(&["Command", "exit"])
        || *kind == parser_kind(&["Command", "namespace"])
        || *kind == parser_kind(&["Command", "section"])
        || *kind == parser_kind(&["Command", "end"])
        || *kind == parser_kind(&["Command", "universe"])
        || *kind == parser_kind(&["Command", "include"])
        || *kind == parser_kind(&["Command", "omit"])
        || *kind == parser_kind(&["Command", "variable"])
        || *kind == parser_kind(&["Command", "attribute"])
        || *kind == parser_kind(&["Command", "open"])
        || *kind == parser_kind(&["Command", "set_option"])
        || *kind == parser_kind(&["Command", "in"])
        || *kind == parser_kind(&["Command", "export"])
        || *kind == Name::from_components(["Lean", "guardMsgsCmd"])
}

/// The pin's tree for a scope command (`namespace`, `section`, `end`, `open`, `universe`,
/// `variable`, `include`, `omit`, `set_option`, `attribute`, a module doc, and
/// `open`/`set_option … in <command>`), or `None` for any other command or a form this module
/// does not build.
pub fn tree(source: &[u8]) -> Result<Option<Syntax>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let (syntax, _) = crate::extensions::parse_active_command(&view)?;
    Ok(is_scope_command_kind(syntax.kind()).then_some(syntax))
}

/// The original syntax of a scope command's head, retaining its `in` atom but
/// leaving the nested command missing. Clients that replay lexical scopes must
/// parse that command only after applying the head: `open scoped N in ...` can
/// change the grammar of its body. No source bytes or identifiers are invented.
pub fn head_tree(source: &[u8]) -> Result<Option<Syntax>, DefinitionParseError> {
    let body = match super::parse(source)? {
        Some(
            ScopeCommand::OpenIn { body, .. }
            | ScopeCommand::SetOptionIn { body, .. }
            | ScopeCommand::In { body, .. },
        ) => body,
        _ => return tree(source),
    };
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let Some((at, token)) = tokens
        .iter()
        .enumerate()
        .take_while(|(_, token)| view.to_original(token.extent.end()).0 <= body)
        .last()
    else {
        return Ok(None);
    };
    if !matches!(&token.kind, TokenKind::Symbol(word) if word == "in") {
        return Ok(None);
    }
    let head_end = view.to_original(token.extent.start()).0;
    let head = match tree(&source[..head_end])? {
        Some(head) => head,
        None => parse_source_command(&source[..head_end])?.syntax,
    };
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    Ok(Some(Syntax::node(
        parser_kind(&["Command", "in"]),
        vec![head, leaves.leaf(at)?, Syntax::Missing],
    )))
}

/// The pin's tree for any command, parsed through the unified generated registry engine.
pub fn command_tree(source: &[u8]) -> Result<Syntax, DefinitionParseError> {
    parse_source_command(source).map(|parsed| parsed.syntax)
}

/// `section`: `sectionHeader "section" (ident)?`, with `sectionHeader := ("@[" "expose" "]")?
/// ("public")? ("noncomputable")? ("meta")?`, each optional slot a node of its own.
struct SectionParts {
    expose: bool,
    slots: [Option<usize>; 3],
    keyword: usize,
    name: Option<usize>,
}

fn section_parts(view: &SourceView, tokens: &[LexedToken]) -> Option<SectionParts> {
    let word = |at: usize, text: &str| {
        tokens
            .get(at)
            .is_some_and(|token| view.normalized().span_str(token.extent) == Some(text))
    };
    let mut at = 0;
    let expose = word(0, "@[") && word(1, "expose") && word(2, "]");
    if expose {
        at = 3;
    }
    let mut slots = [None; 3];
    for (slot, keyword) in slots.iter_mut().zip(["public", "noncomputable", "meta"]) {
        *slot = word(at, keyword).then_some(at);
        if word(at, keyword) {
            at += 1;
        }
    }
    if !matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == "section") {
        return None;
    }
    let name = match tokens.len() - at {
        1 => None,
        2 if matches!(&tokens[at + 1].kind, TokenKind::Ident(_)) => Some(at + 1),
        _ => return None,
    };
    Some(SectionParts {
        expose,
        slots,
        keyword: at,
        name,
    })
}

/// Recognize the supported lexical section flags from the same scan used to
/// build its exact syntax tree. Unsupported scope effects keep their tree and
/// are refused by the ordinary source-command path.
pub(super) fn modified_section(view: &SourceView, tokens: &[LexedToken]) -> Option<ScopeCommand> {
    let parts = section_parts(view, tokens)?;
    if parts.keyword == 0 || parts.slots[2].is_some() {
        return None;
    }
    let name = parts.name.map(|at| match &tokens[at].kind {
        TokenKind::Ident(name) => name.clone(),
        _ => unreachable!("section_parts validated the name"),
    });
    Some(ScopeCommand::SectionWithModifiers {
        name,
        public: parts.slots[0].is_some(),
        expose: parts.expose,
        noncomputable: parts.slots[1].is_some(),
    })
}

/// `openDecl` over `tokens[start..end]`, the tokens after `open` (for the command and for the
/// tactic `open … in`): `openHiding <|> openRenaming <|> openOnly <|> openSimple <|> openScoped`.
pub(crate) fn open_declaration(
    leaves: &Leaves,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<Option<Syntax>, DefinitionParseError> {
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    let ident = |at: usize| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(_)));
    let idents = |from: usize, to: usize| from < to && (from..to).all(ident);
    let names = |from: usize, to: usize| -> Result<Syntax, DefinitionParseError> {
        Ok(null_node(
            (from..to)
                .map(|at| leaves.leaf(at))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    };
    let node = |kind: &str, args: Vec<Syntax>| Syntax::node(parser_kind(&["Command", kind]), args);
    let (first, second, third) = (start, start + 1, start + 2);
    Ok(Some(if is(first, "scoped") && idents(second, end) {
        node("openScoped", vec![leaves.leaf(first)?, names(second, end)?])
    } else if ident(first)
        && is(second, "(")
        && end > start + 3
        && is(end - 1, ")")
        && idents(third, end - 1)
    {
        node(
            "openOnly",
            vec![
                leaves.leaf(first)?,
                leaves.leaf(second)?,
                names(third, end - 1)?,
                leaves.leaf(end - 1)?,
            ],
        )
    } else if ident(first) && is(second, "hiding") && idents(third, end) {
        node(
            "openHiding",
            vec![
                leaves.leaf(first)?,
                leaves.leaf(second)?,
                names(third, end)?,
            ],
        )
    } else if ident(first) && is(second, "renaming") {
        // `sepBy1 openRenamingItem ", "`, `openRenamingItem := ident unicodeSymbol " → " " -> " ident`.
        let mut items = Vec::new();
        let mut at = third;
        loop {
            if !(ident(at) && (is(at + 1, "→") || is(at + 1, "->")) && ident(at + 2)) {
                return Ok(None);
            }
            items.push(node(
                "openRenamingItem",
                vec![leaves.leaf(at)?, leaves.leaf(at + 1)?, leaves.leaf(at + 2)?],
            ));
            at += 3;
            if at == end {
                break;
            }
            if !is(at, ",") {
                return Ok(None);
            }
            items.push(leaves.leaf(at)?);
            at += 1;
        }
        node(
            "openRenaming",
            vec![leaves.leaf(first)?, leaves.leaf(second)?, null_node(items)],
        )
    } else if idents(first, end) {
        node("openSimple", vec![names(first, end)?])
    } else {
        return Ok(None);
    }))
}

/// `optionValue := "true" <|> "false" <|> str <|> num` (each a non-reserved symbol or a literal)
/// at token `at`; `None` for anything else.
pub(crate) fn option_value(
    leaves: &Leaves,
    tokens: &[LexedToken],
    at: usize,
) -> Result<Option<Syntax>, NatDefinitionParseError> {
    Ok(Some(match &tokens[at].kind {
        _ if term_locals::word(tokens, at, "true") || term_locals::word(tokens, at, "false") => {
            // nonReservedSymbolFnAux compares the raw identifier spelling, not
            // its resolved name: an escaped identifier is not a boolean token.
            Syntax::Atom {
                info: leaves.leaf(at)?.info(),
                val: if term_locals::word(tokens, at, "true") {
                    "true"
                } else {
                    "false"
                }
                .to_owned(),
            }
        }
        TokenKind::Literal(LiteralKind::Nat) => {
            Syntax::node(Name::str(Name::anonymous(), "num"), vec![leaves.leaf(at)?])
        }
        TokenKind::Literal(LiteralKind::Str) => {
            Syntax::node(Name::str(Name::anonymous(), "str"), vec![leaves.leaf(at)?])
        }
        _ => return Ok(None),
    }))
}

#[cfg(test)]
mod noncomputable_section_tests {
    use super::*;

    #[test]
    fn section_flags_preserve_the_pin_tree_and_original_command_boundaries() {
        for (source, public, expose) in [
            ("noncomputable section", false, false),
            ("public noncomputable section", true, false),
            ("@[expose] public noncomputable section", true, true),
        ] {
            assert_eq!(
                super::super::parse(source.as_bytes()).unwrap(),
                Some(ScopeCommand::SectionWithModifiers {
                    name: None,
                    public,
                    expose,
                    noncomputable: true,
                })
            );
            assert_eq!(
                tree(source.as_bytes()).unwrap().unwrap().kind(),
                Some(&parser_kind(&["Command", "section"]))
            );
        }
        let source = b"/- leading -/\r\n@[expose]\r\npublic\r\nnoncomputable\r\nsection A.B\r\ndef x := 7\r\nend B\r\nend A\r\n";
        let commands = super::super::partition(source).unwrap();
        assert_eq!(commands.len(), 4);
        assert!(matches!(
            super::super::parse(commands[0].1).unwrap(),
            Some(ScopeCommand::SectionWithModifiers {
                noncomputable: true,
                ..
            })
        ));
        assert_eq!(
            commands
                .iter()
                .flat_map(|(_, bytes)| bytes.iter().copied())
                .collect::<Vec<_>>(),
            source
        );
    }

    #[test]
    fn escaped_and_unsupported_modifiers_do_not_acquire_section_authority() {
        for source in [
            "«noncomputable» section",
            "noncomputable meta section",
            "noncomputable public section",
            "noncomputable noncomputable section",
        ] {
            assert!(
                !matches!(
                    super::super::parse(source.as_bytes()),
                    Ok(Some(ScopeCommand::SectionWithModifiers { .. }))
                ),
                "{source}"
            );
        }
    }
}
