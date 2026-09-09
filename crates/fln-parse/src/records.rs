//! Bounded record/class declarations using the ordinary token leaves and types.
//! No source rewriting or fabricated definitions: field scopes survive as syntax.
//! Inheritance, custom constructors and deriving remain explicit
//! refusals rather than ignored command suffixes.
use super::*;
use std::ops::Range;

fn refuse(view: &SourceView, tokens: &[LexedToken], index: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, index),
        expected: NatDefinitionExpectation::RecordField,
    }
}
fn symbol(tokens: &[LexedToken], index: usize, text: &str) -> bool {
    matches!(tokens.get(index).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}
pub(super) fn modifiers() -> Syntax {
    Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        (0..7).map(|_| null_node(Vec::new())).collect(),
    )
}
pub(super) fn optional_type(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.is_empty() {
        return Ok(null_node(Vec::new()));
    }
    if !symbol(tokens, range.start, ":") {
        return Err(refuse(view, tokens, range.start));
    }
    Ok(null_node(vec![Syntax::node(
        parser_kind(&["Term", "typeSpec"]),
        vec![
            leaves.leaf(range.start)?,
            bounded_type(
                leaves,
                view,
                tokens,
                range.start + 1..range.end,
                DefinitionGrammar::Scalar,
            )?,
        ],
    )]))
}

fn field(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if !matches!(
        tokens.get(range.start).map(|t| &t.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(refuse(view, tokens, range.start));
    }
    let (groups, colon) = bounded_binders(
        view,
        &tokens[..range.end],
        range.start + 1,
        DefinitionGrammar::Scalar,
    )?;
    if !symbol(tokens, colon, ":") || colon >= range.end {
        return Err(refuse(view, tokens, colon));
    }
    let parameters =
        bounded_binder_syntax(leaves, view, tokens, groups, DefinitionGrammar::Scalar)?;
    let type_limit = type_end(&tokens[..range.end], colon, ":=");
    let default = if type_limit < range.end {
        let bounded_tokens = &tokens[..range.end];
        let (bindings, body_start) = bounded_let_bindings(view, bounded_tokens, type_limit + 1)?;
        null_node(vec![Syntax::node(
            parser_kind(&["Term", "binderDefault"]),
            vec![
                leaves.leaf(type_limit)?,
                bounded_value_syntax(
                    leaves,
                    view,
                    bounded_tokens,
                    bindings,
                    body_start,
                    DefinitionGrammar::Scalar,
                )?,
            ],
        )])
    } else {
        null_node(Vec::new())
    };
    Ok(Syntax::node(
        parser_kind(&["Command", "structSimpleBinder"]),
        vec![
            modifiers(),
            leaves.leaf(range.start)?,
            Syntax::node(
                parser_kind(&["Command", "optDeclSig"]),
                vec![
                    null_node(parameters),
                    optional_type(leaves, view, tokens, colon..type_limit)?,
                ],
            ),
            default,
        ],
    ))
}

fn fields(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<Vec<Syntax>, NatDefinitionParseError> {
    if start == tokens.len() {
        return Ok(Vec::new());
    }
    let source = view.normalized();
    let column = |index: usize| {
        let at = tokens[index].extent.start();
        at.0 - source
            .line_start(source.line_of(at))
            .expect("token's line exists")
            .0
    };
    let base = column(start);
    if source.line_of(tokens[start].extent.start()) > source.line_of(tokens[0].extent.start())
        && base <= column(0)
    {
        return Err(refuse(view, tokens, start));
    }
    let mut output = Vec::new();
    let mut first = start;
    let mut stack = Vec::new();
    for index in start..tokens.len() {
        let begins_line = index > first
            && source.line_of(tokens[index].extent.start())
                > source.line_of(tokens[index - 1].extent.end());
        if stack.is_empty() && begins_line && column(index) <= base {
            if column(index) != base {
                return Err(refuse(view, tokens, index));
            }
            output.push(field(leaves, view, tokens, first..index)?);
            first = index;
        }
        if let TokenKind::Symbol(s) = &tokens[index].kind {
            match s.as_str() {
                "(" => stack.push(")"),
                "{" => stack.push("}"),
                "[" => stack.push("]"),
                "⦃" => stack.push("⦄"),
                ")" | "}" | "]" | "⦄" => {
                    if stack.pop() != Some(s.as_str()) {
                        return Err(refuse(view, tokens, index));
                    }
                }
                "where" | "extends" | "deriving" => return Err(refuse(view, tokens, index)),
                _ => {}
            }
        }
    }
    if !stack.is_empty() {
        return Err(refuse(view, tokens, tokens.len()));
    }
    output.push(field(leaves, view, tokens, first..tokens.len())?);
    Ok(output)
}

pub(super) fn parse(
    view: SourceView,
    tokens: Vec<LexedToken>,
) -> Result<ParsedDefinition, NatDefinitionParseError> {
    let is_class = symbol(&tokens, 0, "class");
    if !matches!(tokens.get(1).map(|t| &t.kind), Some(TokenKind::Ident(_))) {
        return Err(refuse(&view, &tokens, 1));
    }
    let (groups, cursor) = bounded_binders(&view, &tokens, 2, DefinitionGrammar::Scalar)?;
    let end_header = if symbol(&tokens, cursor, ":") {
        type_end(&tokens, cursor, "where")
    } else {
        cursor
    };
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    let parameters =
        bounded_binder_syntax(&leaves, &view, &tokens, groups, DefinitionGrammar::Scalar)?;
    let result = optional_type(&leaves, &view, &tokens, cursor..end_header)?;
    let body = if end_header == tokens.len() {
        null_node(Vec::new())
    } else {
        if !symbol(&tokens, end_header, "where") {
            return Err(refuse(&view, &tokens, end_header));
        }
        let fields = fields(&leaves, &view, &tokens, end_header + 1)?;
        null_node(vec![
            leaves.leaf(end_header)?,
            null_node(Vec::new()),
            Syntax::node(
                parser_kind(&["Command", "structFields"]),
                vec![null_node(fields)],
            ),
        ])
    };
    let structure = Syntax::node(
        parser_kind(&["Command", "structure"]),
        vec![
            Syntax::node(
                parser_kind(&["Command", if is_class { "classTk" } else { "structureTk" }]),
                vec![leaves.leaf(0)?],
            ),
            Syntax::node(
                parser_kind(&["Command", "declId"]),
                vec![leaves.leaf(1)?, null_node(Vec::new())],
            ),
            Syntax::node(
                parser_kind(&["Command", "optDeclSig"]),
                vec![null_node(parameters), result],
            ),
            null_node(Vec::new()),
            body,
            Syntax::node(
                parser_kind(&["Command", "optDeriving"]),
                vec![null_node(Vec::new())],
            ),
        ],
    );
    Ok(ParsedDefinition {
        source_view: view,
        syntax: Syntax::node(
            parser_kind(&["Command", "declaration"]),
            vec![modifiers(), structure],
        ),
        epilogue,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn records_preserve_token_leaves_comments_and_original_offsets() {
        let text = "-- header\r\nclass Value (A : Type) where\r\n  -- field\r\n  get : A\r\n  transform (x : A) : A\r\n";
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            text.replace("\r\n", "\n").as_bytes()
        );
        assert_eq!(
            parse_source_command(text.as_bytes()).unwrap().kind(),
            SourceCommandKind::Definition
        );
        assert!(parse_nat_definition(text.as_bytes()).is_err());
    }
    #[test]
    fn records_partition_as_commands_without_losing_field_lines() {
        let text = b"structure Point where\n  x : Nat\n  y : Nat\nclass Chosen where\n  point : Point\ndef result : Nat := 9";
        let parts = partition_definition_commands(text).unwrap();
        assert_eq!(parts.len(), 3);
        for (_, source) in parts {
            parse_definition(source).unwrap();
        }
    }
    #[test]
    fn unsupported_record_forms_and_bad_indentation_do_not_disappear() {
        for text in [
            "structure A extends B where x : Nat",
            "structure A where\nx : Nat",
            "structure A where\n  x : Nat\n y : Nat",
            "structure A where\n  x : Nat :=",
            "structure A where\n  x : Nat\nderiving Inhabited",
            "structure A where\n  x Nat",
            "class A where\n  x : (Nat",
            "structure A where\n  mk ::",
            "structure A extra",
        ] {
            assert!(
                parse_definition(text.as_bytes()).is_err(),
                "accepted {text}"
            );
        }
        for text in [
            "structure Empty",
            "structure Empty where",
            "structure Empty : Type where",
        ] {
            assert!(parse_definition(text.as_bytes()).is_ok(), "refused {text}");
        }
    }
    #[test]
    fn default_bodies_preserve_crlf_comments_nested_literals_and_method_bindings() {
        let text = "structure Config where\r\n  -- header\r\n  inner : Inner := { value := 7 }\r\n  twice : Nat := let x := inner.value; x + x\r\n  apply (x : Nat) : Nat := x + twice\r\n";
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            text.replace("\r\n", "\n").as_bytes()
        );
        assert!(parse_nat_definition(text.as_bytes()).is_err());
    }
    #[test]
    fn malformed_defaults_are_not_silently_dropped() {
        for text in [
            "structure Config where\n  x : Nat :=",
            "structure Config where\n  x : Nat := 1 := 2",
            "structure Config where\n  x : Nat := let y := 1",
            "structure Config where\n  x : Nat := { value := 2",
        ] {
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
        }
    }
}
