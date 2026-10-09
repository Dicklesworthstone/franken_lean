//! Bounded record/class declarations using the ordinary token leaves and types.
//! No source rewriting or fabricated definitions: field scopes survive as syntax.
//! Parent clauses retain their original type syntax and optional projection names.
//! Deriving clauses retain their handlers; custom constructors remain refused.
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

/// The declaration parser consumes a deriving suffix without discarding its
/// token leaves. Only a top-level keyword ends the constructor/field telescope.
pub(super) fn deriving_start(tokens: &[LexedToken], start: usize) -> usize {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        if let TokenKind::Symbol(symbol) = &token.kind {
            match crate::canonical_bracket(symbol.as_str()) {
                "deriving" if depth == 0 => return index,
                "(" | "{" | ".{" | "[" | "⦃" | "⟨" => depth += 1,
                ")" | "}" | "]" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    tokens.len()
}

pub(super) fn deriving_suffix(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    Ok(Syntax::node(
        parser_kind(&["Command", "optDeriving"]),
        vec![deriving_clause(leaves, view, tokens, start)?],
    ))
}

/// `("deriving " derivingClass,+)?` from `start` to the last token, as its optional node: empty,
/// or the keyword and the classes (each a name), as `optDeriving` and `optDefDeriving` hold it.
pub(super) fn deriving_clause(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut suffix = Vec::new();
    if start < tokens.len() {
        if !symbol(tokens, start, "deriving") || start + 1 == tokens.len() {
            return Err(refuse(view, tokens, start));
        }
        let mut classes = Vec::new();
        for index in start + 1..tokens.len() {
            if (index - start) % 2 == 1 {
                if !matches!(&tokens[index].kind, TokenKind::Ident(_)) {
                    return Err(refuse(view, tokens, index));
                }
                classes.push(Syntax::node(
                    parser_kind(&["Command", "derivingClass"]),
                    vec![null_node(Vec::new()), leaves.leaf(index)?],
                ));
            } else {
                if !symbol(tokens, index, ",") || index + 1 == tokens.len() {
                    return Err(refuse(view, tokens, index));
                }
                classes.push(leaves.leaf(index)?);
            }
        }
        suffix = vec![leaves.leaf(start)?, null_node(classes)];
    }
    Ok(null_node(suffix))
}
pub(super) fn modifiers() -> Syntax {
    Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        (0..7).map(|_| null_node(Vec::new())).collect(),
    )
}

/// A `declModifiers` node holding only the doc comment at token `doc`, if any.
fn modifiers_with_doc(
    view: &SourceView,
    leaves: &Leaves,
    tokens: &[LexedToken],
    doc: Option<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut parts: Vec<Syntax> = (0..7).map(|_| null_node(Vec::new())).collect();
    if let Some(doc) = doc {
        parts[0] = crate::doc_comment_syntax(view, leaves, tokens, doc)?;
    }
    Ok(Syntax::node(
        parser_kind(&["Command", "declModifiers"]),
        parts,
    ))
}

/// Whether token `at` is a declaration doc comment (`/--`), which leads a field as it leads a
/// declaration: `structSimpleBinder`'s own `declModifiers` (`Lean/Parser/Command.lean`).
fn doc_at(tokens: &[LexedToken], at: usize) -> bool {
    symbol(tokens, at, "/--")
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
    let doc = doc_at(tokens, range.start).then_some(range.start);
    let range = range.start + usize::from(doc.is_some())..range.end;
    // `private` or `protected` before the field's name.
    let visibility = ["private", "protected"]
        .into_iter()
        .find(|word| symbol(tokens, range.start, word))
        .map(|word| (word, range.start));
    let range = range.start + usize::from(visibility.is_some())..range.end;
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
        let value = bounded_value_syntax(
            leaves,
            view,
            bounded_tokens,
            bindings,
            body_start,
            DefinitionGrammar::Scalar,
        )?;
        // `:= by tac` is `binderTactic` (an `autoParam` field), not a default value that happens
        // to be a proof: `" := " " by " tacticSeq` wins over `binderDefault` at the pin.
        let tactic = symbol(tokens, type_limit + 1, "by")
            && value.kind() == Some(&parser_kind(&["Term", "byTactic"]));
        null_node(vec![match (tactic, &value) {
            (true, Syntax::Node { args, .. }) if args.len() == 2 => Syntax::node(
                parser_kind(&["Term", "binderTactic"]),
                vec![leaves.leaf(type_limit)?, args[0].clone(), args[1].clone()],
            ),
            _ => Syntax::node(
                parser_kind(&["Term", "binderDefault"]),
                vec![leaves.leaf(type_limit)?, value],
            ),
        }])
    } else {
        null_node(Vec::new())
    };
    let mut field_modifiers = modifiers_with_doc(view, leaves, tokens, doc)?;
    // `declModifiers := docComment? attributes? visibility? protected? …`: `private` is a
    // visibility, `protected` a slot of its own.
    if let (Some((word, at)), Syntax::Node { args, .. }) = (visibility, &mut field_modifiers) {
        let slot = if word == "protected" { 3 } else { 2 };
        args[slot] = null_node(vec![Syntax::node(
            parser_kind(&["Command", word]),
            vec![leaves.leaf(at)?],
        )]);
    }
    Ok(Syntax::node(
        parser_kind(&["Command", "structSimpleBinder"]),
        vec![
            field_modifiers,
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
    keyword: usize,
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
    if source.line_of(tokens[start].extent.start()) > source.line_of(tokens[keyword].extent.start())
        && base <= column(keyword)
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
        // A field's doc comment and its name start lines of one field.
        let after_doc = index == first + 1 && doc_at(tokens, first);
        if stack.is_empty() && begins_line && !after_doc && column(index) <= base {
            if column(index) != base {
                return Err(refuse(view, tokens, index));
            }
            output.push(field(leaves, view, tokens, first..index)?);
            first = index;
        }
        if let TokenKind::Symbol(s) = &tokens[index].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" => stack.push(")"),
                "{" | ".{" => stack.push("}"),
                "[" => stack.push("]"),
                "⦃" => stack.push("⦄"),
                "⟨" => stack.push("⟩"),
                ")" | "}" | "]" | "⦄" | "⟩"
                    if stack.pop() != Some(crate::canonical_bracket(s.as_str())) =>
                {
                    return Err(refuse(view, tokens, index));
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

/// Keep the Reference's `extends` / `structParent` node shapes. Commas
/// nested in a parent type do not split the parent list.
fn parents(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    start: usize,
    end: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    if start == end {
        return Ok(null_node(Vec::new()));
    }
    if !symbol(tokens, start, "extends") {
        return Err(refuse(view, tokens, start));
    }
    let mut rows = Vec::new();
    let mut first = start + 1;
    let mut stack = Vec::new();
    for index in start + 1..=end {
        if index == end || (stack.is_empty() && symbol(tokens, index, ",")) {
            let mut type_start = first;
            let name = if matches!(
                tokens.get(first).map(|t| &t.kind),
                Some(TokenKind::Ident(_))
            ) && symbol(tokens, first + 1, ":")
            {
                type_start += 2;
                null_node(vec![leaves.leaf(first)?, leaves.leaf(first + 1)?])
            } else {
                null_node(Vec::new())
            };
            if type_start >= index {
                return Err(refuse(view, tokens, type_start));
            }
            rows.push(Syntax::node(
                parser_kind(&["Command", "structParent"]),
                vec![
                    name,
                    bounded_type(
                        leaves,
                        view,
                        tokens,
                        type_start..index,
                        DefinitionGrammar::Scalar,
                    )?,
                ],
            ));
            if index < end {
                rows.push(leaves.leaf(index)?);
            }
            first = index + 1;
        } else if let TokenKind::Symbol(s) = &tokens[index].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" => stack.push(")"),
                "{" | ".{" => stack.push("}"),
                "[" => stack.push("]"),
                "⦃" => stack.push("⦄"),
                "⟨" => stack.push("⟩"),
                ")" | "}" | "]" | "⦄" | "⟩"
                    if stack.pop() != Some(crate::canonical_bracket(s.as_str())) =>
                {
                    return Err(refuse(view, tokens, index));
                }
                _ => {}
            }
        }
    }
    if !stack.is_empty() {
        return Err(refuse(view, tokens, end));
    }
    Ok(null_node(vec![Syntax::node(
        parser_kind(&["Command", "extends"]),
        vec![leaves.leaf(start)?, null_node(rows), null_node(Vec::new())],
    )]))
}

/// `structure`/`class` after its `declModifiers`: `prefix` is where the doc comment, the
/// attributes and the modifier keywords end, the last being the keyword's token.
pub(super) fn parse(
    view: SourceView,
    tokens: Vec<LexedToken>,
    prefix: (usize, usize, usize),
) -> Result<ParsedDefinition, NatDefinitionParseError> {
    let (doc_end, attributes_end, keyword) = prefix;
    let is_class = symbol(&tokens, keyword, "class");
    if !matches!(
        tokens.get(keyword + 1).map(|t| &t.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(refuse(&view, &tokens, keyword + 1));
    }
    let (universe_suffix, cursor) = levels::declaration_suffix(&view, &tokens, keyword + 2)?;
    let (groups, cursor) = bounded_binders(&view, &tokens, cursor, DefinitionGrammar::Scalar)?;
    let end_body = deriving_start(&tokens, cursor);
    let body_tokens = &tokens[..end_body];
    let end_result = if symbol(&tokens, cursor, ":") {
        type_end(body_tokens, cursor, "where").min(type_end(body_tokens, cursor, "extends"))
    } else {
        cursor
    };
    let end_header = if symbol(&tokens, end_result, "extends") {
        type_end(body_tokens, end_result, "where")
    } else {
        end_result
    };
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    let parameters =
        bounded_binder_syntax(&leaves, &view, &tokens, groups, DefinitionGrammar::Scalar)?;
    let result = optional_type(&leaves, &view, &tokens, cursor..end_result)?;
    let inheritance = parents(&leaves, &view, &tokens, end_result, end_header)?;
    let body = if end_header == end_body {
        null_node(Vec::new())
    } else {
        if !symbol(&tokens, end_header, "where") {
            return Err(refuse(&view, &tokens, end_header));
        }
        // `structCtor := declModifiers ident " :: "`: the constructor's own name, after its doc
        // comment and visibility if any (which otherwise lead the first field).
        let mut name = end_header + 1;
        let doc = doc_at(&tokens, name).then_some(name);
        name += usize::from(doc.is_some());
        let visibility = ["private", "protected"]
            .into_iter()
            .find(|word| symbol(&tokens, name, word))
            .map(|word| (word, name));
        name += usize::from(visibility.is_some());
        let named_ctor = matches!(tokens.get(name).map(|t| &t.kind), Some(TokenKind::Ident(_)))
            && symbol(&tokens, name + 1, "::");
        let ctor = if named_ctor {
            let mut ctor_modifiers = modifiers_with_doc(&view, &leaves, &tokens, doc)?;
            if let (Some((word, at)), Syntax::Node { args, .. }) = (visibility, &mut ctor_modifiers)
            {
                let slot = if word == "protected" { 3 } else { 2 };
                args[slot] = null_node(vec![Syntax::node(
                    parser_kind(&["Command", word]),
                    vec![leaves.leaf(at)?],
                )]);
            }
            null_node(vec![Syntax::node(
                parser_kind(&["Command", "structCtor"]),
                vec![
                    ctor_modifiers,
                    leaves.leaf(name)?,
                    null_node(Vec::new()),
                    leaves.leaf(name + 1)?,
                ],
            )])
        } else {
            null_node(Vec::new())
        };
        let first_field = if named_ctor { name + 2 } else { end_header + 1 };
        // Fields are indented past the command's start, its modifiers included.
        let fields = fields(&leaves, &view, body_tokens, 0, first_field)?;
        null_node(vec![
            leaves.leaf(end_header)?,
            ctor,
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
                vec![leaves.leaf(keyword)?],
            ),
            Syntax::node(
                parser_kind(&["Command", "declId"]),
                vec![
                    leaves.leaf(keyword + 1)?,
                    levels::declaration_syntax(&leaves, universe_suffix)?,
                ],
            ),
            Syntax::node(
                parser_kind(&["Command", "optDeclSig"]),
                vec![null_node(parameters), result],
            ),
            inheritance,
            body,
            deriving_suffix(&leaves, &view, &tokens, end_body)?,
        ],
    );
    let modifiers =
        crate::declaration_modifiers(&view, &leaves, &tokens, doc_end, attributes_end, keyword)?;
    Ok(ParsedDefinition {
        source_view: view,
        syntax: Syntax::node(
            parser_kind(&["Command", "declaration"]),
            vec![modifiers, structure],
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
            "structure A extends where x : Nat",
            "structure A where\nx : Nat",
            "structure A where\n  x : Nat\n y : Nat",
            "structure A where\n  x : Nat :=",
            "structure A where\n  x : Nat\nderiving",
            "structure A where\n  x Nat",
            "class A where\n  x : (Nat",
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
            // A named constructor and no fields (`structCtor`), which the elaborator refuses.
            "structure A where\n  mk ::",
        ] {
            assert!(parse_definition(text.as_bytes()).is_ok(), "refused {text}");
        }
    }

    #[test]
    fn deriving_preserves_handlers_and_original_bytes() {
        for text in [
            "structure Point where\r\n  x : Nat\r\n  deriving Inhabited, Repr\r\n",
            "structure Empty deriving Inhabited",
            "structure Child extends Parent deriving Inhabited",
        ] {
            let parsed = parse_definition(text.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                text.replace("\r\n", "\n").as_bytes()
            );
        }
        for text in [
            "structure A deriving Inhabited,",
            "structure A deriving Inhabited Repr",
            "structure A deriving , Inhabited",
        ] {
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
        }
    }
    #[test]
    fn inherited_records_preserve_parent_types_projection_names_and_source_bytes() {
        for text in [
            "structure Tagged (A : Type) extends Box A where\n  tag : Nat",
            "class Rich (A : Type) : Type extends toValue : Value A, More A where\n  tag : Nat",
            "structure Child extends Parent",
            "-- header\r\nstructure C extends -- first\r\n  left : Box (Nat -> Nat), -- second\r\n  Right where\r\n  x : Nat\r\n",
        ] {
            let parsed =
                parse_definition(text.as_bytes()).unwrap_or_else(|e| panic!("{text}: {e:?}"));
            assert_eq!(parsed.reconstruct_original(), text.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                text.replace("\r\n", "\n").as_bytes()
            );
            assert!(parse_nat_definition(text.as_bytes()).is_err());
        }
    }

    #[test]
    fn malformed_parent_clauses_do_not_drop_tokens() {
        for text in [
            "structure C extends",
            "structure C extends , A",
            "structure C extends A,",
            "structure C extends A,,B",
            "structure C extends p :",
            "structure C extends A Nat : Type",
            "structure C extends (A",
            "structure C extends A)",
        ] {
            assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
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
