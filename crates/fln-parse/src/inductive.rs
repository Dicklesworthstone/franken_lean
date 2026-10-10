//! Native single-family inductive syntax, retaining every original token leaf.
//! Index telescopes and constructor results are retained; unsupported mutual
//! blocks and deriving handlers are not dropped or repaired.
use super::*;
use std::ops::Range;

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}
fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::InductiveConstructor,
    }
}
/// `rawIdent` at `at`: an identifier, or a keyword spelled as one (`| return : σ → T`), named by its
/// text.
fn raw_ident(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    at: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let token = tokens.get(at).ok_or_else(|| refuse(view, tokens, at))?;
    match &token.kind {
        TokenKind::Ident(_) => Ok(leaves.leaf(at)?),
        TokenKind::Symbol(text) if crate::spells_identifier(text) => Ok(Syntax::Ident {
            info: leaves.leaf(at)?.info(),
            raw_val: token.extent,
            val: Name::from_components([text.as_str()]),
            preresolved: Vec::new(),
        }),
        _ => Err(refuse(view, tokens, at)),
    }
}

fn ctor(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    // `ctor := optional docComment >> "| " >> declModifiers >> rawIdent >> optDeclSig`
    // (`Lean/Parser/Command.lean`): a constructor's doc comes before its `|`.
    let doc = if symbol(tokens, range.start, "/--") {
        // `doc_comment_syntax` is already the optional slot: `null[docComment]`.
        crate::doc_comment_syntax(view, leaves, tokens, range.start)?
    } else {
        null_node(vec![])
    };
    let start = range.start + usize::from(symbol(tokens, range.start, "/--"));
    if !symbol(tokens, start, "|") {
        return Err(refuse(view, tokens, start));
    }
    // `declModifiers` after the `|`: a doc comment (`| /-- … -/ first`), then `private` or
    // `protected`.
    let inner_doc = symbol(tokens, start + 1, "/--").then_some(start + 1);
    let mut name = start + 1 + usize::from(inner_doc.is_some());
    let visibility = ["private", "protected"]
        .into_iter()
        .find(|word| symbol(tokens, name, word))
        .map(|word| (word, name));
    name += usize::from(visibility.is_some());
    let modifiers = records::modifiers_with(view, leaves, tokens, inner_doc, visibility)?;
    let name_syntax = raw_ident(leaves, view, tokens, name)?;
    let (groups, end) = bounded_binders(
        view,
        &tokens[..range.end],
        name + 1,
        DefinitionGrammar::Scalar,
    )?;
    let binders = bounded_binder_syntax(leaves, view, tokens, groups, DefinitionGrammar::Scalar)?;
    let result = records::optional_type(leaves, view, tokens, end..range.end)?;
    Ok(Syntax::node(
        parser_kind(&["Command", "ctor"]),
        vec![
            doc,
            leaves.leaf(start)?,
            modifiers,
            name_syntax,
            Syntax::node(
                parser_kind(&["Command", "optDeclSig"]),
                vec![null_node(binders), result],
            ),
        ],
    ))
}

/// `inductive` at token `keyword` of `prefix` (the doc comment's end, the attributes' end and the
/// keyword, as `declaration_prefix` finds them).
pub(super) fn parse(
    view: SourceView,
    tokens: Vec<LexedToken>,
    prefix: (usize, usize, usize),
) -> Result<ParsedDefinition, NatDefinitionParseError> {
    let (doc_end, attributes_end, keyword) = prefix;
    if !matches!(
        tokens.get(keyword + 1).map(|t| &t.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(refuse(&view, &tokens, keyword + 1));
    }
    let (universe_suffix, cursor) = levels::declaration_suffix(&view, &tokens, keyword + 2)?;
    let (groups, cursor) = bounded_binders(&view, &tokens, cursor, DefinitionGrammar::Scalar)?;
    let end_body = records::deriving_start(&tokens, cursor);
    let mut end_header = cursor;
    let mut nesting = Vec::new();
    while end_header < end_body {
        // Without `where`, the first constructor's doc comment ends the header (`ctor` opens
        // with `optional docComment`).
        if nesting.is_empty()
            && (symbol(&tokens, end_header, "where")
                || symbol(&tokens, end_header, ":=")
                || symbol(&tokens, end_header, "|")
                || symbol(&tokens, end_header, "/--"))
        {
            break;
        }
        if let TokenKind::Symbol(s) = &tokens[end_header].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" => nesting.push(")"),
                "{" | ".{" => nesting.push("}"),
                "[" => nesting.push("]"),
                "⦃" => nesting.push("⦄"),
                "⟨" => nesting.push("⟩"),
                ")" | "}" | "]" | "⦄" | "⟩"
                    if nesting.pop() != Some(crate::canonical_bracket(s.as_str())) =>
                {
                    return Err(refuse(&view, &tokens, end_header));
                }
                _ => {}
            }
        }
        end_header += 1;
    }
    if !nesting.is_empty() {
        return Err(refuse(&view, &tokens, end_header));
    }
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    let params = bounded_binder_syntax(&leaves, &view, &tokens, groups, DefinitionGrammar::Scalar)?;
    let result = records::optional_type(&leaves, &view, &tokens, cursor..end_header)?;
    let body_keyword = if symbol(&tokens, end_header, "where") || symbol(&tokens, end_header, ":=")
    {
        let keyword = null_node(vec![leaves.leaf(end_header)?]);
        end_header += 1;
        keyword
    } else {
        null_node(vec![])
    };
    let mut begins = Vec::new();
    for at in end_header..end_body {
        if nesting.is_empty() && symbol(&tokens, at, "|") {
            // A constructor's doc comment begins it.
            let doc = at > end_header && symbol(&tokens, at - 1, "/--");
            begins.push(if doc { at - 1 } else { at });
        }
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" => nesting.push(")"),
                "{" | ".{" => nesting.push("}"),
                "[" => nesting.push("]"),
                "⦃" => nesting.push("⦄"),
                "⟨" => nesting.push("⟩"),
                ")" | "}" | "]" | "⦄" | "⟩" => {
                    if nesting.pop() != Some(crate::canonical_bracket(s.as_str())) {
                        return Err(refuse(&view, &tokens, at));
                    }
                }
                "deriving" | "where" => return Err(refuse(&view, &tokens, at)),
                _ => {}
            }
        }
    }
    if !nesting.is_empty() || (end_header < end_body && begins.first() != Some(&end_header)) {
        return Err(refuse(&view, &tokens, end_header));
    }
    begins.push(end_body);
    let ctors = begins
        .windows(2)
        .map(|w| ctor(&leaves, &view, &tokens, w[0]..w[1]))
        .collect::<Result<Vec<_>, _>>()?;
    let command = Syntax::node(
        parser_kind(&["Command", "inductive"]),
        vec![
            leaves.leaf(keyword)?,
            Syntax::node(
                parser_kind(&["Command", "declId"]),
                vec![
                    leaves.leaf(keyword + 1)?,
                    levels::declaration_syntax(&leaves, universe_suffix)?,
                ],
            ),
            Syntax::node(
                parser_kind(&["Command", "optDeclSig"]),
                vec![null_node(params), result],
            ),
            body_keyword,
            null_node(ctors),
            null_node(vec![]),
            records::deriving_suffix(&leaves, &view, &tokens, end_body)?,
        ],
    );
    let modifiers =
        crate::declaration_modifiers(&view, &leaves, &tokens, doc_end, attributes_end, keyword)?;
    Ok(ParsedDefinition {
        source_view: view,
        syntax: Syntax::node(
            parser_kind(&["Command", "declaration"]),
            vec![modifiers, command],
        ),
        epilogue,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn constructor_syntax_retains_comments_crlf_and_declared_results() {
        let text = "-- item\r\ninductive Choice (A : Type) where\r\n | none : Choice A\r\n | some (value : A) : Choice A\r\n";
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            text.replace("\r\n", "\n").as_bytes()
        );
        assert!(parse_nat_definition(text.as_bytes()).is_err());
    }
    #[test]
    fn constructors_and_later_declarations_have_distinct_boundaries() {
        let source = b"inductive Flag where | off | on\ndef selected : Flag := Flag.on";
        assert_eq!(partition_definition_commands(source).unwrap().len(), 2);
        for source in [
            "inductive X where |",
            "inductive X where | c (x : Nat",
            "inductive X where | c deriving",
        ] {
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn deriving_follows_the_complete_constructor_telescope() {
        let text = "inductive Choice (A : Type) where\r\n | value (a : A)\r\n | empty\r\n deriving Inhabited, Repr\r\n";
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            text.replace("\r\n", "\n").as_bytes()
        );
    }
}
