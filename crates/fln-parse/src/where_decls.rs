//! A definition's trailing `where` block: `Term.whereDecls`, `"where" >> sepByIndent
//! letRecDecl "; "` (`Lean/Parser/Term.lean`), in `declValSimple`'s last slot.
//!
//! Each declaration is `name binders [: type] := value`, the `letIdDecl` form of `let rec`;
//! declarations are separated by a new line at the first declaration's column. The pin
//! elaborates the block as `let rec` declarations scoping over the body
//! (`Lean.Elab.expandWhereDecls`); equation-style declarations (`| …`) are refused here.
use super::*;

fn refuse(view: &SourceView, tokens: &[LexedToken], at: usize) -> NatDefinitionParseError {
    NatDefinitionParseError::OutsideSeedGrammar {
        at: original_position(view, tokens, at),
        expected: NatDefinitionExpectation::LocalAssignment,
    }
}

fn opens(tokens: &[LexedToken], at: usize) -> bool {
    matches!(&tokens[at].kind, TokenKind::Symbol(s) if matches!(crate::canonical_bracket(s.as_str()), "(" | "{" | ".{" | "[" | "⦃" | "⟨"))
}

fn closes(tokens: &[LexedToken], at: usize) -> bool {
    matches!(&tokens[at].kind, TokenKind::Symbol(s) if matches!(crate::canonical_bracket(s.as_str()), ")" | "}" | "]" | "⦄" | "⟩"))
}

/// The `where` keyword ending a definition body that starts at `from`, if any: the first
/// `where` outside every bracket.
pub(super) fn start(tokens: &[LexedToken], from: usize) -> Option<usize> {
    let mut depth = 0usize;
    for at in from..tokens.len() {
        if opens(tokens, at) {
            depth += 1;
        } else if closes(tokens, at) {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "where") {
            return Some(at);
        }
    }
    None
}

fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let source = view.normalized();
    let pos = tokens[at].extent.start();
    pos.0
        - source
            .line_start(source.line_of(pos))
            .map_or(0, |start| start.0)
}

fn line(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    view.normalized().line_of(tokens[at].extent.start())
}

/// The `Term.whereDecls` node for the block whose `where` keyword is at `keyword`.
pub(super) fn syntax(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    keyword: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let starts = declaration_starts(view, tokens, keyword)?;
    let mut items = Vec::with_capacity(starts.len() * 2);
    for (index, &name) in starts.iter().enumerate() {
        let end = starts.get(index + 1).copied().unwrap_or(tokens.len());
        if index > 0 {
            // `sepByIndent`'s separator: absent when the next declaration is on its own line.
            items.push(null_node(Vec::new()));
        }
        items.push(declaration(leaves, view, tokens, name, end)?);
    }
    Ok(Syntax::node(
        parser_kind(&["Term", "whereDecls"]),
        vec![
            leaves.leaf(keyword)?,
            null_node(items),
            null_node(Vec::new()),
        ],
    ))
}

/// One `letRecDecl` spanning `name..end`.
fn declaration(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    name: usize,
    end: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let (parameters, mut cursor) =
        bounded_binders(view, tokens, name + 1, DefinitionGrammar::Scalar)?;
    let explicit_type =
        if cursor < end && matches!(&tokens[cursor].kind, TokenKind::Symbol(s) if s == ":") {
            let colon = cursor;
            let mut type_end = type_end(tokens, colon + 1, ":=").min(end);
            // A declaration defined by equations ends its type at the first alternative's `|`,
            // unless a `match` in the type owns it.
            let pipe = crate::type_end(tokens, colon + 1, "|").min(end);
            if !crate::top_level_match(tokens, colon + 1, pipe) {
                type_end = type_end.min(pipe);
            }
            cursor = type_end;
            null_node(vec![Syntax::node(
                parser_kind(&["Term", "typeSpec"]),
                vec![
                    leaves.leaf(colon)?,
                    bounded_type(
                        leaves,
                        view,
                        tokens,
                        colon + 1..type_end,
                        DefinitionGrammar::Scalar,
                    )?,
                ],
            )])
        } else {
            null_node(Vec::new())
        };
    // `letEqnsDecl := letIdLhs matchAlts` (`Lean/Parser/Term.lean`): `go : T | p => e | …`.
    if cursor < end && matches!(&tokens[cursor].kind, TokenKind::Symbol(s) if s == "|") {
        let alternatives = matching::declaration_equations(
            leaves,
            view,
            tokens,
            cursor..end,
            DefinitionGrammar::Scalar,
        )?;
        let declaration = Syntax::node(
            parser_kind(&["Term", "letEqnsDecl"]),
            vec![
                Syntax::node(parser_kind(&["Term", "letId"]), vec![leaves.leaf(name)?]),
                null_node(bounded_binder_syntax(
                    leaves,
                    view,
                    tokens,
                    parameters,
                    DefinitionGrammar::Scalar,
                )?),
                explicit_type,
                alternatives,
            ],
        );
        return Ok(rec_declaration(declaration));
    }
    if cursor >= end || !matches!(&tokens[cursor].kind, TokenKind::Symbol(s) if s == ":=") {
        return Err(refuse(view, tokens, cursor.min(end)));
    }
    let assignment = cursor;
    if assignment + 1 >= end {
        return Err(refuse(view, tokens, end));
    }
    let value = bounded_term(
        leaves,
        view,
        tokens,
        assignment + 1..end,
        DefinitionGrammar::Scalar,
    )?;
    let declaration = Syntax::node(
        parser_kind(&["Term", "letIdDecl"]),
        vec![
            Syntax::node(parser_kind(&["Term", "letId"]), vec![leaves.leaf(name)?]),
            null_node(bounded_binder_syntax(
                leaves,
                view,
                tokens,
                parameters,
                DefinitionGrammar::Scalar,
            )?),
            explicit_type,
            leaves.leaf(assignment)?,
            value,
        ],
    );
    Ok(rec_declaration(declaration))
}

/// A `letRecDecl` around one `letIdDecl` or `letEqnsDecl`, with no attributes or termination
/// hints.
fn rec_declaration(declaration: Syntax) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "letRecDecl"]),
        vec![
            null_node(Vec::new()),
            null_node(Vec::new()),
            Syntax::node(parser_kind(&["Term", "letDecl"]), vec![declaration]),
            Syntax::node(
                parser_kind(&["Termination", "suffix"]),
                vec![null_node(Vec::new()), null_node(Vec::new())],
            ),
        ],
    )
}

/// `instance … where fields` (`Command.whereStructInst`, `"where" structInstFields
/// optDeriving`): one `structInstField` per field, `name binders [: type] := value`, delimited like
/// `where` declarations. The elaborator reads it as the structure instance `{ fields }`,
/// with a field's binders abstracted over its value.
pub(super) fn struct_instance(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    keyword: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    let starts = declaration_starts(view, tokens, keyword)?;
    let mut fields = Vec::with_capacity(starts.len() * 2);
    for (index, &name) in starts.iter().enumerate() {
        let end = starts.get(index + 1).copied().unwrap_or(tokens.len());
        if index > 0 {
            fields.push(null_node(Vec::new()));
        }
        fields.push(struct_field(leaves, view, tokens, name, end)?);
    }
    Ok(Syntax::node(
        parser_kind(&["Command", "whereStructInst"]),
        vec![
            leaves.leaf(keyword)?,
            Syntax::node(
                parser_kind(&["Term", "structInstFields"]),
                vec![null_node(fields)],
            ),
            null_node(Vec::new()),
        ],
    ))
}

/// The first token of each item of a `where` block: a name at the first item's column,
/// on a later line, outside every bracket.
fn declaration_starts(
    view: &SourceView,
    tokens: &[LexedToken],
    keyword: usize,
) -> Result<Vec<usize>, NatDefinitionParseError> {
    let first = keyword + 1;
    if !matches!(
        tokens.get(first).map(|t| &t.kind),
        Some(TokenKind::Ident(_))
    ) {
        return Err(refuse(view, tokens, first));
    }
    let indent = column(view, tokens, first);
    let mut starts = vec![first];
    let mut depth = 0usize;
    for at in first + 1..tokens.len() {
        if opens(tokens, at) {
            depth += 1;
        } else if closes(tokens, at) {
            depth = depth.saturating_sub(1);
        } else if depth == 0
            && matches!(tokens[at].kind, TokenKind::Ident(_))
            && line(view, tokens, at) > line(view, tokens, at - 1)
            && column(view, tokens, at) == indent
        {
            starts.push(at);
        }
    }
    Ok(starts)
}

/// Reuse the ordinary structure-field telescope grammar. Each annotation and
/// body is parsed on the term parser's heap frames; this driver only locates
/// the enclosing header delimiter within this field's indentation boundary.
fn struct_field(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    name: usize,
    end: usize,
) -> Result<Syntax, NatDefinitionParseError> {
    // A field defined by equations (`toString | true => "t" | false => "f"`):
    // `structInstFieldEqns` over the alternatives (`Lean/Parser/Term.lean`).
    if matches!(tokens.get(name + 1).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == "|") {
        let alternatives = matching::declaration_equations(
            leaves,
            view,
            tokens,
            name + 1..end,
            DefinitionGrammar::Scalar,
        )?;
        return Ok(Syntax::node(
            parser_kind(&["Term", "structInstField"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "structInstLVal"]),
                    vec![leaves.leaf(name)?, null_node(Vec::new())],
                ),
                null_node(vec![
                    null_node(Vec::new()),
                    null_node(Vec::new()),
                    Syntax::node(
                        parser_kind(&["Term", "structInstFieldEqns"]),
                        vec![null_node(Vec::new()), alternatives],
                    ),
                ]),
            ],
        ));
    }
    let mut cursor = name + 1;
    let mut prefix = term_binders::Prefix::field(leaves, view, tokens, name, &mut cursor, end)?;
    while !prefix.body() {
        let start = cursor;
        let mut depth = 0usize;
        while cursor < end {
            if depth == 0 && prefix.closes_header(tokens, cursor) {
                break;
            }
            if opens(tokens, cursor) {
                depth += 1;
            } else if closes(tokens, cursor) {
                if depth == 0 {
                    return Err(refuse(view, tokens, cursor));
                }
                depth -= 1;
            }
            cursor += 1;
        }
        if cursor == start || cursor == end {
            return Err(refuse(view, tokens, cursor));
        }
        let domain = bounded_term(
            leaves,
            view,
            tokens,
            start..cursor,
            DefinitionGrammar::Scalar,
        )?;
        (prefix, cursor) = prefix.finish_header(leaves, view, tokens, cursor, domain, end)?;
    }
    if cursor >= end {
        return Err(refuse(view, tokens, end));
    }
    let body = bounded_term(leaves, view, tokens, cursor..end, DefinitionGrammar::Scalar)?;
    prefix.finish(leaves, body).map(|(field, _)| field)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nodes<'a>(syntax: &'a Syntax, kind: &Name, output: &mut Vec<&'a [Syntax]>) {
        if let Syntax::Node {
            kind: actual, args, ..
        } = syntax
        {
            if actual == kind {
                output.push(args);
            }
            for arg in args {
                nodes(arg, kind, output);
            }
        }
    }

    fn children(syntax: &Syntax) -> &[Syntax] {
        let Syntax::Node { args, .. } = syntax else {
            panic!("expected a syntax node");
        };
        args
    }

    #[test]
    fn where_fields_preserve_wildcards_binder_groups_and_result_annotations() {
        let source = "instance printer : Printer Nat where\r\n  -- parameter comments\r\n  reprPrec _ (prec : Nat) : Std.Format := Std.Format.text \"ok\"\r\n  apply {A : Type} ⦃B : Type⦄ [Inhabited A] [i : Inhabited B] (value : A) := value\r\n";
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        let mut fields = Vec::new();
        nodes(
            parsed.syntax(),
            &parser_kind(&["Term", "structInstField"]),
            &mut fields,
        );
        assert_eq!(fields.len(), 2);
        let first = children(&fields[0][1]);
        let binders = children(&first[0]);
        assert!(matches!(&binders[0], Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Term", "hole"]) && args.len() == 1));
        assert!(matches!(&binders[1], Syntax::Node { kind, .. }
            if kind == &parser_kind(&["Term", "explicitBinder"])));
        let annotation = children(&first[1]);
        assert!(matches!(&annotation[0], Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Term", "typeSpec"]) && args.len() == 2));
        let second = children(&fields[1][1]);
        let binders = children(&second[0]);
        for (binder, expected) in binders.iter().zip([
            "implicitBinder",
            "strictImplicitBinder",
            "instBinder",
            "instBinder",
            "explicitBinder",
        ]) {
            assert!(matches!(binder, Syntax::Node { kind, .. }
                if kind == &parser_kind(&["Term", expected])));
        }
        assert_eq!(binders.len(), 5);
        assert!(children(&second[1]).is_empty());
    }

    #[test]
    fn where_field_annotations_keep_nested_typed_terms_inside_the_field() {
        for source in [
            "instance f : Factory where\n  make (f : (Nat → Nat)) (_ : Nat) : (Nat → Nat) := f",
            "instance f : Factory where\n  make (x) {A} [i : Inhabited A] := x",
            "instance f : Factory where\n  make (x : {A : Type} → A → A) := x\n  other _ : Nat := 1",
            "instance f : Factory where\n  make [C (Nat → Nat)] := fun x => x",
            "instance f : Factory where\n  make x : (let A := Nat; A) := x",
        ] {
            let parsed = parse_definition(source.as_bytes())
                .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        }
    }

    #[test]
    fn malformed_where_field_headers_refuse_at_their_own_boundary() {
        for source in [
            "instance f : Factory where\n  make (x : Nat] := x",
            "instance f : Factory where\n  make (x : ) := x",
            "instance f : Factory where\n  make [C Nat := x",
            "instance f : Factory where\n  make x : := x",
            "instance f : Factory where\n  make x : Nat\n  other := 1",
            "instance f : Factory where\n  make _ : Nat :=\n  other := 1",
            "instance f : Factory where\n  make (x : Nat) : Nat",
        ] {
            assert!(
                parse_definition(source.as_bytes()).is_err(),
                "accepted {source}"
            );
        }
        let source = "instance f : Factory where\r\n  make _ : Nat :=\r\n  other := 1";
        let error = parse_definition(source.as_bytes()).unwrap_err();
        assert!(
            matches!(error, NatDefinitionParseError::OutsideSeedGrammar { at, .. }
            if at == BytePos(source.find("other").unwrap()))
        );
    }
}
