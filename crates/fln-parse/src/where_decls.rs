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
    matches!(&tokens[at].kind, TokenKind::Symbol(s) if matches!(s.as_str(), "(" | "{" | ".{" | "[" | "⦃" | "⟨"))
}

fn closes(tokens: &[LexedToken], at: usize) -> bool {
    matches!(&tokens[at].kind, TokenKind::Symbol(s) if matches!(s.as_str(), ")" | "}" | "]" | "⦄" | "⟩"))
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
            let type_end = type_end(tokens, colon + 1, ":=").min(end);
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
    Ok(Syntax::node(
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
    ))
}

/// `instance … where fields` (`Command.whereStructInst`, `"where" structInstFields
/// optDeriving`): one `structInstField` per field, `name binders := value`, delimited like
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
        // `name binder* := value`, binders bare names only.
        let mut cursor = name + 1;
        let mut binders = Vec::new();
        while cursor < end
            && matches!(&tokens[cursor].kind, TokenKind::Ident(_))
            && !matches!(&tokens[cursor].kind, TokenKind::Symbol(s) if s == ":=")
        {
            binders.push(leaves.leaf(cursor)?);
            cursor += 1;
        }
        if cursor >= end || !matches!(&tokens[cursor].kind, TokenKind::Symbol(s) if s == ":=") {
            return Err(refuse(view, tokens, cursor.min(end)));
        }
        if cursor + 1 >= end {
            return Err(refuse(view, tokens, end));
        }
        let value = bounded_term(
            leaves,
            view,
            tokens,
            cursor + 1..end,
            DefinitionGrammar::Scalar,
        )?;
        fields.push(Syntax::node(
            parser_kind(&["Term", "structInstField"]),
            vec![
                Syntax::node(
                    parser_kind(&["Term", "structInstLVal"]),
                    vec![leaves.leaf(name)?, null_node(Vec::new())],
                ),
                null_node(vec![
                    null_node(binders),
                    null_node(Vec::new()),
                    Syntax::node(
                        parser_kind(&["Term", "structInstFieldDef"]),
                        vec![leaves.leaf(cursor)?, null_node(Vec::new()), value],
                    ),
                ]),
            ],
        ));
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
