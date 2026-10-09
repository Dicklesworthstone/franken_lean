//! The pin's command trees for the scope commands (`Lean/Parser/Command.lean`).
//!
//! [`super::parse`] reads what a scope command does to the environment; this module reads how the
//! pin's parser builds it. The two accept the same commands except where the checker does not
//! model what the tree says: a `section` with a header (`public`, `noncomputable`, `meta`,
//! `@[expose]`) has a tree here, and [`parse_source_command`] hands it to the checker as a command
//! it does not read, which refuses it.
use super::*;

/// The pin's tree for a scope command (`namespace`, `section`, `end`, `open`, `universe`,
/// `variable`, `include`, `omit`, `set_option`, `attribute`, a module doc, and
/// `open`/`set_option … in <command>`), or `None` for any other command or a form this module
/// does not build.
pub fn tree(source: &[u8]) -> Result<Option<Syntax>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    scope_tree(source, &view, &tokens)
}

/// The pin's tree for any command: a scope command's from [`tree`], every other command's from
/// [`parse_source_command`].
pub fn command_tree(source: &[u8]) -> Result<Syntax, DefinitionParseError> {
    match tree(source)? {
        Some(tree) => Ok(tree),
        None => parse_source_command(source).map(|parsed| parsed.syntax),
    }
}

#[inline(never)]
fn scope_tree(
    source: &[u8],
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<Syntax>, DefinitionParseError> {
    let Some(TokenKind::Symbol(keyword)) = tokens.first().map(|token| &token.kind) else {
        return Ok(None);
    };
    if keyword == "/-!" && tokens.len() == 1 {
        let leaves = Leaves::build(view.normalized(), tokens)?;
        return module_doc_syntax(view, &leaves, tokens, 0).map(Some);
    }
    let ident = |at: usize| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(_)));
    let idents = |from: usize, to: usize| from < to && (from..to).all(ident);
    let leaves = || Leaves::build(view.normalized(), tokens);
    let names = |leaves: &Leaves, from: usize, to: usize| -> Result<Syntax, DefinitionParseError> {
        Ok(null_node(
            (from..to)
                .map(|at| leaves.leaf(at))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    };
    let node = |kind: &str, args: Vec<Syntax>| Syntax::node(parser_kind(&["Command", kind]), args);
    // `variable`, `include` and `omit` may end at a top-level `in` before a command
    // (`Command.in`); the head is read up to it.
    let stop = if matches!(keyword.as_str(), "variable" | "include" | "omit") {
        let mut depth = 0usize;
        let mut stop = tokens.len();
        for (at, token) in tokens.iter().enumerate().skip(1) {
            if let TokenKind::Symbol(s) = &token.kind {
                match crate::canonical_bracket(s.as_str()) {
                    "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                    ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                    "in" if depth == 0 => {
                        stop = at;
                        break;
                    }
                    _ => {}
                }
            }
        }
        stop
    } else {
        tokens.len()
    };
    let tree = match keyword.as_str() {
        "namespace" if tokens.len() == 2 && ident(1) => {
            let leaves = leaves()?;
            node("namespace", vec![leaves.leaf(0)?, leaves.leaf(1)?])
        }
        // `"end" (ident (noWs "." noWs ident)?)?`: the optional partial trailing dot is not read.
        "end" if tokens.len() == 1 || tokens.len() == 2 && ident(1) => {
            let leaves = leaves()?;
            let name = if tokens.len() == 2 {
                null_node(vec![leaves.leaf(1)?, null_node(Vec::new())])
            } else {
                null_node(Vec::new())
            };
            node("end", vec![leaves.leaf(0)?, name])
        }
        "universe" | "include" if idents(1, stop) => {
            let leaves = leaves()?;
            node(keyword, vec![leaves.leaf(0)?, names(&leaves, 1, stop)?])
        }
        // `"omit" (ident <|> Term.instBinder)+`.
        "omit" => {
            let Ok((groups, end)) =
                crate::signature_binders(view, &tokens[..stop], 1, DefinitionGrammar::Scalar)
            else {
                return Ok(None);
            };
            if groups.is_empty()
                || end != stop
                || groups
                    .iter()
                    .any(|group| !matches!(group.kind, "bare" | "instBinder"))
            {
                return Ok(None);
            }
            let leaves = leaves()?;
            let items = crate::bounded_binder_syntax(
                &leaves,
                view,
                tokens,
                groups,
                DefinitionGrammar::Scalar,
            )?;
            node("omit", vec![leaves.leaf(0)?, null_node(items)])
        }
        "variable" => {
            let Ok(binders) = variables::parse_until(view, tokens, stop) else {
                return Ok(None);
            };
            let leaves = leaves()?;
            node("variable", vec![leaves.leaf(0)?, binders])
        }
        "attribute" => {
            let leaves = leaves()?;
            return attributes::command_syntax(view, tokens, &leaves);
        }
        "open" => return open(source, view, tokens),
        "set_option" => return set_option(source, view, tokens),
        _ => {
            let leaves = leaves()?;
            return Ok(section(&leaves, tokens)?.map(|(tree, _)| tree));
        }
    };
    if stop < tokens.len() {
        let leaves = leaves()?;
        return within(source, view, tokens, &leaves, tree, stop).map(Some);
    }
    Ok(Some(tree))
}

/// `section`: `sectionHeader "section" (ident)?`, with `sectionHeader := ("@[" "expose" "]")?
/// ("public")? ("noncomputable")? ("meta")?`, each optional slot a node of its own. Also returns
/// whether the header is not empty.
#[inline(never)]
fn section(
    leaves: &Leaves,
    tokens: &[LexedToken],
) -> Result<Option<(Syntax, bool)>, DefinitionParseError> {
    let word = |at: usize, text: &str| match tokens.get(at).map(|t| &t.kind) {
        Some(TokenKind::Symbol(s)) => s == text,
        Some(TokenKind::Ident(name)) => *name == Name::from_components([text]),
        _ => false,
    };
    let mut at = 0;
    let expose = word(0, "@[") && word(1, "expose") && word(2, "]");
    if expose {
        at = 3;
    }
    let mut slots = Vec::new();
    for keyword in ["public", "noncomputable", "meta"] {
        slots.push(word(at, keyword).then_some(at));
        if word(at, keyword) {
            at += 1;
        }
    }
    if !matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == "section") {
        return Ok(None);
    }
    let name = match tokens.len() - at {
        1 => None,
        2 if matches!(&tokens[at + 1].kind, TokenKind::Ident(_)) => Some(at + 1),
        _ => return Ok(None),
    };
    let atom = |at: usize, text: &str| -> Result<Syntax, DefinitionParseError> {
        Ok(Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: text.to_owned(),
        })
    };
    let mut header = vec![if expose {
        null_node(vec![leaves.leaf(0)?, atom(1, "expose")?, leaves.leaf(2)?])
    } else {
        null_node(Vec::new())
    }];
    for (slot, keyword) in slots.into_iter().zip(["public", "noncomputable", "meta"]) {
        header.push(match slot {
            Some(index) => null_node(vec![atom(index, keyword)?]),
            None => null_node(Vec::new()),
        });
    }
    let name = match name {
        Some(index) => null_node(vec![leaves.leaf(index)?]),
        None => null_node(Vec::new()),
    };
    Ok(Some((
        Syntax::node(
            parser_kind(&["Command", "section"]),
            vec![
                Syntax::node(parser_kind(&["Command", "sectionHeader"]), header),
                leaves.leaf(at)?,
                name,
            ],
        ),
        at > 0,
    )))
}

/// A scope command as its tree, for `parse_source_command`, which reaches it for a `section` with
/// a header (`public section`, `noncomputable section`, …): [`super::parse`] does not read one as
/// a scope, and the checker models neither the module system's visibility nor `noncomputable`
/// scopes, so it refuses the command. `None` for a command with no such tree.
pub(crate) fn unread(source: &[u8]) -> Result<Option<ParsedSourceCommand>, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let tokens = tokens(&view)?;
    let Some(syntax) = scope_tree(source, &view, &tokens)? else {
        return Ok(None);
    };
    let leaves = Leaves::build(view.normalized(), &tokens)?;
    let epilogue = leaves.attachment().epilogue();
    Ok(Some(ParsedSourceCommand {
        kind: SourceCommandKind::Definition,
        source_view: view,
        syntax,
        epilogue,
        query_term: None,
    }))
}

/// `open openDecl`, `openDecl := openHiding <|> openRenaming <|> openOnly <|> openSimple <|>
/// openScoped`, optionally followed by `in <command>`.
#[inline(never)]
fn open(
    source: &[u8],
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<Syntax>, DefinitionParseError> {
    let is = |at: usize, text: &str| matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text);
    // The declaration ends at a top-level `in` (no `in` can occur inside an `openDecl`).
    let end = (1..tokens.len())
        .find(|&at| is(at, "in"))
        .unwrap_or(tokens.len());
    let leaves = Leaves::build(view.normalized(), tokens)?;
    let Some(declaration) = open_declaration(&leaves, tokens, 1, end)? else {
        return Ok(None);
    };
    let node = |kind: &str, args: Vec<Syntax>| Syntax::node(parser_kind(&["Command", kind]), args);
    let command = node("open", vec![leaves.leaf(0)?, declaration]);
    if end == tokens.len() {
        return Ok(Some(command));
    }
    within(source, view, tokens, &leaves, command, end).map(Some)
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

/// `set_option ident optionValue`, `optionValue := "true" <|> "false" <|> str <|> num` (each a
/// non-reserved symbol or a literal), optionally followed by `in <command>`.
#[inline(never)]
fn set_option(
    source: &[u8],
    view: &SourceView,
    tokens: &[LexedToken],
) -> Result<Option<Syntax>, DefinitionParseError> {
    if tokens.len() < 3 || !matches!(&tokens[1].kind, TokenKind::Ident(_)) {
        return Ok(None);
    }
    let in_at = (tokens.len() > 3).then_some(3);
    if in_at.is_some_and(|at| {
        !matches!(&tokens[at].kind, TokenKind::Symbol(s) if s == "in") || tokens.len() == at + 1
    }) {
        return Ok(None);
    }
    let leaves = Leaves::build(view.normalized(), tokens)?;
    let value = match &tokens[2].kind {
        TokenKind::Ident(name)
            if *name == Name::from_components(["true"])
                || *name == Name::from_components(["false"]) =>
        {
            Syntax::Atom {
                info: leaves.leaf(2)?.info(),
                val: if *name == Name::from_components(["true"]) {
                    "true"
                } else {
                    "false"
                }
                .to_owned(),
            }
        }
        TokenKind::Literal(LiteralKind::Nat) => {
            Syntax::node(Name::str(Name::anonymous(), "num"), vec![leaves.leaf(2)?])
        }
        TokenKind::Literal(LiteralKind::Str) => {
            Syntax::node(Name::str(Name::anonymous(), "str"), vec![leaves.leaf(2)?])
        }
        _ => return Ok(None),
    };
    let command = Syntax::node(
        parser_kind(&["Command", "set_option"]),
        vec![
            leaves.leaf(0)?,
            leaves.leaf(1)?,
            null_node(Vec::new()),
            value,
        ],
    );
    match in_at {
        None => Ok(Some(command)),
        Some(at) => within(source, view, tokens, &leaves, command, at).map(Some),
    }
}

/// `Command.in`: `command`, the `in` at `in_at`, and the command after it. That command is read
/// in place, from a copy of the source whose prefix is blank, so its positions stay this command's
/// own; its first token then leads with what this command's own leaves give it (a comment, say),
/// not with the blanks.
#[inline(never)]
fn within(
    source: &[u8],
    view: &SourceView,
    tokens: &[LexedToken],
    leaves: &Leaves,
    command: Syntax,
    in_at: usize,
) -> Result<Syntax, DefinitionParseError> {
    // `open A in` with nothing after it is refused, not read past the last token.
    let Some(next) = tokens.get(in_at + 1) else {
        return Err(NatDefinitionParseError::OutsideSeedGrammar {
            at: BytePos(source.len()),
            expected: NatDefinitionExpectation::DefinitionKeyword,
        });
    };
    let inner_start = view.to_original(next.extent.start()).0;
    let mut blank = source.to_vec();
    // A byte-order mark is not text: blanking it would move every position after it.
    let skip = if source.starts_with(b"\xEF\xBB\xBF") {
        3
    } else {
        0
    };
    for byte in &mut blank[skip..inner_start] {
        if *byte != b'\n' && *byte != b'\r' {
            *byte = b' ';
        }
    }
    let mut inner = command_tree(&blank)?;
    if let (
        Some(SourceInfo::Original { leading, .. }),
        SourceInfo::Original {
            leading: actual, ..
        },
    ) = (first_leaf_info(&mut inner), leaves.leaf(in_at + 1)?.info())
    {
        *leading = actual;
    }
    Ok(Syntax::node(
        parser_kind(&["Command", "in"]),
        vec![command, leaves.leaf(in_at)?, inner],
    ))
}

/// The first leaf's source info, found without recursion and then reached by its path.
fn first_leaf_info(syntax: &mut Syntax) -> Option<&mut SourceInfo> {
    let mut path = Vec::new();
    let mut stack = vec![(syntax as &Syntax, Vec::<usize>::new())];
    while let Some((node, at)) = stack.pop() {
        match node {
            Syntax::Atom { .. } | Syntax::Ident { .. } => {
                path = at;
                break;
            }
            Syntax::Node { args, .. } => {
                for (index, arg) in args.iter().enumerate().rev() {
                    let mut next = at.clone();
                    next.push(index);
                    stack.push((arg, next));
                }
            }
            Syntax::Missing => {}
        }
    }
    let mut node = syntax;
    for index in path {
        let Syntax::Node { args, .. } = node else {
            return None;
        };
        node = args.get_mut(index)?;
    }
    match node {
        Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => Some(info),
        _ => None,
    }
}
