//! `conv` blocks (`Init/Conv.lean`): `"conv" (" at " ident)? (" in " (occs)? term)? " => "
//! convSeq`, where `convSeq` is `sepByIndent conv "; "`. The conv tactics read are the ones the
//! corpus uses most: `lhs`, `rhs`, `congr`, `arg n`, `enter [n, …]`, `ext x …`, `rw [rules]`,
//! `simp`, `apply e` and a nested `· convSeq`; any other is refused where it starts. The
//! elaborator does not run conv mode: it refuses the block.
use super::*;

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}

fn word(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    crate::term_locals::word(tokens, at, text)
}

fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let pos = tokens[at].extent.start();
    let source = view.normalized();
    pos.0
        - source
            .line_start(source.line_of(pos))
            .expect("token line")
            .0
}

fn starts_line(view: &SourceView, tokens: &[LexedToken], at: usize) -> bool {
    at > 0
        && view.normalized().line_of(tokens[at].extent.start())
            > view.normalized().line_of(tokens[at - 1].extent.end())
}

fn conv_kind(name: &str) -> Name {
    parser_kind(&["Tactic", "Conv", name])
}

/// The `conv` tactic over `range`, `keyword` its first token's atom.
#[inline(never)]
pub(super) fn tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let mut depth = 0usize;
    let mut arrow = None;
    for at in start + 1..range.end {
        if depth == 0 && symbol(tokens, at, "=>") {
            arrow = Some(at);
            break;
        }
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    let Some(arrow) = arrow else {
        return Err(refusal(view, tokens, start));
    };
    let mut next = start + 1;
    let at_slot = if word(tokens, next, "at")
        && matches!(
            tokens.get(next + 1).map(|t| &t.kind),
            Some(TokenKind::Ident(_))
        ) {
        next += 2;
        null_node(vec![leaves.leaf(next - 2)?, leaves.leaf(next - 1)?])
    } else {
        null_node(Vec::new())
    };
    let in_slot = if symbol(tokens, next, "in") && next + 1 < arrow {
        let term = bounded_term(
            leaves,
            view,
            tokens,
            next + 1..arrow,
            DefinitionGrammar::Scalar,
        )?;
        let slot = null_node(vec![leaves.leaf(next)?, null_node(Vec::new()), term]);
        next = arrow;
        slot
    } else {
        null_node(Vec::new())
    };
    if next != arrow {
        return Err(refusal(view, tokens, next));
    }
    let body = sequence(leaves, view, tokens, arrow + 1..range.end)?;
    Ok(Syntax::node(
        conv_kind("conv"),
        vec![keyword, at_slot, in_slot, leaves.leaf(arrow)?, body],
    ))
}

/// `convSeq1Indented := sepByIndent conv "; "`: conv tactics separated by `;` or by a line at the
/// first one's column (the pin's empty separator).
fn sequence(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    let base = column(view, tokens, range.start);
    let mut items = Vec::new();
    let mut item = range.start;
    let mut depth = 0usize;
    for at in range.start..=range.end {
        let boundary = at == range.end
            || depth == 0
                && (symbol(tokens, at, ";")
                    || at > item
                        && starts_line(view, tokens, at)
                        && column(view, tokens, at) == base);
        if boundary {
            items.push(conv_tactic(leaves, view, tokens, item..at)?);
            if at < range.end {
                if symbol(tokens, at, ";") {
                    items.push(leaves.leaf(at)?);
                    item = at + 1;
                } else {
                    items.push(null_node(Vec::new()));
                    item = at;
                }
            }
            continue;
        }
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(Syntax::node(
        conv_kind("convSeq"),
        vec![Syntax::node(
            conv_kind("convSeq1Indented"),
            vec![null_node(items)],
        )],
    ))
}

/// `argArg := "@"? "-"? num` with only the numeral.
fn arg_arg(leaves: &Leaves, at: usize) -> Result<Syntax, NatDefinitionParseError> {
    Ok(Syntax::node(
        conv_kind("argArg"),
        vec![
            null_node(Vec::new()),
            null_node(Vec::new()),
            Syntax::node(Name::str(Name::anonymous(), "num"), vec![leaves.leaf(at)?]),
        ],
    ))
}

/// `macro:1 x:conv tk:" <;> " y:conv:0 : conv` (`Init/Conv.lean`): the operands between the
/// item's top-level `<;>`s, nested to the right (the right operand is at precedence 0).
fn conv_tactic(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut separators = Vec::new();
    let mut depth = 0usize;
    for at in range.clone() {
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                "<;>" if depth == 0 => separators.push(at),
                _ => {}
            }
        }
    }
    let mut operands = Vec::new();
    let mut operand = range.start;
    for &separator in separators.iter().chain(std::iter::once(&range.end)) {
        operands.push(conv_operand(leaves, view, tokens, operand..separator)?);
        operand = separator + 1;
    }
    let mut chain = operands.pop().expect("one operand at least");
    for (left, separator) in operands.into_iter().zip(separators).rev() {
        chain = Syntax::node(
            conv_kind("conv_<;>_"),
            vec![left, leaves.leaf(separator)?, chain],
        );
    }
    Ok(chain)
}

fn conv_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let number = |at: usize| {
        matches!(
            tokens.get(at).map(|t| &t.kind),
            Some(TokenKind::Literal(LiteralKind::Nat))
        )
    };
    let atom = |at: usize, text: &str| -> Result<Syntax, NatDefinitionParseError> {
        Ok(Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: text.to_owned(),
        })
    };
    if range.is_empty() {
        return Err(refusal(view, tokens, start));
    }
    // `syntax (name := skip) "skip" : conv` (`Init/Conv.lean`), and the others' leaves.
    for name in ["lhs", "rhs", "congr", "skip"] {
        if word(tokens, start, name) && range.len() == 1 {
            return Ok(Syntax::node(conv_kind(name), vec![atom(start, name)?]));
        }
    }
    if word(tokens, start, "arg") && range.len() == 2 && number(start + 1) {
        return Ok(Syntax::node(
            conv_kind("arg"),
            vec![atom(start, "arg")?, arg_arg(leaves, start + 1)?],
        ));
    }
    if word(tokens, start, "enter")
        && range.len() >= 4
        && symbol(tokens, start + 1, "[")
        && symbol(tokens, range.end - 1, "]")
    {
        let mut args = Vec::new();
        let mut at = start + 2;
        while at < range.end - 1 {
            if !number(at) {
                return Err(refusal(view, tokens, at));
            }
            args.push(Syntax::node(
                conv_kind("enterArg"),
                vec![arg_arg(leaves, at)?],
            ));
            at += 1;
            if at < range.end - 1 {
                if !symbol(tokens, at, ",") {
                    return Err(refusal(view, tokens, at));
                }
                args.push(leaves.leaf(at)?);
                at += 1;
            }
        }
        return Ok(Syntax::node(
            conv_kind("enter"),
            vec![
                atom(start, "enter")?,
                leaves.leaf(start + 1)?,
                null_node(args),
                leaves.leaf(range.end - 1)?,
            ],
        ));
    }
    if word(tokens, start, "ext")
        && range.len() >= 2
        && (start + 1..range.end).all(|at| matches!(&tokens[at].kind, TokenKind::Ident(_)))
    {
        let names = (start + 1..range.end)
            .map(|at| {
                Ok(Syntax::node(
                    Name::from_components(["Lean", "binderIdent"]),
                    vec![leaves.leaf(at)?],
                ))
            })
            .collect::<Result<Vec<_>, NatDefinitionParseError>>()?;
        return Ok(Syntax::node(
            conv_kind("ext"),
            vec![atom(start, "ext")?, null_node(names)],
        ));
    }
    if word(tokens, start, "rw") {
        // `"rw " optConfig rwRuleSeq` (`Conv.convRw__`): the tactic's rules, with no location.
        let keyword = atom(start, "rw")?;
        let rewritten = rewrite(leaves, view, tokens, range, keyword, "rw")?;
        let Syntax::Node { args, .. } = &rewritten else {
            return Err(refusal(view, tokens, start));
        };
        let [keyword, config, rules, location] = args.as_slice() else {
            return Err(refusal(view, tokens, start));
        };
        if !matches!(location, Syntax::Node { args, .. } if args.is_empty()) {
            return Err(refusal(view, tokens, start));
        }
        return Ok(Syntax::node(
            conv_kind("convRw__"),
            vec![keyword.clone(), config.clone(), rules.clone()],
        ));
    }
    // `"· " convSeq` (`conv·_`): a nested sequence, focused on the first goal.
    if symbol(tokens, start, "·") || symbol(tokens, start, ".") {
        let dot = leaves.leaf(start)?;
        return Ok(Syntax::node(
            conv_kind("conv·_"),
            vec![dot, sequence(leaves, view, tokens, start + 1..range.end)?],
        ));
    }
    // `"apply " term` (`convApply_`).
    if word(tokens, start, "apply") && range.len() > 1 {
        let term = bounded_term(
            leaves,
            view,
            tokens,
            start + 1..range.end,
            DefinitionGrammar::Scalar,
        )?;
        return Ok(Syntax::node(
            conv_kind("convApply_"),
            vec![atom(start, "apply")?, term],
        ));
    }
    // `simp`'s slots without a location (`Conv.simp`).
    if word(tokens, start, "simp") {
        let keyword = atom(start, "simp")?;
        let simplified = simplify(leaves, view, tokens, range, keyword, "simp")?;
        let Syntax::Node { args, .. } = &simplified else {
            return Err(refusal(view, tokens, start));
        };
        let [keyword, config, discharger, only, rules, location] = args.as_slice() else {
            return Err(refusal(view, tokens, start));
        };
        if !matches!(location, Syntax::Node { args, .. } if args.is_empty()) {
            return Err(refusal(view, tokens, start));
        }
        return Ok(Syntax::node(
            conv_kind("simp"),
            vec![
                keyword.clone(),
                config.clone(),
                discharger.clone(),
                only.clone(),
                rules.clone(),
            ],
        ));
    }
    Err(refusal(view, tokens, start))
}
