//! `conv` blocks (`Init/Conv.lean`): `"conv" (" at " ident)? (" in " (occs)? term)? " => "
//! convSeq`, where `convSeq` is `sepByIndent conv "; "` or `"{" … "}"`. The conv tactics read
//! are the one-keyword ones (`lhs`, `congr`, `whnf`, `left`, `rfl`, …), `arg (@)?(-)?n`,
//! `enter [n, @n, x, in p, …]`, `ext x …`, `intro x …`, `unfold f …`, `delta f …`, `rw [rules]`,
//! `rewrite`, `simp`, `dsimp`, `apply e`, `change e`, `pattern (occs)? p`, `clear h …`,
//! `tactic => tacs`, `first | … | …`, `try`, `repeat`, `fail_if_success`, a nested `conv => …`,
//! `· convSeq`, `{ … }`, `( … )` and `calc`; any other is refused where it starts. A tactic
//! ending in a sequence of its own takes the `;`-separated tactics after it, as the pin's
//! `sepByIndent` does. Columns count codepoints. A `(conv| …)` quotation holds one of them.
use super::*;

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Symbol(s)) if s == text)
}

fn word(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    crate::term_locals::word(tokens, at, text)
}

/// The token's column in codepoints, as the pin's positions count it: `· lhs` puts `lhs` at
/// the column of a line indented by four spaces under it, though `·` is two bytes.
fn column(view: &SourceView, tokens: &[LexedToken], at: usize) -> usize {
    let pos = tokens[at].extent.start();
    let source = view.normalized();
    let start = source
        .line_start(source.line_of(pos))
        .expect("token line")
        .0;
    source
        .as_str()
        .get(start..pos.0)
        .map_or(pos.0 - start, |prefix| prefix.chars().count())
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
        let (occs, after) = occurrences(leaves, view, tokens, next + 1, arrow)?;
        if after >= arrow {
            return Err(refusal(view, tokens, after));
        }
        let term = bounded_term(
            leaves,
            view,
            tokens,
            after..arrow,
            DefinitionGrammar::Scalar,
        )?;
        let slot = null_node(vec![leaves.leaf(next)?, occs, term]);
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

/// The conv tactic of a `(conv| …)` quotation (`conv.quot`).
pub(super) fn quoted(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    conv_tactic(leaves, view, tokens, range)
}

/// `occs := atomic("(" &"occs") " := " (occsWildcard <|> occsIndexed) ") "` at `at`, if there is
/// one before `limit`: the optional slot holding it, and where the term after it starts.
fn occurrences(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    at: usize,
    limit: usize,
) -> Result<(Syntax, usize), NatDefinitionParseError> {
    if !(symbol(tokens, at, "(") && word(tokens, at + 1, "occs") && symbol(tokens, at + 2, ":=")) {
        return Ok((null_node(Vec::new()), at));
    }
    let atom = |at: usize, text: &str| -> Result<Syntax, NatDefinitionParseError> {
        Ok(Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: text.to_owned(),
        })
    };
    let mut close = at + 3;
    while close < limit && !symbol(tokens, close, ")") {
        close += 1;
    }
    if close >= limit || close == at + 3 {
        return Err(refusal(view, tokens, close.min(limit.saturating_sub(1))));
    }
    let inner = if symbol(tokens, at + 3, "*") {
        if close != at + 4 {
            return Err(refusal(view, tokens, at + 4));
        }
        Syntax::node(conv_kind("occsWildcard"), vec![leaves.leaf(at + 3)?])
    } else {
        let mut numbers = Vec::new();
        for index in at + 3..close {
            if !matches!(tokens[index].kind, TokenKind::Literal(LiteralKind::Nat)) {
                return Err(refusal(view, tokens, index));
            }
            numbers.push(Syntax::node(
                Name::str(Name::anonymous(), "num"),
                vec![leaves.leaf(index)?],
            ));
        }
        Syntax::node(conv_kind("occsIndexed"), vec![null_node(numbers)])
    };
    let occs = Syntax::node(
        conv_kind("occs"),
        vec![
            leaves.leaf(at)?,
            atom(at + 1, "occs")?,
            leaves.leaf(at + 2)?,
            inner,
            leaves.leaf(close)?,
        ],
    );
    Ok((null_node(vec![occs]), close + 1))
}

/// The index of the bracket closing the one at `open`, before `limit`.
fn closing(tokens: &[LexedToken], open: usize, limit: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (at, token) in tokens.iter().enumerate().take(limit).skip(open) {
        if let TokenKind::Symbol(s) = &token.kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return Some(at);
                    }
                }
                _ => {}
            }
        }
    }
    None
}

/// `convSeq := convSeqBracketed <|> convSeq1Indented`, where `convSeqBracketed := "{"
/// sepByIndentSemicolon(conv) "}"` and `convSeq1Indented := sepByIndent conv "; "`: conv tactics
/// separated by `;` or by a line at the first one's column (the pin's empty separator).
fn sequence(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if range.is_empty() {
        return Err(refusal(view, tokens, range.start));
    }
    if symbol(tokens, range.start, "{")
        && closing(tokens, range.start, range.end) == Some(range.end - 1)
    {
        return Ok(Syntax::node(
            conv_kind("convSeq"),
            vec![bracketed(leaves, view, tokens, range)?],
        ));
    }
    Ok(Syntax::node(
        conv_kind("convSeq"),
        vec![Syntax::node(
            conv_kind("convSeq1Indented"),
            vec![null_node(items(leaves, view, tokens, range)?)],
        )],
    ))
}

/// `convSeqBracketed := "{" sepByIndentSemicolon(conv) "}"` over `range`, its braces included.
fn bracketed(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let inner = range.start + 1..range.end - 1;
    let rows = if inner.is_empty() {
        Vec::new()
    } else {
        items(leaves, view, tokens, inner)?
    };
    Ok(Syntax::node(
        conv_kind("convSeqBracketed"),
        vec![
            leaves.leaf(range.start)?,
            null_node(rows),
            leaves.leaf(range.end - 1)?,
        ],
    ))
}

/// The tactics and separators of a `sepByIndent conv "; "` over `range`.
fn items(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Vec<Syntax>, NatDefinitionParseError> {
    let base = column(view, tokens, range.start);
    let mut items = Vec::new();
    let mut item = range.start;
    let mut depth = 0usize;
    for at in range.start..=range.end {
        // A tactic ending in a sequence of its own (`conv => s`, `· s`, `try s`, `first | s`,
        // `tactic => t`, …) takes the `;`-separated tactics after it into that sequence.
        let boundary = at == range.end
            || depth == 0
                && (symbol(tokens, at, ";") && !takes_sequence(tokens, item)
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
    Ok(items)
}

/// Whether the conv tactic at `at` ends in a sequence (`convSeq` or `tacticSeq`) of its own.
fn takes_sequence(tokens: &[LexedToken], at: usize) -> bool {
    symbol(tokens, at, "·")
        || symbol(tokens, at, ".")
        || ["try", "repeat", "fail_if_success", "first"]
            .iter()
            .any(|keyword| word(tokens, at, keyword))
        || ["conv", "tactic", "tactic'"]
            .iter()
            .any(|keyword| word(tokens, at, keyword) && symbol(tokens, at + 1, "=>"))
}

/// `argArg := "@"? "-"? num` at `at`, if there is one: the node and the index after it.
fn arg_arg(
    leaves: &Leaves,
    tokens: &[LexedToken],
    at: usize,
) -> Result<Option<(Syntax, usize)>, NatDefinitionParseError> {
    let mut next = at;
    let explicit = if symbol(tokens, next, "@") {
        next += 1;
        null_node(vec![leaves.leaf(next - 1)?])
    } else {
        null_node(Vec::new())
    };
    let negative = if symbol(tokens, next, "-") {
        next += 1;
        null_node(vec![leaves.leaf(next - 1)?])
    } else {
        null_node(Vec::new())
    };
    if !matches!(
        tokens.get(next).map(|t| &t.kind),
        Some(TokenKind::Literal(LiteralKind::Nat))
    ) {
        return Ok(None);
    }
    Ok(Some((
        Syntax::node(
            conv_kind("argArg"),
            vec![
                explicit,
                negative,
                Syntax::node(
                    Name::str(Name::anonymous(), "num"),
                    vec![leaves.leaf(next)?],
                ),
            ],
        ),
        next + 1,
    )))
}

/// `binderIdent := ident <|> hole` at `at`.
fn binder_ident(
    leaves: &Leaves,
    tokens: &[LexedToken],
    at: usize,
) -> Result<Option<Syntax>, NatDefinitionParseError> {
    let binder = if symbol(tokens, at, "_") {
        Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(at)?])
    } else if matches!(tokens.get(at).map(|t| &t.kind), Some(TokenKind::Ident(_))) {
        leaves.leaf(at)?
    } else {
        return Ok(None);
    };
    Ok(Some(Syntax::node(
        Name::from_components(["Lean", "binderIdent"]),
        vec![binder],
    )))
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

/// The conv tactics that are one keyword (`syntax (name := skip) "skip" : conv`, `Init/Conv.lean`)
/// and the one-keyword macros (`macro "left" : conv`, kind `convLeft`): spelling, kind.
const KEYWORDS: [(&str, &str); 16] = [
    ("lhs", "lhs"),
    ("rhs", "rhs"),
    ("congr", "congr"),
    ("skip", "skip"),
    ("cbv", "cbv"),
    ("fun", "fun"),
    ("whnf", "whnf"),
    ("zeta", "zeta"),
    ("reduce", "reduce"),
    ("simp_match", "simpMatch"),
    ("rfl", "convRfl"),
    ("done", "convDone"),
    ("trace_state", "convTrace_state"),
    ("args", "convArgs"),
    ("left", "convLeft"),
    ("right", "convRight"),
];

fn conv_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let atom = |at: usize, text: &str| -> Result<Syntax, NatDefinitionParseError> {
        Ok(Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: text.to_owned(),
        })
    };
    if range.is_empty() {
        return Err(refusal(view, tokens, start));
    }
    if range.len() == 1
        && let Some(&(name, kind)) = KEYWORDS.iter().find(|(name, _)| word(tokens, start, name))
    {
        return Ok(Syntax::node(conv_kind(kind), vec![atom(start, name)?]));
    }
    // `"arg " argArg` (`Conv.arg`), `argArg := "@"? "-"? num`.
    if word(tokens, start, "arg")
        && let Some((argument, next)) = arg_arg(leaves, tokens, start + 1)?
        && next == range.end
    {
        return Ok(Syntax::node(
            conv_kind("arg"),
            vec![atom(start, "arg")?, argument],
        ));
    }
    // `"enter" " [" enterArg,+ "]"` (`Conv.enter`), `enterArg := binderIdent <|> argArg <|>
    // enterPattern` and `enterPattern := "in " (occs)? term`.
    if word(tokens, start, "enter")
        && range.len() >= 4
        && symbol(tokens, start + 1, "[")
        && symbol(tokens, range.end - 1, "]")
    {
        let close = range.end - 1;
        let mut args = Vec::new();
        let mut at = start + 2;
        while at < close {
            // The argument runs to the next top-level comma.
            let mut end = at;
            let mut depth = 0usize;
            while end < close && !(depth == 0 && symbol(tokens, end, ",")) {
                if let TokenKind::Symbol(s) = &tokens[end].kind {
                    match crate::canonical_bracket(s.as_str()) {
                        "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                        ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                        _ => {}
                    }
                }
                end += 1;
            }
            if end == at {
                return Err(refusal(view, tokens, at));
            }
            let inner = if let Some((argument, next)) = arg_arg(leaves, tokens, at)?
                && next == end
            {
                argument
            } else if end == at + 1
                && let Some(binder) = binder_ident(leaves, tokens, at)?
            {
                binder
            } else if symbol(tokens, at, "in") {
                let (occs, after) = occurrences(leaves, view, tokens, at + 1, end)?;
                if after >= end {
                    return Err(refusal(view, tokens, after.min(end)));
                }
                let term =
                    bounded_term(leaves, view, tokens, after..end, DefinitionGrammar::Scalar)?;
                Syntax::node(
                    conv_kind("enterPattern"),
                    vec![leaves.leaf(at)?, occs, term],
                )
            } else {
                return Err(refusal(view, tokens, at));
            };
            args.push(Syntax::node(conv_kind("enterArg"), vec![inner]));
            at = end;
            if at < close {
                args.push(leaves.leaf(at)?);
                at += 1;
                if at == close {
                    return Err(refusal(view, tokens, at));
                }
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
    // `"ext" (ppSpace colGt binderIdent)*` (`Conv.ext`) and the macro `"intro"` of the same shape
    // (`convIntro___`), where `binderIdent := ident <|> hole`.
    for (name, kind) in [("ext", "ext"), ("intro", "convIntro___")] {
        if word(tokens, start, name) {
            let mut names = Vec::new();
            for at in start + 1..range.end {
                let Some(binder) = binder_ident(leaves, tokens, at)? else {
                    return Err(refusal(view, tokens, at));
                };
                names.push(binder);
            }
            return Ok(Syntax::node(
                conv_kind(kind),
                vec![atom(start, name)?, null_node(names)],
            ));
        }
    }
    // `"unfold" (ppSpace colGt ident)+` (`Conv.unfold`) and `"delta"` of the same shape.
    for name in ["unfold", "delta"] {
        if word(tokens, start, name) && range.len() > 1 {
            let mut names = Vec::new();
            for at in start + 1..range.end {
                if !matches!(&tokens[at].kind, TokenKind::Ident(_)) {
                    return Err(refusal(view, tokens, at));
                }
                names.push(leaves.leaf(at)?);
            }
            return Ok(Syntax::node(
                conv_kind(name),
                vec![atom(start, name)?, null_node(names)],
            ));
        }
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
    // `"apply " term` (the macro `convApply_`) and `"change " term` (`Conv.change`).
    for (name, kind) in [("apply", "convApply_"), ("change", "change")] {
        if word(tokens, start, name) && range.len() > 1 {
            let term = bounded_term(
                leaves,
                view,
                tokens,
                start + 1..range.end,
                DefinitionGrammar::Scalar,
            )?;
            return Ok(Syntax::node(
                conv_kind(kind),
                vec![atom(start, name)?, term],
            ));
        }
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
    // `"tactic" " => " tacticSeq` (`Conv.nestedTactic`) and `"tactic'" " => " tacticSeq`
    // (`Conv.nestedTacticCore`).
    for (name, kind) in [("tactic", "nestedTactic"), ("tactic'", "nestedTacticCore")] {
        if word(tokens, start, name) && symbol(tokens, start + 1, "=>") && range.len() > 2 {
            return Ok(Syntax::node(
                conv_kind(kind),
                vec![
                    atom(start, name)?,
                    leaves.leaf(start + 1)?,
                    tactic_seq(leaves, view, tokens, start + 2..range.end)?,
                ],
            ));
        }
    }
    if word(tokens, start, "rewrite") && range.len() > 1 {
        return rewrite_operand(leaves, view, tokens, range, atom(start, "rewrite")?);
    }
    if word(tokens, start, "first") && symbol(tokens, start + 1, "|") {
        return first_operand(leaves, view, tokens, range, atom(start, "first")?);
    }
    extended_operand(leaves, view, tokens, range)
}

/// The conv tactics beyond [`conv_operand`]'s: `dsimp`, `pattern`, `clear`, a nested `conv =>`,
/// `try`, `repeat`, `fail_if_success`, `{ … }`, `( … )` and `calc`.
#[inline(never)]
fn extended_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    let atom = |at: usize, text: &str| -> Result<Syntax, NatDefinitionParseError> {
        Ok(Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: text.to_owned(),
        })
    };
    // `"dsimp" optConfig (discharger)? (&" only")? (" [" (simpErase <|> simpLemma),* "]")?`
    // (`Conv.dsimp`): `dsimp`'s slots without a location.
    if word(tokens, start, "dsimp") {
        let keyword = atom(start, "dsimp")?;
        let simplified = simplify(leaves, view, tokens, range, keyword, "dsimp")?;
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
            conv_kind("dsimp"),
            vec![
                keyword.clone(),
                config.clone(),
                discharger.clone(),
                only.clone(),
                rules.clone(),
            ],
        ));
    }
    // `"pattern " (occs)? term` (`Conv.pattern`).
    if word(tokens, start, "pattern") && range.len() > 1 {
        let (occs, after) = occurrences(leaves, view, tokens, start + 1, range.end)?;
        if after >= range.end {
            return Err(refusal(view, tokens, after.min(range.end - 1)));
        }
        let term = bounded_term(
            leaves,
            view,
            tokens,
            after..range.end,
            DefinitionGrammar::Scalar,
        )?;
        return Ok(Syntax::node(
            conv_kind("pattern"),
            vec![atom(start, "pattern")?, occs, term],
        ));
    }
    // `"clear" (ppSpace colGt term:max)+` (`Conv.clear`), its terms the locals' names.
    if word(tokens, start, "clear") && range.len() > 1 {
        let mut names = Vec::new();
        for at in start + 1..range.end {
            if !matches!(&tokens[at].kind, TokenKind::Ident(_)) {
                return Err(refusal(view, tokens, at));
            }
            names.push(leaves.leaf(at)?);
        }
        return Ok(Syntax::node(
            conv_kind("clear"),
            vec![atom(start, "clear")?, null_node(names)],
        ));
    }
    // `"conv" " => " convSeq` (`Conv.convConvSeq`).
    if word(tokens, start, "conv") && symbol(tokens, start + 1, "=>") && range.len() > 2 {
        return Ok(Syntax::node(
            conv_kind("convConvSeq"),
            vec![
                atom(start, "conv")?,
                leaves.leaf(start + 1)?,
                sequence(leaves, view, tokens, start + 2..range.end)?,
            ],
        ));
    }
    // `macro "try " t:convSeq : conv` (`convTry_`), `syntax "repeat " convSeq : conv`
    // (`convRepeat_`) and `macro "fail_if_success " convSeq : conv` (`Conv.failIfSuccess`).
    for (name, kind) in [
        ("try", "convTry_"),
        ("repeat", "convRepeat_"),
        ("fail_if_success", "failIfSuccess"),
    ] {
        if word(tokens, start, name) && range.len() > 1 {
            return Ok(Syntax::node(
                conv_kind(kind),
                vec![
                    atom(start, name)?,
                    sequence(leaves, view, tokens, start + 1..range.end)?,
                ],
            ));
        }
    }
    // `convSeqBracketed` (`Conv.nestedConv`) and `"(" convSeq ")"` (`Conv.paren`).
    if symbol(tokens, start, "{") && closing(tokens, start, range.end) == Some(range.end - 1) {
        return Ok(Syntax::node(
            conv_kind("nestedConv"),
            vec![bracketed(leaves, view, tokens, range)?],
        ));
    }
    if symbol(tokens, start, "(")
        && closing(tokens, start, range.end) == Some(range.end - 1)
        && range.len() > 2
    {
        return Ok(Syntax::node(
            conv_kind("paren"),
            vec![
                leaves.leaf(start)?,
                sequence(leaves, view, tokens, start + 1..range.end - 1)?,
                leaves.leaf(range.end - 1)?,
            ],
        ));
    }
    // `macro tk:"calc" steps:calcSteps : conv` (`Lean.convCalc_`, `Init/NotationExtra.lean`).
    if symbol(tokens, start, "calc") {
        let (calculation, end) =
            super::elimination::calculation(leaves, view, tokens, start, range.end)?;
        if end != range.end {
            return Err(refusal(view, tokens, end));
        }
        let Syntax::Node { args, .. } = &calculation else {
            return Err(refusal(view, tokens, start));
        };
        return Ok(Syntax::node(
            Name::from_components(["Lean", "convCalc_"]),
            args.clone(),
        ));
    }
    Err(refusal(view, tokens, start))
}

/// `"rewrite" optConfig rwRuleSeq` (`Conv.rewrite`), its configuration and rules read, or, in a
/// quotation, antiquotations of both (`rewrite $c:optConfig $s`, the `rw` macro's template).
fn rewrite_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start;
    if symbol(tokens, start + 1, "$") {
        // Only a configuration named as one: an antiquotation with no kind would be read as the
        // configuration's too, which is not established here.
        if !(symbol(tokens, start + 3, ":") && word(tokens, start + 4, "optConfig")) {
            return Err(refusal(view, tokens, start + 1));
        }
        let position = crate::quotations::Position::OptConfig;
        let Some((config, next)) =
            crate::quotations::antiquotation(leaves, view, tokens, start + 1, range.end, position)?
        else {
            return Err(refusal(view, tokens, start + 1));
        };
        let position = crate::quotations::Position::RwRuleSeq;
        let Some((rules, end)) =
            crate::quotations::antiquotation(leaves, view, tokens, next, range.end, position)?
        else {
            return Err(refusal(view, tokens, next));
        };
        if end != range.end {
            return Err(refusal(view, tokens, end));
        }
        return Ok(Syntax::node(
            conv_kind("rewrite"),
            vec![keyword, config, rules],
        ));
    }
    let rewritten = rewrite(leaves, view, tokens, range, keyword, "rewrite")?;
    let Syntax::Node { args, .. } = &rewritten else {
        return Err(refusal(view, tokens, start));
    };
    let [keyword, config, rules, location] = args.as_slice() else {
        return Err(refusal(view, tokens, start));
    };
    if !matches!(location, Syntax::Node { args, .. } if args.is_empty()) {
        return Err(refusal(view, tokens, start));
    }
    Ok(Syntax::node(
        conv_kind("rewrite"),
        vec![keyword.clone(), config.clone(), rules.clone()],
    ))
}

/// `"first " withPosition((ppDedent(ppLine) colGe "| " convSeq)+)` (`Conv.first`): each
/// alternative a `group` of its `|` and its sequence, or, in a quotation, an antiquotation of one
/// (`first | $t | skip`).
fn first_operand(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut pipes = Vec::new();
    let mut depth = 0usize;
    for at in range.start + 1..range.end {
        if depth == 0 && symbol(tokens, at, "|") {
            pipes.push(at);
        }
        if let TokenKind::Symbol(s) = &tokens[at].kind {
            match crate::canonical_bracket(s.as_str()) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    let mut alternatives = Vec::new();
    for (index, &pipe) in pipes.iter().enumerate() {
        let end = pipes.get(index + 1).copied().unwrap_or(range.end);
        if pipe + 1 >= end {
            return Err(refusal(view, tokens, pipe + 1));
        }
        let position = crate::quotations::Position::ConvSeq;
        let body = match crate::quotations::antiquotation(
            leaves,
            view,
            tokens,
            pipe + 1,
            end,
            position,
        )? {
            Some((antiquotation, next)) if next == end => antiquotation,
            _ => sequence(leaves, view, tokens, pipe + 1..end)?,
        };
        alternatives.push(Syntax::node(
            Name::from_components(["group"]),
            vec![leaves.leaf(pipe)?, body],
        ));
    }
    Ok(Syntax::node(
        conv_kind("first"),
        vec![keyword, null_node(alternatives)],
    ))
}
