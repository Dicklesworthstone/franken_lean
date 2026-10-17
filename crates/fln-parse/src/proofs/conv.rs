//! `conv` blocks (`Init/Conv.lean`): `"conv" (" at " ident)? (" in " (occs)? term)? " => "
//! convSeq`, where `convSeq` is `sepByIndent conv "; "`. The conv tactics read are the ones the
//! corpus uses most: the one-keyword ones (`lhs`, `congr`, `whnf`, `left`, `rfl`, …), `arg n`,
//! `enter [n, …]`, `ext x …`, `intro x …`, `unfold f …`, `delta f …`, `rw [rules]`,
//! `rewrite`, `simp`, `apply e`, `change e`, `tactic => tacs`, `first | … | …` and a nested
//! `· convSeq`; any other is refused where it starts. A `(conv| …)` quotation holds one of them.
//! The elaborator does not run conv mode: it refuses the block.
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
    if range.len() == 1
        && let Some(&(name, kind)) = KEYWORDS.iter().find(|(name, _)| word(tokens, start, name))
    {
        return Ok(Syntax::node(conv_kind(kind), vec![atom(start, name)?]));
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
    // `"ext" (ppSpace colGt binderIdent)*` (`Conv.ext`) and the macro `"intro"` of the same shape
    // (`convIntro___`), where `binderIdent := ident <|> hole`.
    for (name, kind) in [("ext", "ext"), ("intro", "convIntro___")] {
        if word(tokens, start, name) {
            let mut names = Vec::new();
            for at in start + 1..range.end {
                let binder = if symbol(tokens, at, "_") {
                    Syntax::node(parser_kind(&["Term", "hole"]), vec![leaves.leaf(at)?])
                } else if matches!(&tokens[at].kind, TokenKind::Ident(_)) {
                    leaves.leaf(at)?
                } else {
                    return Err(refusal(view, tokens, at));
                };
                names.push(Syntax::node(
                    Name::from_components(["Lean", "binderIdent"]),
                    vec![binder],
                ));
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
