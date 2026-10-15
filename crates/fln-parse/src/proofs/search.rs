//! `solve_by_elim`'s selected-lemma grammar from the pinned Init/Tactics.lean.
//! Keep the six optional slots and each argument's category node; terms use
//! the ordinary bounded parser, never token-spelling lookup in the elaborator.
use super::*;

fn kind(name: &str) -> Name {
    parser_kind(&["Tactic", "SolveByElim", name])
}

fn symbol(tokens: &[LexedToken], at: usize, text: &str) -> bool {
    matches!(tokens.get(at).map(|token| &token.kind), Some(TokenKind::Symbol(word)) if word == text)
}

#[inline(never)]
pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let mut at = range.start + 1;
    let all_goals = if at < range.end && symbol(tokens, at, "*") {
        let slot = null_node(vec![leaves.leaf(at)?]);
        at += 1;
        slot
    } else {
        null_node(Vec::new())
    };
    let (config, after_config) = config(leaves, view, tokens, at, range.end)?;
    if after_config != at {
        // Selected lemmas are supported, configurable search is not yet.
        return Err(refusal(view, tokens, at));
    }
    at = after_config;
    let only = if at < range.end
        && matches!(&tokens[at].kind, TokenKind::Ident(name) if *name == Name::from_components(["only"]))
    {
        let slot = null_node(vec![Syntax::Atom {
            info: leaves.leaf(at)?.info(),
            val: "only".into(),
        }]);
        at += 1;
        slot
    } else {
        null_node(Vec::new())
    };
    let arguments = if at < range.end && symbol(tokens, at, "[") {
        let close = rcases::closing(tokens, at)
            .filter(|&close| close < range.end && symbol(tokens, close, "]"))
            .ok_or_else(|| refusal(view, tokens, at))?;
        let mut rows = Vec::new();
        if close > at + 1 {
            for item in comma_separated(tokens, at + 1..close) {
                if item.is_empty() {
                    // sepBy allows a final comma, never a leading/doubled one.
                    if item.start == close && !rows.is_empty() {
                        break;
                    }
                    return Err(refusal(view, tokens, item.start));
                }
                let end = item.end;
                let argument = argument(leaves, view, tokens, item)?;
                rows.push(Syntax::node(kind("arg"), vec![argument]));
                if end < close {
                    rows.push(leaves.leaf(end)?);
                }
            }
        }
        let result = null_node(vec![Syntax::node(
            kind("args"),
            vec![leaves.leaf(at)?, null_node(rows), leaves.leaf(close)?],
        )]);
        at = close + 1;
        result
    } else {
        null_node(Vec::new())
    };
    // Label-attribute lookup is not implemented. Never accept and ignore a
    // `using` suffix (nor an arbitrary trailing token).
    if at != range.end {
        return Err(refusal(view, tokens, at));
    }
    Ok(Syntax::node(
        parser_kind(&["Tactic", "solveByElim"]),
        vec![
            keyword,
            all_goals,
            config,
            only,
            arguments,
            null_node(Vec::new()),
        ],
    ))
}

fn argument(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    item: Range<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    if symbol(tokens, item.start, "*") {
        if item.len() != 1 {
            return Err(refusal(view, tokens, item.start + 1));
        }
        return Ok(Syntax::node(kind("star"), vec![leaves.leaf(item.start)?]));
    }
    let erase = symbol(tokens, item.start, "-");
    let first = item.start + usize::from(erase);
    if first >= item.end {
        return Err(refusal(view, tokens, item.end));
    }
    if erase {
        // The pin's erase takes term:max, not an unparenthesized application.
        let end = match &tokens[first].kind {
            TokenKind::Ident(_) => first + 1,
            TokenKind::Symbol(word) if crate::canonical_bracket(word) == "(" => {
                rcases::closing(tokens, first)
                    .map(|close| close + 1)
                    .ok_or_else(|| refusal(view, tokens, first))?
            }
            _ => return Err(refusal(view, tokens, first)),
        };
        if end != item.end {
            return Err(refusal(view, tokens, end));
        }
    }
    let term = bounded_term(
        leaves,
        view,
        tokens,
        first..item.end,
        DefinitionGrammar::Scalar,
    )?;
    Ok(if erase {
        Syntax::node(kind("erase"), vec![leaves.leaf(item.start)?, term])
    } else {
        term
    })
}
