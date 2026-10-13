//! Native `guard_hyp` syntax, with the pin's separate optional type/value slots.
//!
//! The subject is a local identifier or a parenthesized term. Keeping each term
//! on the ordinary term parser preserves token leaves and source positions. An
//! unparenthesized type containing a top-level assignment is refused rather
//! than guessing whether that assignment belongs to the guard or to the type.

use super::*;

const TYPE_RELATIONS: [(&str, &str); 4] = [
    (":", "colonR"),
    (":~", "colonD"),
    (":ₛ", "colonS"),
    (":ₐ", "colonA"),
];
const VALUE_RELATIONS: [(&str, &str); 4] = [
    (":=", "colonEqR"),
    (":=~", "colonEqD"),
    (":=ₛ", "colonEqS"),
    (":=ₐ", "colonEqA"),
];

fn spelling(token: &LexedToken) -> Option<&str> {
    match &token.kind {
        TokenKind::Symbol(symbol) => Some(symbol.as_str()),
        _ => None,
    }
}

fn relation(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    at: usize,
    category: &str,
    choices: &[(&str, &str)],
) -> Result<Syntax, NatDefinitionParseError> {
    let kind = tokens
        .get(at)
        .and_then(spelling)
        .and_then(|word| choices.iter().find(|(text, _)| *text == word))
        .map(|(_, kind)| *kind)
        .ok_or_else(|| refusal(view, tokens, at))?;
    Ok(Syntax::node(
        parser_kind(&[category]),
        vec![Syntax::node(parser_kind(&[kind]), vec![leaves.leaf(at)?])],
    ))
}

#[inline(never)]
pub(super) fn parse(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    range: Range<usize>,
    keyword: Syntax,
) -> Result<Syntax, NatDefinitionParseError> {
    let start = range.start + 1;
    if start >= range.end {
        return Err(refusal(view, tokens, range.end));
    }
    // `term:max`: do not silently accept a bare application as the subject.
    let end = match &tokens[start].kind {
        TokenKind::Ident(_) => start + 1,
        TokenKind::Symbol(symbol) if crate::canonical_bracket(symbol) == "(" => {
            rcases::closing(tokens, start)
                .filter(|&close| close < range.end)
                .map(|close| close + 1)
                .ok_or_else(|| refusal(view, tokens, start))?
        }
        _ => return Err(refusal(view, tokens, start)),
    };
    let subject = bounded_term(leaves, view, tokens, start..end, DefinitionGrammar::Scalar)?;
    let mut type_slot = null_node(Vec::new());
    let mut value_slot = null_node(Vec::new());
    let mut cursor = end;
    if cursor < range.end
        && spelling(&tokens[cursor])
            .is_some_and(|word| TYPE_RELATIONS.iter().any(|(text, _)| *text == word))
    {
        let colon = relation(leaves, view, tokens, cursor, "colon", &TYPE_RELATIONS)?;
        let type_start = cursor + 1;
        let mut depth = 0_usize;
        cursor = range.end;
        for at in type_start..range.end {
            let Some(word) = spelling(&tokens[at]) else {
                continue;
            };
            match crate::canonical_bracket(word) {
                "(" | "[" | "{" | ".{" | "⦃" | "⟨" => depth += 1,
                ")" | "]" | "}" | "⦄" | "⟩" => {
                    depth = depth
                        .checked_sub(1)
                        .ok_or_else(|| refusal(view, tokens, at))?;
                }
                _ if depth == 0 && VALUE_RELATIONS.iter().any(|(text, _)| *text == word) => {
                    cursor = at;
                    break;
                }
                _ => {}
            }
        }
        if type_start == cursor {
            return Err(refusal(view, tokens, cursor));
        }
        let type_ = bounded_term(
            leaves,
            view,
            tokens,
            type_start..cursor,
            DefinitionGrammar::Scalar,
        )?;
        type_slot = null_node(vec![colon, type_]);
    }
    if cursor < range.end {
        let assign = relation(leaves, view, tokens, cursor, "colonEq", &VALUE_RELATIONS)?;
        if cursor + 1 >= range.end {
            return Err(refusal(view, tokens, range.end));
        }
        let value = bounded_term(
            leaves,
            view,
            tokens,
            cursor + 1..range.end,
            DefinitionGrammar::Scalar,
        )?;
        value_slot = null_node(vec![assign, value]);
    }
    Ok(Syntax::node(
        parser_kind(&["Tactic", "guardHyp"]),
        vec![keyword, subject, type_slot, value_slot],
    ))
}
