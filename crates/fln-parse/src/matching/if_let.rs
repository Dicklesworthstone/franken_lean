//! Pattern-test headers share the existing match-pattern parser and term plan.
//! No source text is fabricated and no nested term gains statement scope.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn condition(
    leaves: &Leaves,
    view: &SourceView,
    tokens: &[LexedToken],
    plan: &ConditionalPlan,
    grammar: DefinitionGrammar,
    splices: &mut Splices,
    updates: &HashSet<usize>,
) -> Result<Syntax, NatDefinitionParseError> {
    let assignment = plan
        .pattern_assignment
        .ok_or_else(|| refuse(view, tokens, plan.start + 1))?;
    let then_at = plan
        .then_at
        .ok_or_else(|| refuse(view, tokens, plan.start))?;
    if assignment <= plan.start + 2 || assignment + 1 >= then_at {
        return Err(refuse(view, tokens, assignment));
    }
    let pattern = pattern(leaves, view, tokens, plan.start + 2..assignment)?;
    let value = branch_value(
        leaves,
        view,
        tokens,
        assignment + 1..then_at,
        grammar,
        splices,
        updates,
    )?;
    let kind = if is_symbol(tokens, assignment, ":=") {
        "doIfLetPure"
    } else {
        "doIfLetBind"
    };
    Ok(Syntax::node(
        parser_kind(&["Term", "doIfLet"]),
        vec![
            leaves.leaf(plan.start + 1)?,
            pattern,
            Syntax::node(
                parser_kind(&["Term", kind]),
                vec![leaves.leaf(assignment)?, value],
            ),
        ],
    ))
}
