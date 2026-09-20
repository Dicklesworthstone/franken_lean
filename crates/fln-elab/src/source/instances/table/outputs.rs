//! Canonical keys for structured outputs and bare semi-output holes.
//! Hole alias patterns, declared types, binders and sharing remain explicit.
//! Dependent hole types are part of the same canonical, cycle-checked graph.
//! Answer keys may retain independent universe variants; cycle keys preserve
//! the existing universe identity rules. Neither operation assigns a hole.
use super::*;

mod syntax;

pub(super) struct Canonical {
    pub expected: Expr,
    pub types: Vec<Expr>,
    pub units: usize,
}

#[cfg(test)]
pub(super) fn canonical(
    context: &mut Context,
    frame: &Frame,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    canonical_with_ancestors(context, frame, &[])
}

pub(super) fn canonical_with_ancestors(
    context: &mut Context,
    frame: &Frame,
    ancestors: &[Frame],
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    if frame.expected.has_loose_bvars() {
        return Ok(None);
    }
    pattern(context, frame, &frame.expected, Some(ancestors))
}

/// Prepared keys contain top-level output wildcards, never proof terms.
/// Keep these fixed while alpha-renaming only retained semi-output holes.
pub(super) fn cycle_key(
    context: &mut Context,
    frame: &Frame,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    pattern(context, frame, &frame.key, None)
}

fn pattern(
    context: &mut Context,
    frame: &Frame,
    expression: &Expr,
    ancestors: Option<&[Frame]>,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    if expression.has_level_mvar() && ancestors.is_none() {
        return Ok(None);
    }
    if ground(expression) {
        return Ok(Some(Canonical {
            expected: expression.clone(),
            types: Vec::new(),
            units: 0,
        }));
    }
    let mut expected = expression;
    let mut shape = &frame.key;
    let mut arguments = Vec::new();
    // Collect before numbering, so placeholder order follows the telescope.
    loop {
        context.tick()?;
        match (expected.node(), shape.node()) {
            (ExprNode::App { f: ef, a: ea }, ExprNode::App { f: sf, a: sa }) => {
                // Unknown ordinary inputs never pass target preparation.
                // Retained unknowns are semi-outputs: their entire structure
                // and each typed hole stay in the key, unlike output wildcards.
                arguments.push((ea, matches!(sa.node(), ExprNode::BVar { .. }) || ea == sa));
                expected = ef;
                shape = sf;
            }
            _ if expected == shape && !expected.has_expr_mvar() => break,
            _ => return Ok(None),
        }
    }
    let mut templates = syntax::Templates::default();
    if let Some(ancestors) = ancestors
        && !templates.anchor(context, ancestors)?
    {
        return Ok(None);
    }
    let Some(mut canonical) = templates.rewrite(context, frame, expected)? else {
        return Ok(None);
    };
    let mut spine_units = 0;
    for (argument, output) in arguments.into_iter().rev() {
        context.tick()?;
        let argument = if ground(argument) {
            argument.clone()
        } else {
            if !output && argument.has_expr_mvar() {
                return Ok(None);
            }
            let Some(value) = templates.rewrite(context, frame, argument)? else {
                return Ok(None);
            };
            value
        };
        canonical = Expr::app(canonical, argument);
        spine_units += 1;
    }
    let units = spine_units + templates.units();
    Ok(Some(Canonical {
        expected: canonical,
        types: templates.types,
        units,
    }))
}
