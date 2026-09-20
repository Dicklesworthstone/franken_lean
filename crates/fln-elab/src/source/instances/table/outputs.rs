//! Canonical keys for structured outputs and bare semi-output holes.
//! Hole alias patterns, declared types, binders and sharing remain explicit.
//! Dependent hole types are part of the same canonical, cycle-checked graph.
//! Opaque/delayed holes, unknown universes and foreign scopes are not guessed.
use super::*;

mod syntax;

pub(super) struct Canonical {
    pub expected: Expr,
    pub types: Vec<Expr>,
    pub units: usize,
}

pub(super) fn canonical(
    context: &mut Context,
    frame: &Frame,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    if frame.expected.has_loose_bvars() {
        return Ok(None);
    }
    pattern(context, frame, &frame.expected)
}

/// Prepared keys contain top-level output wildcards, never proof terms.
/// Keep these fixed while alpha-renaming only retained semi-output holes.
pub(super) fn cycle_key(
    context: &mut Context,
    frame: &Frame,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    pattern(context, frame, &frame.key)
}

fn pattern(
    context: &mut Context,
    frame: &Frame,
    expression: &Expr,
) -> Result<Option<Canonical>, NatDefinitionElabError> {
    if expression.has_level_mvar() {
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
            _ if expected == shape && ground(expected) => break,
            _ => return Ok(None),
        }
    }
    let mut canonical = expected.clone();
    let mut templates = syntax::Templates::default();
    let mut spine_units = 0;
    for (argument, output) in arguments.into_iter().rev() {
        context.tick()?;
        let argument = if ground(argument) {
            argument.clone()
        } else {
            if !output {
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
