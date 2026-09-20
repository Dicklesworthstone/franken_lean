//! Canonical keys for structured outputs and bare semi-output holes.
//! Hole alias patterns, declared types, binders and sharing remain explicit.
//! Opaque/delayed holes, open declared types and foreign scopes are not guessed.
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
    if frame.expected.has_level_mvar() || frame.expected.has_loose_bvars() {
        return Ok(None);
    }
    if ground(&frame.expected) {
        return Ok(Some(Canonical {
            expected: frame.expected.clone(),
            types: Vec::new(),
            units: 0,
        }));
    }
    let mut expected = &frame.expected;
    let mut shape = &frame.key;
    let mut arguments = Vec::new();
    // Collect before numbering, so placeholder order follows the telescope.
    loop {
        context.tick()?;
        match (expected.node(), shape.node()) {
            (ExprNode::App { f: ef, a: ea }, ExprNode::App { f: sf, a: sa }) => {
                arguments.push((ea, matches!(sa.node(), ExprNode::BVar { .. })));
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
