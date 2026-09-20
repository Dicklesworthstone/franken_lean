//! Canonical keys for fresh, bare output and semi-output holes. Placeholders are key data only.
//! Sharing preserves repeated-hole identity and the exact declared hole types.
//! Arbitrary open terms, opaque/delayed holes and foreign scopes are not guessed.
use super::*;

pub(super) fn canonical(
    context: &mut Context,
    frame: &Frame,
) -> Result<Option<(Expr, Vec<Expr>)>, NatDefinitionElabError> {
    if ground(&frame.expected) {
        return Ok(Some((frame.expected.clone(), Vec::new())));
    }
    if frame.expected.has_level_mvar() {
        return Ok(None);
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
    let mut holes = Vec::new();
    let mut types = Vec::new();
    for (argument, output) in arguments.into_iter().rev() {
        context.tick()?;
        let argument = if ground(argument) {
            argument.clone()
        } else {
            let ExprNode::MVar { id } = argument.node() else {
                return Ok(None);
            };
            if !output {
                return Ok(None);
            }
            let Some(decl) = frame.base.txn.mvars.get_decl(id) else {
                return Ok(None);
            };
            if decl.kind != MetavarKind::Natural
                || decl.depth != 0
                || decl.delayed.is_some()
                || frame.base.txn.mvars.is_assigned(id)
                || decl.lctx != frame.base.txn.lctx
                || !ground(&decl.type_)
            {
                return Ok(None);
            }
            let mut previous = None;
            for (index, old) in holes.iter().enumerate() {
                context.tick()?;
                if old == id {
                    previous = Some(index);
                    break;
                }
            }
            let position = if let Some(index) = previous {
                index
            } else {
                if holes.len() >= MAX_KEY_UNITS {
                    return Ok(None);
                }
                holes.push(id.clone());
                types.push(decl.type_.clone());
                holes.len() - 1
            };
            Expr::bvar((position + 1) as u32).map_err(|_| failure(SourceInferenceError::Scope))?
        };
        canonical = Expr::app(canonical, argument);
    }
    Ok(Some((canonical, types)))
}
