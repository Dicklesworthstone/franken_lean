//! The cycle key deliberately freshens output-only universe slots. That is
//! selection policy, not the identity of the original typed answer query.
//! Keep the original head in answer keys and validate all non-output slots.
use super::*;
use fln_core::level::LevelView;

pub(super) fn compatible_heads(
    context: &mut Context,
    original: &Expr,
    prepared: &Expr,
    shape: &Expr,
) -> Result<bool, NatDefinitionElabError> {
    if original == prepared && original == shape {
        return Ok(true);
    }
    let (
        ExprNode::Const {
            name: on,
            levels: ol,
        },
        ExprNode::Const {
            name: pn,
            levels: pl,
        },
        ExprNode::Const {
            name: sn,
            levels: sl,
        },
    ) = (original.node(), prepared.node(), shape.node())
    else {
        return Ok(false);
    };
    if on != pn || on != sn || ol.len() != pl.len() || ol.len() != sl.len() {
        return Ok(false);
    }
    for (index, ((original, prepared), key)) in ol.iter().zip(pl).zip(sl).enumerate() {
        context.tick()?;
        if original == prepared && original == key {
            continue;
        }
        let placeholder = Name::num(
            Name::from_components(["_fln_instance_output_universe"]),
            index as u64,
        );
        if !matches!(key.view(), LevelView::Param(name) if name == &placeholder)
            || !(original == prepared || matches!(prepared.view(), LevelView::MVar(_)))
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
