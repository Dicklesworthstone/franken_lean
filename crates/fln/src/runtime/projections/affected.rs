//! Syntax-only negative information for one projection-lowering invocation.
//! No receiver type, layout, or executable result is memoized here. A subtree
//! with no executable Proj is returned unchanged, even when it has free locals.
use super::*;
use std::collections::HashMap;

pub(super) struct Affected<'a> {
    nodes: HashMap<usize, bool>,
    _input: &'a Expr,
}

impl<'a> Affected<'a> {
    pub(super) fn read(
        preparation: &mut Preparation<'_>,
        input: &'a Expr,
    ) -> Result<Self, IngressError> {
        let mut nodes = HashMap::new();
        let mut pending = vec![(input, false)];
        while let Some((expression, finish)) = pending.pop() {
            if !can_contain(expression) {
                continue;
            }
            preparation.tick()?;
            let key = expression.allocation_identity();
            if nodes.contains_key(&key) {
                continue;
            }
            if !finish {
                reserve(&mut pending, preparation.limits.max_nodes)?;
                pending.push((expression, true));
                let mut push = |child| -> Result<(), IngressError> {
                    reserve(&mut pending, preparation.limits.max_nodes)?;
                    pending.push((child, false));
                    Ok(())
                };
                match expression.node() {
                    ExprNode::App { f, a } => {
                        push(a)?;
                        push(f)?;
                    }
                    ExprNode::Lam { body, .. }
                    | ExprNode::MData { expr: body, .. }
                    | ExprNode::Proj { expr: body, .. } => push(body)?,
                    ExprNode::LetE { value, body, .. } => {
                        push(body)?;
                        push(value)?;
                    }
                    _ => {}
                }
                continue;
            }
            let affected = |child: &Expr| -> Result<bool, IngressError> {
                if !can_contain(child) {
                    return Ok(false);
                }
                nodes
                    .get(&child.allocation_identity())
                    .copied()
                    .ok_or_else(|| unsupported("projection scan dependency"))
            };
            let present = match expression.node() {
                ExprNode::Proj { .. } => true,
                ExprNode::App { f, a } => affected(f)? || affected(a)?,
                ExprNode::Lam { body, .. } | ExprNode::MData { expr: body, .. } => affected(body)?,
                ExprNode::LetE { value, body, .. } => affected(value)? || affected(body)?,
                _ => false,
            };
            let observed = nodes.len().saturating_add(1);
            if observed > preparation.limits.max_nodes {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit: preparation.limits.max_nodes,
                    observed,
                });
            }
            nodes
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::Nodes,
                    requested: observed,
                })?;
            nodes.insert(key, present);
        }
        Ok(Self {
            nodes,
            _input: input,
        })
    }

    pub(super) fn contains(&self, expression: &Expr) -> bool {
        // Unknown syntax must still be walked. In particular this object is
        // never a permit to skip a newly constructed expression or a layout.
        can_contain(expression)
            && self
                .nodes
                .get(&expression.allocation_identity())
                .copied()
                .unwrap_or(true)
    }
}

fn can_contain(expression: &Expr) -> bool {
    matches!(
        expression.node(),
        ExprNode::App { .. }
            | ExprNode::Lam { .. }
            | ExprNode::LetE { .. }
            | ExprNode::MData { .. }
            | ExprNode::Proj { .. }
    )
}
