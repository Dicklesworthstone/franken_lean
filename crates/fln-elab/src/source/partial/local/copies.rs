//! Generated visits of one source binding may share a declaration only after
//! their complete checked candidates agree. Binder names are lexical labels;
//! styles, metadata, universe arguments and all computational nodes stay exact.
use super::*;

pub(super) fn equivalent(
    context: &mut Context,
    left: &Expr,
    right: &Expr,
) -> Result<bool, NatDefinitionElabError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        context.tick()?;
        if !seen.insert((left.allocation_identity(), right.allocation_identity())) {
            continue;
        }
        match (left.node(), right.node()) {
            (ExprNode::App { f: lf, a: la }, ExprNode::App { f: rf, a: ra }) => {
                pending.extend([(lf, rf), (la, ra)]);
            }
            (
                ExprNode::Lam {
                    binder_type: lt,
                    body: lb,
                    binder_info: li,
                    ..
                },
                ExprNode::Lam {
                    binder_type: rt,
                    body: rb,
                    binder_info: ri,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: lt,
                    body: lb,
                    binder_info: li,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: rt,
                    body: rb,
                    binder_info: ri,
                    ..
                },
            ) => {
                if li != ri {
                    return Ok(false);
                }
                pending.extend([(lt, rt), (lb, rb)]);
            }
            (
                ExprNode::LetE {
                    type_: lt,
                    value: lv,
                    body: lb,
                    non_dep: ln,
                    ..
                },
                ExprNode::LetE {
                    type_: rt,
                    value: rv,
                    body: rb,
                    non_dep: rn,
                    ..
                },
            ) => {
                if ln != rn {
                    return Ok(false);
                }
                pending.extend([(lt, rt), (lv, rv), (lb, rb)]);
            }
            (ExprNode::MData { data: ld, expr: le }, ExprNode::MData { data: rd, expr: re }) => {
                if ld != rd {
                    return Ok(false);
                }
                pending.push((le, re));
            }
            (
                ExprNode::Proj {
                    struct_name: ln,
                    idx: li,
                    expr: le,
                },
                ExprNode::Proj {
                    struct_name: rn,
                    idx: ri,
                    expr: re,
                },
            ) => {
                if ln != rn || li != ri {
                    return Ok(false);
                }
                pending.push((le, re));
            }
            // Closed leaf equality includes the full constant name and its
            // universe list. In particular, no peer or data value is erased.
            (ExprNode::BVar { .. }, ExprNode::BVar { .. })
            | (ExprNode::Sort { .. }, ExprNode::Sort { .. })
            | (ExprNode::Const { .. }, ExprNode::Const { .. })
            | (ExprNode::Lit { .. }, ExprNode::Lit { .. }) => {
                if left != right {
                    return Ok(false);
                }
            }
            // Open locals/metavariables have no place in closed candidates.
            _ => return Ok(false),
        }
    }
    Ok(true)
}
