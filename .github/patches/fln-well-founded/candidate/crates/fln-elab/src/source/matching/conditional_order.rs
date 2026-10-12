//! Source order for well-founded conditional branches. The admitted recursor
//! still receives its minors in declaration order; only their elaboration is
//! scheduled in the source's then-before-else order. Recursive calls therefore
//! create decreasing obligations in the same order as the source elaborator,
//! including nested calls and conditionals.
use super::*;

pub(super) struct ConditionalOrder {
    domains: std::collections::VecDeque<Expr>,
    first: Option<Typed>,
    branch_scope_depth: Option<usize>,
}

impl Context {
    pub(super) fn next_ordered_conditional_domain(
        &mut self,
        order: &mut ConditionalOrder,
    ) -> Result<Expr, NatDefinitionElabError> {
        let domain = order
            .domains
            .pop_front()
            .ok_or_else(|| error(MatchError::UnsupportedFamily))?;
        if let Some(depth) = order.branch_scope_depth {
            self.enter_well_founded_branch(depth)?;
        }
        Ok(domain)
    }

    pub(super) fn order_well_founded_conditional(
        &mut self,
        conditional: bool,
        family: &Name,
        recursor: &Typed,
        branches: &mut std::collections::VecDeque<Branch<'_>>,
    ) -> Result<Option<ConditionalOrder>, NatDefinitionElabError> {
        if !conditional
            || !self
                .well_founded
                .as_ref()
                .is_some_and(|state| !state.proving)
        {
            return Ok(None);
        }
        let names = if family == &Name::from_components(["Decidable"]) {
            ["isFalse", "isTrue"]
        } else if family == &Name::from_components(["Bool"]) {
            ["false", "true"]
        } else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        if branches.len() != 2
            || branches.iter().zip(names).any(|(branch, name)| {
                branch.constructor.base.name != Name::str(family.clone(), name)
            })
        {
            return Err(error(MatchError::UnsupportedFamily));
        }
        let telescope = self.whnf(&recursor.type_)?;
        let ExprNode::ForallE {
            binder_type: no_domain,
            body,
            ..
        } = telescope.node()
        else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        // The second minor of Bool/Decidable does not depend on the first.
        // Verify that actual admitted telescope before reading it outside the
        // first binder; no placeholder or equality transport is introduced.
        if body.has_loose_bvars() {
            return Err(error(MatchError::UnsupportedFamily));
        }
        let tail = self.whnf(body)?;
        let ExprNode::ForallE {
            binder_type: yes_domain,
            ..
        } = tail.node()
        else {
            return Err(error(MatchError::UnsupportedFamily));
        };
        branches.rotate_left(1);
        Ok(Some(ConditionalOrder {
            domains: [yes_domain.clone(), no_domain.clone()].into(),
            first: None,
            branch_scope_depth: if family == &Name::from_components(["Bool"]) {
                self.well_founded_branch_depth()
            } else {
                None
            },
        }))
    }

    pub(super) fn accept_ordered_conditional_minor(
        &mut self,
        state: &mut MatchBuild<'_>,
        value: Typed,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(order) = &mut state.conditional_order else {
            return Ok(false);
        };
        if let Some(depth) = order.branch_scope_depth {
            self.leave_well_founded_branch(depth)?;
        }
        if let Some(first) = order.first.take() {
            if !order.domains.is_empty() {
                return Err(error(MatchError::UnsupportedFamily));
            }
            // `first` is the source's then branch. Reassemble false before
            // true exactly as the admitted recursor expects, checking both
            // ordinary dependent applications.
            let recursor = self.match_apply(state.recursor.clone(), value)?;
            state.recursor = self.match_apply(recursor, first)?;
            state.conditional_order = None;
        } else {
            order.first = Some(value);
        }
        Ok(true)
    }
}
