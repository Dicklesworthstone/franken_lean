//! Nullary singleton-Prop elimination without assigning the major proof.
//!
//! The admitted recursor's K flag is necessary, not a substitute for matching
//! its indices. Reconstruct the actual major domain from its telescope and
//! compare it with the instantiated constructor result. This is a sufficient
//! conversion rule, never an index-unification or proof-synthesis heuristic.
//! Like beta/iota, it is a reduction aid, not an input typing judgment.
use super::*;

impl Engine<'_> {
    pub(super) fn k_iota(
        &mut self,
        rec_head: &Expr,
        recursor: &RecursorVal,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, UnificationError> {
        self.meter.node()?;
        if !recursor.k
            || recursor.is_unsafe
            || recursor.all.len() != 1
            || recursor.num_motives != 1
            || recursor.num_minors != 1
            || recursor.rules.len() != 1
        {
            return Ok(None);
        }
        let rec_head = self.instantiate(rec_head)?;
        let ExprNode::Const { levels, .. } = rec_head.node() else {
            return Ok(None);
        };
        if levels.len() != recursor.base.level_params.len() {
            return Ok(None);
        }
        let (prefix, major) = recursor_positions(recursor)?;
        if major >= arguments.len() {
            return Ok(None);
        }
        let rule = &recursor.rules[0];
        let Some(ConstantInfo::Induct(family)) = self.work.env.find(&recursor.all[0]) else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(ctor)) = self.work.env.find(&rule.ctor) else {
            return Ok(None);
        };
        if family.is_unsafe
            || family.num_nested != 0
            || family.all != recursor.all
            || family.num_indices != recursor.num_indices
            || family.num_params != recursor.num_params
            || family.ctors.len() != 1
            || family.ctors[0] != rule.ctor
            || ctor.is_unsafe
            || ctor.induct != family.base.name
            || ctor.num_params != family.num_params
            || ctor.num_fields != 0
            || rule.nfields != 0
            || ctor.base.level_params != family.base.level_params
        {
            return Ok(None);
        }
        // K is only available to a proposition, not arbitrary singleton data.
        let mut result_sort = &family.base.type_;
        while let ExprNode::ForallE { body, .. } = result_sort.node() {
            self.meter.node()?;
            result_sort = body;
        }
        if !matches!(result_sort.node(), ExprNode::Sort { level } if level.is_zero()) {
            return Ok(None);
        }
        for _ in &family.base.level_params {
            self.meter.node()?;
        }
        let family_parameters = family.base.level_params.clone();
        let constructor_type = ctor.base.type_.clone();
        let family_levels = if recursor.base.level_params == family_parameters {
            levels.as_slice()
        } else if recursor.base.level_params.len() == family_parameters.len() + 1
            && recursor.base.level_params[1..] == family_parameters
        {
            &levels[1..]
        } else {
            return Ok(None);
        };
        self.scan(&recursor.base.type_)?;
        let mut telescope = crate::universe::parameters::instantiate(
            || self.meter.node(),
            || UnificationError::ExpressionScope,
            &recursor.base.type_,
            &recursor.base.level_params,
            levels,
        )?;
        for argument in arguments.iter().rev().take(major) {
            self.meter.node()?;
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                return Ok(None);
            };
            telescope = self.substitute(body, argument)?;
        }
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            return Ok(None);
        };
        let major_domain = self.instantiate(binder_type)?;
        self.scan(&constructor_type)?;
        let mut constructor_result = crate::universe::parameters::instantiate(
            || self.meter.node(),
            || UnificationError::ExpressionScope,
            &constructor_type,
            &family_parameters,
            family_levels,
        )?;
        for parameter in arguments.iter().rev().take(count(recursor.num_params)?) {
            self.meter.node()?;
            let ExprNode::ForallE { body, .. } = constructor_result.node() else {
                return Ok(None);
            };
            constructor_result = self.substitute(body, parameter)?;
        }
        let constructor_result = self.instantiate(&constructor_result)?;
        // No recursive whnf here: nested transports stay on the parent's heap
        // continuation stack. Unresolved/different indices simply stay stuck.
        if !same_terms(&major_domain, &constructor_result, &mut self.meter)? {
            return Ok(None);
        }
        self.scan(&rule.rhs)?;
        let mut result = crate::universe::parameters::instantiate(
            || self.meter.node(),
            || UnificationError::ExpressionScope,
            &rule.rhs,
            &recursor.base.level_params,
            levels,
        )?;
        for argument in arguments.iter().rev().take(prefix) {
            self.meter.node()?;
            result = Expr::app(result, argument.clone());
        }
        Ok(Some(result))
    }
}
