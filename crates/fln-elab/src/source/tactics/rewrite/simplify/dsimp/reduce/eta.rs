//! Record eta is admitted only for an actual single-constructor data family,
//! the exact generated fields, a common receiver, and a completed conversion.
use super::*;

impl Context {
    pub(super) fn dsimp_eta_structure(
        &mut self,
        term: &Expr,
        head: &Expr,
        arguments: &[Expr],
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Induct(family)) = self.txn.env.find(&constructor.induct).cloned()
        else {
            return Ok(None);
        };
        if constructor.is_unsafe
            || family.is_unsafe
            || family.num_indices != 0
            || family.ctors != [name.clone()]
            || constructor.num_fields == 0
            || u64::try_from(arguments.len()).ok()
                != Some(u64::from(constructor.num_params) + u64::from(constructor.num_fields))
        {
            return Ok(None);
        }
        let mut receiver: Option<Expr> = None;
        for (index, field) in arguments
            .iter()
            .skip(constructor.num_params as usize)
            .enumerate()
        {
            self.tick()?;
            let index =
                u64::try_from(index).map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
            let Some(actual) = self.dsimp_field_receiver(field, &constructor.induct, index)? else {
                return Ok(None);
            };
            if let Some(expected) = &receiver {
                if !self.rewrite_same(expected, &actual)? {
                    return Ok(None);
                }
            } else {
                receiver = Some(actual);
            }
        }
        let receiver = receiver.expect("nonempty record fields");
        let mut trial = self.rewrite_trial();
        let result = (|| {
            let Some(actual) = trial.known_type(term)? else {
                return Ok(false);
            };
            let Some(expected) = trial.known_type(&receiver)? else {
                return Ok(false);
            };
            let mut budget = UnificationBudget::new(trial.kernel);
            budget.transparency = UnificationTransparency::Instances;
            budget.zeta_delta = false;
            if !trial.proof_types_match_with_budget(&actual, &expected, budget)? {
                return Ok(false);
            }
            trial.proof_types_match_with_budget(term, &receiver, budget)
        })();
        self.charge_rewrite_trial(&trial);
        if result? {
            *self = trial;
            Ok(Some(receiver))
        } else {
            Ok(None)
        }
    }

    fn dsimp_field_receiver(
        &mut self,
        term: &Expr,
        structure: &Name,
        index: u64,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if let ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } = term.node()
        {
            return Ok((struct_name == structure && *idx == index).then(|| expr.clone()));
        }
        let (head, arguments) = self.dsimp_spine(term)?;
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(name).cloned() else {
            return Ok(None);
        };
        let environment = self.txn.env.clone();
        let Some(projection) =
            crate::records::projection::generated_projection(&environment, &definition, || {
                self.tick()
            })?
        else {
            return Ok(None);
        };
        Ok((projection.structure == *structure
            && projection.index == index
            && arguments.len() == projection.parameters + 1)
            .then(|| arguments[projection.parameters].clone()))
    }
}
