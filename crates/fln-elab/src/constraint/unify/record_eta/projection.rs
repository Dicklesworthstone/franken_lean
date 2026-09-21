//! Singleton projection inversion (Athanor, plan §10.2).
//!
//! The pinned `Lean/Meta/ExprDefEq.lean::isDefEqProj.isDefEqSingleton`
//! solves `(?m ...).field = value` as `?m ... = Constructor ... value`
//! only for non-class, nonrecursive records with exactly one field. We use
//! the ordinary pattern solver and replay the original projection equation.
//! No new admission authority, assumed proof, or arbitrary field is introduced.

use super::*;
use crate::instances::InstanceRegistry;

impl Engine<'_> {
    pub(super) fn invert_singleton_projection(
        &mut self,
        projected: &Expr,
        value: &Expr,
        locals: &LocalContext,
        pending: &mut VecDeque<Equation>,
    ) -> Result<bool, UnificationError> {
        let ExprNode::Proj {
            struct_name,
            idx: 0,
            expr: receiver,
        } = projected.node()
        else {
            return Ok(false);
        };
        // The Reference's projection/projection case has priority over its
        // singleton rule. Do not replace it with a different approximation.
        if matches!(value.node(), ExprNode::Proj { .. }) {
            return Ok(false);
        }
        let receiver = self.whnf(receiver, locals)?;
        let (head, _) = self.eta_spine(&receiver)?;
        let ExprNode::MVar { id } = head.node() else {
            return Ok(false);
        };
        let Some(declaration) = self.work.mvars.get_decl(id) else {
            return Ok(false);
        };
        if self.work.mvars.is_assigned(id)
            || declaration.kind == MetavarKind::SyntheticOpaque
            || declaration.depth > self.budget.max_metavar_depth
            || declaration.delayed.is_some()
        {
            return Ok(false);
        }
        let Some(shape) = self.eta_shape(struct_name)? else {
            return Ok(false);
        };
        if shape.fields != 1 || !self.singleton_classification_allows(struct_name)? {
            return Ok(false);
        }
        // The declared receiver type selects the parameters and universes, not
        // the unchecked projection annotation or the proposed field value.
        let Some(receiver_type) = self.eta_neutral_type(&receiver, locals)? else {
            return Ok(false);
        };
        let (head, parameters) = self.eta_spine(&receiver_type)?;
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(false);
        };
        if name != struct_name
            || parameters.len() != shape.parameters
            || levels.len() != shape.level_params.len()
        {
            return Ok(false);
        }
        // Checks the full constructor telescope and its result family, including
        // known Type-valuedness. This does not type-check the proposed value:
        // assignment typing and the final K1 barrier retain that authority.
        if self
            .eta_projection_type(receiver_type, struct_name, 0, &receiver, locals)?
            .is_none()
        {
            return Ok(false);
        }
        let mut constructor = Expr::const_(shape.constructor, levels.clone());
        for parameter in parameters {
            self.meter.node()?;
            constructor = Expr::app(constructor, parameter);
        }
        self.meter.node()?;
        constructor = Expr::app(constructor, value.clone());
        match self.pattern(&receiver, &constructor, locals, pending) {
            Ok(true) => {
                self.meter.node()?;
                pending.push_back((projected.clone(), value.clone(), locals.clone()));
                Ok(true)
            }
            // A nonpattern, escaping local or blocked assignment is not a
            // reason to suppress the remaining comparison rungs.
            Ok(false) | Err(UnificationError::Deferred(_)) => Ok(false),
            Err(error) => Err(error),
        }
    }

    fn singleton_classification_allows(
        &mut self,
        structure: &Name,
    ) -> Result<bool, UnificationError> {
        // Class inversion bypasses instance selection (Reference issue #2011).
        // Meter the bounded journal before its decoder runs. A corrupt journal
        // cannot establish that a family is a non-class, so this rung refuses.
        let registry_name = Name::from_components(["FrankenLean", "sourceInstances", "v1"]);
        if let Some(extension) = self.work.env.extension(&registry_name) {
            for entry in extension.entries() {
                self.meter.node()?;
                for _ in entry.payload.iter() {
                    self.meter.node()?;
                }
            }
        }
        Ok(InstanceRegistry::read(&self.work.env)
            .is_ok_and(|registry| !registry.is_class(structure)))
    }
}
