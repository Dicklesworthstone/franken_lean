//! Parameter modes for native instance search, derived from admitted class types.
//!
//! Output annotations affect search only. They do not erase a typing obligation:
//! the selected result must still unify with the original goal before publication.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParameterMode {
    Input,
    Output,
    SemiOutput,
}

pub(super) struct PreparedTarget {
    pub target: Expr,
    pub expected: Expr,
    /// Outputs are erased; bare unknown semi-outputs are alpha-canonicalized.
    /// This expression is never used as a term or submitted to a checker.
    pub key: Expr,
}

impl Context {
    fn instance_parameter_mode(
        &mut self,
        domain: &Expr,
    ) -> Result<ParameterMode, NatDefinitionElabError> {
        // Do not unfold the annotation itself: both gadgets are identities.
        // Only the exact root names have parameter-mode semantics.
        let mut domain = domain;
        loop {
            self.tick()?;
            match domain.node() {
                ExprNode::MData { expr, .. } => domain = expr,
                ExprNode::App { f, .. } => {
                    let mut head = f;
                    loop {
                        self.tick()?;
                        match head.node() {
                            ExprNode::MData { expr, .. } => head = expr,
                            ExprNode::Const { name, .. }
                                if name == &Name::from_components(["outParam"]) =>
                            {
                                return Ok(ParameterMode::Output);
                            }
                            ExprNode::Const { name, .. }
                                if name == &Name::from_components(["semiOutParam"]) =>
                            {
                                return Ok(ParameterMode::SemiOutput);
                            }
                            _ => return Ok(ParameterMode::Input),
                        }
                    }
                }
                _ => return Ok(ParameterMode::Input),
            }
        }
    }

    /// `None` is a blocked input, not an exhausted instance search. Callers run
    /// this in a speculative context, so preparation never publishes fresh holes
    /// when a later input is blocked. The class must already be registered.
    pub(super) fn prepare_instance_target(
        &mut self,
        target: &Expr,
    ) -> Result<Option<PreparedTarget>, NatDefinitionElabError> {
        let mut head = target.clone();
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                ExprNode::MData { expr, .. } => head = expr.clone(),
                _ => break,
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(failure(SourceInferenceError::InvalidInstanceBinder));
        };
        // Universe metavariables are equations for candidate matching, not
        // unknown expression inputs. In particular an output parameter may
        // determine its own universe. Final publication still requires every
        // universe in the selected term and goal to be resolved.
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        let base = info.constant_val();
        let mut telescope = self.instantiate_params(&base.type_, &base.level_params, levels)?;
        let mut prepared = head.clone();
        let mut key = head;
        let mut semi_holes = Vec::new();
        for argument in arguments.into_iter().rev() {
            self.tick()?;
            telescope = self.instance_type(&telescope)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = telescope.node()
            else {
                return Err(failure(SourceInferenceError::InvalidInstanceBinder));
            };
            let body = body.clone();
            let mode = self.instance_parameter_mode(binder_type)?;
            let selected = match mode {
                ParameterMode::Input => {
                    if argument.has_expr_mvar() || argument.has_level_mvar() {
                        return Ok(None);
                    }
                    argument.clone()
                }
                // Ignore even pre-existing output values during selection.
                // Reconcile them only after the first successful candidate.
                ParameterMode::Output => self.hole(binder_type.clone())?,
                ParameterMode::SemiOutput => argument.clone(),
            };
            let key_argument = if mode == ParameterMode::Output {
                Expr::bvar(0).expect("fixed cycle-key placeholder")
            } else if mode == ParameterMode::SemiOutput
                && let ExprNode::MVar { id } = argument.node()
            {
                // Unknown semi-outputs are query variables, not fresh query
                // identities. Preserve repeated-variable equality, and never
                // erase a known semi-output (which filters candidate matching).
                let mut position = None;
                for (index, previous) in semi_holes.iter().enumerate() {
                    self.tick()?;
                    if previous == id {
                        position = Some(index);
                        break;
                    }
                }
                let index = position.unwrap_or(semi_holes.len());
                if position.is_none() {
                    semi_holes.push(id.clone());
                }
                let index = u32::try_from(index + 1)
                    .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
                Expr::bvar(index).map_err(|_| failure(SourceInferenceError::Scope))?
            } else {
                argument
            };
            telescope = self.substitute(&body, &selected)?;
            prepared = Expr::app(prepared, selected);
            key = Expr::app(key, key_argument);
        }
        if !matches!(
            self.instance_type(&telescope)?.node(),
            ExprNode::Sort { .. }
        ) {
            return Err(failure(SourceInferenceError::InvalidInstanceBinder));
        }
        Ok(Some(PreparedTarget {
            target: prepared,
            expected: target.clone(),
            key,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parameter_modes_recognize_only_exact_fully_applied_root_annotations() {
        let mut context = Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        );
        let sort = Expr::sort(Level::one());
        for (name, expected) in [
            (Name::from_components(["outParam"]), ParameterMode::Output),
            (
                Name::from_components(["semiOutParam"]),
                ParameterMode::SemiOutput,
            ),
            (
                Name::from_components(["User", "outParam"]),
                ParameterMode::Input,
            ),
        ] {
            let head = Expr::const_(name, vec![]);
            assert_eq!(
                context.instance_parameter_mode(&head).unwrap(),
                ParameterMode::Input
            );
            let annotation = Expr::app(head, sort.clone());
            assert_eq!(
                context.instance_parameter_mode(&annotation).unwrap(),
                expected
            );
            assert_eq!(
                context
                    .instance_parameter_mode(&Expr::app(annotation, sort.clone()))
                    .unwrap(),
                ParameterMode::Input
            );
        }
        assert_eq!(
            context.instance_parameter_mode(&sort).unwrap(),
            ParameterMode::Input
        );
    }
}
