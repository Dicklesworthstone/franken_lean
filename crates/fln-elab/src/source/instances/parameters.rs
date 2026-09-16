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
    /// Output holes are deliberately absent from this cycle-detection key.
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
        // Keep the existing bounded universe profile. Output *expression*
        // parameters may be unknown; unresolved class universes still postpone.
        if head.has_level_mvar() {
            return Ok(None);
        }
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
            } else {
                argument
            };
            telescope = self.substitute(&body, &selected)?;
            prepared = Expr::app(prepared, selected);
            key = Expr::app(key, key_argument);
        }
        if !matches!(self.instance_type(&telescope)?.node(), ExprNode::Sort { .. }) {
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
            assert_eq!(context.instance_parameter_mode(&annotation).unwrap(), expected);
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
