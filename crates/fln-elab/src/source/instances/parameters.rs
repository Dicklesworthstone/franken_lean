//! Parameter modes for native instance search, derived from admitted class types.
//!
//! Output annotations affect search only. They do not erase a typing obligation:
//! the selected result must still unify with the original goal before publication.
use super::*;

mod universes;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ParameterMode {
    Input,
    Output,
    SemiOutput,
}

pub(super) struct PreparedTarget {
    pub target: Expr,
    pub expected: Expr,
    /// Outputs and their exclusive universes are erased; bare unknown
    /// semi-outputs are alpha-canonicalized. Never submitted to a checker.
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

    /// Classify the declared telescope, before substituting any query arguments.
    /// An instance parameter depending on an output is itself an output (Lean
    /// v4.32.0 Class.checkOutParam, issue #1852). Ordinary dependent parameters
    /// are invalid: replacing their dependencies alone would make the target
    /// ill-typed. Semi-outputs do not propagate this rule.
    fn instance_parameter_modes(
        &mut self,
        class_type: &Expr,
    ) -> Result<Vec<ParameterMode>, NatDefinitionElabError> {
        let mut modes = Vec::new();
        let mut telescope = class_type;
        loop {
            self.tick()?;
            match telescope.node() {
                ExprNode::MData { expr, .. } => telescope = expr,
                ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } => {
                    let mut mode = self.instance_parameter_mode(binder_type)?;
                    if mode != ParameterMode::Output {
                        for (index, previous) in modes.iter().rev().enumerate() {
                            self.tick()?;
                            if *previous != ParameterMode::Output {
                                continue;
                            }
                            let index = u32::try_from(index)
                                .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
                            // has_loose_bvar accounts for binders inside the
                            // domain; a nested binder is not a class parameter.
                            if binder_type.has_loose_bvar(index) {
                                if *binder_info != BinderInfo::InstImplicit {
                                    return Err(failure(SourceInferenceError::InvalidInstanceBinder));
                                }
                                mode = ParameterMode::Output;
                                break;
                            }
                        }
                    }
                    modes.push(mode);
                    telescope = body;
                }
                ExprNode::Sort { .. } => return Ok(modes),
                _ => return Err(failure(SourceInferenceError::InvalidInstanceBinder)),
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
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        let base = info.constant_val();
        let modes = self.instance_parameter_modes(&base.type_)?;
        if arguments.len() != modes.len() {
            return Err(failure(SourceInferenceError::InvalidInstanceBinder));
        }
        // Output-only universes must not filter candidate selection, even when
        // the caller already knows them. Reconcile with the original target
        // only after selecting the first successful candidate.
        let (levels, key_levels) =
            self.instance_search_levels(&base.type_, &modes, &base.level_params, levels)?;
        let mut telescope = self.instantiate_params(&base.type_, &base.level_params, &levels)?;
        let mut prepared = Expr::const_(name.clone(), levels);
        let mut key = Expr::const_(name.clone(), key_levels);
        let mut semi_holes = Vec::new();
        for (argument, mode) in arguments.into_iter().rev().zip(modes) {
            self.tick()?;
            telescope = self.instance_type(&telescope)?;
            let ExprNode::ForallE {
                binder_type, body, ..
            } = telescope.node()
            else {
                return Err(failure(SourceInferenceError::InvalidInstanceBinder));
            };
            let body = body.clone();
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

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    fn annotation(name: &str, domain: Expr) -> Expr {
        Expr::app(Expr::const_(Name::from_components([name]), vec![]), domain)
    }

    fn telescope(parameters: Vec<(Expr, BinderInfo)>) -> Expr {
        parameters.into_iter().rev().fold(
            Expr::sort(Level::one()),
            |body, (domain, binder_info)| {
                Expr::forall_e(Name::anonymous(), domain, body, binder_info)
            },
        )
    }

    #[test]
    fn parameter_modes_recognize_only_exact_fully_applied_root_annotations() {
        let mut context = context();
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

    #[test]
    fn dependent_instance_outputs_propagate_transitively() {
        let type_ = telescope(vec![
            (
                annotation("outParam", Expr::sort(Level::one())),
                BinderInfo::Default,
            ),
            (annotation("D", Expr::bvar(0).unwrap()), BinderInfo::InstImplicit),
            (annotation("E", Expr::bvar(0).unwrap()), BinderInfo::InstImplicit),
        ]);
        assert_eq!(
            context().instance_parameter_modes(&type_).unwrap(),
            vec![ParameterMode::Output; 3]
        );
    }

    #[test]
    fn output_dependencies_count_intervening_inputs_and_nested_binders() {
        let sort = Expr::sort(Level::one());
        let nested = Expr::forall_e(
            Name::anonymous(),
            sort.clone(),
            annotation("D", Expr::bvar(2).unwrap()),
            BinderInfo::Default,
        );
        let type_ = telescope(vec![
            (annotation("outParam", sort.clone()), BinderInfo::Default),
            (sort, BinderInfo::Default),
            (nested, BinderInfo::InstImplicit),
        ]);
        assert_eq!(
            context().instance_parameter_modes(&type_).unwrap(),
            vec![ParameterMode::Output, ParameterMode::Input, ParameterMode::Output]
        );
    }

    #[test]
    fn nested_bound_variables_are_not_output_dependencies() {
        let sort = Expr::sort(Level::one());
        let nested = Expr::forall_e(
            Name::anonymous(),
            sort.clone(),
            annotation("D", Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let type_ = telescope(vec![
            (annotation("outParam", sort), BinderInfo::Default),
            (nested, BinderInfo::InstImplicit),
        ]);
        assert_eq!(
            context().instance_parameter_modes(&type_).unwrap(),
            vec![ParameterMode::Output, ParameterMode::Input]
        );
    }

    #[test]
    fn ordinary_output_dependencies_are_refused_unless_explicitly_marked() {
        for binder_info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
        ] {
            let output = annotation("outParam", Expr::sort(Level::one()));
            let invalid = telescope(vec![
                (output.clone(), BinderInfo::Default),
                (Expr::bvar(0).unwrap(), binder_info),
            ]);
            assert!(matches!(
                context().instance_parameter_modes(&invalid),
                Err(NatDefinitionElabError::Inference(SourceInferenceError::InvalidInstanceBinder))
            ));
            let valid = telescope(vec![
                (output, BinderInfo::Default),
                (annotation("outParam", Expr::bvar(0).unwrap()), binder_info),
            ]);
            assert_eq!(
                context().instance_parameter_modes(&valid).unwrap(),
                vec![ParameterMode::Output; 2]
            );
        }
    }

    #[test]
    fn semi_outputs_do_not_turn_dependent_instances_into_outputs() {
        let type_ = telescope(vec![
            (
                annotation("semiOutParam", Expr::sort(Level::one())),
                BinderInfo::Default,
            ),
            (annotation("D", Expr::bvar(0).unwrap()), BinderInfo::InstImplicit),
        ]);
        assert_eq!(
            context().instance_parameter_modes(&type_).unwrap(),
            vec![ParameterMode::SemiOutput, ParameterMode::Input]
        );
    }

    #[test]
    fn parameter_classification_exhaustion_is_not_a_class_refusal() {
        let mut context = context();
        context.txn.budget.heartbeats_consumed = context.txn.budget.max_heartbeats;
        assert!(matches!(
            context.instance_parameter_modes(&Expr::sort(Level::one())),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
        ));
    }
}
