//! Output-only universes participate in result reconciliation, not selection.
//! Derive them from the admitted telescope (Lean v4.32.0 computeOutLevelParams).
//! The cycle-key placeholders are not types, terms or universe assignments.
use super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

impl Context {
    pub(super) fn instance_search_levels(
        &mut self,
        class_type: &Expr,
        modes: &[ParameterMode],
        params: &[Name],
        levels: &[Level],
    ) -> Result<(Vec<Level>, Vec<Level>), NatDefinitionElabError> {
        self.tick()?;
        if params.len() != levels.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        // Preserve the pin's parameterless-class exception. A universe on a
        // class such as ToLevel is not treated as an output merely because
        // there are no term-parameter domains mentioning it.
        if modes.is_empty() || params.is_empty() {
            return Ok((levels.to_vec(), levels.to_vec()));
        }

        let mut domains = Vec::new();
        let mut telescope = class_type;
        let mut index = 0;
        loop {
            self.tick()?;
            match telescope.node() {
                ExprNode::MData { expr, .. } => telescope = expr,
                ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let mode = modes
                        .get(index)
                        .ok_or_else(|| failure(SourceInferenceError::InvalidInstanceBinder))?;
                    if *mode != ParameterMode::Output {
                        domains.push(binder_type);
                    }
                    index += 1;
                    telescope = body;
                }
                ExprNode::Sort { .. } if index == modes.len() => break,
                _ => return Err(failure(SourceInferenceError::InvalidInstanceBinder)),
            }
        }

        // Traverse the DAG explicitly and meter all work. In particular, levels
        // in constants, nested binders, lets, and metadata/projections count.
        // The result sort is intentionally excluded, as in the pinned rule.
        let mut input_levels = HashSet::new();
        let mut seen = HashSet::new();
        let mut level_seen = HashSet::new();
        while let Some(expr) = domains.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            let mut work = Vec::new();
            match expr.node() {
                ExprNode::Sort { level } => work.push(level),
                ExprNode::Const { levels, .. } => work.extend(levels.iter().rev()),
                ExprNode::App { f, a } => domains.extend([a, f]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => domains.extend([body, binder_type]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => domains.extend([body, value, type_]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => domains.push(expr),
                _ => {}
            }
            while let Some(level) = work.pop() {
                self.tick()?;
                if !level_seen.insert(std::ptr::from_ref(level)) {
                    continue;
                }
                match level.view() {
                    LevelView::Param(name) => {
                        input_levels.insert(name.clone());
                    }
                    LevelView::Succ(inner) => work.push(inner),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        work.extend([right, left]);
                    }
                    LevelView::Zero | LevelView::MVar(_) => {}
                }
            }
        }

        let mut prepared = Vec::with_capacity(levels.len());
        let mut key = Vec::with_capacity(levels.len());
        for (index, (param, level)) in params.iter().zip(levels).enumerate() {
            self.tick()?;
            if input_levels.contains(param) {
                prepared.push(level.clone());
                key.push(level.clone());
            } else {
                prepared.push(self.level()?);
                let index = u64::try_from(index)
                    .map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
                key.push(Level::param(Name::num(
                    Name::from_components(["_fln_instance_output_universe"]),
                    index,
                )));
            }
        }
        // Each search gets independent fresh equations, but identical cycle
        // keys: a recursive instance cannot evade cycle detection by allocating
        // new output universes. The original target remains the final typing
        // obligation. The answer table conservatively skips normalized-head
        // variants it cannot replay; it never invents a negative cache entry.
        Ok((prepared, key))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(value: &str) -> Name {
        Name::from_components([value])
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn annotated(name: &str, domain: Expr) -> Expr {
        Expr::app(Expr::const_(n(name), vec![]), domain)
    }
    fn pi(domain: Expr, body: Expr) -> Expr {
        Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
    }
    fn type_at(name: &str) -> Expr {
        Expr::sort(Level::param(n(name)))
    }

    #[test]
    fn known_outputs_are_freshened_but_input_universes_are_preserved() {
        let class = pi(
            type_at("u"),
            pi(annotated("outParam", type_at("v")), type_at("r")),
        );
        let mut context = context();
        let modes = context.instance_parameter_modes(&class).unwrap();
        let params = [n("u"), n("v"), n("r")];
        let original = [Level::zero(), Level::one(), Level::one()];
        let before = context.txn.universes.clone();
        let (first, key) = context
            .instance_search_levels(&class, &modes, &params, &original)
            .unwrap();
        let (second, other_key) = context
            .instance_search_levels(&class, &modes, &params, &original)
            .unwrap();
        assert_eq!(first[0], original[0]);
        assert_eq!(key[0], original[0]);
        for index in [1, 2] {
            assert!(matches!(first[index].view(), LevelView::MVar(_)));
            assert_ne!(first[index], second[index]);
            assert_ne!(first[index], original[index]);
            assert!(matches!(key[index].view(), LevelView::Param(_)));
        }
        assert_eq!(key, other_key);
        assert_eq!(context.txn.universes, before);
    }

    #[test]
    fn universes_shared_with_inputs_or_semi_outputs_are_not_erased() {
        let shared = Level::max(Level::param(n("u")), Level::param(n("v"))).unwrap();
        let class = pi(
            type_at("u"),
            pi(
                annotated("semiOutParam", type_at("v")),
                pi(annotated("outParam", Expr::sort(shared)), Expr::sort(Level::one())),
            ),
        );
        let mut context = context();
        let modes = context.instance_parameter_modes(&class).unwrap();
        let original = [Level::zero(), Level::one()];
        let (prepared, key) = context
            .instance_search_levels(&class, &modes, &[n("u"), n("v")], &original)
            .unwrap();
        assert_eq!(prepared, original);
        assert_eq!(key, original);
    }

    #[test]
    fn dependent_dictionary_outputs_do_not_pin_output_universes() {
        let class = pi(
            annotated("outParam", type_at("u")),
            Expr::forall_e(
                n("dictionary"),
                Expr::app(
                    Expr::const_(n("Dictionary"), vec![Level::param(n("v"))]),
                    Expr::bvar(0).unwrap(),
                ),
                Expr::sort(Level::one()),
                BinderInfo::InstImplicit,
            ),
        );
        let mut context = context();
        let modes = context.instance_parameter_modes(&class).unwrap();
        assert_eq!(modes, vec![ParameterMode::Output; 2]);
        let (prepared, _) = context
            .instance_search_levels(
                &class,
                &modes,
                &[n("u"), n("v")],
                &[Level::one(), Level::one()],
            )
            .unwrap();
        assert!(prepared.iter().all(|level| matches!(level.view(), LevelView::MVar(_))));
        assert_ne!(prepared[0], prepared[1]);
    }

    #[test]
    fn output_aliases_to_input_universes_are_separated_during_selection() {
        let class = pi(
            type_at("u"),
            pi(annotated("outParam", type_at("v")), Expr::sort(Level::one())),
        );
        let mut context = context();
        let modes = context.instance_parameter_modes(&class).unwrap();
        let original = context.level().unwrap();
        let (prepared, _) = context
            .instance_search_levels(
                &class,
                &modes,
                &[n("u"), n("v")],
                &[original.clone(), original.clone()],
            )
            .unwrap();
        assert_eq!(prepared[0], original);
        assert_ne!(prepared[1], original);
    }

    #[test]
    fn nested_input_constant_universes_remain_inputs() {
        let domain = pi(
            type_at("u"),
            Expr::const_(n("Family"), vec![Level::param(n("v"))]),
        );
        let class = pi(domain, Expr::sort(Level::one()));
        let mut context = context();
        let modes = context.instance_parameter_modes(&class).unwrap();
        let original = [Level::zero(), Level::one()];
        let (prepared, key) = context
            .instance_search_levels(&class, &modes, &[n("u"), n("v")], &original)
            .unwrap();
        assert_eq!(prepared, original);
        assert_eq!(key, original);
    }

    #[test]
    fn parameterless_class_universes_keep_the_pinned_exception() {
        let original = [Level::one()];
        let (prepared, key) = context()
            .instance_search_levels(&type_at("u"), &[], &[n("u")], &original)
            .unwrap();
        assert_eq!(prepared, original);
        assert_eq!(key, original);
    }

    #[test]
    fn invalid_arity_and_exhaustion_do_not_assign_caller_universes() {
        let mut context = context();
        let before = context.txn.universes.clone();
        assert!(matches!(
            context.instance_search_levels(&type_at("u"), &[], &[n("u")], &[]),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Scope))
        ));
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
        assert!(matches!(
            context.instance_search_levels(&type_at("u"), &[], &[n("u")], &[Level::one()]),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
        ));
        assert_eq!(context.txn.universes, before);
    }
}
