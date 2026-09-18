//! Transactional instantiation of quantified equality rules at goal occurrences.
//! Failed candidates cannot assign another goal's metavariables or consume an
//! unresolved premise. All successful rule applications retain their proof term.

use super::*;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq)]
enum RigidTypeHead {
    Sort,
    Forall,
    Inductive(Name),
}

impl Context {
    /// Compile an equivalence to an ordinary equality proof. This is not a
    /// host-side conversion of propositions: the explicit propext application
    /// and the original rule must survive into the checked transport term.
    fn equivalence_rewrite_rule(&mut self, rule: Typed) -> Result<Typed, NatDefinitionElabError> {
        self.tick()?;
        let ExprNode::App { f, a: right } = rule.type_.node() else {
            return Ok(rule);
        };
        let ExprNode::App { f: head, a: left } = f.node() else {
            return Ok(rule);
        };
        if !matches!(head.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["Iff"]) && levels.is_empty())
        {
            return Ok(rule);
        }
        let left = left.clone();
        let right = right.clone();
        // Resolving the actual declaration makes an absent propext a typed
        // refusal even when a later conversion could discard this proof.
        let propext = self.constant(&Name::from_components(["propext"]))?;
        Ok(Typed {
            value: app(propext.value, [left.clone(), right.clone(), rule.value]),
            type_: app(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                [Expr::sort(Level::zero()), left, right],
            ),
        })
    }

    /// A sufficient negative discrimination on types, not a conversion result.
    /// These outer forms cannot reduce into each other. Everything else (holes,
    /// aliases, lets, projections and stuck eliminators) goes to the full solver.
    /// Inductive applications must have their actual admitted arity; mere name
    /// spelling is never enough to classify an expression here.
    fn rigid_rewrite_type_head(
        &mut self,
        expr: &Expr,
    ) -> Result<Option<RigidTypeHead>, NatDefinitionElabError> {
        let mut head = expr;
        let mut arguments = 0_u64;
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, .. } => {
                    arguments = arguments
                        .checked_add(1)
                        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                ExprNode::Sort { .. } if arguments == 0 => {
                    return Ok(Some(RigidTypeHead::Sort));
                }
                ExprNode::ForallE { .. } if arguments == 0 => {
                    return Ok(Some(RigidTypeHead::Forall));
                }
                ExprNode::Const { name, levels } => {
                    let Some(fln_env::constants::ConstantInfo::Induct(family)) =
                        self.txn.env.find(name)
                    else {
                        return Ok(None);
                    };
                    return Ok((!family.is_unsafe
                        && levels.len() == family.base.level_params.len()
                        && arguments
                            == u64::from(family.num_params) + u64::from(family.num_indices))
                    .then(|| RigidTypeHead::Inductive(name.clone())));
                }
                _ => return Ok(None),
            }
        }
    }

    pub(super) fn rewrite_trial(&self) -> Self {
        self.clone()
    }

    /// Retain the cost of unsuccessful alternatives without retaining their
    /// semantic state. Every trial begins at the already charged parent budget.
    pub(super) fn charge_rewrite_trial(&mut self, trial: &Self) {
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
    }

    pub(super) fn rewrite_nonmatch(error: &NatDefinitionElabError) -> bool {
        let NatDefinitionElabError::Inference(SourceInferenceError::Unification(error)) = error
        else {
            return false;
        };
        match error.as_ref() {
            UnificationError::Deferred(_)
            | UnificationError::Metavariable(MetavarError::OccursCheckFailed { .. }) => true,
            UnificationError::AssignmentCheck { outcome, .. } => {
                matches!(
                    outcome.as_ref(),
                    Outcome::Complete(Verdict::Rejected { .. })
                )
            }
            _ => false,
        }
    }

    /// Match both the term and its type. `constrain` contributes universe
    /// equations, while the explicit equations also check closed mismatches
    /// (ordinary source elaboration leaves those to final declaration checking).
    fn match_rewrite_occurrence(
        &mut self,
        pattern: &Expr,
        alpha: &Expr,
        occurrence: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(occurrence)? else {
            return Ok(false);
        };
        // In a dependent recursor, most visited subterms are types, proofs or
        // partially applied functions, not values of the rule's carrier type.
        // Do not unify their large proof terms after their types already have
        // irreconcilable rigid heads. This accepts nothing and assigns no hole.
        if let (Some(actual), Some(expected)) = (
            self.rigid_rewrite_type_head(&type_)?,
            self.rigid_rewrite_type_head(alpha)?,
        ) && actual != expected
        {
            return Ok(false);
        }
        self.constrain(&type_, alpha)?;
        self.constrain(occurrence, pattern)?;
        self.equations
            .push(SourceEquation::selection(type_, alpha.clone()));
        self.equations.push(SourceEquation::selection(
            occurrence.clone(),
            pattern.clone(),
        ));
        self.flush(true)?;
        Ok(true)
    }

    fn discharge_rewrite_premises(
        &mut self,
        holes: &[MVarId],
        selected_rules: &[SimpRule<'_>],
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            let before = self.txn.mvars.assignments().len();
            for id in holes {
                self.tick()?;
                if self.txn.mvars.is_assigned(id) || self.instance_goals.contains(id) {
                    continue;
                }
                let raw = self
                    .txn
                    .mvars
                    .get_decl(id)
                    .expect("rule parameter was declared")
                    .type_
                    .clone();
                let target = self.instantiate(&raw)?;
                // Simp may discharge a proposition fixed by the match, but may
                // not guess a remaining data parameter from a selected proof.
                if target.has_expr_mvar() || target.has_level_mvar() {
                    continue;
                }
                let Some(universe) = self.known_type(&target)? else {
                    continue;
                };
                let universe = self.whnf(&universe)?;
                // Data parameters are inferred by the occurrence match, never
                // guessed from a value mentioned in the selected simp set.
                if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                    continue;
                }
                let value = self.simp_discharge_premise(id, &target, selected_rules)?;
                if let Some(value) = value {
                    self.txn
                        .assign_mvar(
                            id.clone(),
                            value,
                            AssignmentJustification::Tactic {
                                tactic_name: Name::from_components(["rewrite", "discharge"]),
                            },
                        )
                        .map_err(|e| {
                            failure(SourceInferenceError::Unification(Box::new(
                                UnificationError::Metavariable(e),
                            )))
                        })?;
                }
            }
            if holes.iter().all(|id| self.txn.mvars.is_assigned(id)) {
                return Ok(true);
            }
            if self.txn.mvars.assignments().len() == before {
                return Ok(false);
            }
        }
    }

    /// Instantiate a rule afresh at the first eligible occurrence. Traversal
    /// order is explicit: rewriting searches outside-in, simplification inside-out.
    /// Bound-variable occurrences needing a newly opened binder are not guessed.
    pub(in crate::source) fn instantiate_rewrite_rule(
        &mut self,
        mut rule: Typed,
        target: &Expr,
        reverse: bool,
        inside_out: bool,
        selected_rules: &[SimpRule<'_>],
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        self.flush(false)?;
        let mut template = self.rewrite_trial();
        let mut implicit_holes = Vec::new();
        // Rule elaboration has already inserted implicit arguments. They are
        // obligations too, even when equality transport later erases the rule.
        rule.value = template.instantiate(&rule.value)?;
        let mut pending = vec![&rule.value];
        let mut visited = HashSet::new();
        while let Some(term) = pending.pop() {
            template.tick()?;
            if !visited.insert(term.allocation_identity()) {
                continue;
            }
            if let ExprNode::MVar { id } = term.node()
                && !implicit_holes.contains(id)
            {
                implicit_holes.push(id.clone());
            }
            pending.extend(children(term).into_iter().rev().flatten());
        }
        let mut holes = Vec::new();
        loop {
            template.tick()?;
            rule.type_ = template.whnf(&rule.type_)?;
            // A refutation is a rewrite of its proposition to False, not an
            // implication whose antecedent simp must first prove. Stop before
            // consuming that final proof binder; outer parameters still infer
            // normally from the selected occurrence.
            if inside_out && template.simp_negated_proposition(&rule.type_)?.is_some() {
                break;
            }
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = rule.type_.node()
            else {
                break;
            };
            let domain = binder_type.clone();
            let body = body.clone();
            let argument = if *binder_info == BinderInfo::InstImplicit {
                template.instance_hole(domain)?
            } else {
                template.hole(domain)?
            };
            if let ExprNode::MVar { id } = argument.node() {
                holes.push(id.clone());
            }
            rule.type_ = template.substitute(&body, &argument)?;
            rule.value = Expr::app(rule.value, argument);
        }
        // Rewrite's newly applied parameters precede the unresolved implicit
        // arguments inserted while elaborating the selected rule expression.
        holes.extend(implicit_holes);
        // A known class input must select its dictionary before matching a
        // pattern containing that dictionary. Synthetic-opaque instance holes
        // cannot be assigned by occurrence unification. Inputs learned from
        // the occurrence still get the second synthesis pass below.
        let resolution = template.resolve_instances(false);
        self.charge_rewrite_trial(&template);
        resolution?;
        let compiled = (|| {
            let rule = template.equivalence_rewrite_rule(rule)?;
            if inside_out {
                let rule = template.simp_proposition_rewrite_rule(rule, reverse)?;
                template.equivalence_rewrite_rule(rule)
            } else {
                Ok(rule)
            }
        })();
        self.charge_rewrite_trial(&template);
        let rule = compiled?;
        let Some((_, alpha, lhs, rhs)) = equality_target(&rule.type_) else {
            // An explicitly selected proposition proof can discharge another
            // rule's premise without itself being an equality rewrite.
            if inside_out && let Some(universe) = template.known_type(&rule.type_)? {
                let universe = template.whnf(&universe)?;
                if matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                    self.charge_rewrite_trial(&template);
                    return Ok(None);
                }
            }
            return Err(error(TacticError::ExpectedEquality));
        };
        let pattern = if reverse { rhs } else { lhs };
        self.charge_rewrite_trial(&template);
        if !inside_out {
            let pattern = template.instantiate(&pattern)?;
            self.charge_rewrite_trial(&template);
            let mut head = &pattern;
            loop {
                self.tick()?;
                match head.node() {
                    ExprNode::App { f, .. } => head = f,
                    ExprNode::MData { expr, .. } => head = expr,
                    ExprNode::MVar { .. } => {
                        return Err(error(TacticError::RewriteMetavariablePattern));
                    }
                    _ => break,
                }
            }
        }
        let mut pending = vec![(target, false)];
        let mut visited = HashSet::new();
        while let Some((term, exit)) = pending.pop() {
            self.tick()?;
            if !exit {
                if !visited.insert(term.allocation_identity()) {
                    continue;
                }
                if inside_out {
                    pending.push((term, true));
                    pending.extend(
                        children(term)
                            .into_iter()
                            .rev()
                            .flatten()
                            .map(|child| (child, false)),
                    );
                    continue;
                }
                pending.extend(
                    children(term)
                        .into_iter()
                        .rev()
                        .flatten()
                        .map(|child| (child, false)),
                );
            }
            if term.has_loose_bvars() {
                continue;
            }
            let mut trial = template.rewrite_trial();
            trial.txn.budget = self.txn.budget.clone();
            let attempt = (|| {
                if !trial.match_rewrite_occurrence(&pattern, &alpha, term)? {
                    return Ok(None);
                }
                trial.resolve_instances(false)?;
                if holes
                    .iter()
                    .any(|id| trial.instance_goals.contains(id) && !trial.txn.mvars.is_assigned(id))
                {
                    return Ok(None);
                }
                if inside_out && !trial.discharge_rewrite_premises(&holes, selected_rules)? {
                    return Ok(None);
                }
                let value = trial.instantiate(&rule.value)?;
                let type_ = trial.instantiate(&rule.type_)?;
                if value.has_level_mvar()
                    || type_.has_level_mvar()
                    || inside_out && (value.has_expr_mvar() || type_.has_expr_mvar())
                {
                    return Ok(None);
                }
                let occurrence = trial.instantiate(term)?;
                if inside_out {
                    let (_, _, from, to) =
                        equality_target(&type_).expect("instantiated equality retains its shape");
                    let replacement = if reverse { from } else { to };
                    if trial.rewrite_same(&occurrence, &replacement)? {
                        return Ok(None);
                    }
                }
                let mut premises = Vec::new();
                if !inside_out {
                    for id in &holes {
                        trial.tick()?;
                        if trial.txn.mvars.is_assigned(id) {
                            continue;
                        }
                        let declaration = trial
                            .txn
                            .mvars
                            .get_decl(id)
                            .expect("rule parameter was declared")
                            .clone();
                        let target = trial.instantiate(&declaration.type_)?;
                        if let Some(universe) = trial.known_type(&target)? {
                            let universe = trial.whnf(&universe)?;
                            if matches!(universe.node(), ExprNode::Sort { level } if level.is_zero())
                            {
                                trial
                                    .txn
                                    .mvars
                                    .set_kind(id, MetavarKind::SyntheticOpaque)
                                    .map_err(|e| {
                                        failure(SourceInferenceError::Unification(Box::new(
                                            UnificationError::Metavariable(e),
                                        )))
                                    })?;
                            }
                        }
                        premises.push(ProofGoal {
                            id: id.clone(),
                            target,
                            lctx: declaration.lctx,
                            introduced: Vec::new(),
                        });
                    }
                }
                Ok(Some(RewriteMatch {
                    rule: Typed { value, type_ },
                    occurrence,
                    premises,
                }))
            })();
            self.charge_rewrite_trial(&trial);
            match attempt {
                Ok(Some(rule)) => {
                    *self = trial;
                    return Ok(Some(rule));
                }
                Ok(None) => {}
                Err(error) if Self::rewrite_nonmatch(&error) => {}
                Err(error) => return Err(error),
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod outcome_tests {
    use super::*;

    fn context() -> Context {
        use fln_env::environment::DeclarationBudget;
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let mut env = Environment::new();
        for declaration in [
            crate::seed::nat_inductive_seed_declaration(),
            crate::seed::bool_seed_declaration(),
            crate::seed::eq_seed_declaration(),
        ] {
            let Outcome::Complete(admitted) = admit(&env, declaration, budget) else {
                panic!("seed admission did not complete");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("seed was rejected");
            };
            let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) else {
                panic!("seed publication did not complete");
            };
            env = publication.environment;
        }
        Context::new(&env, budget)
    }

    #[test]
    fn incompatible_type_heads_skip_large_terms_without_spending_the_match_budget() {
        let mut ctx = context();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let id = FVarId(Name::from_components(["function"]));
        ctx.txn.lctx.add_param(
            id.clone(),
            id.0.clone(),
            Expr::forall_e(
                Name::anonymous(),
                nat.clone(),
                nat.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut pattern = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let succ = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
        for _ in 0..128 {
            pattern = Expr::app(succ.clone(), pattern);
        }
        let before = ctx.txn.clone();
        ctx.txn.budget.max_heartbeats = 64;
        assert!(
            !ctx.match_rewrite_occurrence(&pattern, &nat, &Expr::fvar(id))
                .unwrap()
        );
        assert!(ctx.txn.budget.heartbeats_consumed < 64);
        assert!(ctx.txn.budget.heartbeats_consumed > 0);
        assert_eq!(ctx.txn.env, before.env);
        assert_eq!(ctx.txn.mvars, before.mvars);
        assert_eq!(ctx.txn.universes, before.universes);
        assert_eq!(ctx.txn.lctx, before.lctx);
        assert!(ctx.equations.is_empty());
    }

    #[test]
    fn type_head_discrimination_requires_real_arity_and_leaves_flexible_types_to_inference() {
        let mut ctx = context();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        assert_eq!(
            ctx.rigid_rewrite_type_head(&nat).unwrap(),
            Some(RigidTypeHead::Inductive(Name::from_components(["Nat"])))
        );
        for unknown in [
            Expr::const_(Name::from_components(["Missing"]), vec![]),
            Expr::const_(Name::from_components(["Nat"]), vec![Level::one()]),
            Expr::app(nat.clone(), zero.clone()),
            Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
            Expr::let_e(
                Name::anonymous(),
                Expr::sort(Level::one()),
                nat.clone(),
                Expr::bvar(0).unwrap(),
                false,
            ),
        ] {
            assert_eq!(ctx.rigid_rewrite_type_head(&unknown).unwrap(), None);
        }
        let carrier = ctx.hole(Expr::sort(Level::one())).unwrap();
        assert_eq!(ctx.rigid_rewrite_type_head(&carrier).unwrap(), None);
        assert!(
            ctx.match_rewrite_occurrence(&zero, &carrier, &zero)
                .unwrap()
        );
        assert_eq!(ctx.instantiate(&carrier).unwrap(), nat);
    }

    #[test]
    fn matching_same_type_heads_still_checks_indices_and_resource_stops() {
        let mut ctx = context();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_components(["Nat", "succ"]), vec![]),
            zero.clone(),
        );
        let eq = Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]);
        let equal = app(eq.clone(), [nat.clone(), zero.clone(), zero.clone()]);
        let unequal = app(eq, [nat.clone(), zero.clone(), one]);
        assert_eq!(
            ctx.rigid_rewrite_type_head(&equal).unwrap(),
            ctx.rigid_rewrite_type_head(&unequal).unwrap()
        );
        let id = FVarId(Name::from_components(["proof"]));
        ctx.txn
            .lctx
            .add_param(id.clone(), id.0.clone(), equal, BinderInfo::Default);
        let term = Expr::fvar(id);
        let problem = ctx
            .match_rewrite_occurrence(&term, &unequal, &term)
            .unwrap_err();
        assert!(Context::rewrite_nonmatch(&problem));
        assert!(ctx.txn.mvars.assignments().is_empty());
        ctx.txn.budget.max_heartbeats = ctx.txn.budget.heartbeats_consumed + 1;
        let problem = ctx
            .rigid_rewrite_type_head(&Expr::app(nat, zero))
            .unwrap_err();
        assert!(matches!(
            problem,
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
        ));
        assert!(!Context::rewrite_nonmatch(&problem));
    }

    #[test]
    fn proof_conversion_stops_cannot_be_hidden_by_tactics_rewriting_or_instance_search() {
        use fln_core::outcome::InternalFault;
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let exhausted = fln_kernel::check_def_eq(
            &Environment::new(),
            &[],
            &Expr::sort(Level::zero()),
            &Expr::sort(Level::zero()),
            budget.narrowed(0, budget.depth),
        );
        assert!(matches!(&exhausted, Outcome::Inconclusive(_)));
        for outcome in [
            exhausted,
            Outcome::InternalFault(InternalFault::new("planted conversion", "test fault")),
        ] {
            let problem = failure(SourceInferenceError::Unification(Box::new(
                UnificationError::ConversionCheck {
                    outcome: Box::new(outcome),
                },
            )));
            assert!(!crate::source::tactics::backtrack::recoverable(&problem));
            assert!(!crate::source::instances::nonmatch(&problem));
            assert!(!Context::rewrite_nonmatch(&problem));
        }
    }
}
