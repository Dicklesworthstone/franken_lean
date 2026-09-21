//! Simplification of local types retains every transport and selected proof.
//! Whole-context saturation shares its productive budget with goal simplification.
use super::*;

impl Context {
    pub(super) fn simp_hypothesis_step(
        &mut self,
        local: &LocalDecl,
        rule: &SimpRule<'_>,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let target = self.instantiate(&local.type_)?;
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(type_) => Ok(Some(Typed {
                value: Expr::fvar(local.id.clone()),
                type_,
            })),
            UnfoldResult::NotDefinition => {
                let mut term = self.selected_simp_term(rule)?;
                term.type_ = self.simp_premise_target(&term.type_, rules)?;
                let Some(RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                }) = self.instantiate_rewrite_rule(term, &target, rule.reverse(), true, rules)?
                else {
                    return Ok(None);
                };
                assert!(premises.is_empty(), "simp discharges its own premises");
                self.rewrite_hypothesis_value(local, term, &occurrence, rule.reverse())
                    .map(Some)
            }
        }
    }

    /// `simp_all` selects the current propositional evidence and revisits
    /// earlier hypotheses whenever a later one changes. This is not a loop of
    /// independent `simp` calls: identities, cycle history and spent work survive
    /// every round, and the goal consumes the same productive-step budget.
    pub(in crate::source) fn simplify_all_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, config, discharger, only, arguments] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "simp_all", "whole-context simplification keyword")?;
        expect_empty_null(config, "default simplification configuration")?;
        // Reuse the ordinary set parser without reparsing source or changing
        // the persistent registry. Its location slot is an empty null node.
        let selection = [
            Syntax::Atom {
                info: keyword.info(),
                val: "simp".to_string(),
            },
            config.clone(),
            discharger.clone(),
            only.clone(),
            arguments.clone(),
            config.clone(),
        ];
        self.txn.lctx = initial.lctx.clone();
        let mut rules = self.simp_rules(&selection)?;
        let mut hypotheses = Vec::new();
        let mut selected = HashSet::new();
        for rule in &rules {
            self.tick()?;
            if let SimpRule::Local(id) = rule {
                selected.insert(id.clone());
            }
        }
        for local in initial.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            let Some(sort) = self.known_type(&type_)? else {
                continue;
            };
            let sort = self.whnf(&sort)?;
            if sort.has_expr_mvar()
                || sort.has_level_mvar()
                || !self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
            {
                continue;
            }
            if selected.insert(local.id.clone()) {
                rules.push(SimpRule::Local(local.id.clone()));
            }
            // Shadowed and inaccessible locals may provide evidence by ID,
            // but must never redirect a source-visible simplification location.
            if !local.user_name.is_anonymous()
                && scope::components(&local.user_name).is_ok()
                && initial
                    .lctx
                    .find_by_user_name(&local.user_name)
                    .is_some_and(|visible| visible.id == local.id)
            {
                hypotheses.push(local.user_name.clone());
            }
        }
        let locations = super::super::locations::RewriteLocations {
            hypotheses,
            target: true,
            all: true,
        };
        self.simplify_location_rules(proof, &initial, locations, rules, true)
    }

    pub(super) fn simplify_at_locations(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: &ProofGoal,
        args: &[Syntax],
    ) -> Result<bool, NatDefinitionElabError> {
        let [_, _, _, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        self.txn.lctx = initial.lctx.clone();
        let Some(locations) = self.rewrite_locations(location)? else {
            return Ok(false);
        };
        let rules = self.simp_rules(args)?;
        self.simplify_location_rules(proof, initial, locations, rules, false)?;
        Ok(true)
    }

    fn simplify_location_rules(
        &mut self,
        proof: &mut ProofState<'_>,
        initial: &ProofGoal,
        locations: super::super::locations::RewriteLocations,
        mut rules: Vec<SimpRule<'_>>,
        saturate: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let mut protected = HashSet::new();
        if locations.all {
            // Preserve explicitly selected evidence for the entire traversal.
            // Automatically selected locals are remapped after each transport.
            for rule in &rules {
                self.tick()?;
                if !matches!(rule, SimpRule::Explicit(_)) {
                    continue;
                }
                let mut trial = self.rewrite_trial();
                let inspected = (|| {
                    let term = trial.selected_simp_term(rule)?;
                    trial.flush(false)?;
                    trial.wildcard_rule_dependencies(&term)
                })();
                self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
                protected.extend(inspected?);
            }
        }
        let mut histories = Vec::new();
        for name in &locations.hypotheses {
            self.tick()?;
            let local = initial
                .lctx
                .find_by_user_name(name)
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            histories.push(vec![self.instantiate(&local.type_)?]);
        }
        let mut goal = initial.clone();
        let mut steps = 0;
        loop {
            let previous_steps = steps;
            for (name, history) in locations.hypotheses.iter().zip(&mut histories) {
                self.txn.lctx = goal.lctx.clone();
                let local = goal
                    .lctx
                    .find_by_user_name(name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                if protected.contains(&local.id) {
                    continue;
                }
                loop {
                    self.tick()?;
                    self.txn.lctx = goal.lctx.clone();
                    let local = goal
                        .lctx
                        .find_by_user_name(name)
                        .cloned()
                        .ok_or_else(|| error(TacticError::RewriteLocation))?;
                    let mut advanced = false;
                    // Self evidence is also unavailable for premise discharge.
                    let active: Vec<_> = rules
                        .iter()
                        .filter(|rule| !matches!(rule, SimpRule::Local(id) if id == &local.id))
                        .cloned()
                        .collect();
                    for rule in &active {
                        self.tick()?;
                        let original = self.rewrite_trial();
                        let Some(replacement) = self.simp_hypothesis_step(&local, rule, &active)?
                        else {
                            self.restore_simp_trial(original);
                            continue;
                        };
                        if steps >= MAX_SIMPLIFICATION_STEPS {
                            return Err(failure(SourceInferenceError::ResourceLimit));
                        }
                        let target = self.instantiate(&replacement.type_)?;
                        for previous in history.iter() {
                            self.tick()?;
                            if self.rewrite_same(previous, &target)? {
                                return Err(error(TacticError::SimplificationCycle));
                            }
                        }
                        history.push(target);
                        let (next, parent, value) =
                            self.replace_rewritten_hypothesis(goal, &local, replacement)?;
                        let replacement_id = next
                            .lctx
                            .find_by_user_name(name)
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?
                            .id
                            .clone();
                        for rule in &mut rules {
                            self.tick()?;
                            if let SimpRule::Local(id) = rule
                                && id == &local.id
                            {
                                *id = replacement_id.clone();
                            }
                        }
                        proof.work.push(Work::Close(parent, value));
                        goal = next;
                        steps += 1;
                        advanced = true;
                        break;
                    }
                    if !advanced {
                        break;
                    }
                }
            }
            if !saturate || steps == previous_steps {
                break;
            }
        }
        if locations.target {
            return self.simplify_goal_with_rules(proof, goal, &rules, steps, None);
        }
        if steps == 0 {
            return Err(error(TacticError::SimplificationNoProgress));
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }
}
