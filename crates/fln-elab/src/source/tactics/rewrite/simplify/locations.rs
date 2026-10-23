//! Simplification of local types retains every transport and selected proof.
//! Whole-context saturation shares its productive budget with goal simplification.
use super::*;

impl Context {
    /// One rewriting step on a located hypothesis, and whether it unfolded a definition,
    /// which needs no proof.
    pub(super) fn simp_hypothesis_step(
        &mut self,
        local: &LocalDecl,
        rule: &SimpRule<'_>,
        rules: &[SimpRule<'_>],
    ) -> Result<Option<(Typed, bool)>, NatDefinitionElabError> {
        let target = self.instantiate(&local.type_)?;
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(type_) => Ok(Some((
                Typed {
                    value: Expr::fvar(local.id.clone()),
                    type_,
                },
                true,
            ))),
            UnfoldResult::NotDefinition => {
                let Some((term, occurrence, reverse)) =
                    self.simp_rule_evidence(&target, rule, rules)?
                else {
                    return Ok(None);
                };
                self.rewrite_hypothesis_value(local, term, &occurrence, reverse)
                    .map(|replacement| Some((replacement, false)))
            }
        }
    }

    /// Whether a rule rewrites definitionally, as the pin's `isRflProof` classifies a simp
    /// theorem's proof: a defeq-tagged constant or a structural `rfl`. A local hypothesis is
    /// never one. The tags are read once per tactic, on the first step that asks.
    fn simp_rule_reflexive(
        &mut self,
        rule: &SimpRule<'_>,
        tagged: &mut Option<std::collections::BTreeSet<Name>>,
    ) -> Result<bool, NatDefinitionElabError> {
        // A linear normalization's proof is a reflection proof, not `rfl`.
        if matches!(rule, SimpRule::Local(_) | SimpRule::Arith) {
            return Ok(false);
        }
        let tagged = match tagged {
            Some(tagged) => &*tagged,
            None => {
                let environment = self.txn.env.clone();
                &*tagged.insert(scope::simp::defeq::read(&environment, || self.tick())?)
            }
        };
        if let SimpRule::Global(entry) = rule {
            let name = entry.proof.as_ref().unwrap_or(&entry.declaration);
            if matches!(self.txn.env.find(name), Some(ConstantInfo::Thm(_))) {
                return Ok(tagged.contains(name));
            }
        }
        let mut trial = self.rewrite_trial();
        let reflexive = (|| {
            let term = trial.selected_simp_term(rule)?;
            trial.dsimp_rfl_proof(term, tagged)
        })();
        self.charge_rewrite_trial(&trial);
        reflexive
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
        // The configuration is read, and `+arith` admitted, by the ordinary set parser.
        // Reuse the ordinary set parser without reparsing source or changing
        // the persistent registry. Its location slot is an empty null node.
        let no_location = Syntax::node(Name::from_components(["null"]), Vec::new());
        let selection = [
            Syntax::Atom {
                info: keyword.info(),
                val: "simp".to_string(),
            },
            config.clone(),
            discharger.clone(),
            only.clone(),
            arguments.clone(),
            no_location,
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
        // `+arith`'s normalization stays after every rule, the context's facts included.
        if let Some(index) = rules
            .iter()
            .position(|rule| matches!(rule, SimpRule::Arith))
        {
            let arith = rules.remove(index);
            rules.push(arith);
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
        let mut tagged = None;
        // `simp_all` hypotheses it reduced to `True` and cleared, never asserted again.
        let mut cleared = HashSet::new();
        loop {
            let previous_steps = steps;
            for (name, history) in locations.hypotheses.iter().zip(&mut histories) {
                if cleared.contains(name) {
                    continue;
                }
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
                    let target = self.instantiate(&local.type_)?;
                    let index = self.simp_target_index(&target)?;
                    for rule in &active {
                        if !self.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite) {
                            continue;
                        }
                        self.tick()?;
                        let original = self.rewrite_trial();
                        let Some((replacement, unfolded)) =
                            self.simp_hypothesis_step(&local, rule, &active)?
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
                        // A hypothesis simplified to `False` closes the goal (`applySimpResult`,
                        // `Simp/Main.lean:808`): `False.elim` of the rewritten evidence.
                        if is_false(&self.instantiate(&replacement.type_)?) {
                            let target = self.instantiate(&goal.target)?;
                            let sort = self
                                .known_type(&target)?
                                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                            let level = self.sort_level(&Typed {
                                value: target.clone(),
                                type_: sort,
                            })?;
                            self.constant(&Name::from_components(["False", "elim"]))?;
                            let value = app(
                                Expr::const_(Name::from_components(["False", "elim"]), vec![level]),
                                [target, replacement.value],
                            );
                            return self.close_proof_goal(goal, value);
                        }
                        // `SimpAll.main` asserts no hypothesis that became `True`: it leaves
                        // the goal, and its rewriting proof never enters the term.
                        let removed = HashSet::from([local.id.clone()]);
                        if saturate
                            && is_true(&self.instantiate(&replacement.type_)?)
                            && self.clear_blocker(&goal, &removed)?.is_none()
                        {
                            rules.retain(
                                |rule| !matches!(rule, SimpRule::Local(id) if id == &local.id),
                            );
                            goal = self.cleared_proof_goal(proof, goal, &removed)?;
                            cleared.insert(name.clone());
                            steps += 1;
                            break;
                        }
                        // `simpGoal` asserts a hypothesis whose simplification needs a proof
                        // after every local, in located order, and changes one simplified only
                        // definitionally in place (`replaceLocalDeclDefEq`). Measured at
                        // v4.32.0: `h : 1 = 1` becomes the last local, `h : a + 0 = 1` stays.
                        // `simp_all` re-asserts by its own rule.
                        let at_end = !saturate
                            && !unfolded
                            && !self.simp_rule_reflexive(rule, &mut tagged)?;
                        let (next, parent, value) =
                            self.replace_rewritten_hypothesis(goal, &local, replacement, at_end)?;
                        let replacement_id = next
                            .lctx
                            .find_by_user_name(name)
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?
                            .id
                            .clone();
                        if saturate {
                            for rule in &mut rules {
                                self.tick()?;
                                if let SimpRule::Local(id) = rule
                                    && id == &local.id
                                {
                                    *id = replacement_id.clone();
                                }
                            }
                        } else {
                            // The pin builds its simp set once, so a located
                            // hypothesis that was actually rewritten keeps no
                            // rule for the rest of the tactic — measured at
                            // v4.32.0: neither its old form nor its rewritten
                            // form fires afterwards, while an unrewritten
                            // located hypothesis's rule stays live. Only
                            // `simp_all`'s saturating revisits remap.
                            let _ = &replacement_id;
                            rules.retain(
                                |rule| !matches!(rule, SimpRule::Local(id) if id == &local.id),
                            );
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
        if saturate {
            // `simp_all` keeps no hypothesis left as `True` (`SimpAll.main`'s `tryClearMany`),
            // one it was given as `True` included, while `simp at h` does.
            let mut trivial = Vec::new();
            for name in &locations.hypotheses {
                self.tick()?;
                if cleared.contains(name) {
                    continue;
                }
                let Some(local) = goal.lctx.find_by_user_name(name) else {
                    continue;
                };
                if is_true(&self.instantiate(&local.type_)?) {
                    trivial.push(local.id.clone());
                }
            }
            if !trivial.is_empty() {
                let before: HashSet<_> = goal
                    .lctx
                    .decls()
                    .iter()
                    .map(|local| local.id.clone())
                    .collect();
                goal = self.try_clear_proof_locals(proof, goal, &trivial)?;
                let after: HashSet<_> = goal
                    .lctx
                    .decls()
                    .iter()
                    .map(|local| local.id.clone())
                    .collect();
                rules.retain(|rule| {
                    !matches!(rule, SimpRule::Local(id) if before.contains(id) && !after.contains(id))
                });
            }
            // `SimpAll.main` re-asserts the first hypothesis whose type changed and every
            // hypothesis after it, at the end of the context in their order, and clears the
            // originals: measured at v4.32.0, `(h₁ : a + 0 = 1) (q : Prop) (h₃ : b = 2)
            // (r : Prop)` ends as `q r : Prop`, `h₁ : a = 1`, `h₃ : b = 2`. A hypothesis left as
            // `True` is not asserted, and one that other locals or the target read is not one
            // of its entries.
            let mut moving = false;
            for (name, history) in locations.hypotheses.iter().zip(&histories) {
                self.tick()?;
                if cleared.contains(name) {
                    continue;
                }
                let Some(local) = goal.lctx.find_by_user_name(name).cloned() else {
                    continue;
                };
                if is_true(&self.instantiate(&local.type_)?) {
                    continue;
                }
                moving |= history.len() > 1;
                if !moving
                    || self
                        .clear_blocker(&goal, &HashSet::from([local.id.clone()]))?
                        .is_some()
                {
                    continue;
                }
                self.txn.lctx = goal.lctx.clone();
                let moved = Typed {
                    value: Expr::fvar(local.id.clone()),
                    type_: local.type_.clone(),
                };
                let (next, parent, value) =
                    self.replace_rewritten_hypothesis(goal, &local, moved, true)?;
                let moved_id = next
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
                        *id = moved_id.clone();
                    }
                }
                proof.work.push(Work::Close(parent, value));
                goal = next;
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

fn is_true(type_: &Expr) -> bool {
    matches!(type_.node(), ExprNode::Const { name, levels }
        if levels.is_empty() && *name == Name::from_components(["True"]))
}

fn is_false(type_: &Expr) -> bool {
    matches!(type_.node(), ExprNode::Const { name, levels }
        if levels.is_empty() && *name == Name::from_components(["False"]))
}
