//! Reflexivity classification is structural, never proof-irrelevance conversion.
use super::*;

impl Context {
    pub(super) fn dsimp_set<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<DsimpSet<'a>, NatDefinitionElabError> {
        let environment = self.txn.env.clone();
        let tagged = scope::simp::defeq::read(&environment, || self.tick())?;
        let mut set = DsimpSet {
            definitions: Vec::new(),
            rewrites: Vec::new(),
            tagged,
        };
        for rule in self.simp_rules(args)? {
            // A named, admitted theorem already has a proposition telescope.
            // The pin's isRflProof classifies a constant by its defeq tag,
            // without instantiating universes or re-inferring that telescope.
            // Test the actual proof, not its attribute origin: imported rules
            // may store a distinct, already-oriented proof declaration.
            if let SimpRule::Global(entry) = &rule {
                self.tick()?;
                let name = entry.proof.as_ref().unwrap_or(&entry.declaration);
                if matches!(self.txn.env.find(name), Some(ConstantInfo::Thm(_))) {
                    if set.tagged.contains(name) {
                        set.rewrites.push((rule, std::cell::Cell::new(Some(true))));
                    }
                    continue;
                }
            }
            // Other registered proof forms retain the existing lazy validation.
            // Missing declarations, axioms and definition-backed proofs must
            // not gain theorem authority from their journal entry alone.
            if matches!(rule, SimpRule::Global(_)) && !self.simp_rule_may_unfold(&rule) {
                set.rewrites.push((rule, std::cell::Cell::new(None)));
                continue;
            }
            // A registered definition selects itself by name: no elaboration, so no
            // speculative copy of the context, which cost one clone per registered
            // definition per call. Only an explicit term needs the trial below.
            if matches!(rule, SimpRule::Global(_))
                && let Some(selection) = self.simp_unfold_selection_for_rule(&rule)?
            {
                set.definitions.push(selection);
                continue;
            }
            self.tick()?;
            // Eligibility probes are not instance-synthesis/admission effects.
            // Resolve fully and charge each candidate without keeping its holes.
            let mut trial = self.rewrite_trial();
            let classified = (|| {
                if let Some(selection) = trial.simp_unfold_selection_for_rule(&rule)? {
                    return Ok((Some(selection), false));
                }
                Ok((None, trial.dsimp_reflexive_rule(&rule, &set.tagged)?))
            })();
            self.charge_rewrite_trial(&trial);
            let (selection, reflexive) = classified?;
            if let Some(selection) = selection {
                set.definitions.push(selection);
            }
            if reflexive {
                set.rewrites.push((rule, std::cell::Cell::new(Some(true))));
            }
        }
        Ok(set)
    }

    /// Whether a theorem rule is structurally reflexive: a proposition whose proof is
    /// `rfl` (or carries the pin's `rfl` tag). A non-proposition is a malformed rule.
    fn dsimp_reflexive_rule(
        &mut self,
        rule: &SimpRule<'_>,
        tagged: &std::collections::BTreeSet<Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        let term = self.selected_simp_term(rule)?;
        if !self.dsimp_is_proposition(&term.type_)? {
            return Err(error(TacticError::InvalidSimpTheorem));
        }
        self.dsimp_rfl_proof(term, tagged)
    }

    pub(super) fn dsimp_spine(
        &mut self,
        term: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = term.clone();
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
        arguments.reverse();
        Ok((head, arguments))
    }

    /// Constant proofs are classified by source metadata, not by unfolding
    /// theorem bodies. Parenthesized/tactic proofs do not implicitly acquire the
    /// pin's automatic `:= rfl` tag. Nonconstant reflexivity proofs retain the
    /// structural Eq.refl / rfl / Eq.symm cases from the pinned implementation.
    pub(in crate::source) fn dsimp_rfl_proof(
        &mut self,
        mut term: Typed,
        tagged: &std::collections::BTreeSet<Name>,
    ) -> Result<bool, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let ExprNode::Const { name, .. } = term.value.node() {
                return Ok(tagged.contains(name));
            }
            while let ExprNode::ForallE {
                body: type_body, ..
            } = term.type_.node()
            {
                self.tick()?;
                let ExprNode::Lam { body, .. } = term.value.node() else {
                    return Ok(false);
                };
                term = Typed {
                    value: body.clone(),
                    type_: type_body.clone(),
                };
            }
            if equality_target(&term.type_).is_none() {
                return Ok(false);
            }
            let (head, arguments) = self.dsimp_spine(&term.value)?;
            let ExprNode::Const { name, .. } = head.node() else {
                return Ok(false);
            };
            if arguments.len() == 2
                && (name == &Name::from_components(["Eq", "refl"])
                    || name == &Name::from_components(["rfl"]))
            {
                return Ok(true);
            }
            if name == &Name::from_components(["Eq", "symm"]) && arguments.len() == 4 {
                term.value = arguments[3].clone();
                continue;
            }
            return Ok(tagged.contains(name));
        }
    }

    /// Validate the whole user theorem with rigid parameters, never a lucky
    /// use-site specialization. Naked source `:= rfl` prepends the explicit
    /// defeq attribute in the pin; that validator allows safe delta, including
    /// irreducible definitions. Generated-equation inference is a different API.
    /// Arbitrary local equality evidence does not enter this metadata path.
    pub(in crate::source) fn dsimp_generic_defeq(
        &mut self,
        type_: &Expr,
        levels: &[Name],
    ) -> Result<bool, NatDefinitionElabError> {
        let mut trial = self.rewrite_trial();
        let result = (|| {
            for level in levels {
                trial.tick()?;
                if !trial.level_params.contains(level) {
                    trial.level_params.push(level.clone());
                }
            }
            let mut target = type_.clone();
            loop {
                trial.tick()?;
                target = trial.whnf_with_transparency(
                    &target,
                    UnificationTransparency::SafeDefinitions,
                    false,
                )?;
                let ExprNode::ForallE {
                    binder_type,
                    body,
                    binder_info,
                    ..
                } = target.node()
                else {
                    break;
                };
                let mut local = trial.equality_local(binder_type.clone())?;
                local.binder_info = *binder_info;
                eliminate::add_local(&mut trial.txn.lctx, &local);
                target = trial.substitute(body, &Expr::fvar(local.id))?;
            }
            let Some((_, _, left, right)) = equality_target(&target) else {
                return Ok(false);
            };
            let mut budget = UnificationBudget::new(trial.kernel);
            budget.transparency = UnificationTransparency::SafeDefinitions;
            budget.zeta_delta = false;
            trial.proof_types_match_with_budget(&left, &right, budget)
        })();
        self.charge_rewrite_trial(&trial);
        result
    }

    /// Try at this exact node. The caller has already selected which children
    /// are eligible; a recursive rule search would violate that decision.
    pub(super) fn dsimp_rewrite(
        &mut self,
        target: &Expr,
        set: &DsimpSet<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let index = self.simp_root_index(target)?;
        for (rule, reflexive) in &set.rewrites {
            if !self.simp_rule_admitted(rule, index.as_ref(), SimpKeySide::Rewrite) {
                continue;
            }
            if reflexive.get().is_none() {
                self.tick()?;
                let mut trial = self.rewrite_trial();
                let classified = trial.dsimp_reflexive_rule(rule, &set.tagged);
                self.charge_rewrite_trial(&trial);
                reflexive.set(Some(classified?));
            }
            if reflexive.get() != Some(true) {
                continue;
            }
            self.tick()?;
            let mut trial = self.rewrite_trial();
            let attempt = (|| {
                let term = trial.selected_simp_term(rule)?;
                let Some(found) = trial.instantiate_dsimp_rule(term, target, rule.reverse())?
                else {
                    return Ok(None);
                };
                if !found.premises.is_empty() || !trial.rewrite_same(target, &found.occurrence)? {
                    return Err(error(TacticError::MalformedScript));
                }
                let (_, _, left, right) = equality_target(&found.rule.type_)
                    .ok_or_else(|| error(TacticError::ExpectedEquality))?;
                let replacement = if rule.reverse() { left } else { right };
                // Matching remains at the selected-rule policy. Only after a
                // tagged, admitted reflexivity rule matches may its replacement
                // use the attribute validator's stronger conversion policy.
                let mut budget = UnificationBudget::new(trial.kernel);
                budget.transparency = UnificationTransparency::SafeDefinitions;
                budget.zeta_delta = false;
                if !trial.proof_types_match_with_budget(target, &replacement, budget)? {
                    return Ok(None);
                }
                let replacement = trial.instantiate(&replacement)?;
                if trial.rewrite_same(target, &replacement)? {
                    return Ok(None);
                }
                Ok(Some(replacement))
            })();
            self.charge_rewrite_trial(&trial);
            match attempt? {
                Some(next) => {
                    *self = trial;
                    return Ok(next);
                }
                None => continue,
            }
        }
        Ok(target.clone())
    }
}

#[cfg(test)]
mod selection_tests {
    use super::*;
    use fln_env::constants::{ConstantVal, TheoremVal};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_syntax::source::SourceInfo;

    fn n(label: &str) -> Name {
        Name::from_components(label.split('.'))
    }
    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }
    fn publish(env: &Environment, decl: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(env, decl, budget()) else {
            panic!("fixture admission must complete")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture must pass the kernel")
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("fixture publication: {other:?}"),
        }
    }
    fn theorem(env: &Environment, label: &str, depth: usize) -> Environment {
        let u = Level::param(n("u"));
        let a = Expr::bvar(1).unwrap();
        let x = Expr::bvar(0).unwrap();
        let mut type_ = Expr::forall_e(
            n("A"),
            Expr::sort(u.clone()),
            Expr::forall_e(
                n("x"),
                Expr::bvar(0).unwrap(),
                app(
                    Expr::const_(n("Eq"), vec![u.clone()]),
                    [a.clone(), x.clone(), x.clone()],
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut value = Expr::lam(
            n("A"),
            Expr::sort(u.clone()),
            Expr::lam(
                n("x"),
                Expr::bvar(0).unwrap(),
                app(Expr::const_(n("Eq.refl"), vec![u]), [a, x]),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        for _ in 0..depth {
            type_ = Expr::forall_e(
                n("unused"),
                Expr::sort(Level::one()),
                type_,
                BinderInfo::Default,
            );
            value = Expr::lam(
                n("unused"),
                Expr::sort(Level::one()),
                value,
                BinderInfo::Default,
            );
        }
        publish(
            env,
            Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: n(label),
                    level_params: vec![n("u")],
                    type_,
                },
                value,
                all: vec![n(label)],
            }),
        )
    }
    fn environment() -> Environment {
        publish(&Environment::new(), crate::seed::eq_seed_declaration())
    }
    fn args() -> Vec<Syntax> {
        let null = || Syntax::node(n("null"), vec![]);
        vec![
            Syntax::atom(SourceInfo::None, "dsimp"),
            Syntax::node(parser_kind(&["Tactic", "optConfig"]), vec![null()]),
            null(),
            null(),
            null(),
            null(),
        ]
    }
    fn registered(env: &Environment, origin: &str, proof: &str) -> Environment {
        scope::simp::register_imported_proof(env, &n(origin), &n(proof), 1000).unwrap()
    }

    #[test]
    fn tags_classify_the_selected_proof_not_its_attribute_origin() {
        let env = theorem(&theorem(&environment(), "origin", 0), "selected", 0);
        let env = registered(&env, "origin", "selected");
        let env = scope::simp::defeq::register_imported(&env, &n("origin")).unwrap();
        let mut ctx = Context::new(&env, budget());
        let arguments = args();
        let before = ctx.txn.clone();
        let start = ctx.next;
        assert!(ctx.dsimp_set(&arguments).unwrap().rewrites.is_empty());
        ctx.txn.budget = before.budget.clone();
        assert_eq!(ctx.txn, before);
        assert_eq!(ctx.next, start);
        let tagged = scope::simp::defeq::register_imported(&env, &n("selected")).unwrap();
        let mut ctx = Context::new(&tagged, budget());
        let set = ctx.dsimp_set(&arguments).unwrap();
        assert_eq!(set.rewrites.len(), 1);
        let (SimpRule::Global(entry), reflexive) = &set.rewrites[0] else {
            panic!("named proof")
        };
        assert_eq!(entry.declaration, n("origin"));
        assert_eq!(entry.proof, Some(n("selected")));
        assert_eq!(reflexive.get(), Some(true));
    }

    #[test]
    fn named_theorem_selection_does_not_reinfer_its_generic_telescope() {
        let mut charged = Vec::new();
        for depth in [0, 64] {
            let env = theorem(&environment(), "theorem", depth);
            let env = registered(&env, "theorem", "theorem");
            for tagged in [false, true] {
                let env = if tagged {
                    scope::simp::defeq::register_imported(&env, &n("theorem")).unwrap()
                } else {
                    env.clone()
                };
                let mut ctx = Context::new(&env, budget());
                let before = ctx.clone();
                let arguments = args();
                let set = ctx.dsimp_set(&arguments).unwrap();
                assert_eq!(set.rewrites.len(), usize::from(tagged));
                charged.push(
                    ctx.txn.budget.heartbeats_consumed - before.txn.budget.heartbeats_consumed,
                );
                ctx.txn.budget = before.txn.budget.clone();
                assert_eq!(ctx.txn, before.txn);
                assert_eq!(ctx.next, before.next);
                assert_eq!(ctx.instance_goals, before.instance_goals);
            }
        }
        assert_eq!(charged[0], charged[2]);
        assert_eq!(charged[1], charged[3]);
    }

    #[test]
    fn malformed_tag_journals_are_not_hidden_by_skipping_unselected_theorems() {
        let env = theorem(&environment(), "theorem", 0);
        let env = registered(&env, "theorem", "theorem");
        let env = scope::simp::defeq::register_imported(&env, &n("theorem")).unwrap();
        let damaged = env
            .push_extension_entry(&n("FrankenLean.sourceDefEq.v1"), vec![0])
            .unwrap();
        let arguments = args();
        let error = Context::new(&damaged, budget())
            .dsimp_set(&arguments)
            .err()
            .expect("bad metadata refuses");
        assert!(!backtrack::recoverable(&error));
        assert_eq!(
            Context::new(&env, budget())
                .dsimp_set(&arguments)
                .unwrap()
                .rewrites
                .len(),
            1
        );
    }

    #[test]
    fn named_selection_resource_stops_preserve_the_transaction_and_retry() {
        let env = theorem(&environment(), "theorem", 8);
        let env = registered(&env, "theorem", "theorem");
        let env = scope::simp::defeq::register_imported(&env, &n("theorem")).unwrap();
        let original = Context::new(&env, budget());
        let arguments = args();
        let mut full = original.clone();
        assert_eq!(full.dsimp_set(&arguments).unwrap().rewrites.len(), 1);
        let used = full.txn.budget.heartbeats_consumed;
        // ElabBudget uses zero for an unlimited heartbeat allowance.
        for allowance in 1..used {
            let mut limited = original.clone();
            limited.txn.budget.max_heartbeats = allowance;
            let error = limited
                .dsimp_set(&arguments)
                .err()
                .expect("bounded selection must stop");
            assert!(!backtrack::recoverable(&error), "{allowance}: {error:?}");
            limited.txn.budget = original.txn.budget.clone();
            assert_eq!(limited.txn, original.txn);
            assert_eq!(limited.next, original.next);
        }
        let mut retry = original.clone();
        assert_eq!(retry.dsimp_set(&arguments).unwrap().rewrites.len(), 1);
        assert_eq!(retry.txn.budget.heartbeats_consumed, used);
    }
}
