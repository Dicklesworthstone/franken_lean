//! The pin's `ac_nf0` location policy and `ac_nf`'s optional final `trivial`.
//! Normalize the target first. Wildcard selection includes only nondependent
//! proposition parameters; explicit locations may select dependent hypotheses.

use super::*;

impl Context {
    pub(in crate::source) fn ac_normalize_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        args: &[Syntax],
        close: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(
            keyword,
            if close { "ac_nf" } else { "ac_nf0" },
            "AC normalization tactic",
        )?;
        self.require_declared_tactic(&[
            "Lean",
            "Parser",
            "Tactic",
            if close { "tacticAc_nf_" } else { "acNf0" },
        ])?;
        self.txn.lctx = goal.lctx.clone();
        let locations = self.rewrite_locations(location)?;
        if locations.as_ref().is_none_or(|locations| locations.target) {
            let original = self.instantiate(&goal.target)?;
            let (normalized, evidence) = self.ac_normalize_expression(&original)?;
            if let Some(value) = evidence {
                let rule = self.ac_type_equality(&original, normalized, value)?;
                let (next, value) = self.rewrite_transport(&goal, rule, &original, false, false)?;
                proof.work.push(Work::Close(goal, value));
                goal = next;
            } else {
                goal.target = normalized;
            }
        }
        self.txn.lctx = goal.lctx.clone();
        let ids: Vec<(FVarId, Option<Name>)> = match locations {
            Some(locations) if locations.all => self
                .ac_nondependent_propositions(&goal)?
                .into_iter()
                .map(|id| (id, None))
                .collect(),
            Some(locations) => {
                // Resolve every written location before rewriting any of them,
                // retaining identity even when earlier transports change names.
                let mut ids = Vec::new();
                for name in locations.hypotheses {
                    self.tick()?;
                    if let Some(local) = goal.lctx.find_by_user_name(&name) {
                        ids.push((local.id.clone(), None));
                        continue;
                    }
                    // The pin's getFVarId resolves an auxiliary self explicitly,
                    // although implicit search and wildcard locations hide it.
                    // Use ordinary source resolution to retain namespace and
                    // root-qualified boundaries; globals are never locations.
                    let syntax = Syntax::Ident {
                        info: fln_syntax::source::SourceInfo::None,
                        raw_val: Default::default(),
                        val: name.clone(),
                        preresolved: Vec::new(),
                    };
                    let reference = self.atom(&syntax, None).map_err(|problem| {
                        if backtrack::recoverable(&problem) {
                            error(TacticError::RewriteLocation)
                        } else {
                            problem
                        }
                    })?;
                    let ExprNode::FVar { id } = reference.value.node() else {
                        return Err(error(TacticError::RewriteLocation));
                    };
                    if !self.is_private_self(id) || !goal.lctx.contains(id) {
                        return Err(error(TacticError::RewriteLocation));
                    }
                    ids.push((id.clone(), Some(name)));
                }
                ids
            }
            None => Vec::new(),
        };
        for (id, private_name) in ids {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut local = goal
                .lctx
                .find(&id)
                .cloned()
                .ok_or_else(|| error(TacticError::RewriteLocation))?;
            if let Some(name) = private_name {
                // A proof-bearing replacement is an ordinary named hypothesis
                // at the pin. Its checked transport still retains the original
                // self identity; an unused replacement may be discarded.
                local.user_name = name;
            }
            let original = self.instantiate(&local.type_)?;
            let (normalized, evidence) = self.ac_normalize_expression(&original)?;
            if let Some(value) = evidence {
                let rule = self.ac_type_equality(&original, normalized, value)?;
                let replacement =
                    self.rewrite_hypothesis_value(&local, rule, &original, false, false)?;
                // applySimpResultToLocalDecl asserts proof-bearing replacements
                // at the end and keeps any old identity still used by dependents.
                let (next, parent, value) =
                    self.replace_rewritten_hypothesis(goal, &local, replacement, true)?;
                proof.work.push(Work::Close(parent, value));
                goal = next;
            } else if normalized != original {
                // A definitional-only change keeps the hypothesis identity and
                // its position, as replaceLocalDeclDefEq does at the pin.
                let mut context = LocalContext::new();
                for other in goal.lctx.decls() {
                    self.tick()?;
                    let mut other = other.clone();
                    if other.id == id {
                        other.type_ = normalized.clone();
                    }
                    eliminate::add_local(&mut context, &other);
                }
                goal.lctx = context;
            }
        }
        self.txn.lctx = goal.lctx.clone();
        if close {
            // `ac_nf` expands to `ac_nf0 ... <;> try trivial`. An ordinary
            // unsuccessful close leaves the normalized goal for the next tactic;
            // cancellation, resource limits and internal faults still propagate.
            let mut trial = self.rewrite_trial();
            match trial.trivial_proof_goal(goal.clone()) {
                Ok(()) => {
                    *self = trial;
                    return Ok(());
                }
                Err(problem) => {
                    self.charge_rewrite_trial(&trial);
                    if !backtrack::recoverable(&problem) {
                        return Err(problem);
                    }
                }
            }
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// Equality between types can live above Prop; explicit locations may name
    /// a data parameter's type as well as a proof's proposition.
    fn ac_type_equality(
        &mut self,
        original: &Expr,
        normalized: Expr,
        value: Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        let domain = self
            .known_type(original)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self
            .known_type(&domain)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let level = self.sort_level(&Typed {
            value: domain.clone(),
            type_: sort,
        })?;
        Ok(Typed {
            value,
            type_: equality::equation(level, domain, original.clone(), normalized),
        })
    }

    /// getNondepPropHyps removes each earlier candidate read by a later local's
    /// type/value or by the target, and never selects a let-bound proof.
    fn ac_nondependent_propositions(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Vec<FVarId>, NatDefinitionElabError> {
        let mut selected = HashSet::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            if self.is_matrix_hypothesis(local) {
                continue;
            }
            let type_ = self.instantiate(&local.type_)?;
            for dependency in self.elimination_reads(&type_)? {
                selected.remove(&dependency);
            }
            if let Some(value) = &local.value {
                let value = self.instantiate(value)?;
                for dependency in self.elimination_reads(&value)? {
                    selected.remove(&dependency);
                }
            } else if let Some(sort) = self.known_type(&type_)? {
                let sort = self.whnf_with_transparency(
                    &sort,
                    UnificationTransparency::Abbreviations,
                    false,
                )?;
                if !sort.has_expr_mvar()
                    && !sort.has_level_mvar()
                    && self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
                {
                    selected.insert(local.id.clone());
                }
            }
        }
        let target = self.instantiate(&goal.target)?;
        for dependency in self.elimination_reads(&target)? {
            selected.remove(&dependency);
        }
        Ok(goal
            .lctx
            .decls()
            .iter()
            .filter(|local| selected.contains(&local.id))
            .map(|local| local.id.clone())
            .collect())
    }
}
