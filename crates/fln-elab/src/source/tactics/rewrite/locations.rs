//! Hypothesis rewriting constructs a checked transport and a fresh local.
//! Old identities are never retagged with new types. Dependents keep the old
//! identity under an inaccessible name; otherwise it leaves the live context.
use super::*;

impl Context {
    pub(super) fn rewrite_locations(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Vec<Name>>, NatDefinitionElabError> {
        let optional = expect_null_args(syntax, "optional rewrite location")?;
        let [location] = optional else {
            return if optional.is_empty() {
                Ok(None)
            } else {
                Err(error(TacticError::MalformedScript))
            };
        };
        let parts = expect_node(
            location,
            &parser_kind(&["Tactic", "location"]),
            2,
            "rewrite location",
        )?;
        expect_atom(&parts[0], "at", "location keyword")?;
        let parts = expect_node(
            &parts[1],
            &parser_kind(&["Tactic", "locationHyp"]),
            1,
            "hypothesis locations",
        )?;
        let names = expect_null_args(&parts[0], "hypothesis location list")?;
        if names.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let mut result = Vec::new();
        for name in names {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Err(error(TacticError::MalformedScript));
            };
            if val.is_anonymous() {
                return Err(error(TacticError::RewriteLocation));
            }
            result.push(val.clone());
        }
        Ok(Some(result))
    }

    fn located_rule_term(&mut self, syntax: &Syntax) -> Result<Typed, NatDefinitionElabError> {
        // One bounded re-entry into the term driver, as for simp rules. Direct
        // Syntax clients cannot smuggle another proof driver into this frame.
        let mut pending = vec![syntax];
        while let Some(term) = pending.pop() {
            self.tick()?;
            if let Syntax::Node { kind, args, .. } = term {
                if kind == &parser_kind(&["Term", "byTactic"]) {
                    return Err(error(TacticError::MalformedScript));
                }
                pending.extend(args);
            }
        }
        self.term(syntax, None)
    }

    /// Produce a forward map T a -> T b rather than the contravariant map
    /// used for goals. Reverse rewriting first builds genuine symmetric evidence.
    pub(super) fn rewrite_hypothesis_value(
        &mut self,
        local: &LocalDecl,
        rule: Typed,
        occurrence: &Expr,
        reverse: bool,
    ) -> Result<Typed, NatDefinitionElabError> {
        let rule_type = self.whnf(&rule.type_)?;
        let (u, alpha, from, to) =
            equality_target(&rule_type).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let alpha = self.instantiate(&alpha)?;
        let from = self.instantiate(&from)?;
        let to = self.instantiate(&to)?;
        let mut evidence = self.instantiate(&rule.value)?;
        let (start, end) = if reverse {
            evidence = self.symmetric_equality(&u, &alpha, &from, &to, evidence)?;
            (to, from)
        } else {
            (from, to)
        };
        if occurrence.has_expr_mvar() || occurrence.has_level_mvar() || occurrence.has_loose_bvars()
        {
            return Err(error(TacticError::ExpectedEquality));
        }
        let original = self.instantiate(&local.type_)?;
        let marker = self.equality_local(alpha.clone())?;
        let (template, matched) =
            self.rewrite_template(&original, occurrence, &Expr::fvar(marker.id.clone()))?;
        if !matched {
            return Err(error(TacticError::RewriteNoMatch));
        }
        let target = self.specialize_locals(&template, &[(marker.id.clone(), end.clone())])?;
        let sort = self
            .known_type(&original)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let v = self.sort_level(&Typed {
            value: original,
            type_: sort,
        })?;
        let witness = self.equality_local(equality::equation(
            u.clone(),
            alpha.clone(),
            start.clone(),
            Expr::fvar(marker.id.clone()),
        ))?;
        let motive = self.close_equality_binder(&witness, template, true)?;
        let motive = self.close_equality_binder(&marker, motive, true)?;
        let value = [
            alpha,
            start,
            motive,
            Expr::fvar(local.id.clone()),
            end,
            evidence,
        ]
        .into_iter()
        .fold(
            Expr::const_(Name::from_components(["Eq", "rec"]), vec![v, u]),
            Expr::app,
        );
        Ok(Typed {
            value,
            type_: target,
        })
    }

    pub(super) fn replace_rewritten_hypothesis(
        &mut self,
        mut parent: ProofGoal,
        local: &LocalDecl,
        replacement: Typed,
    ) -> Result<(ProofGoal, ProofGoal, Expr), NatDefinitionElabError> {
        let target = self.instantiate(&parent.target)?;
        let mut needed =
            target.has_expr_mvar() || self.elimination_reads(&target)?.contains(&local.id);
        for other in parent.lctx.decls() {
            self.tick()?;
            if other.id == local.id {
                continue;
            }
            let other_type = self.instantiate(&other.type_)?;
            needed |= other_type.has_expr_mvar()
                || self.elimination_reads(&other_type)?.contains(&local.id);
            if let Some(value) = &other.value {
                let value = self.instantiate(value)?;
                needed |=
                    value.has_expr_mvar() || self.elimination_reads(&value)?.contains(&local.id);
            }
        }
        let id = FVarId(self.fresh_name()?);
        let binding = LocalDecl {
            id: id.clone(),
            user_name: local.user_name.clone(),
            type_: replacement.type_.clone(),
            value: Some(replacement.value),
            binder_info: local.binder_info,
            index: 0,
        };
        let dependencies = self.elimination_reads(&replacement.type_)?;
        needed |= dependencies.contains(&local.id);
        let insert_after = parent
            .lctx
            .decls()
            .iter()
            .filter(|other| other.id == local.id || dependencies.contains(&other.id))
            .map(|other| other.index)
            .max()
            .ok_or_else(|| error(TacticError::RewriteLocation))?;
        let mut context = LocalContext::new();
        let hidden = self.fresh_name()?;
        for other in parent.lctx.decls() {
            self.tick()?;
            if other.id != local.id {
                eliminate::add_local(&mut context, other);
            } else if needed {
                let mut original = other.clone();
                original.user_name = hidden.clone();
                eliminate::add_local(&mut context, &original);
            }
            if other.index == insert_after {
                context.add_param(
                    id.clone(),
                    local.user_name.clone(),
                    replacement.type_.clone(),
                    local.binder_info,
                );
            }
        }
        self.txn.lctx = context.clone();
        let (child, next) = self.proof_goal(target)?;
        // Delay abstraction until the child and all rule premises are solved.
        // The parent retains the old variable needed by the transport's RHS.
        parent.introduced.push(binding);
        parent.lctx = context;
        Ok((next, parent, child))
    }

    pub(in crate::source) fn rewrite_at_locations<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        initial: &ProofGoal,
        args: &'a [Syntax],
        close: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        let [_, _, _, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        let Some(locations) = self.rewrite_locations(location)? else {
            return Ok(false);
        };
        let rules = self.rewrite_rules(args, close)?;
        // Resolve every requested name before making a successful prefix.
        for name in &locations {
            if initial.lctx.find_by_user_name(name).is_none() {
                return Err(error(TacticError::RewriteLocation));
            }
        }
        let mut goal = initial.clone();
        for rule in rules {
            for name in &locations {
                self.tick()?;
                self.txn.lctx = goal.lctx.clone();
                let local = goal
                    .lctx
                    .find_by_user_name(name)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))?;
                let term = self.located_rule_term(rule.syntax)?;
                self.flush(false)?;
                let target = self.instantiate(&local.type_)?;
                let RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                } = self
                    .instantiate_rewrite_rule(term, &target, rule.reverse, false, &[])?
                    .ok_or_else(|| error(TacticError::RewriteNoMatch))?;
                let replacement =
                    self.rewrite_hypothesis_value(&local, term, &occurrence, rule.reverse)?;
                let (next, parent, value) =
                    self.replace_rewritten_hypothesis(goal, &local, replacement)?;
                proof.work.push(Work::Close(parent, value));
                proof
                    .work
                    .extend(premises.into_iter().rev().map(Work::Goal));
                goal = next;
            }
        }
        if !close || !self.rewrite_reflexivity(&goal)? {
            proof.work.push(Work::Goal(goal));
        }
        Ok(true)
    }
}
