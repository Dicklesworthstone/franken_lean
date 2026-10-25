//! Simplification beneath binders opens fresh locals and lifts actual evidence.
//! The traversal and its closing continuations live on the heap. No raw bound
//! variable is ever assigned to a rewrite metavariable from an outer context.
use super::*;
mod quantifiers;
#[cfg(test)]
mod tests;

struct BinderFrame {
    parent: Option<usize>,
    root: Expr,
    binder: Expr,
    local: LocalDecl,
    outer: LocalContext,
    inner: LocalContext,
}

struct Scan {
    root: Expr,
    term: Expr,
    parent: Option<usize>,
}

impl Context {
    /// Goal, hypothesis and `simpa using` simplification select identical
    /// evidence. A scoped rewrite lifts to an equality of the whole target;
    /// ordinary closed occurrences keep their existing transport direction.
    pub(super) fn simp_rule_evidence(
        &mut self,
        target: &Expr,
        rule: &SimpRule<'_>,
        premises: &[SimpRule<'_>],
    ) -> Result<Option<(Typed, Expr, bool, SimpPlace)>, NatDefinitionElabError> {
        // A rewrite at a node is already chosen: one beneath a binder or by `+arith` comes later.
        let limited = self.simp_reach_limit.is_some();
        if matches!(rule, SimpRule::Arith) {
            if limited {
                self.simp_reach_limit = None;
                return Ok(None);
            }
            let place = SimpPlace::of(SimpReach::Arith);
            if let Some((evidence, occurrence)) = self.simp_arith_evidence(target)? {
                return Ok(Some((evidence, occurrence, false, place)));
            }
            return Ok(self
                .simp_binder_rule(target, rule, premises)?
                .map(|evidence| (evidence, target.clone(), false, place)));
        }
        let mut term = self.selected_simp_term(rule)?;
        term.type_ = self.simp_premise_target(&term.type_, premises)?;
        let key = self.simp_rule_node_key(rule)?;
        if let Some(found) =
            self.instantiate_simp_rule(term, target, rule.reverse(), premises, key.as_ref())?
        {
            assert!(
                found.premises.is_empty(),
                "simp discharges its own premises"
            );
            let place = SimpPlace {
                reach: SimpReach::Node(found.position),
                pattern: found.pattern,
            };
            return Ok(Some((found.rule, found.occurrence, rule.reverse(), place)));
        }
        if limited {
            return Ok(None);
        }
        Ok(self
            .simp_binder_rule(target, rule, premises)?
            .map(|evidence| {
                (
                    evidence,
                    target.clone(),
                    false,
                    SimpPlace::of(SimpReach::Binder),
                )
            }))
    }

    /// Lift equality of an occurrence through a constant-result context. A
    /// dependent context is not silently coerced into homogeneous congruence.
    fn simp_occurrence_equality(
        &mut self,
        root: &Expr,
        occurrence: &Expr,
        mut evidence: Typed,
        reverse: bool,
    ) -> Result<(Expr, Typed), NatDefinitionElabError> {
        let (level, domain, left, right) =
            equality_target(&evidence.type_).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let replacement = if reverse { left.clone() } else { right.clone() };
        if reverse {
            evidence.value =
                self.symmetric_equality(&level, &domain, &left, &right, evidence.value)?;
            evidence.type_ = equality::equation(level, domain.clone(), right, left);
        }
        if self.rewrite_same(root, occurrence)? {
            return Ok((replacement, evidence));
        }
        let result_type = self
            .known_type(root)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let result_sort = self
            .known_type(&result_type)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let universe = self.sort_level(&Typed {
            value: result_type.clone(),
            type_: result_sort,
        })?;
        let marker = self.equality_local(domain.clone())?;
        let (template, matched) =
            self.rewrite_template(root, occurrence, &Expr::fvar(marker.id.clone()))?;
        if !matched {
            return Err(error(TacticError::RewriteNoMatch));
        }
        let selector = self.close_equality_binder(&marker, template, true)?;
        let Some(selector_type) = self.known_type(&selector)? else {
            return Err(error(TacticError::ApplyMismatch));
        };
        let expected = Expr::forall_e(
            Name::anonymous(),
            domain,
            result_type.clone(),
            BinderInfo::Default,
        );
        if !self.proof_types_match(&selector_type, &expected)? {
            return Err(error(TacticError::ApplyMismatch));
        }
        let next = self.rewrite_template(root, occurrence, &replacement)?.0;
        let result = self.selector_congruence(&evidence, &result_type, &universe, &selector)?;
        Ok((
            next.clone(),
            Typed {
                value: result.value,
                type_: equality::equation(universe, result_type, root.clone(), next.clone()),
            },
        ))
    }

    fn simp_open_body_rule(
        &mut self,
        body: &Expr,
        rule: &SimpRule<'_>,
        premises: &[SimpRule<'_>],
    ) -> Result<Option<(Expr, Typed)>, NatDefinitionElabError> {
        if matches!(rule, SimpRule::Arith) {
            let Some((evidence, occurrence)) = self.simp_arith_evidence(body)? else {
                return Ok(None);
            };
            return self
                .simp_occurrence_equality(body, &occurrence, evidence, false)
                .map(Some);
        }
        let mut term = self.selected_simp_term(rule)?;
        term.type_ = self.simp_premise_target(&term.type_, premises)?;
        let key = self.simp_rule_node_key(rule)?;
        let Some(found) =
            self.instantiate_simp_rule(term, body, rule.reverse(), premises, key.as_ref())?
        else {
            return Ok(None);
        };
        assert!(found.premises.is_empty(), "simp discharges its premises");
        self.simp_occurrence_equality(body, &found.occurrence, found.rule, rule.reverse())
            .map(Some)
    }

    fn simp_close_lambda(
        &mut self,
        frame: &BinderFrame,
        body: Expr,
        evidence: Typed,
    ) -> Result<(Expr, Typed), NatDefinitionElabError> {
        let ExprNode::Lam {
            binder_name,
            binder_type,
            binder_info,
            ..
        } = frame.binder.node()
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let closed = body
            .abstract_fvar(&frame.local.id, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let next = Expr::lam(
            binder_name.clone(),
            binder_type.clone(),
            closed,
            *binder_info,
        );
        // Abstract the body evidence before restoring the enclosing context.
        let pointwise = self.close_equality_binder(&frame.local, evidence.value, true)?;
        self.txn.lctx = frame.outer.clone();
        let type_ = self
            .known_type(&frame.binder)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self
            .known_type(&type_)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let level = self.sort_level(&Typed {
            value: type_.clone(),
            type_: sort,
        })?;
        let equation = equality::equation(level, type_, frame.binder.clone(), next.clone());
        let (_, goal) = self.proof_goal(equation.clone())?;
        let (value, child) = self.funext_step(&goal)?;
        self.close_proof_goal(child, pointwise)?;
        let value = self.instantiate(&value)?;
        Ok((
            next,
            Typed {
                value,
                type_: equation,
            },
        ))
    }

    fn simp_binder_walk(
        &mut self,
        target: &Expr,
        rule: &SimpRule<'_>,
        premises: &[SimpRule<'_>],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let mut frames = Vec::<BinderFrame>::new();
        let outer = self.txn.lctx.clone();
        let mut pending = vec![Scan {
            root: target.clone(),
            term: target.clone(),
            parent: None,
        }];
        // Allocation identity alone is insufficient after opening binders.
        // Keep every traversed term alive and distinguish lexical contexts.
        let mut visited = HashSet::new();
        let mut retained = Vec::new();
        while let Some(scan) = pending.pop() {
            self.tick()?;
            if !visited.insert((scan.parent, scan.term.allocation_identity())) {
                continue;
            }
            retained.push(scan.term.clone());
            if scan.term.has_loose_bvars() {
                continue;
            }
            if let ExprNode::Lam {
                binder_type,
                body,
                binder_info,
                ..
            }
            | ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = scan.term.node()
            {
                // Applications share an arena context index; cloning a whole
                // local telescope at every expression edge is unnecessary.
                self.txn.lctx = match scan.parent {
                    Some(index) => frames[index].inner.clone(),
                    None => outer.clone(),
                };
                if matches!(scan.term.node(), ExprNode::ForallE { .. })
                    && !self.simp_known_proposition(&scan.term)?
                {
                    // The pin's dependent non-Prop Pi path only performs
                    // definitional simplification, not theorem rewriting.
                    continue;
                }
                let enclosing = self.txn.lctx.clone();
                let mut local = self.equality_local(binder_type.clone())?;
                local.binder_info = *binder_info;
                // Generated names cannot capture a selected source lemma.
                let opened = self.substitute(body, &Expr::fvar(local.id.clone()))?;
                eliminate::add_local(&mut self.txn.lctx, &local);
                let frame = BinderFrame {
                    parent: scan.parent,
                    root: scan.root.clone(),
                    binder: scan.term.clone(),
                    local: local.clone(),
                    outer: enclosing,
                    inner: self.txn.lctx.clone(),
                };
                let index = frames.len();
                frames.push(frame);
                let before = self.rewrite_trial();
                match self.simp_open_body_rule(&opened, rule, premises) {
                    Ok(Some((mut next, mut evidence))) => {
                        let mut current = Some(index);
                        while let Some(at) = current {
                            self.tick()?;
                            let frame = &frames[at];
                            let (_, lifted) = match frame.binder.node() {
                                ExprNode::Lam { .. } => {
                                    self.simp_close_lambda(frame, next, evidence)?
                                }
                                ExprNode::ForallE { .. } => {
                                    self.simp_close_forall(frame, next, evidence)?
                                }
                                _ => unreachable!("only opened binders have frames"),
                            };
                            (next, evidence) = self.simp_occurrence_equality(
                                &frame.root,
                                &frame.binder,
                                lifted,
                                false,
                            )?;
                            current = frame.parent;
                        }
                        return Ok(Some(evidence));
                    }
                    Ok(None) => self.restore_simp_trial(before),
                    Err(problem) => return Err(problem),
                }
                pending.push(Scan {
                    root: opened.clone(),
                    term: opened,
                    parent: Some(index),
                });
                continue;
            }
            // Binder bodies are entered only by the scoped path above. Domains
            // and arbitrary type-level Pi congruence are not rewrite targets.
            if matches!(scan.term.node(), ExprNode::LetE { .. }) {
                continue;
            }
            for child in children(&scan.term).into_iter().rev().flatten() {
                self.tick()?;
                pending.push(Scan {
                    root: scan.root.clone(),
                    term: child.clone(),
                    parent: scan.parent,
                });
            }
        }
        Ok(None)
    }

    pub(super) fn simp_binder_rule(
        &mut self,
        target: &Expr,
        rule: &SimpRule<'_>,
        premises: &[SimpRule<'_>],
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let before = self.rewrite_trial();
        let result = self.simp_binder_walk(target, rule, premises);
        if !matches!(result, Ok(Some(_))) {
            self.restore_simp_trial(before);
        }
        result
    }
}
