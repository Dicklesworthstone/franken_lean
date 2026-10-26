//! Transactional instantiation of quantified equality rules at goal occurrences.
//! Failed candidates cannot assign another goal's metavariables or consume an
//! unresolved premise. All successful rule applications retain their proof term.

use super::*;
use std::collections::HashSet;
mod instance_args;

/// Where a rule instantiation looks for its occurrence.
#[derive(Clone, Copy)]
enum Occurrences<'a> {
    /// Every subterm, in the traversal order of the caller.
    Every,
    /// The target itself only (dsimp's per-node lookup).
    Root,
    /// Every subterm whose own key the rule's key admits (simp's per-node retrieval).
    Admitted(&'a super::simplify::SimpKey),
}

/// The pin's `HeadIndex` (vendored Lean/HeadIndex.lean:28-36).
#[derive(PartialEq, Eq)]
pub(in crate::source) enum HeadIndex {
    Local(FVarId),
    Hole(MVarId),
    Constant(Name),
    Projection(Name, u64),
    Literal(Literal),
    Sort,
    Lambda,
    Forall,
}

/// Which subterms `rw` may abstract: the pin's `kabstract` keys.
enum RewriteKey {
    /// A local pattern is abstracted exactly where it occurs (`Expr.abstract`).
    Local(FVarId),
    /// The head symbol and argument count a candidate must share with the pattern.
    Head(Option<(HeadIndex, usize)>),
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum RigidTypeHead {
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
    pub(super) fn rigid_rewrite_type_head(
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

    pub(super) fn rewrite_types_have_distinct_heads(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let (Some(actual), Some(expected)) = (
            self.rigid_rewrite_type_head(left)?,
            self.rigid_rewrite_type_head(right)?,
        ) else {
            return Ok(false);
        };
        Ok(actual != expected)
    }

    /// Inspect the type skeleton after EXACTLY the supplied arguments. A bare
    /// constant or partial application can still be function-valued; stripping
    /// its entire telescope would falsely discard rewrites of that function.
    /// Only the stable outer constructors recognized by rigid_rewrite_type_head
    /// are used. A bare result type parameter selects its exact supplied
    /// argument; applied motives, aliases, and redexes stay unknown. This filter
    /// neither unfolds a definition nor infers a caller's argument types.
    pub(super) fn rigid_rewrite_constant_result(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<RigidTypeHead>, NatDefinitionElabError> {
        let mut head = expression;
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
                _ => break,
            }
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(info) = self.txn.env.find(name) else {
            return Ok(None);
        };
        let base = info.constant_val();
        if levels.len() != base.level_params.len() {
            return Ok(None);
        }
        let mut result = base.type_.clone();
        while arguments != 0 {
            self.tick()?;
            match result.node() {
                ExprNode::ForallE { body, .. } => {
                    result = body.clone();
                    arguments -= 1;
                }
                ExprNode::MData { expr, .. } => result = expr.clone(),
                // Overapplication and reducible/unknown telescope tails must
                // go to ordinary type reconstruction, never guessed arity.
                _ => return Ok(None),
            }
        }
        let mut result_head = &result;
        while let ExprNode::MData { expr, .. } = result_head.node() {
            self.tick()?;
            result_head = expr;
        }
        if let ExprNode::BVar { idx } = result_head.node() {
            // The telescope's last consumed binder has index zero. Walk the
            // actual application spine in the same order; never guess the
            // carrier of a polymorphic constant (including numeric methods).
            let mut applied = expression;
            let mut remaining = *idx;
            loop {
                self.tick()?;
                match applied.node() {
                    ExprNode::MData { expr, .. } => applied = expr,
                    ExprNode::App { f, a } => {
                        if remaining == 0 {
                            return self.rigid_rewrite_type_head(a);
                        }
                        remaining -= 1;
                        applied = f;
                    }
                    _ => return Ok(None),
                }
            }
        }
        self.rigid_rewrite_type_head(result_head)
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
        if let NatDefinitionElabError::Inference(SourceInferenceError::ConversionRefused(verdict)) =
            error
        {
            return matches!(
                verdict.as_ref(),
                Verdict::Rejected {
                    class: fln_kernel::verdict::RejectClass::NotDefEq,
                    ..
                }
            );
        }
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

    /// Queue a selection equation and its universe-typing obligations without
    /// first running ordinary source inference. `constrain` flushes immediately
    /// and may retry at Default transparency before a selection marker exists.
    /// That can unfold an irrelevant rule or change which occurrence it matches.
    fn queue_rewrite_selection(
        &mut self,
        left: &Expr,
        right: &Expr,
        rewrite: bool,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        let equation = if rewrite {
            SourceEquation::rewrite_selection
        } else {
            SourceEquation::selection
        };
        if let (Some(a), Some(b)) = (self.known_type(&left)?, self.known_type(&right)?)
            && (a.has_level_mvar() || b.has_level_mvar())
        {
            self.equations.push(equation(a, b));
        }
        self.equations.push(equation(left, right));
        Ok(())
    }

    /// Match the term and its type in ONE selection-policy transaction. Even
    /// ground equations must be established before a rule can be selected.
    /// `rewrite` is `rw`'s query, the pin's `kabstract` `isDefEq` under
    /// `Rewrite.Config` (reducible, offset constraints); otherwise `instances`.
    fn match_rewrite_occurrence(
        &mut self,
        pattern: &Expr,
        alpha: &Expr,
        occurrence: &Expr,
        rewrite: bool,
    ) -> Result<bool, NatDefinitionElabError> {
        // Sorts, dependent function types and saturated admitted inductives
        // are rigid as terms too. Distinct heads cannot become equal through
        // conversion; avoid inferring and solving that impossible occurrence.
        if self.rewrite_types_have_distinct_heads(pattern, occurrence)? {
            return Ok(false);
        }
        if let (Some(actual), Some(expected)) = (
            self.rigid_rewrite_constant_result(occurrence)?,
            self.rigid_rewrite_type_head(alpha)?,
        ) && actual != expected
        {
            return Ok(false);
        }
        let Some(type_) = self.known_type(occurrence)? else {
            return Ok(false);
        };
        // In a dependent recursor, most visited subterms are types, proofs or
        // partially applied functions, not values of the rule's carrier type.
        // Do not unify their large proof terms after their types already have
        // irreconcilable rigid heads. This accepts nothing and assigns no hole.
        if self.rewrite_types_have_distinct_heads(&type_, alpha)? {
            return Ok(false);
        }
        self.queue_rewrite_selection(&type_, alpha, rewrite)?;
        self.queue_rewrite_selection(occurrence, pattern, rewrite)?;
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
        rule: Typed,
        target: &Expr,
        reverse: bool,
        inside_out: bool,
        selected_rules: &[SimpRule<'_>],
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        self.instantiate_rewrite_rule_with_scope(
            rule,
            target,
            reverse,
            inside_out,
            selected_rules,
            Occurrences::Every,
        )
    }

    /// Simplification's instantiation: inside-out, trying `rule` only at the nodes
    /// its rewrite key admits (`simp_rule_node_key`), as the pin's discrimination
    /// tree retrieves it.
    pub(super) fn instantiate_simp_rule(
        &mut self,
        rule: Typed,
        target: &Expr,
        reverse: bool,
        selected_rules: &[SimpRule<'_>],
        node_key: Option<&super::simplify::SimpKey>,
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        self.instantiate_rewrite_rule_with_scope(
            rule,
            target,
            reverse,
            true,
            selected_rules,
            node_key.map_or(Occurrences::Every, Occurrences::Admitted),
        )
    }

    pub(in crate::source) fn instantiate_dsimp_rule(
        &mut self,
        rule: Typed,
        target: &Expr,
        reverse: bool,
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        self.instantiate_rewrite_rule_with_scope(
            rule,
            target,
            reverse,
            true,
            &[],
            Occurrences::Root,
        )
    }

    fn instantiate_rewrite_rule_with_scope(
        &mut self,
        mut rule: Typed,
        target: &Expr,
        reverse: bool,
        inside_out: bool,
        selected_rules: &[SimpRule<'_>],
        occurrences: Occurrences<'_>,
    ) -> Result<Option<RewriteMatch>, NatDefinitionElabError> {
        let root_only = matches!(occurrences, Occurrences::Root);
        self.flush(false)?;
        let mut template = self.rewrite_trial();
        // Preparing a rule is speculative too. Charge its private context on
        // EVERY exit, including interruption while opening its telescope.
        let prepared = (|| {
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
            let mut rule_instances = Vec::new();
            loop {
                template.tick()?;
                // The pin prepares simp theorems at reducible transparency without
                // unfolding local lets. Preserve the final proposition's head too:
                // unfolding Nat.lt here would hide it from the occurrence matcher.
                rule.type_ = if inside_out {
                    template.whnf_with_transparency(
                        &rule.type_,
                        UnificationTransparency::Abbreviations,
                        false,
                    )?
                } else {
                    template.whnf(&rule.type_)?
                };
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
                // Simp theorem parameters are patterns; ordinary rw retains
                // its existing elaboration-time dictionary synthesis.
                let argument = if !inside_out && *binder_info == BinderInfo::InstImplicit {
                    template.instance_hole(domain)?
                } else {
                    template.hole(domain)?
                };
                if let ExprNode::MVar { id } = argument.node() {
                    holes.push(id.clone());
                    if inside_out && *binder_info == BinderInfo::InstImplicit {
                        rule_instances.push(id.clone());
                    }
                }
                rule.type_ = template.substitute(&body, &argument)?;
                rule.value = Expr::app(rule.value, argument);
            }
            // Rewrite's newly applied parameters precede the unresolved implicit
            // arguments inserted while elaborating the selected rule expression.
            holes.extend(implicit_holes);
            // Only ordinary rw pre-synthesizes its rule arguments. Simp first
            // matches occurrence dictionaries, then synthesizes missing ones.
            if !inside_out {
                let resolution = template.resolve_instances(false);
                self.charge_rewrite_trial(&template);
                resolution?;
            }
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
            if root_only {
                // Dsimp's rule lookup is head-directed. A conversion-based
                // occurrence match must not unfold a named pattern into an
                // unrelated node (e.g. `wrap ?n` into every Nat literal). That
                // both expands the rule's domain and cycles with literal
                // refolding. Parameter-headed patterns still use the solver.
                let mut pattern_head = &pattern;
                let mut target_head = target;
                loop {
                    template.tick()?;
                    match pattern_head.node() {
                        ExprNode::App { f, .. } => pattern_head = f,
                        ExprNode::MData { expr, .. } => pattern_head = expr,
                        _ => break,
                    }
                }
                loop {
                    template.tick()?;
                    match target_head.node() {
                        ExprNode::App { f, .. } => target_head = f,
                        ExprNode::MData { expr, .. } => target_head = expr,
                        _ => break,
                    }
                }
                let mismatch = match pattern_head.node() {
                    ExprNode::Const { name, .. } => !matches!(
                        target_head.node(), ExprNode::Const { name: actual, .. } if actual == name
                    ),
                    ExprNode::FVar { id } => !matches!(
                        target_head.node(), ExprNode::FVar { id: actual } if actual == id
                    ),
                    _ => false,
                };
                if mismatch {
                    return Ok(None);
                }
            }

            self.charge_rewrite_trial(&template);
            if !inside_out {
                let pattern = template.instantiate(&pattern)?;
                self.charge_rewrite_trial(&template);
                let mut head = &pattern;
                loop {
                    template.tick()?;
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
            Ok(Some((rule, alpha, pattern, holes, rule_instances)))
        })();
        self.charge_rewrite_trial(&template);
        let Some((rule, alpha, pattern, holes, rule_instances)) = prepared? else {
            return Ok(None);
        };
        // `rw` abstracts like the pin's `kabstract` (vendored Lean/Meta/KAbstract.lean:30-55):
        // a local pattern only at that local, any other only at a subterm with the pattern's
        // head symbol and argument count.
        let key = if inside_out {
            None
        } else {
            let pattern = template.instantiate(&pattern)?;
            self.charge_rewrite_trial(&template);
            Some(match pattern.node() {
                ExprNode::FVar { id } => RewriteKey::Local(id.clone()),
                _ => RewriteKey::Head(self.rewrite_head_key(&pattern)?),
            })
        };
        // The pin's simp unifies at reducible transparency (`withReducible`,
        // `Lean/Meta/Tactic/Simp/Types.lean:966`); a selection query here runs at `instances`,
        // which unfolds `Nat.add` and so would close `n + 0 = n`. A pattern relating one
        // variable to itself (`eq_self`'s `?a = ?a`, `iff_self`'s `?p ↔ ?p`) is a reflexivity
        // test, so its occurrence's two sides must also agree at reducible transparency.
        let reflexive = inside_out && reflexive_pattern(&pattern);
        let mut pending = vec![(target, false)];
        let mut visited = HashSet::new();
        while let Some((term, exit)) = pending.pop() {
            self.tick()?;
            if !exit {
                if !visited.insert(term.allocation_identity()) {
                    continue;
                }
                if inside_out && !root_only {
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
                if !root_only {
                    pending.extend(
                        children(term)
                            .into_iter()
                            .rev()
                            .flatten()
                            .map(|child| (child, false)),
                    );
                }
            }
            if term.has_loose_bvars() {
                continue;
            }
            match &key {
                Some(RewriteKey::Local(id)) if !matches!(term.node(), ExprNode::FVar { id: local } if local == id) =>
                {
                    continue;
                }
                Some(RewriteKey::Head(head)) if &self.rewrite_head_key(term)? != head => continue,
                _ => {}
            }
            if let Occurrences::Admitted(key) = occurrences
                && !self.simp_node_admits(key, term)?
            {
                continue;
            }
            let mut trial = template.rewrite_trial();
            trial.txn.budget = self.txn.budget.clone();
            let attempt = (|| {
                let matched = if reflexive {
                    // The pattern selects `l = l` (or `l ↔ l`); whether `r` is `l` is the pin's
                    // reducible test alone, which instances-transparency selection would widen.
                    match reflexive_instance(term) {
                        Some(instance) => {
                            trial.reflexive_sides_agree(term)?
                                && trial
                                    .match_rewrite_occurrence(&pattern, &alpha, &instance, false)?
                        }
                        None => false,
                    }
                } else {
                    trial.match_rewrite_occurrence(&pattern, &alpha, term, !inside_out)?
                };
                if !matched {
                    return Ok(None);
                }
                if inside_out && !trial.synthesize_simp_rule_instances(&holes, &rule_instances)? {
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

impl Context {
    /// `expression`'s `toHeadIndex` and `headNumArgs` (vendored Lean/HeadIndex.lean:55-112).
    /// A `let` contributes its body; a body headed by its own bound variable takes the
    /// value's head, as `toHeadIndexSlow` does. A source ascription `let _ : T := e; _`
    /// (this elaborator's spelling of `(e : T)`, absent from the pin's term) is read as `e`.
    /// `None` only for a loose bound variable.
    pub(in crate::source) fn rewrite_head_key(
        &mut self,
        expression: &Expr,
    ) -> Result<Option<(HeadIndex, usize)>, NatDefinitionElabError> {
        let mut arguments = 0_usize;
        let mut head = expression;
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, .. } => {
                    arguments += 1;
                    head = f;
                }
                ExprNode::LetE { value, .. } if is_ascription(head) => head = value,
                ExprNode::LetE { body, .. } => head = body,
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let mut head = expression.clone();
        loop {
            self.tick()?;
            let next = match head.node() {
                ExprNode::App { f, .. } => f.clone(),
                ExprNode::MData { expr, .. } => expr.clone(),
                ExprNode::LetE { value, .. } if is_ascription(&head) => value.clone(),
                ExprNode::LetE { value, body, .. } => {
                    let mut quick = body;
                    while let ExprNode::App { f: inner, .. }
                    | ExprNode::MData { expr: inner, .. }
                    | ExprNode::LetE { body: inner, .. } = quick.node()
                    {
                        self.tick()?;
                        quick = inner;
                    }
                    if matches!(quick.node(), ExprNode::BVar { .. }) {
                        self.substitute(body, value)?
                    } else {
                        body.clone()
                    }
                }
                ExprNode::FVar { id } => {
                    return Ok(Some((HeadIndex::Local(id.clone()), arguments)));
                }
                ExprNode::MVar { id } => return Ok(Some((HeadIndex::Hole(id.clone()), arguments))),
                ExprNode::Const { name, .. } => {
                    return Ok(Some((HeadIndex::Constant(name.clone()), arguments)));
                }
                ExprNode::Proj {
                    struct_name, idx, ..
                } => {
                    return Ok(Some((
                        HeadIndex::Projection(struct_name.clone(), *idx),
                        arguments,
                    )));
                }
                ExprNode::Lit { literal } => {
                    return Ok(Some((HeadIndex::Literal(literal.clone()), arguments)));
                }
                ExprNode::Sort { .. } => return Ok(Some((HeadIndex::Sort, arguments))),
                ExprNode::Lam { .. } => return Ok(Some((HeadIndex::Lambda, arguments))),
                ExprNode::ForallE { .. } => return Ok(Some((HeadIndex::Forall, arguments))),
                ExprNode::BVar { .. } => return Ok(None),
            };
            head = next;
        }
    }

    /// Whether the two sides of an `=` or `↔` occurrence agree as the pin's reducible
    /// `isDefEq` decides it, unfolding no local `let`. For `=` that is the automatic closure's
    /// test, which adds the pin's `isDefEqOffset` (Nat offsets and closed literal arithmetic,
    /// `Lean/Meta/Offset.lean`) to reducible conversion.
    fn reflexive_sides_agree(&mut self, occurrence: &Expr) -> Result<bool, NatDefinitionElabError> {
        if equality_target(occurrence).is_some() {
            let mut check = self.rewrite_trial();
            let agreed = (|| {
                let hole = check.hole(occurrence.clone())?;
                let ExprNode::MVar { id } = hole.node() else {
                    return Err(failure(SourceInferenceError::Scope));
                };
                let goal = ProofGoal {
                    id: id.clone(),
                    target: occurrence.clone(),
                    lctx: check.txn.lctx.clone(),
                    introduced: Vec::new(),
                };
                Ok(check
                    .automatic_reflexivity_candidate(&goal, false)?
                    .is_some())
            })();
            self.charge_rewrite_trial(&check);
            return agreed;
        }
        let Some((left, right)) = reflexive_sides(occurrence) else {
            return Ok(false);
        };
        let mut budget = UnificationBudget::new(self.kernel);
        budget.zeta_delta = false;
        budget.max_assignments = 0;
        self.proof_types_match_with_budget(&left, &right, budget)
    }
}

/// `let _ : T := e; _`, the term this elaborator keeps for a source ascription `(e : T)`.
pub(super) fn is_ascription(expression: &Expr) -> bool {
    matches!(expression.node(), ExprNode::LetE { decl_name, body, .. }
        if decl_name.is_anonymous() && matches!(body.node(), ExprNode::BVar { idx: 0 }))
}

/// The two related sides of `@Eq α a b` or `Iff a b`.
fn reflexive_sides(expr: &Expr) -> Option<(Expr, Expr)> {
    if let Some((_, _, left, right)) = equality_target(expr) {
        return Some((left, right));
    }
    let ExprNode::App { f, a: right } = expr.node() else {
        return None;
    };
    let ExprNode::App { f, a: left } = f.node() else {
        return None;
    };
    matches!(f.node(), ExprNode::Const { name, levels }
        if levels.is_empty() && *name == Name::from_components(["Iff"]))
    .then(|| (left.clone(), right.clone()))
}

/// `occurrence` with its right side replaced by its left: `@Eq α l l` or `Iff l l`.
fn reflexive_instance(occurrence: &Expr) -> Option<Expr> {
    if let Some((level, alpha, left, _)) = equality_target(occurrence) {
        return Some(app(
            Expr::const_(Name::from_components(["Eq"]), vec![level]),
            [alpha, left.clone(), left],
        ));
    }
    let (left, _) = reflexive_sides(occurrence)?;
    Some(app(
        Expr::const_(Name::from_components(["Iff"]), Vec::new()),
        [left.clone(), left],
    ))
}

/// A pattern whose two sides are one and the same metavariable.
fn reflexive_pattern(pattern: &Expr) -> bool {
    reflexive_sides(pattern).is_some_and(|(left, right)| {
        matches!((left.node(), right.node()), (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b)
    })
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
    fn constant_result_discrimination_uses_the_actual_type_parameter() {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};

        let mut ctx = context();
        for source in [
            "def carrier_first (A B : Type) (a : A) (b : B) : A := a",
            "def carrier_second (A B : Type) (a : A) (b : B) : B := b",
        ] {
            let declaration =
                crate::check_definition_source(source.as_bytes(), &ctx.txn.env, ctx.kernel)
                    .unwrap()
                    .declaration;
            let Outcome::Complete(admitted) = admit(&ctx.txn.env, declaration, ctx.kernel) else {
                panic!("definition admission did not complete");
            };
            let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
            else {
                panic!("definition was rejected");
            };
            let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                publication,
            ))) = checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
            else {
                panic!("definition publication did not complete");
            };
            ctx.txn.env = publication.environment;
        }
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let bool_ = Expr::const_(Name::from_components(["Bool"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let false_ = Expr::const_(Name::from_components(["Bool", "false"]), vec![]);
        for (name, result) in [("carrier_first", "Nat"), ("carrier_second", "Bool")] {
            let selected = Expr::const_(Name::from_components([name]), vec![]);
            assert_eq!(
                ctx.rigid_rewrite_constant_result(&app(
                    selected.clone(),
                    [nat.clone(), bool_.clone(), zero.clone(), false_.clone()],
                ))
                .unwrap(),
                Some(RigidTypeHead::Inductive(Name::from_components([result])))
            );
            assert_eq!(
                ctx.rigid_rewrite_constant_result(&app(
                    selected,
                    [nat.clone(), bool_.clone(), zero.clone()],
                ))
                .unwrap(),
                Some(RigidTypeHead::Forall)
            );
        }
        let carrier = ctx.hole(Expr::sort(Level::one())).unwrap();
        let before = ctx.txn.mvars.clone();
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&app(
                Expr::const_(Name::from_components(["carrier_first"]), vec![]),
                [carrier, bool_, zero, false_],
            ))
            .unwrap(),
            None
        );
        assert_eq!(ctx.txn.mvars, before);
    }

    #[test]
    fn selection_does_not_retry_an_irrelevant_definition_at_inference_transparency() {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};

        let mut ctx = context();
        let source = format!(
            "def costly (n : Nat) : Nat := {}n{}",
            "Nat.succ (".repeat(128),
            ")".repeat(128)
        );
        let declaration =
            crate::check_definition_source(source.as_bytes(), &ctx.txn.env, ctx.kernel)
                .unwrap()
                .declaration;
        let Outcome::Complete(admitted) = admit(&ctx.txn.env, declaration, ctx.kernel) else {
            panic!("definition admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("definition was rejected");
        };
        let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) =
            checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
        else {
            panic!("definition publication did not complete");
        };
        ctx.txn.env = publication.environment;
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let costly = Expr::const_(Name::from_components(["costly"]), vec![]);
        let hole = ctx.hole(nat.clone()).unwrap();
        let pattern = Expr::app(costly.clone(), hole.clone());
        let before = ctx.txn.clone();
        let mut trial = ctx.rewrite_trial();
        trial.txn.budget.max_heartbeats = trial.txn.budget.heartbeats_consumed + 512;
        let problem = trial
            .match_rewrite_occurrence(&pattern, &nat, &zero, false)
            .unwrap_err();
        assert!(Context::rewrite_nonmatch(&problem), "{problem:?}");
        ctx.charge_rewrite_trial(&trial);
        assert_eq!(ctx.txn.mvars, before.mvars);
        assert_eq!(ctx.txn.universes, before.universes);
        assert_eq!(ctx.txn.env, before.env);

        let mut same_head = ctx.rewrite_trial();
        assert!(
            same_head
                .match_rewrite_occurrence(&pattern, &nat, &Expr::app(costly, zero.clone()), false)
                .unwrap()
        );
        assert_eq!(same_head.instantiate(&hole).unwrap(), zero);

        // Ordinary source conversion still unfolds safe definitions; selection
        // alone must avoid the expensive second attempt on an irrelevant rule.
        let mut expanded = zero.clone();
        let succ = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
        for _ in 0..128 {
            expanded = Expr::app(succ.clone(), expanded);
        }
        ctx.constrain(&pattern, &expanded).unwrap();
        // Delta/Nat reduction returns a literal, unlike the same-head match
        // above. The independent control below pins this pre-existing result.
        assert_eq!(
            ctx.instantiate(&hole).unwrap(),
            Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(0)
            ))
        );
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
            !ctx.match_rewrite_occurrence(&pattern, &nat, &Expr::fvar(id), false)
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
            ctx.match_rewrite_occurrence(&zero, &carrier, &zero, false)
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
            .match_rewrite_occurrence(&term, &unequal, &term, false)
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

    #[test]
    fn failed_occurrence_does_not_commit_its_carrier_assignment() {
        let mut ctx = context();
        let carrier = ctx.hole(Expr::sort(Level::one())).unwrap();
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let one = Expr::app(
            Expr::const_(Name::from_components(["Nat", "succ"]), vec![]),
            zero.clone(),
        );
        let before = ctx.txn.clone();
        let problem = ctx
            .match_rewrite_occurrence(&zero, &carrier, &one, false)
            .unwrap_err();
        assert!(Context::rewrite_nonmatch(&problem), "{problem:?}");
        assert_eq!(ctx.txn.mvars, before.mvars);
        assert_eq!(ctx.txn.universes, before.universes);
        assert_eq!(ctx.txn.env, before.env);
        assert!(ctx.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
        // A fresh trial from the original context must still match a real occurrence.
        let mut recovery = Context::new(&before.env, ctx.kernel);
        let carrier = recovery.hole(Expr::sort(Level::one())).unwrap();
        assert!(
            recovery
                .match_rewrite_occurrence(&zero, &carrier, &zero, false)
                .unwrap()
        );
        assert_eq!(
            recovery.instantiate(&carrier).unwrap(),
            Expr::const_(Name::from_components(["Nat"]), vec![])
        );
    }

    #[test]
    fn selection_retains_polymorphic_carrier_and_value_obligations() {
        let mut ctx = context();
        let level = ctx.level().unwrap();
        let carrier = ctx.hole(Expr::sort(level)).unwrap();
        let pattern = ctx.hole(carrier.clone()).unwrap();
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        assert!(
            ctx.match_rewrite_occurrence(&pattern, &carrier, &zero, false)
                .unwrap()
        );
        assert_eq!(
            ctx.instantiate(&carrier).unwrap(),
            Expr::const_(Name::from_components(["Nat"]), vec![])
        );
        assert_eq!(ctx.instantiate(&pattern).unwrap(), zero);
        assert!(ctx.equations.is_empty());
    }

    #[test]
    fn ordinary_delta_inference_returns_canonical_nat_zero() {
        use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
        use fln_env::pmap::CollisionBudget;
        use fln_kernel::capability::{Published, admit};
        use fln_kernel::council::{Council, CouncilOutcome, convene};

        let mut ctx = context();
        let source = format!(
            "def costly (n : Nat) : Nat := {}n{}",
            "Nat.succ (".repeat(128),
            ")".repeat(128)
        );
        let declaration =
            crate::check_definition_source(source.as_bytes(), &ctx.txn.env, ctx.kernel)
                .unwrap()
                .declaration;
        let Outcome::Complete(admitted) = admit(&ctx.txn.env, declaration, ctx.kernel) else {
            panic!("definition admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("definition was rejected");
        };
        let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) =
            checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            )
        else {
            panic!("definition publication did not complete");
        };
        ctx.txn.env = publication.environment;
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let costly = Expr::const_(Name::from_components(["costly"]), vec![]);
        let hole = ctx.hole(nat.clone()).unwrap();
        let pattern = Expr::app(costly.clone(), hole.clone());

        let mut expanded = zero;
        let succ = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
        for _ in 0..128 {
            expanded = Expr::app(succ.clone(), expanded);
        }
        ctx.constrain(&pattern, &expanded).unwrap();
        assert_eq!(
            ctx.instantiate(&hole).unwrap(),
            Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(0)
            ))
        );
    }

    #[test]
    fn constant_result_discrimination_preserves_partial_function_types() {
        let mut ctx = context();
        let succ = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&succ).unwrap(),
            Some(RigidTypeHead::Forall)
        );
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&Expr::app(succ.clone(), zero.clone()))
                .unwrap(),
            Some(RigidTypeHead::Inductive(Name::from_components(["Nat"])))
        );
        let wrapped = Expr::mdata(KVMap::new(), succ.clone());
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&wrapped).unwrap(),
            Some(RigidTypeHead::Forall)
        );
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&Expr::app(wrapped, zero.clone()))
                .unwrap(),
            Some(RigidTypeHead::Inductive(Name::from_components(["Nat"])))
        );
        for unknown in [
            Expr::app(Expr::app(succ, zero.clone()), zero),
            Expr::const_(Name::from_components(["Nat", "succ"]), vec![Level::one()]),
            Expr::const_(Name::from_components(["absent"]), vec![]),
        ] {
            assert_eq!(ctx.rigid_rewrite_constant_result(&unknown).unwrap(), None);
        }
    }

    #[test]
    fn constant_result_discrimination_leaves_dependent_results_unknown() {
        let mut ctx = context();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let zero = Expr::const_(Name::from_components(["Nat", "zero"]), vec![]);
        let constructor = Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]);
        // The unsupplied value binder remains a function type, not Eq.
        let partial = Expr::app(constructor, nat.clone());
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&partial).unwrap(),
            Some(RigidTypeHead::Forall)
        );
        assert_eq!(
            ctx.rigid_rewrite_constant_result(&Expr::app(partial, zero))
                .unwrap(),
            Some(RigidTypeHead::Inductive(Name::from_components(["Eq"])))
        );
        // The result of this fully applied recursor is headed by its motive,
        // not the recursor's name or the function type of a partial application.
        let recursor = Expr::const_(Name::from_components(["Nat", "rec"]), vec![Level::one()]);
        let mut applied = recursor;
        for _ in 0..4 {
            applied = Expr::app(applied, nat.clone());
        }
        assert_eq!(ctx.rigid_rewrite_constant_result(&applied).unwrap(), None);
    }

    #[test]
    fn constant_result_spine_walk_is_metered_without_semantic_mutation() {
        let mut ctx = context();
        let before = ctx.txn.clone();
        let mut term = Expr::const_(Name::from_components(["Nat", "succ"]), vec![]);
        for _ in 0..128 {
            term = Expr::mdata(KVMap::new(), term);
        }
        ctx.txn.budget.max_heartbeats = ctx.txn.budget.heartbeats_consumed + 32;
        let problem = ctx.rigid_rewrite_constant_result(&term).unwrap_err();
        assert!(matches!(
            problem,
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
        ));
        assert!(!Context::rewrite_nonmatch(&problem));
        assert_eq!(ctx.txn.mvars, before.mvars);
        assert_eq!(ctx.txn.universes, before.universes);
        assert_eq!(ctx.txn.env, before.env);
        assert_eq!(ctx.txn.lctx, before.lctx);
        assert!(ctx.equations.is_empty());
    }
}
