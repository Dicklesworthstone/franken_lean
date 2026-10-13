//! Proof-producing simplification with explicit and immutable registered rules.
//! Rules are tried deterministically and re-instantiated for every application.
//! An unsuccessful alternative restores its complete elaboration state while
//! retaining spent work. Every productive step is ordinary Eq.rec transport.

mod locations;
mod simpa;
mod unfold;

use super::*;
use unfold::UnfoldResult;

const MAX_SIMPLIFICATION_STEPS: usize = 256;

/// Registered names are resolved once by the attribute command. They must not
/// be reparsed or captured by a same-named local or a later namespace scope.
#[derive(Clone)]
pub(in crate::source) enum SimpRule<'a> {
    Explicit(RewriteRule<'a>),
    Global(scope::simp::SimpEntry),
    /// A wildcard selects a proof by local identity, not its display spelling.
    /// Location simplification remaps this identity when replacing the local.
    Local(FVarId),
}
impl SimpRule<'_> {
    fn reverse(&self) -> bool {
        match self {
            Self::Explicit(rule) => rule.reverse,
            Self::Global(rule) => rule.reverse,
            Self::Local(_) => false,
        }
    }
}

/// Preserve selection order while indexing the rules that can unfold a type.
/// The theorem set can be large; rescanning it for every candidate theorem is
/// quadratic work even when none of those entries can unfold anything.
#[derive(Default)]
pub(in crate::source) struct SimpRules<'a> {
    selected: Vec<SimpRule<'a>>,
    unfolding: Vec<usize>,
    global_unfolding: HashSet<Name>,
    explicit_unfolding: bool,
}

impl Context {
    fn index_simp_rules<'a>(
        &mut self,
        selected: Vec<SimpRule<'a>>,
    ) -> Result<SimpRules<'a>, NatDefinitionElabError> {
        let mut unfolding = Vec::new();
        let mut global_unfolding = HashSet::new();
        let mut explicit_unfolding = false;
        for (index, rule) in selected.iter().enumerate() {
            self.tick()?;
            let candidate = match rule {
                // Explicit names can denote local lets, and local identities
                // may change during hypothesis transport. Resolve them at use.
                SimpRule::Explicit(_) => {
                    explicit_unfolding = true;
                    true
                }
                SimpRule::Local(_) => false,
                SimpRule::Global(entry) => {
                    !entry.reverse
                        && matches!(self.txn.env.find(&entry.declaration),
                            Some(fln_env::constants::ConstantInfo::Defn(definition))
                                if definition.safety == DefinitionSafety::Safe)
                }
            };
            if candidate {
                unfolding.push(index);
                if let SimpRule::Global(entry) = rule {
                    global_unfolding.insert(entry.declaration.clone());
                }
            }
        }
        Ok(SimpRules {
            selected,
            unfolding,
            global_unfolding,
            explicit_unfolding,
        })
    }
    /// Recognize a refutation only when the antecedent is known to be a
    /// proposition. An unknown sort is not permission to guess Prop.
    pub(super) fn simp_negated_proposition(
        &mut self,
        type_: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.tick()?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Ok(None);
        };
        if !matches!(body.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["False"]) && levels.is_empty())
        {
            return Ok(None);
        }
        let Some(sort) = self.known_type(binder_type)? else {
            return Ok(None);
        };
        let sort = self.whnf(&sort)?;
        Ok(
            matches!(sort.node(), ExprNode::Sort { level } if level.is_zero())
                .then(|| binder_type.clone()),
        )
    }

    /// A selected proof of P rewrites P to True; a selected refutation rewrites
    /// P to False. Build an actual equivalence, retaining the original evidence,
    /// then use the same explicit propext/transport path as Iff rewrite rules.
    pub(super) fn simp_proposition_rewrite_rule(
        &mut self,
        rule: Typed,
        reverse: bool,
    ) -> Result<Typed, NatDefinitionElabError> {
        if equality_target(&rule.type_).is_some() {
            return Ok(rule);
        }
        self.tick()?;
        let Some(sort) = self.known_type(&rule.type_)? else {
            return Ok(rule);
        };
        let sort = self.whnf(&sort)?;
        if sort.has_expr_mvar()
            || sort.has_level_mvar()
            || !self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
        {
            return Ok(rule);
        }
        // Reversing a fact's generated True/False rule is not an orientation
        // request on an equality. Keep that unsupported form a typed refusal.
        if reverse {
            return Err(error(TacticError::ExpectedEquality));
        }
        let lambda = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
        let (left, right, forward, backward) =
            if let Some(proposition) = self.simp_negated_proposition(&rule.type_)? {
                let false_ = self.constant(&Name::from_components(["False"]))?.value;
                let recursor =
                    Expr::const_(Name::from_components(["False", "rec"]), vec![Level::zero()]);
                let motive = lambda(false_.clone(), proposition.clone());
                let from_false = lambda(
                    false_.clone(),
                    app(recursor, [motive, Expr::bvar(0).expect("zero index")]),
                );
                (proposition, false_, rule.value, from_false)
            } else {
                let true_ = self.constant(&Name::from_components(["True"]))?.value;
                let intro = self
                    .constant(&Name::from_components(["True", "intro"]))?
                    .value;
                let to_true = lambda(rule.type_.clone(), intro);
                let from_true = lambda(true_.clone(), rule.value);
                (rule.type_, true_, to_true, from_true)
            };
        let iff = self.constant(&Name::from_components(["Iff"]))?.value;
        let intro = self
            .constant(&Name::from_components(["Iff", "intro"]))?
            .value;
        Ok(Typed {
            value: app(intro, [left.clone(), right.clone(), forward, backward]),
            type_: app(iff, [left, right]),
        })
    }

    /// An erasure names a global declaration, even when a local has the same
    /// spelling. Hypothesis erasure belongs to the separate `[*]` profile.
    fn simp_erasure_name(&mut self, name: &Name) -> Result<Name, NatDefinitionElabError> {
        for _ in 0..self
            .source_scope
            .opened
            .len()
            .saturating_add(
                scope::components(&self.source_scope.namespace)
                    .map_err(|e| failure(SourceInferenceError::NameScope(e)))?
                    .len(),
            )
            .saturating_add(1)
        {
            self.tick()?;
        }
        self.source_scope
            .resolve(name, |candidate| self.txn.env.contains(candidate))
            .map_err(|e| failure(SourceInferenceError::NameScope(e)))?
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))
    }

    /// Keep the origin of a bare global selection while assembling this call's
    /// rule set. Applied lemmas have their own expression origin: erasing the
    /// global does not erase an explicitly instantiated proof. Parentheses do
    /// not change identity, and local shadowing follows ordinary term lookup.
    fn simp_rule_global(
        &mut self,
        mut syntax: &Syntax,
    ) -> Result<Option<Name>, NatDefinitionElabError> {
        loop {
            self.tick()?;
            if let Some(inner) = parenthesized_inner(syntax)? {
                syntax = inner;
                continue;
            }
            match syntax {
                Syntax::Ident { val, .. } => {
                    if self.txn.lctx.find_by_user_name(val).is_some() {
                        return Ok(None);
                    }
                    let resolved = self.resolve_source_name(val)?.ok_or_else(|| {
                        failure(SourceInferenceError::UnknownConstant(val.clone()))
                    })?;
                    return Ok((self.txn.lctx.find_by_user_name(&resolved).is_none()
                        && self.txn.env.contains(&resolved))
                    .then_some(resolved));
                }
                _ => return Ok(None),
            }
        }
    }

    fn selected_simp_term(&mut self, rule: &SimpRule<'_>) -> Result<Typed, NatDefinitionElabError> {
        match rule {
            SimpRule::Explicit(rule) => self.simp_rule_term(rule.syntax),
            SimpRule::Global(rule) => self.constant(&rule.declaration),
            SimpRule::Local(id) => {
                self.tick()?;
                let local = self
                    .txn
                    .lctx
                    .find(id)
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                Ok(Typed {
                    value: Expr::fvar(id.clone()),
                    type_: local.type_.clone(),
                })
            }
        }
    }

    /// A bare, explicitly selected induction hypothesis can use its checked
    /// companion without changing the public hypothesis's application API.
    /// Both declarations must still be in this branch. Following only direct
    /// local aliases preserves annotations and local shadowing; ordinary term
    /// applications continue to elaborate the full conditional hypothesis.
    fn simp_rule_term(&mut self, syntax: &Syntax) -> Result<Typed, NatDefinitionElabError> {
        if let Some(term) = self.specialized_induction_rule(syntax)? {
            return Ok(term);
        }
        self.term(syntax, None)
    }

    fn specialized_induction_rule(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if let Syntax::Ident { val, .. } = syntax {
            let mut selected = self.txn.lctx.find_by_user_name(val).cloned();
            let mut seen = std::collections::HashSet::new();
            while let Some(local) = selected {
                self.tick()?;
                if !seen.insert(local.id.clone()) {
                    break;
                }
                if let Some((_, specialized)) = self
                    .induction_specializations
                    .iter()
                    .rev()
                    .find(|(raw, _)| raw == &local.user_name)
                    && let Some(companion) = self.txn.lctx.find_by_user_name(specialized)
                {
                    return Ok(Some(Typed {
                        value: Expr::fvar(companion.id.clone()),
                        type_: companion.type_.clone(),
                    }));
                }
                selected = match local.value.as_ref().map(Expr::node) {
                    Some(ExprNode::FVar { id }) => self.txn.lctx.find(id).cloned(),
                    _ => None,
                };
            }
        }
        Ok(None)
    }

    fn simp_rules<'a>(
        &mut self,
        args: &'a [Syntax],
    ) -> Result<SimpRules<'a>, NatDefinitionElabError> {
        self.tick()?;
        let [keyword, config, discharger, only, arguments, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        let simpa = matches!(keyword, Syntax::Atom { val, .. } if val == "simpa");
        expect_atom(
            keyword,
            if simpa { "simpa" } else { "simp" },
            "simplification keyword",
        )?;
        expect_empty_null(config, "default simplification configuration")?;
        expect_empty_null(discharger, "default simplification discharger")?;
        if !simpa {
            self.rewrite_locations(location)?;
        }
        let use_default = match expect_null_args(only, "optional explicit simp set")? {
            [] => true,
            [only] => {
                expect_atom(only, "only", "explicit-set simplification")?;
                false
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        // Even `simp []` reads the default set; `simp only` never reads it. A
        // malformed registry therefore cannot silently become an empty success.
        let mut defaults = if use_default {
            scope::simp::read(&self.txn.env)
                .map_err(|e| failure(SourceInferenceError::SimpSet(e)))?
                .into_iter()
                .map(SimpRule::Global)
                .collect()
        } else {
            Vec::new()
        };
        for _ in &defaults {
            self.tick()?;
        }
        let arguments = expect_null_args(arguments, "optional simp rule list")?;
        if arguments.is_empty() {
            return self.index_simp_rules(defaults);
        }
        let [open, rows, close] = arguments else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(open, "[", "simp rule opener")?;
        expect_atom(close, "]", "simp rule closer")?;
        let rows = expect_null_args(rows, "simp rules")?;
        let mut rules: Vec<(Option<Name>, SimpRule<'a>)> = Vec::new();
        let mut wildcard_ids = std::collections::HashSet::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "simp rule separator")?;
                continue;
            }
            if matches!(row, Syntax::Node { kind, .. } if kind == &parser_kind(&["Tactic", "simpStar"]))
            {
                let parts = expect_node(
                    row,
                    &parser_kind(&["Tactic", "simpStar"]),
                    1,
                    "simp wildcard",
                )?;
                expect_atom(&parts[0], "*", "simp wildcard marker")?;
                // Work on an immutable snapshot: rule elaboration may allocate
                // holes, but never contributes synthetic premises to `[*]`.
                let locals = self.txn.lctx.decls().to_vec();
                for local in locals {
                    self.tick()?;
                    if self.is_matrix_hypothesis(&local) || !wildcard_ids.insert(local.id.clone()) {
                        continue;
                    }
                    let type_ = self.instantiate(&local.type_)?;
                    let Some(sort) = self.known_type(&type_)? else {
                        continue;
                    };
                    let sort = self.whnf(&sort)?;
                    if !sort.has_expr_mvar()
                        && !sort.has_level_mvar()
                        && self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
                    {
                        rules.push((None, SimpRule::Local(local.id)));
                    }
                }
                continue;
            }
            if matches!(row, Syntax::Node { kind, .. } if kind == &parser_kind(&["Tactic", "simpErase"]))
            {
                let parts = expect_node(
                    row,
                    &parser_kind(&["Tactic", "simpErase"]),
                    2,
                    "simp erasure",
                )?;
                expect_atom(&parts[0], "-", "simp erasure marker")?;
                let Syntax::Ident { val, .. } = &parts[1] else {
                    return Err(error(TacticError::MalformedScript));
                };
                let name = self.simp_erasure_name(val)?;
                for _ in 0..rules.len().saturating_add(defaults.len()) {
                    self.tick()?;
                }
                rules.retain(|(origin, _)| origin.as_ref() != Some(&name));
                defaults.retain(
                    |rule| !matches!(rule, SimpRule::Global(entry) if entry.declaration == name),
                );
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "simpLemma"]), 3, "simp lemma")?;
            expect_empty_null(&parts[0], "default post-order simp rule")?;
            let reverse = match expect_null_args(&parts[1], "simp direction")? {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            // `term` below runs the normal heap-driven elaborator. The source
            // parser already forbids nested proof scripts, but a caller can
            // supply Syntax directly: enforce the same boundary here so this
            // one level of re-entry can never grow with source-controlled depth.
            let mut pending = vec![&parts[2]];
            while let Some(term) = pending.pop() {
                self.tick()?;
                if let Syntax::Node { kind, args, .. } = term {
                    if kind == &parser_kind(&["Term", "byTactic"]) {
                        return Err(error(TacticError::MalformedScript));
                    }
                    pending.extend(args);
                }
            }
            let origin = self.simp_rule_global(&parts[2])?;
            if let Some(name) = &origin {
                // One selected direction per named rule. In particular,
                // `simp [← lemma]` must not retain the default forward rule.
                for _ in 0..rules.len().saturating_add(defaults.len()) {
                    self.tick()?;
                }
                rules.retain(|(previous, _)| previous.as_ref() != Some(name));
                defaults.retain(
                    |rule| !matches!(rule, SimpRule::Global(entry) if &entry.declaration == name),
                );
            }
            rules.push((
                origin,
                SimpRule::Explicit(RewriteRule {
                    syntax: &parts[2],
                    reverse,
                }),
            ));
        }
        // Explicit arguments have precedence; registered rules follow in their
        // stable priority/registration order. `only` leaves this tail empty.
        self.index_simp_rules(
            rules
                .into_iter()
                .map(|(_, rule)| rule)
                .chain(defaults)
                .collect(),
        )
    }

    fn restore_simp_trial(&mut self, mut original: Self) {
        original.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
        *self = original;
    }

    /// An admitted monomorphic theorem's matching obligations depend on its
    /// type and direction, not on which proof constant inhabits that type.
    /// Reuse only a completed nonmatch for this exact goal/context snapshot.
    /// Hashes choose a bucket; metered structural comparison and exact equality
    /// (including binder annotations) establish identity, never the hash alone.
    fn previously_failed_simp_type(
        &mut self,
        rule: &SimpRule<'_>,
        failed: &HashMap<(u64, bool), Vec<Expr>>,
    ) -> Result<(bool, Option<Expr>), NatDefinitionElabError> {
        let SimpRule::Global(entry) = rule else {
            return Ok((false, None));
        };
        let Some(fln_env::constants::ConstantInfo::Thm(theorem)) =
            self.txn.env.find(&entry.declaration)
        else {
            return Ok((false, None));
        };
        if !theorem.base.level_params.is_empty() {
            return Ok((false, None));
        }
        let type_ = theorem.base.type_.clone();
        if let Some(previous) = failed.get(&(type_.hash(), entry.reverse)) {
            for candidate in previous {
                if self.rewrite_same(candidate, &type_)? && candidate == &type_ {
                    return Ok((true, None));
                }
            }
        }
        Ok((false, Some(type_)))
    }

    /// Only selected definitions participate in conversion of a side condition.
    fn simp_premise_target(
        &mut self,
        target: &Expr,
        rules: &SimpRules<'_>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut target = target.clone();
        for _ in 0..MAX_SIMPLIFICATION_STEPS {
            let mut names = None::<HashSet<Name>>;
            let mut absent_normalized = false;
            let mut changed = false;
            for &index in &rules.unfolding {
                self.tick()?;
                let rule = &rules.selected[index];
                if names.is_none() {
                    names = Some(self.simp_constant_names(&target)?);
                }
                let absent = matches!(rule, SimpRule::Global(entry)
                    if names.as_ref().is_some_and(|names| !names.contains(&entry.declaration)));
                if absent && absent_normalized {
                    continue;
                }
                match self.unfold_simp_rule(rule, &target)? {
                    UnfoldResult::Changed(next) => {
                        target = next;
                        changed = true;
                        names = None;
                        absent_normalized = false;
                    }
                    // An absent global still normalizes beta/zeta/iota redexes.
                    // Only a real unchanged pass permits skipping later absent
                    // globals. Changes above refresh both this fact and names.
                    UnfoldResult::Unchanged if absent => {
                        absent_normalized = true;
                        // Once normalization has actually left this target
                        // unchanged, a disjoint name set proves that every
                        // remaining global would take the same absent shortcut.
                        // Explicit rules still resolve dynamically. Inspect the
                        // smaller name set, charging every lookup so HashSet's
                        // traversal order cannot change the work count.
                        if !rules.explicit_unfolding
                            && let Some(names) = &names
                            && names.len() < rules.global_unfolding.len()
                        {
                            let mut all_absent = true;
                            for name in names {
                                self.tick()?;
                                all_absent &= !rules.global_unfolding.contains(name);
                            }
                            if all_absent {
                                break;
                            }
                        }
                    }
                    // Explicit terms resolve against the current local context;
                    // never carry the shortcut across their work.
                    _ if matches!(rule, SimpRule::Explicit(_)) => absent_normalized = false,
                    _ => {}
                }
            }
            if !changed {
                return Ok(target);
            }
        }
        Err(failure(SourceInferenceError::ResourceLimit))
    }

    fn simp_constant_names(
        &mut self,
        root: &Expr,
    ) -> Result<HashSet<Name>, NatDefinitionElabError> {
        let mut names = HashSet::new();
        let mut seen = HashSet::new();
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            self.tick()?;
            if let ExprNode::Const { name, .. } = term.node() {
                names.insert(name.clone());
            }
            pending.extend(children(term).into_iter().flatten());
        }
        Ok(names)
    }

    fn simp_selected_proof(
        &mut self,
        target: &Expr,
        rules: &SimpRules<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        for rule in &rules.selected {
            self.tick()?;
            let selected = self.selected_simp_term(rule)?;
            // Selected unfolding cannot change a rigid Sort, Forall or admitted
            // inductive head. Reject that mismatch before walking every node
            // of an unrelated theorem type through the unfolding selections.
            if self.rewrite_types_have_distinct_heads(&selected.type_, target)? {
                continue;
            }
            let type_ = self.simp_premise_target(&selected.type_, rules)?;
            // A completed rewrite search may leave an unsolvable target. Do
            // not send every unrelated fact through conversion merely to
            // rediscover that their admitted inductive heads differ.
            if self.rewrite_types_have_distinct_heads(&type_, target)? {
                continue;
            }
            let Some(universe) = self.known_type(&type_)? else {
                continue;
            };
            let universe = self.whnf(&universe)?;
            if !matches!(universe.node(), ExprNode::Sort { level } if level.is_zero()) {
                continue;
            }
            let mut budget = UnificationBudget::new(self.kernel);
            budget.zeta_delta = false;
            if self.proof_types_match_with_budget(&type_, target, budget)? {
                let value = self.instantiate(&selected.value)?;
                if !value.has_expr_mvar() && !value.has_level_mvar() {
                    return Ok(Some(value));
                }
            }
        }
        Ok(None)
    }

    pub(super) fn simp_discharge_premise(
        &mut self,
        id: &MVarId,
        target: &Expr,
        rules: &SimpRules<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let target = self.simp_premise_target(target, rules)?;
        if let Some(value) = self.simp_selected_proof(&target, rules)? {
            return Ok(Some(value));
        }
        let goal = ProofGoal {
            id: id.clone(),
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        if let Some(value) = self.simp_reflexivity(&goal)? {
            return Ok(Some(value));
        }
        if rules.selected.is_empty() {
            return Ok(None);
        }
        let original = self.rewrite_trial();
        let value = self.rewrite_simp_premise(&goal.target, rules)?;
        if value.is_none() {
            self.restore_simp_trial(original);
        }
        Ok(value)
    }

    /// Construct a premise proof using the selected equalities and definitions.
    /// Parents live on the heap; rewriting a premise never recursively invokes
    /// the same selected set. Inner rules may discharge reflexive premises only.
    fn rewrite_simp_premise(
        &mut self,
        target: &Expr,
        rules: &SimpRules<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let (root, mut goal) = self.proof_goal(target.clone())?;
        let mut parents = Vec::new();
        let mut history = vec![target.clone()];
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            let mut failed = HashMap::<(u64, bool), Vec<Expr>>::new();
            for rule in &rules.selected {
                self.tick()?;
                let (seen, type_) = self.previously_failed_simp_type(rule, &failed)?;
                if seen {
                    continue;
                }
                let original = self.rewrite_trial();
                let Some((next_goal, value)) =
                    self.simp_step(&goal, rule, &SimpRules::default())?
                else {
                    self.restore_simp_trial(original);
                    if let Some(type_) = type_ {
                        failed
                            .entry((type_.hash(), rule.reverse()))
                            .or_default()
                            .push(type_);
                    }
                    continue;
                };
                if parents.len() >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                parents.push((goal, value));
                goal = next_goal;
                advanced = true;
                break;
            }
            if advanced {
                continue;
            }
            let value = match self.simp_selected_proof(&goal.target, rules)? {
                Some(value) => Some(value),
                None => self.simp_reflexivity(&goal)?,
            };
            let Some(value) = value else {
                return Ok(None);
            };
            self.close_proof_goal(goal, value)?;
            while let Some((parent, value)) = parents.pop() {
                self.tick()?;
                self.close_proof_goal(parent, value)?;
            }
            return Ok(Some(self.instantiate(&root)?));
        }
    }

    fn simp_step(
        &mut self,
        goal: &ProofGoal,
        rule: &SimpRule<'_>,
        premise_rules: &SimpRules<'_>,
    ) -> Result<Option<(ProofGoal, Expr)>, NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        match self.unfold_simp_rule(rule, &target)? {
            UnfoldResult::Unchanged => Ok(None),
            UnfoldResult::Changed(next_target) => {
                let (child, next_goal) = self.proof_goal(next_target)?;
                Ok(Some((next_goal, child)))
            }
            UnfoldResult::NotDefinition => {
                // Re-elaboration gives each polymorphic use fresh universes.
                let mut term = self.selected_simp_term(rule)?;
                // Selected definitions normalize the lemma's type as well as
                // the goal. Keep its actual proof term: conversion is checked
                // by the final kernel, never replaced by an equality axiom.
                term.type_ = self.simp_premise_target(&term.type_, premise_rules)?;
                let Some(RewriteMatch {
                    rule: term,
                    occurrence,
                    premises,
                }) = self.instantiate_rewrite_rule(
                    term,
                    &target,
                    rule.reverse(),
                    true,
                    premise_rules,
                )?
                else {
                    return Ok(None);
                };
                assert!(premises.is_empty(), "simp discharges its own premises");
                Ok(Some(self.rewrite_transport(
                    goal,
                    term,
                    &occurrence,
                    rule.reverse(),
                )?))
            }
        }
    }

    /// Check a candidate only after the shared automatic-closure policy admits
    /// it. Full K1 assignment conversion alone would unfold ordinary definitions
    /// that are absent from this tactic's explicit rule set.
    fn simp_reflexivity(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let original = self.rewrite_trial();
        let target = self.whnf_with_transparency(
            &goal.target,
            UnificationTransparency::Abbreviations,
            false,
        )?;
        let candidate = if matches!(target.node(), ExprNode::Const { name, levels }
            if name == &Name::from_components(["True"]) && levels.is_empty())
        {
            Some(
                self.constant(&Name::from_components(["True", "intro"]))?
                    .value,
            )
        } else {
            self.automatic_reflexivity_candidate(goal, false)?
        };
        let Some(candidate) = candidate else {
            self.restore_simp_trial(original);
            return Ok(None);
        };
        let target = self.instantiate(&goal.target)?;
        let mut trial = self.rewrite_trial();
        let hole = trial.hole(target)?;
        let result = trial
            .txn
            .unify(&hole, &candidate, UnificationBudget::new(trial.kernel));
        self.charge_rewrite_trial(&trial);
        match result {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                let candidate = trial.instantiate(&candidate)?;
                *self = trial;
                Ok(Some(candidate))
            }
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if Self::rewrite_nonmatch(&error) {
                    self.restore_simp_trial(original);
                    Ok(None)
                } else {
                    Err(error)
                }
            }
        }
    }

    pub(in crate::source) fn simplify_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        if self.simplify_at_locations(proof, &goal, args)? {
            return Ok(());
        }
        let rules = self.simp_rules(args)?;
        self.simplify_goal_with_rules(proof, goal, &rules, 0, None)
    }

    // Hypothesis and goal simplification share one productive-step limit. A
    // changed hypothesis is sufficient progress when the target stays unchanged.
    fn simplify_goal_with_rules(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        rules: &SimpRules<'_>,
        mut steps: usize,
        completion: Option<&Typed>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut history = vec![self.instantiate(&goal.target)?];
        loop {
            self.tick()?;
            self.txn.lctx = goal.lctx.clone();
            let mut advanced = false;
            let mut failed = HashMap::<(u64, bool), Vec<Expr>>::new();
            for rule in &rules.selected {
                self.tick()?;
                let (seen, type_) = self.previously_failed_simp_type(rule, &failed)?;
                if seen {
                    continue;
                }
                let original = self.rewrite_trial();
                let transition = self.simp_step(&goal, rule, rules)?;
                let Some((next_goal, value)) = transition else {
                    self.restore_simp_trial(original);
                    if let Some(type_) = type_ {
                        failed
                            .entry((type_.hash(), rule.reverse()))
                            .or_default()
                            .push(type_);
                    }
                    continue;
                };
                if steps >= MAX_SIMPLIFICATION_STEPS {
                    return Err(failure(SourceInferenceError::ResourceLimit));
                }
                let next_target = self.instantiate(&next_goal.target)?;
                for previous in &history {
                    self.tick()?;
                    if self.rewrite_same(previous, &next_target)? {
                        return Err(error(TacticError::SimplificationCycle));
                    }
                }
                history.push(next_target);
                proof.work.push(Work::Close(goal, value));
                goal = next_goal;
                steps += 1;
                advanced = true;
                break;
            }
            if advanced {
                continue;
            }
            if let Some(completion) = completion {
                let mut budget = UnificationBudget::new(self.kernel);
                budget.zeta_delta = false;
                if !self.proof_types_match_with_budget(&completion.type_, &goal.target, budget)? {
                    return Err(error(TacticError::NoMatchingAssumption));
                }
                self.close_proof_goal(goal, completion.value.clone())?;
            } else if let Some(value) = self.simp_reflexivity(&goal)? {
                self.close_proof_goal(goal, value)?;
            } else if let Some(value) = self.simp_selected_proof(&goal.target, rules)? {
                self.close_proof_goal(goal, value)?;
            } else if steps > 0 {
                // Simplification can expose a non-reflexive remaining goal.
                // Later instructions must solve it; progress is not completion.
                proof.work.push(Work::Goal(goal));
            } else {
                return Err(error(TacticError::SimplificationNoProgress));
            }
            return Ok(());
        }
    }
}
