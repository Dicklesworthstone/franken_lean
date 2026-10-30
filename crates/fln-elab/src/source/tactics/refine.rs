//! Partial proof terms with explicitly scoped synthetic goals.
//!
//! A hole under a lambda must not be a bare metavariable whose hidden context
//! escapes when that lambda closes. Represent each hole by a closed function
//! metavariable applied to its captured locals, and close that same telescope
//! when its proof-state goal is solved. All transport is explicit core syntax.
use super::*;

#[derive(Clone, Default)]
pub(in crate::source) struct RefinementFrame {
    holes: Vec<(Option<Name>, ProofGoal)>,
    /// `refine'`: a `_` is a new goal too, as the pin's `holesAsSyntheticOpaque` makes it
    /// (`withCollectingNewGoalsFrom` with `allowNaturalHoles`, vendored
    /// src/Lean/Elab/Tactic/ElabTerm.lean:140-180).
    placeholders: bool,
    /// The first fresh name this refinement's elaboration can take: a hole named from it on
    /// was made by the refinement (the pin's `mvarCounterSaved`).
    first_name: u64,
}

impl Context {
    /// The final tactic comparison in the pin's `elabTermEnsuringType` permits
    /// synthetic opaque assignments. Keep that permission local to this one
    /// equation: neither pending elaboration equations nor instance selection
    /// run with the widened policy, and persistent metavariable kinds survive.
    pub(in crate::source) fn ensure_tactic_term_type(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut trial = self.clone();
        let result = (|| {
            let mut declarations: Vec<_> = trial.txn.mvars.decls().keys().cloned().collect();
            declarations.sort_by(|left, right| left.0.cmp(&right.0));
            let mut holes = Vec::new();
            for id in declarations {
                trial.tick()?;
                if trial
                    .txn
                    .mvars
                    .get_decl(&id)
                    .expect("existing declaration")
                    .kind
                    != MetavarKind::SyntheticOpaque
                {
                    continue;
                }
                trial
                    .txn
                    .mvars
                    .set_kind(&id, MetavarKind::Synthetic)
                    .map_err(|e| {
                        failure(SourceInferenceError::Unification(Box::new(
                            UnificationError::Metavariable(e),
                        )))
                    })?;
                holes.push(id);
            }
            trial
                .unify_source_batch(&[(actual.clone(), expected.clone())], true)
                .map_err(|e| failure(SourceInferenceError::Unification(Box::new(e))))?;
            for id in &holes {
                trial.tick()?;
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
            Ok(())
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        result?;
        *self = trial;
        Ok(())
    }

    /// `exact` elaborates holes too, but unlike `refine` cannot leave any of
    /// its new holes to a later tactic (`closeMainGoalUsing`).
    pub(in crate::source) fn finish_exact_refinement(
        &mut self,
        goal: &ProofGoal,
        term: &Typed,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if self.refinements.len() != depth + 1 {
            return Err(error(TacticError::MalformedScript));
        }
        self.txn.lctx = goal.lctx.clone();
        // The pin's tactic `elabTerm` ends with `synthesizeSyntheticMVars (postpone := .no)`
        // (`runTermElab`, vendored `Lean/Elab/Tactic/ElabTerm.lean:29-60`), which applies default
        // instances, before the term's type meets the goal.
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        self.ensure_tactic_term_type(&term.type_, &goal.target)?;
        let frame = self.refinements.pop().expect("checked refinement depth");
        self.refuse_new_natural_holes(&term.value, frame.first_name)?;
        let count = frame
            .holes
            .iter()
            .filter(|(_, hole)| !self.txn.mvars.is_assigned(&hole.id))
            .count();
        if count != 0 {
            return Err(error(TacticError::UnsolvedGoals { count }));
        }
        Ok(())
    }

    pub(in crate::source) fn begin_refinement(&mut self) -> usize {
        let depth = self.refinements.len();
        self.refinements.push(RefinementFrame {
            first_name: self.next,
            ..RefinementFrame::default()
        });
        depth
    }

    /// [`Self::begin_refinement`] for `refine'`, whose `_`s are new goals.
    pub(in crate::source) fn begin_placeholder_refinement(&mut self) -> usize {
        let depth = self.refinements.len();
        self.refinements.push(RefinementFrame {
            holes: Vec::new(),
            placeholders: true,
            first_name: self.next,
        });
        depth
    }

    /// Whether a `_` here is a goal of the innermost `refine'` rather than a natural hole.
    pub(in crate::source) fn placeholders_are_goals(&self) -> bool {
        self.refinements
            .last()
            .is_some_and(|frame| frame.placeholders)
    }

    pub(in crate::source) fn synthetic_proof_hole(
        &mut self,
        name: Option<Name>,
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        if self.refinements.is_empty() {
            return Err(error(TacticError::SyntheticHoleOutsideRefine));
        }
        self.tick()?;
        let type_ = match expected {
            Some(type_) => type_.clone(),
            None => {
                let sort = self.type_expected()?;
                self.hole(sort)?
            }
        };
        let existing = name
            .as_ref()
            .and_then(|name| self.named_refinement_holes.get(name).cloned());
        let goal = if let Some(goal) = existing {
            // The pin first reuses a hole whose captured context is a prefix.
            // A name never silently becomes fresh in another branch/frame.
            if !self.txn.lctx.decls().starts_with(goal.lctx.decls()) {
                // An assigned value may retain locals shared with this scope. Our
                // representation applies a closed telescope to captured locals,
                // so expose that value before checking whether it still captures.
                if self.txn.mvars.is_assigned(&goal.id) {
                    let mut value = Expr::mvar(goal.id.clone());
                    for local in goal.lctx.decls() {
                        self.tick()?;
                        if local.value.is_none() {
                            value = Expr::app(value, Expr::fvar(local.id.clone()));
                        }
                    }
                    let value = self.whnf(&value)?;
                    let actual = self.instantiate(&goal.target)?;
                    let mut scoped_value = value.clone();
                    let mut scoped_type = actual.clone();
                    for local in self.txn.lctx.decls().to_vec() {
                        self.tick()?;
                        scoped_value = scoped_value
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                        scoped_type = scoped_type
                            .abstract_fvar(&local.id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?;
                    }
                    if !scoped_value.has_fvar() && !scoped_type.has_fvar() {
                        self.constrain_type(&actual, &type_)?;
                        return Ok(Typed {
                            value,
                            type_: actual,
                        });
                    }
                } else if goal.lctx.decls().starts_with(self.txn.lctx.decls())
                    && self
                        .txn
                        .mvars
                        .get_decl(&goal.id)
                        .is_some_and(|decl| decl.delayed.is_none())
                {
                    // The later occurrence has a smaller context. Replace the
                    // unassigned hole there, then close the old telescope over
                    // that replacement, as the pin's mvarId.assign does.
                    let replacement = self.synthetic_proof_hole(None, Some(&type_))?;
                    let (replacement_name, replacement_goal) = self
                        .refinements
                        .last_mut()
                        .expect("active refinement")
                        .holes
                        .last_mut()
                        .expect("fresh replacement");
                    *replacement_name = name.clone();
                    let replacement_goal = replacement_goal.clone();
                    self.named_refinement_holes
                        .insert(name.clone().expect("named existing hole"), replacement_goal);
                    let current = self.txn.lctx.clone();
                    let closed = self.close_proof_goal(goal, replacement.value.clone());
                    self.txn.lctx = current;
                    closed?;
                    return Ok(replacement);
                }
                return Err(error(TacticError::IncompatibleSyntheticHole));
            }
            if !self.proof_types_match(&goal.target, &type_)? {
                return Err(error(TacticError::IncompatibleSyntheticHole));
            }
            goal
        } else {
            let locals = self.txn.lctx.decls().to_vec();
            let mut closed_type = type_.clone();
            for local in locals.iter().rev() {
                self.tick()?;
                closed_type = closed_type
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                closed_type = if let Some(value) = &local.value {
                    Expr::let_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                        closed_type,
                        false,
                    )
                } else {
                    Expr::forall_e(
                        local.user_name.clone(),
                        local.type_.clone(),
                        closed_type,
                        local.binder_info,
                    )
                };
            }
            let id = MVarId(self.fresh_name()?);
            self.txn.mvars.declare(
                id.clone(),
                name.clone().unwrap_or_else(|| id.0.clone()),
                closed_type,
                LocalContext::new(),
                MetavarKind::SyntheticOpaque,
                0,
                None,
            );
            let goal = ProofGoal {
                id,
                no_implicit_lambda: self.implicit_lambda_blocked(&type_)?,
                target: type_.clone(),
                lctx: self.txn.lctx.clone(),
                introduced: locals,
            };
            if let Some(name) = &name {
                self.named_refinement_holes
                    .insert(name.clone(), goal.clone());
            }
            self.refinements
                .last_mut()
                .expect("active refinement")
                .holes
                .push((name, goal.clone()));
            goal
        };
        let mut value = Expr::mvar(goal.id);
        for local in goal.lctx.decls() {
            self.tick()?;
            if local.value.is_none() {
                value = Expr::app(value, Expr::fvar(local.id.clone()));
            }
        }
        Ok(Typed { value, type_ })
    }

    /// Tactic `suffices d` is `refine_lift suffices d; ?_` (vendored src/Init/Tactics.lean):
    /// term-mode `suffices` whose witness is a fresh goal. Its continuation (`by …` or
    /// `from …`) proves the original goal from the stated fact, which becomes the main goal.
    pub(super) fn suffices_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        keyword: &Syntax,
        declaration: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
        let syntax = Syntax::node(
            parser_kind(&["Term", "suffices"]),
            vec![
                keyword.clone(),
                declaration.clone(),
                Syntax::node(Name::from_components(["null"]), Vec::new()),
                Syntax::node(
                    parser_kind(&["Term", "syntheticHole"]),
                    vec![atom("?"), atom("_")],
                ),
            ],
        );
        self.txn.lctx = goal.lctx.clone();
        let depth = self.begin_refinement();
        let term = self.term_without_implicit_lambda(&syntax, Some(goal.target.clone()))?;
        self.finish_refinement(proof, goal, term, depth)
    }

    /// The pin's `tagUntaggedGoals parentTag suffix newGoals` (vendored
    /// src/Lean/Elab/Tactic/ElabTerm.lean): among the holes still unassigned, in creation order
    /// (`sortMVarIdsByIndex`), a lone anonymous one takes the parent's tag, and several each take
    /// the parent's tag with `suffix_i` appended. A named hole `?x` is tagged `x`.
    fn tag_refinement_goals(&mut self, parent: &ProofGoal, frame: &RefinementFrame, suffix: &str) {
        let open: Vec<&(Option<Name>, ProofGoal)> = frame
            .holes
            .iter()
            .filter(|(_, hole)| !self.txn.mvars.is_assigned(&hole.id))
            .collect();
        let anonymous = open.iter().filter(|(name, _)| name.is_none()).count();
        let tag = self
            .goal_tags
            .get(&parent.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let mut index = 1;
        for (name, hole) in open {
            match name {
                Some(name) => {
                    self.goal_tags.insert(hole.id.clone(), name.clone());
                }
                None if anonymous == 1 => {
                    self.goal_tags.insert(hole.id.clone(), tag.clone());
                }
                None => {
                    self.goal_tags.insert(
                        hole.id.clone(),
                        Name::str(tag.clone(), format!("{suffix}_{index}")),
                    );
                    index += 1;
                }
            }
        }
    }

    /// `exists e₁, …, eₙ`, the pin's `(refine ⟨e₁, …, eₙ, ?_⟩; try trivial)` (vendored
    /// src/Init/Tactics.lean:1243-1244): `trivial` on the refinement's main goal, undone when it
    /// fails.
    pub(super) fn exists_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, witnesses] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "exists", "exists keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "tacticExists_,,"])?;
        let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
        let mut fields = expect_null_args(witnesses, "exists witnesses")?.to_vec();
        if fields.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        fields.push(atom(","));
        fields.push(Syntax::node(
            parser_kind(&["Term", "syntheticHole"]),
            vec![atom("?"), atom("_")],
        ));
        let syntax = Syntax::node(
            parser_kind(&["Term", "anonymousCtor"]),
            vec![
                atom("⟨"),
                Syntax::node(Name::from_components(["null"]), fields),
                atom("⟩"),
            ],
        );
        self.txn.lctx = goal.lctx.clone();
        let depth = self.begin_refinement();
        let term = self.term(&syntax, Some(goal.target.clone()))?;
        self.finish_refinement(proof, goal, term, depth)?;
        // `try trivial` on the main goal the refinement left.
        let Some(Work::Goal(main)) = proof.work.pop() else {
            return Err(error(TacticError::MalformedScript));
        };
        if self.txn.mvars.is_assigned(&main.id) {
            proof.work.push(Work::Goal(main));
            return Ok(());
        }
        let snapshot = Box::new(self.clone());
        match self.trivial_proof_goal(main.clone()) {
            Ok(()) => Ok(()),
            Err(problem) if backtrack::recoverable(&problem) => {
                let spent = self.txn.budget.heartbeats_consumed;
                let aux_names = self.aux_names.take();
                *self = *snapshot;
                self.txn.budget.heartbeats_consumed = spent;
                self.aux_names = aux_names;
                proof.work.push(Work::Goal(main));
                Ok(())
            }
            Err(problem) => Err(problem),
        }
    }

    /// Tactic `match` (`evalMatch`, vendored src/Lean/Elab/Tactic/Match.lean): the term
    /// `refine no_implicit_lambda% (match … with | p => ?rhs …)`, one alternative per pattern
    /// group, then `case rhs => tac` for each alternative whose right side is a tactic block, in
    /// order, each closing its goal. A `_` right side is a goal tagged `match_i` under the main
    /// goal's tag when there are several alternatives; a `?x` stays as written.
    pub(super) fn match_proof_goal<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        args: &'a [Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [
            keyword,
            generalizing,
            motive,
            discriminants,
            with,
            alternatives,
        ] = args
        else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "match", "match keyword")?;
        expect_atom(with, "with", "match with")?;
        let [rows] = expect_node(
            alternatives,
            &parser_kind(&["Term", "matchAlts"]),
            1,
            "match alternatives",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let rows = expect_null_args(rows, "match alternatives")?;
        let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
        let hole = |name: &str| {
            Syntax::node(
                parser_kind(&["Term", "syntheticHole"]),
                vec![
                    atom("?"),
                    Syntax::Ident {
                        info: fln_syntax::source::SourceInfo::None,
                        raw_val: fln_syntax::source::ByteSpan::default(),
                        val: Name::from_components([name]),
                        preresolved: Vec::new(),
                    },
                ],
            )
        };
        let parent = self
            .goal_tags
            .get(&goal.id)
            .cloned()
            .unwrap_or_else(Name::anonymous);
        let mut alternatives_out = Vec::new();
        // The tactic alternatives' holes, in order, and the `_` holes' tags.
        let mut scripts: Vec<(Name, &'a Syntax)> = Vec::new();
        let mut placeholders: Vec<(Name, Name)> = Vec::new();
        let mut next_placeholder = 1;
        for row in rows {
            self.tick()?;
            let [pipe, groups, arrow, body] = expect_node(
                row,
                &parser_kind(&["Term", "matchAlt"]),
                4,
                "match alternative",
            )?
            else {
                return Err(error(TacticError::MalformedScript));
            };
            for (index, group) in expect_null_args(groups, "match patterns")?
                .iter()
                .enumerate()
            {
                if index % 2 == 1 {
                    expect_atom(group, "|", "match pattern separator")?;
                    continue;
                }
                let rhs = if body.kind() == Some(&parser_kind(&["Term", "syntheticHole"])) {
                    body.clone()
                } else if body.kind() == Some(&parser_kind(&["Term", "hole"])) {
                    let name = format!("_fln_match_{}", self.fresh_name()?.to_display_string());
                    let tag = if rows.len() > 1 {
                        let tag = Name::str(parent.clone(), format!("match_{next_placeholder}"));
                        next_placeholder += 1;
                        tag
                    } else {
                        parent.clone()
                    };
                    placeholders.push((Name::from_components([name.as_str()]), tag));
                    hole(&name)
                } else {
                    let name = format!("_fln_rhs_{}", self.fresh_name()?.to_display_string());
                    scripts.push((Name::from_components([name.as_str()]), body));
                    hole(&name)
                };
                alternatives_out.push(Syntax::node(
                    parser_kind(&["Term", "matchAlt"]),
                    vec![
                        pipe.clone(),
                        Syntax::node(Name::from_components(["null"]), vec![group.clone()]),
                        arrow.clone(),
                        rhs,
                    ],
                ));
            }
        }
        let syntax = Syntax::node(
            parser_kind(&["Term", "match"]),
            vec![
                keyword.clone(),
                generalizing.clone(),
                motive.clone(),
                discriminants.clone(),
                with.clone(),
                Syntax::node(
                    parser_kind(&["Term", "matchAlts"]),
                    vec![Syntax::node(
                        Name::from_components(["null"]),
                        alternatives_out,
                    )],
                ),
            ],
        );
        self.txn.lctx = goal.lctx.clone();
        let depth = self.begin_refinement();
        let term = self.term_without_implicit_lambda(&syntax, Some(goal.target.clone()))?;
        self.finish_refinement(proof, goal, term, depth)?;
        // Each tactic alternative's goal, out of the refinement's goals, runs its block first,
        // in order, as the `case`s after the `refine` do; every other goal keeps its place.
        let mut runs = Vec::new();
        for (name, body) in scripts {
            self.tick()?;
            let position = proof.work.iter().rposition(|work| {
                matches!(work, Work::Goal(hole) if self.goal_tags.get(&hole.id) == Some(&name))
            });
            let Some(position) = position else {
                // Solved by elaboration itself: `case` would find no goal.
                return Err(error(TacticError::CaseTagNotFound(name)));
            };
            let Work::Goal(mut hole) = proof.work.remove(position) else {
                return Err(error(TacticError::MalformedScript));
            };
            self.goal_tags.remove(&hole.id);
            // Each alternative's type is the motive's, made from the annotated expected type.
            hole.no_implicit_lambda = true;
            runs.push(Work::Script(hole, self.proof_instructions(body)?));
        }
        for (name, tag) in placeholders {
            let found = proof.work.iter_mut().find_map(|work| match work {
                Work::Goal(hole) if self.goal_tags.get(&hole.id) == Some(&name) => {
                    hole.no_implicit_lambda = true;
                    Some(hole.id.clone())
                }
                _ => None,
            });
            if let Some(id) = found {
                if tag.is_anonymous() {
                    self.goal_tags.remove(&id);
                } else {
                    self.goal_tags.insert(id, tag);
                }
            }
        }
        proof.work.extend(runs.into_iter().rev());
        Ok(())
    }

    /// Tactic `let rec d`, the pin's `refine_lift let rec d; ?_` (vendored
    /// src/Init/Tactics.lean): `focus (refine no_implicit_lambda% (let rec d; ?_); rotate_right)`,
    /// so the continuation, the last goal made, is the main goal.
    pub(super) fn let_rec_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, rec, declarations] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "let", "let rec keyword")?;
        expect_atom(rec, "rec", "let rec keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "letrec"])?;
        let atom = |text: &str| Syntax::atom(fln_syntax::source::SourceInfo::None, text);
        let syntax = Syntax::node(
            parser_kind(&["Term", "letrec"]),
            vec![
                Syntax::node(
                    Name::str(Name::anonymous(), "group"),
                    vec![keyword.clone(), rec.clone()],
                ),
                declarations.clone(),
                Syntax::node(Name::from_components(["null"]), Vec::new()),
                Syntax::node(
                    parser_kind(&["Term", "syntheticHole"]),
                    vec![atom("?"), atom("_")],
                ),
            ],
        );
        self.txn.lctx = goal.lctx.clone();
        let depth = self.begin_refinement();
        let term = self.term_without_implicit_lambda(&syntax, Some(goal.target.clone()))?;
        let start = proof.work.len();
        self.finish_refinement(proof, goal, term, depth)?;
        // `rotate_right` among the refinement's goals: the last becomes the first.
        let goals: Vec<usize> = (start..proof.work.len())
            .filter(|&index| {
                matches!(&proof.work[index], Work::Goal(hole) if !self.txn.mvars.is_assigned(&hole.id))
            })
            .collect();
        if let (Some(&last), Some(&first)) = (goals.first(), goals.last()) {
            // The stack's top is the first goal; the bottom-most is the last made.
            let moved = proof.work.remove(last);
            proof.work.insert(first, moved);
        }
        Ok(())
    }

    pub(in crate::source) fn finish_refinement(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        term: Typed,
        depth: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if self.refinements.len() != depth + 1 {
            return Err(error(TacticError::MalformedScript));
        }
        let mut frame = self.refinements.pop().expect("checked refinement depth");
        self.txn.lctx = goal.lctx.clone();
        // Default instances apply here too (`finish_exact_refinement`).
        self.resolve_instances_with_defaults()?;
        self.flush(false)?;
        self.ensure_tactic_term_type(&term.type_, &goal.target)?;
        if !frame.placeholders {
            self.refuse_new_natural_holes(&term.value, frame.first_name)?;
        } else {
            // `collectFreshMVars` includes implicit natural holes too, not
            // only syntax holes recorded in the frame. In `refine' rfl` the
            // expected-first application hint can assign an older goal to a
            // new implicit hole, which must now become a goal in its own right.
            let value = self.instantiate(&term.value)?;
            let mut ids: Vec<_> = self.txn.mvars.collect_mvars(&value).into_iter().collect();
            ids.sort_by(|left, right| left.0.cmp(&right.0));
            let source = Name::from_components(["_fln_source"]);
            for id in ids {
                self.tick()?;
                if !matches!(id.0.leaf_view(), LeafView::Num(index) if index >= frame.first_name)
                    || id.0.parent() != source
                    || frame.holes.iter().any(|(_, hole)| hole.id == id)
                {
                    continue;
                }
                let Some(declaration) = self.txn.mvars.get_decl(&id) else {
                    continue;
                };
                if declaration.kind != MetavarKind::Natural || declaration.delayed.is_some() {
                    continue;
                }
                frame.holes.push((
                    None,
                    ProofGoal {
                        id,
                        target: declaration.type_.clone(),
                        lctx: declaration.lctx.clone(),
                        introduced: Vec::new(),
                        no_implicit_lambda: false,
                    },
                ));
            }
            frame
                .holes
                .sort_by(|(_, left), (_, right)| left.id.0.cmp(&right.id.0));
        }
        let suffix = if frame.placeholders {
            "refine'"
        } else {
            "refine"
        };
        self.tag_refinement_goals(&goal, &frame, suffix);
        // The parent is closed only after all holes, including holes in unused
        // let values or annotations, have supplied their actual checked terms.
        proof.work.push(Work::Close(goal, term.value));
        proof.work.extend(
            frame
                .holes
                .into_iter()
                .rev()
                .map(|(_, goal)| Work::Goal(goal)),
        );
        Ok(())
    }

    /// The pin's `withCollectingNewGoalsFrom` without `allowNaturalHoles` (vendored
    /// src/Lean/Elab/Tactic/ElabTerm.lean:160-169): a natural hole the refinement made that is
    /// still unassigned in its term aborts the tactic (`logUnassignedAndAbort`), so
    /// `refine ⟨_, ?_⟩` cannot leave its witness to a later tactic. A hole made before the
    /// refinement, or one deferred to a delayed assignment, is no new natural hole.
    fn refuse_new_natural_holes(
        &mut self,
        value: &Expr,
        first_name: u64,
    ) -> Result<(), NatDefinitionElabError> {
        let value = self.instantiate(value)?;
        let source = Name::from_components(["_fln_source"]);
        let unassigned = self.txn.mvars.collect_mvars(&value);
        let fresh_natural = unassigned.iter().any(|id| {
            matches!(id.0.leaf_view(), LeafView::Num(index) if index >= first_name)
                && id.0.parent() == source
                && self.txn.mvars.get_decl(id).is_some_and(|declaration| {
                    declaration.kind == MetavarKind::Natural && declaration.delayed.is_none()
                })
        });
        if fresh_natural {
            return Err(error(TacticError::UnassignedNaturalHole));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture() -> (Context, Expr, MVarId) {
        let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
        let env = crate::seed::bootstrap_nat_environment(budget).unwrap();
        let mut context = Context::new(&env, budget);
        context.begin_refinement();
        let hole = context
            .synthetic_proof_hole(None, Some(&Expr::sort(Level::one())))
            .unwrap();
        let ExprNode::MVar { id } = hole.value.node() else {
            panic!("fixture hole is not a metavariable");
        };
        (context, hole.value.clone(), id.clone())
    }

    #[test]
    fn final_tactic_comparison_assigns_without_changing_persistent_policy() {
        let (mut context, hole, id) = fixture();
        let unrelated = context
            .synthetic_proof_hole(None, Some(&Expr::sort(Level::one())))
            .unwrap();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        assert!(
            context
                .unify_source_batch(&[(hole.clone(), nat.clone())], true)
                .is_err()
        );
        context.ensure_tactic_term_type(&hole, &nat).unwrap();
        assert_eq!(context.txn.mvars.get_assigned_expr(&id), Some(&nat));
        for declaration in context.txn.mvars.decls().values() {
            assert_eq!(declaration.kind, MetavarKind::SyntheticOpaque);
        }
        assert!(
            context
                .unify_source_batch(&[(unrelated.value, nat)], true)
                .is_err()
        );
    }

    #[test]
    fn failed_final_comparison_keeps_no_assignment_or_policy_change() {
        let (mut context, hole, _) = fixture();
        let before = context.clone();
        let impossible = Expr::app(hole, Expr::sort(Level::zero()));
        assert!(
            context
                .ensure_tactic_term_type(&impossible, &Expr::sort(Level::zero()))
                .is_err()
        );
        assert_eq!(context.txn.mvars, before.txn.mvars);
        assert_eq!(context.txn.universes, before.txn.universes);
        assert_eq!(context.txn.constraints, before.txn.constraints);
        assert_eq!(context.txn.lctx, before.txn.lctx);
        assert!(context.txn.budget.heartbeats_consumed > before.txn.budget.heartbeats_consumed);
    }

    #[test]
    fn exhaustion_during_policy_restoration_discards_the_assignment() {
        let (initial, hole, _) = fixture();
        let nat = Expr::const_(Name::from_components(["Nat"]), vec![]);
        let mut control = initial.clone();
        control.ensure_tactic_term_type(&hole, &nat).unwrap();
        let mut limited = initial.clone();
        limited.txn.budget.max_heartbeats = control.txn.budget.heartbeats_consumed - 1;
        assert!(limited.ensure_tactic_term_type(&hole, &nat).is_err());
        assert_eq!(limited.txn.mvars, initial.txn.mvars);
        assert_eq!(limited.txn.universes, initial.txn.universes);
        assert_eq!(limited.txn.constraints, initial.txn.constraints);
        assert!(limited.txn.budget.heartbeats_consumed > initial.txn.budget.heartbeats_consumed);
    }
}
