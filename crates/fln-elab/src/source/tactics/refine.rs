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
}

impl Context {
    pub(in crate::source) fn begin_refinement(&mut self) -> usize {
        let depth = self.refinements.len();
        self.refinements.push(RefinementFrame::default());
        depth
    }

    /// [`Self::begin_refinement`] for `refine'`, whose `_`s are new goals.
    pub(in crate::source) fn begin_placeholder_refinement(&mut self) -> usize {
        let depth = self.refinements.len();
        self.refinements.push(RefinementFrame {
            holes: Vec::new(),
            placeholders: true,
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
        let existing = name.as_ref().and_then(|name| {
            self.refinements.last().and_then(|frame| {
                frame
                    .holes
                    .iter()
                    .find(|(found, _)| found.as_ref() == Some(name))
                    .map(|(_, goal)| goal.clone())
            })
        });
        let goal = if let Some(goal) = existing {
            // Reuse is intentionally scoped to an identical captured context.
            // Equal spelling in different binder scopes cannot capture a local.
            if goal.lctx != self.txn.lctx || !self.proof_types_match(&goal.target, &type_)? {
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
                target: type_.clone(),
                lctx: self.txn.lctx.clone(),
                introduced: locals,
            };
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
        let term = self.term(&syntax, Some(goal.target.clone()))?;
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
        let term = self.term(&syntax, Some(goal.target.clone()))?;
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
            let Work::Goal(hole) = proof.work.remove(position) else {
                return Err(error(TacticError::MalformedScript));
            };
            self.goal_tags.remove(&hole.id);
            runs.push(Work::Script(hole, self.proof_instructions(body)?));
        }
        for (name, tag) in placeholders {
            let found = proof.work.iter().find_map(|work| match work {
                Work::Goal(hole) if self.goal_tags.get(&hole.id) == Some(&name) => {
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
        let term = self.term(&syntax, Some(goal.target.clone()))?;
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
        let frame = self.refinements.pop().expect("checked refinement depth");
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
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
}
