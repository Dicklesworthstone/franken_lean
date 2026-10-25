//! Scoped goal control over the existing proof worklist.
//!
//! A frame suspends sibling goals and continuations, not their metavariable
//! assignments. All-goals maps over the original frontier, never over goals
//! created by the mapped tactic. Deferred close actions retain dependent terms.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    Solve,
    Focus,
    All,
}
impl Mode {
    pub(super) fn keyword(self) -> &'static str {
        match self {
            Self::Solve => "·",
            Self::Focus => "focus",
            Self::All => "all_goals",
        }
    }
}
/// The pin's `syntax (name := cdot) cdotTk tacticSeqIndentGt : tactic` (`Init/NotationExtra.lean`).
pub(super) fn is_cdot(kind: &Name) -> bool {
    kind == &Name::from_components(["Lean", "cdot"])
}
pub(super) fn mode(kind: &Name) -> Option<Mode> {
    if is_cdot(kind) {
        Some(Mode::Solve)
    } else if kind == &parser_kind(&["Tactic", "focus"]) {
        Some(Mode::Focus)
    } else if kind == &parser_kind(&["Tactic", "allGoals"]) {
        Some(Mode::All)
    } else {
        None
    }
}
pub(super) fn is_scope(kind: &Name) -> bool {
    kind == &parser_kind(&["Tactic", "set_option"])
        || kind == &parser_kind(&["Tactic", "classical"])
        || transparency_scope(kind).is_some()
}

/// `syntax (name := withReducible) "with_reducible " tacticSeq : tactic` and its siblings
/// (vendored src/Init/Tactics.lean:358-376): the keyword, its kind's last component, and the
/// transparency its body runs at (`evalWithReducible` &c., vendored
/// src/Lean/Elab/Tactic/BuiltinTactic.lean). The body runs on every goal, unfocused.
fn transparency_scope(
    kind: &Name,
) -> Option<(&'static str, &'static str, UnificationTransparency)> {
    [
        (
            "with_reducible",
            "withReducible",
            UnificationTransparency::Abbreviations,
        ),
        (
            "with_reducible_and_instances",
            "withReducibleAndInstances",
            UnificationTransparency::Instances,
        ),
        (
            "with_unfolding_none",
            "withUnfoldingNone",
            UnificationTransparency::None,
        ),
    ]
    .into_iter()
    .find(|(_, component, _)| kind == &parser_kind(&["Tactic", component]))
}

/// A name's components, root first, each as a one-component name.
fn components(name: &Name) -> Vec<Name> {
    let mut parts = Vec::new();
    let mut current = name.clone();
    while !current.is_anonymous() {
        parts.push(match current.leaf_view() {
            LeafView::Str(s) => Name::str(Name::anonymous(), s),
            LeafView::Num(n) => Name::num(Name::anonymous(), n),
            LeafView::Anonymous => break,
        });
        current = current.parent();
    }
    parts.reverse();
    parts
}

#[derive(Clone)]
pub(super) struct Frame<'a> {
    mode: Mode,
    body: Vec<&'a Syntax>,
    instructions: Vec<&'a Syntax>,
    cursor: usize,
    waiting: Vec<Work<'a>>,
    // Execution order, reversed exactly once when restoring the outer worklist.
    deferred: Vec<Work<'a>>,
    // A sequencing frame first isolates its left operand, then maps this
    // continuation only over the resulting frontier, not over old siblings.
    after: Option<Vec<&'a Syntax>>,
    // A conversion-mode frame: what its sequence's end does with the goals it leaves.
    conv: Option<Box<super::conv::Finish>>,
    // An all-goals frame over only the first goals of its frontier: how many more it runs on.
    limit: Option<usize>,
    // A `case'` frame: the tag of the goal its current run started on, which a run leaving
    // exactly one goal gives that goal (`evalCase'`'s `g'.setTag mvarTag`).
    retag: Option<Option<Name>>,
}
impl Context {
    /// The index in `goals` of the goal `case tag` would select among them (`findTag?`): the
    /// first whose tag, macro scopes erased, is `tag`, else ends with it, else starts with it;
    /// `_` is the first goal.
    pub(super) fn case_tag_position(
        &mut self,
        goals: &[ProofGoal],
        tag: &Syntax,
    ) -> Result<usize, NatDefinitionElabError> {
        let [tag] = expect_node(
            tag,
            &Name::from_components(["Lean", "binderIdent"]),
            1,
            "case tag",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let tag = match tag {
            Syntax::Ident { val, .. } => val.erase_macro_scopes(),
            hole if hole.kind() == Some(&parser_kind(&["Term", "hole"])) => {
                return if goals.is_empty() {
                    Err(error(TacticError::NoGoals))
                } else {
                    Ok(0)
                };
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let tags: Vec<Vec<Name>> = goals
            .iter()
            .map(|goal| {
                components(
                    &self
                        .goal_tags
                        .get(&goal.id)
                        .map(Name::erase_macro_scopes)
                        .unwrap_or_else(Name::anonymous),
                )
            })
            .collect();
        let wanted = components(&tag);
        tags.iter()
            .position(|tags| *tags == wanted)
            .or_else(|| tags.iter().position(|tags| tags.ends_with(&wanted)))
            .or_else(|| tags.iter().position(|tags| tags.starts_with(&wanted)))
            .ok_or_else(|| error(TacticError::CaseTagNotFound(tag)))
    }

    /// The goal `case tag` selects (`getCaseGoals` and `findTag?`, vendored
    /// src/Lean/Elab/Tactic/BuiltinTactic.lean): among the visible goals in order, the first
    /// whose tag, macro scopes erased, is `tag`, else ends with it, else starts with it. `_`
    /// selects the main goal. The other goals keep their order.
    pub(super) fn case_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        tag: &Syntax,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let [tag] = expect_node(
            tag,
            &Name::from_components(["Lean", "binderIdent"]),
            1,
            "case tag",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let tag = match tag {
            Syntax::Ident { val, .. } => val.erase_macro_scopes(),
            hole if hole.kind() == Some(&parser_kind(&["Term", "hole"])) => return Ok(goal),
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let tag_of = |this: &Self, id: &MVarId| {
            components(
                &this
                    .goal_tags
                    .get(id)
                    .map(Name::erase_macro_scopes)
                    .unwrap_or_else(Name::anonymous),
            )
        };
        // The main goal, then the frontier down to the first barrier; `None` is the main goal.
        let mut visible = vec![(None, tag_of(self, &goal.id))];
        for (index, work) in proof.work.iter().enumerate().rev() {
            self.tick()?;
            match work {
                Work::EndScript(..)
                | Work::EndControl(_)
                | Work::EndAttempt(_)
                | Work::EndOptions(_) => break,
                Work::Goal(other) if !self.txn.mvars.is_assigned(&other.id) => {
                    visible.push((Some(index), tag_of(self, &other.id)));
                }
                _ => {}
            }
        }
        let wanted = components(&tag);
        let found = visible
            .iter()
            .position(|(_, tags)| *tags == wanted)
            .or_else(|| visible.iter().position(|(_, tags)| tags.ends_with(&wanted)))
            .or_else(|| {
                visible
                    .iter()
                    .position(|(_, tags)| tags.starts_with(&wanted))
            })
            .ok_or_else(|| error(TacticError::CaseTagNotFound(tag)))?;
        let Some(index) = visible[found].0 else {
            return Ok(goal);
        };
        let Work::Goal(selected) = proof.work.remove(index) else {
            return Err(error(TacticError::MalformedScript));
        };
        // The main goal stays first among the goals that remain.
        proof.work.push(Work::Goal(goal));
        Ok(selected)
    }

    /// Lexical scopes wrap the whole visible frontier, not just its main goal.
    /// In particular an enclosed all_goals still sees the caller's siblings,
    /// and an unfinished body returns its goals to the outer sequence.
    pub(super) fn start_tactic_scope<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        kind: &Name,
        args: &'a [Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let instance_scopes = self.source_scope.instance_scopes.clone();
        let transparency = self.tactic_transparency;
        let (body, options) = if let Some((word, component, ambient)) = transparency_scope(kind) {
            let [keyword, sequence] = args else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(keyword, word, "transparency tactic")?;
            self.require_declared_tactic(&["Lean", "Parser", "Tactic", component])?;
            let body = self.proof_instructions(sequence)?;
            // The pin's `withTransparency` sets the mode, so an inner scope replaces an outer one.
            self.tactic_transparency = Some(ambient);
            (body, self.txn.options.clone())
        } else if kind == &parser_kind(&["Tactic", "classical"]) {
            let [keyword, sequence] = args else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(keyword, "classical", "classical tactic")?;
            self.require_declared_tactic(&["Lean", "Parser", "Tactic", "classical"])?;
            let body = self.proof_instructions(sequence)?;
            let provider = Name::from_components(["Classical", "propDecidable"]);
            if !self.txn.env.contains(&provider) {
                // An ordinary elaboration failure, not corrupted registry data:
                // `first` may try its next alternative when imports omit this.
                return Err(failure(SourceInferenceError::UnknownConstant(provider)));
            }
            // Lean/Elab/Tactic/Classical.lean adds this already admitted
            // declaration as a LOCAL instance at priority 10. Opening the
            // namespace would activate unrelated instances at other priorities.
            // No persistent registration or new proof authority is installed.
            self.tick()?;
            self.source_scope
                .instance_scopes
                .register_local(&self.txn.env, &provider, 10)
                .map_err(instances::registry_error)?;
            (body, self.txn.options.clone())
        } else {
            let (syntax, options) = self.enter_source_options(args)?;
            (self.proof_instructions(syntax)?, options)
        };
        let boundary = proof
            .work
            .iter()
            .rposition(|work| {
                matches!(
                    work,
                    Work::EndScript(..)
                        | Work::EndControl(_)
                        | Work::EndAttempt(_)
                        | Work::EndOptions(_)
                )
            })
            .map_or(0, |position| position + 1);
        let scope = OptionScope {
            options,
            instance_scopes,
            transparency,
            instructions: std::mem::replace(&mut proof.instructions, body),
            cursor: proof.cursor + 1,
        };
        proof.cursor = 0;
        proof
            .work
            .insert(boundary, Work::EndOptions(Box::new(scope)));
        Ok(())
    }

    pub(super) fn finish_tactic_options<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        scope: OptionScope<'a>,
    ) -> Result<(), NatDefinitionElabError> {
        if proof.cursor != proof.instructions.len() {
            return Err(error(TacticError::NoGoals));
        }
        self.txn.options = scope.options;
        self.source_scope.instance_scopes = scope.instance_scopes;
        self.tactic_transparency = scope.transparency;
        proof.instructions = scope.instructions;
        proof.cursor = scope.cursor;
        Ok(())
    }

    pub(super) fn suspend_tactic_options(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: &ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        for position in (0..proof.work.len()).rev() {
            self.tick()?;
            match &proof.work[position] {
                Work::EndScript(..) | Work::EndControl(_) | Work::EndAttempt(_) => {
                    return Ok(false);
                }
                Work::EndOptions(_) => {
                    let Work::EndOptions(scope) = proof.work.remove(position) else {
                        unreachable!("option boundary");
                    };
                    self.finish_tactic_options(proof, *scope)?;
                    proof.work.push(Work::Goal(goal.clone()));
                    return Ok(true);
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub(super) fn start_goal_control<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        syntax: &'a Syntax,
        mode: Mode,
    ) -> Result<(), NatDefinitionElabError> {
        let body = self.proof_instructions(syntax)?;
        self.start_goal_control_body(proof, goal, body, mode, None)
    }

    pub(super) fn start_goal_sequence<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        left: &'a Syntax,
        right: &'a Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        // The pin's operands are single tactics (or a parenthesized sequence); a sequence is
        // what this elaborator's own syntax may still hold.
        let operand = |this: &mut Self, syntax: &'a Syntax| {
            if syntax.kind() == Some(&parser_kind(&["Tactic", "tacticSeq"])) {
                return this.proof_instructions(syntax);
            }
            if let Syntax::Node { kind, args, .. } = syntax
                && kind == &parser_kind(&["Tactic", "paren"])
            {
                let [open, body, close] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(open, "(", "tactic sequence opening")?;
                expect_atom(close, ")", "tactic sequence closing")?;
                return this.proof_instructions(body);
            }
            Ok(vec![syntax])
        };
        let left = operand(self, left)?;
        let right = operand(self, right)?;
        if right.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        self.start_goal_control_body(proof, goal, left, Mode::Focus, Some(right))
    }

    fn start_goal_control_body<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        body: Vec<&'a Syntax>,
        mode: Mode,
        after: Option<Vec<&'a Syntax>>,
    ) -> Result<(), NatDefinitionElabError> {
        if body.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let frame = Frame {
            mode,
            body: body.clone(),
            instructions: std::mem::replace(&mut proof.instructions, body),
            cursor: std::mem::replace(&mut proof.cursor, 0),
            waiting: std::mem::take(&mut proof.work),
            deferred: Vec::new(),
            after,
            conv: None,
            limit: None,
            retag: None,
        };
        let index = proof.controls.len();
        proof.controls.push(frame);
        proof.work.push(Work::EndControl(index));
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// `syntax`'s sequence run, in turn, on the main goal and the `count - 1` visible goals
    /// after it, each with every other goal suspended, as `all_goals` runs its body; the goals
    /// each run leaves come first, in order, then the goals after those `count`.
    pub(super) fn start_limited_all_goals<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        syntax: &'a Syntax,
        count: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let body = self.proof_instructions(syntax)?;
        let tag = self.goal_tags.get(&goal.id).cloned();
        self.start_goal_control_body(proof, goal, body, Mode::All, None)?;
        let frame = proof
            .controls
            .last_mut()
            .ok_or_else(|| error(TacticError::MalformedScript))?;
        frame.limit = Some(count.saturating_sub(1));
        frame.retag = Some(tag);
        Ok(())
    }

    /// `case'`'s run of `syntax` on `goal` alone, every other goal suspended as `focus` does:
    /// a run leaving exactly one goal gives it `goal`'s tag.
    pub(super) fn start_case_prime_focus<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        syntax: &'a Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let tag = self.goal_tags.get(&goal.id).cloned();
        self.start_goal_control(proof, goal, syntax, Mode::Focus)?;
        let frame = proof
            .controls
            .last_mut()
            .ok_or_else(|| error(TacticError::MalformedScript))?;
        frame.retag = Some(tag);
        Ok(())
    }

    /// Put the visible goals (the main goal `main`, then each unassigned goal from the top of
    /// the worklist down to the first barrier) in the order `order` gives them, the first as
    /// the returned main goal. Each goal takes the slot the goal at its new position held, so
    /// every other worklist entry keeps its place. A placement this engine cannot run is
    /// refused as `kind`: a goal run after the close of a goal whose term reads it, a goal
    /// moved across the close of a goal its target mentions, or a visible entry other than a
    /// goal or a close.
    pub(super) fn reorder_visible_goals(
        &mut self,
        proof: &mut ProofState<'_>,
        main: ProofGoal,
        kind: &Name,
        order: impl FnOnce(&mut Self, Vec<ProofGoal>) -> Result<Vec<ProofGoal>, NatDefinitionElabError>,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let refused = || error(TacticError::UnsupportedTactic(kind.clone()));
        let boundary = proof
            .work
            .iter()
            .rposition(|work| {
                matches!(
                    work,
                    Work::EndScript(..)
                        | Work::EndControl(_)
                        | Work::EndAttempt(_)
                        | Work::EndOptions(_)
                )
            })
            .map_or(0, |position| position + 1);
        // Slot positions, the main goal's above every entry; goals in visible order.
        let top = proof.work.len();
        let mut slots = vec![top];
        let mut goals = vec![main];
        let mut closes = Vec::new();
        for index in (boundary..proof.work.len()).rev() {
            self.tick()?;
            match &proof.work[index] {
                Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id) => {
                    slots.push(index);
                    goals.push(goal.clone());
                }
                Work::Goal(_) => {}
                Work::Close(goal, value) => {
                    let value = self.instantiate(value)?;
                    closes.push((index, goal.id.clone(), value));
                }
                _ => return Err(refused()),
            }
        }
        let original: std::collections::HashMap<MVarId, usize> = goals
            .iter()
            .zip(&slots)
            .map(|(goal, &slot)| (goal.id.clone(), slot))
            .collect();
        let ordered = order(self, goals)?;
        if ordered.len() != slots.len() {
            return Err(error(TacticError::MalformedScript));
        }
        for (goal, &slot) in ordered.iter().zip(&slots) {
            let target = self.instantiate(&goal.target)?;
            let mentioned = self.txn.mvars.collect_mvars(&target);
            let before = original
                .get(&goal.id)
                .copied()
                .ok_or_else(|| error(TacticError::MalformedScript))?;
            for (index, closed, value) in &closes {
                self.tick()?;
                let reads = self.txn.mvars.collect_mvars(value).contains(&goal.id);
                if reads && slot < *index {
                    return Err(refused());
                }
                if mentioned.contains(closed) && ((before > *index) != (slot > *index)) {
                    return Err(refused());
                }
            }
        }
        let mut ordered = ordered.into_iter();
        let main = ordered
            .next()
            .ok_or_else(|| error(TacticError::MalformedScript))?;
        for (goal, &slot) in ordered.zip(&slots[1..]) {
            proof.work[slot] = Work::Goal(goal);
        }
        Ok(main)
    }

    /// A conversion-mode frame over `goals` (the main one first), whose sequence `body` runs
    /// with every other goal suspended, as `focus` runs it. When the sequence ends, `finish`
    /// receives the goals it leaves ([`Self::finish_conv`]).
    pub(super) fn start_conv_frame<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goals: Vec<Work<'a>>,
        body: Vec<&'a Syntax>,
        finish: super::conv::Finish,
    ) -> Result<(), NatDefinitionElabError> {
        let frame = Frame {
            mode: Mode::Focus,
            body: body.clone(),
            instructions: std::mem::replace(&mut proof.instructions, body),
            cursor: std::mem::replace(&mut proof.cursor, 0),
            waiting: std::mem::take(&mut proof.work),
            deferred: Vec::new(),
            after: None,
            conv: Some(Box::new(finish)),
            limit: None,
            retag: None,
        };
        let index = proof.controls.len();
        proof.controls.push(frame);
        proof.work.push(Work::EndControl(index));
        proof.work.extend(goals.into_iter().rev());
        Ok(())
    }

    /// A strict constructor alternative is an intervening barrier. A focus
    /// outside it cannot turn that alternative's unfinished proof into success.
    pub(super) fn suspend_goal_control(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: &ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut boundary = None;
        for work in proof.work.iter().rev() {
            self.tick()?;
            match work {
                Work::EndScript(..) | Work::EndAttempt(_) | Work::EndOptions(_) => {
                    return Ok(false);
                }
                Work::EndControl(index) => {
                    boundary = Some(*index);
                    break;
                }
                _ => {}
            }
        }
        let Some(index) = boundary else {
            return Ok(false);
        };
        let mut pending = std::mem::take(&mut proof.work);
        if !matches!(pending.first(), Some(Work::EndControl(found)) if *found == index) {
            return Err(error(TacticError::MalformedScript));
        }
        pending.remove(0);
        pending.push(Work::Goal(goal.clone()));
        self.finish_goal_control(proof, index, pending)?;
        Ok(true)
    }

    pub(super) fn finish_goal_control<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        index: usize,
        pending: Vec<Work<'a>>,
    ) -> Result<(), NatDefinitionElabError> {
        if index + 1 != proof.controls.len() || !proof.work.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        self.skip_empty_goal_controls(proof)?;
        if proof.cursor != proof.instructions.len() {
            return Err(error(TacticError::NoGoals));
        }
        let mut frame = proof.controls.pop().expect("validated control depth");
        if let Some(tag) = frame.retag.clone() {
            let mut open = pending.iter().filter_map(|work| match work {
                Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id) => Some(goal.id.clone()),
                _ => None,
            });
            if let (Some(only), None) = (open.next(), open.next()) {
                match tag {
                    Some(tag) => {
                        self.goal_tags.insert(only, tag);
                    }
                    None => {
                        self.goal_tags.remove(&only);
                    }
                }
            }
        }
        if let Some(finish) = frame.conv.take() {
            proof.instructions = frame.instructions;
            proof.cursor = frame.cursor;
            proof.work = frame.waiting;
            return self.finish_conv(proof, *finish, pending);
        }
        if let Some(body) = frame.after.take()
            && !pending.is_empty()
        {
            let mut pending = pending;
            let Some(Work::Goal(goal)) = pending.pop() else {
                return Err(error(TacticError::MalformedScript));
            };
            // Keep the original scope as an outer barrier. The all-goals frame
            // sees exactly the newly produced frontier and its close actions.
            proof.instructions = Vec::new();
            proof.cursor = 0;
            proof.controls.push(frame);
            proof.work.push(Work::EndControl(index));
            proof.work.extend(pending);
            return self.start_goal_control_body(proof, goal, body, Mode::All, None);
        }
        if frame.mode == Mode::Solve && !pending.is_empty() {
            let mut count = 0;
            for work in &pending {
                self.tick()?;
                if let Work::Goal(goal) = work
                    && !self.txn.mvars.is_assigned(&goal.id)
                {
                    count += 1;
                }
            }
            return Err(error(TacticError::UnsolvedGoals { count }));
        }
        for work in pending.into_iter().rev() {
            self.tick()?;
            frame.deferred.push(work);
        }
        if frame.mode == Mode::All {
            loop {
                self.tick()?;
                match frame.waiting.last() {
                    Some(Work::Close(..)) => {
                        frame
                            .deferred
                            .push(frame.waiting.pop().expect("last exists"));
                    }
                    Some(Work::Goal(_)) => {
                        if frame.limit == Some(0) {
                            break;
                        }
                        let Some(Work::Goal(goal)) = frame.waiting.pop() else {
                            unreachable!()
                        };
                        if self.txn.mvars.is_assigned(&goal.id) {
                            continue;
                        }
                        if let Some(limit) = &mut frame.limit {
                            *limit -= 1;
                        }
                        if frame.retag.is_some() {
                            frame.retag = Some(self.goal_tags.get(&goal.id).cloned());
                        }
                        proof.instructions = frame.body.clone();
                        proof.cursor = 0;
                        proof.controls.push(frame);
                        proof.work.push(Work::EndControl(index));
                        proof.work.push(Work::Goal(goal));
                        return Ok(());
                    }
                    // Do not cross a scoped branch or an enclosing controller.
                    _ => break,
                }
            }
        }
        proof.instructions = frame.instructions;
        proof.cursor = frame.cursor;
        proof.work = frame.waiting;
        proof.work.extend(frame.deferred.into_iter().rev());
        Ok(())
    }

    /// Like mapping over an empty list, all_goals on no goals succeeds without
    /// executing its body. The parser still validates every token of that body.
    pub(super) fn skip_empty_goal_controls(
        &mut self,
        proof: &mut ProofState<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        while let Some(Syntax::Node { kind, args, .. }) = proof.instructions.get(proof.cursor) {
            self.tick()?;
            if mode(kind) != Some(Mode::All) {
                break;
            }
            let [keyword, sequence] = args.as_slice() else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(keyword, "all_goals", "all-goals keyword")?;
            self.proof_instructions(sequence)?;
            proof.cursor += 1;
        }
        Ok(())
    }
}
