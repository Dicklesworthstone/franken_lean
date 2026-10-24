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
}
impl Context {
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
        let (body, options) = if kind == &parser_kind(&["Tactic", "classical"]) {
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
        };
        let index = proof.controls.len();
        proof.controls.push(frame);
        proof.work.push(Work::EndControl(index));
        proof.work.push(Work::Goal(goal));
        Ok(())
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
                        let Some(Work::Goal(goal)) = frame.waiting.pop() else {
                            unreachable!()
                        };
                        if self.txn.mvars.is_assigned(&goal.id) {
                            continue;
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
