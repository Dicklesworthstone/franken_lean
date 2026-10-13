    /// Name actual constructor fields so dependent specialization preserves the
    /// remaining matrix columns. Names are private binders, never evidence.
    fn empty_field_names(
        &mut self,
        family: &InductiveVal,
    ) -> Result<HashMap<Name, Vec<Name>>, NatDefinitionElabError> {
        let mut fields = HashMap::new();
        for name in &family.ctors {
            self.tick()?;
            let Some(ConstantInfo::Ctor(constructor)) = self.txn.env.find(name) else {
                return Err(error(TacticError::UnsupportedEliminator));
            };
            let count = constructor.num_fields;
            let mut names = Vec::new();
            for _ in 0..count {
                self.tick()?;
                names.push(self.fresh_name()?);
            }
            fields.insert(name.clone(), names);
        }
        Ok(fields)
    }

    fn solve_empty_matrix<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        columns: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        // The pin's ex-falso transition eliminates proof-valued families into
        // False first. Eliminating Or or Exists directly into data is illegal,
        // even if all of their branches are subsequently proved impossible.
        self.txn.lctx = goal.lctx.clone();
        let false_type = Expr::const_(Name::from_components(["False"]), Vec::new());
        let (absurd, child) = self.proof_goal(false_type.clone())?;
        let value = self
            .empty_evidence(
                &Typed {
                    value: absurd,
                    type_: false_type,
                },
                &goal.target,
            )?
            .ok_or_else(|| error(TacticError::UnsupportedEliminator))?;
        let mut pending = vec![
            EmptyTask::Close(goal, value),
            EmptyTask::Split(child, columns.iter().cloned().collect()),
        ];
        while let Some(task) = pending.pop() {
            self.tick()?;
            let (goal, mut remaining) = match task {
                EmptyTask::Close(goal, value) => {
                    self.close_proof_goal(goal, value)?;
                    continue;
                }
                EmptyTask::Split(goal, remaining) => (goal, remaining),
            };
            self.txn.lctx = goal.lctx.clone();
            let Some(column) = remaining.pop_front() else {
                return Err(error(TacticError::EliminationCoverage));
            };
            let mut local = goal
                .lctx
                .find_by_user_name(&column)
                .cloned()
                .ok_or_else(|| error(TacticError::EliminationLocal))?;
            // Follow exact aliases only. Every written value stays in the
            // outer checked let telescope, including unused trailing inputs.
            let mut seen = HashSet::new();
            while let Some(value) = &local.value {
                self.tick()?;
                let ExprNode::FVar { id } = value.node() else {
                    break;
                };
                if !seen.insert(local.id.clone()) {
                    return Err(error(TacticError::EliminationLocal));
                }
                let Some(original) = goal.lctx.find(id) else {
                    break;
                };
                local = original.clone();
            }
            let type_ = self.whnf(&local.type_)?;
            let mut head = &type_;
            while let ExprNode::App { f, .. } = head.node() {
                self.tick()?;
                head = f;
            }
            let family = match head.node() {
                ExprNode::Const { name, .. } => match self.txn.env.find(name) {
                    Some(ConstantInfo::Induct(family)) => Some(family.clone()),
                    _ => None,
                },
                _ => None,
            };
            let Some(family) = family else {
                pending.push(EmptyTask::Split(goal, remaining));
                continue;
            };
            let fields = self.empty_field_names(&family)?;
            let mut ordered_fields = Vec::new();
            for constructor in &family.ctors {
                for field in &fields[constructor] {
                    self.tick()?;
                    ordered_fields.push(field.clone());
                }
            }
            // Match.processConstructor first tries cases, so impossible
            // indices can close even a recursive family. If live cases remain,
            // the pin rolls it back rather than descending forever into Nat,
            // lists, or an inductive with only recursive constructors.
            let saved = family.is_rec.then(|| self.clone());
            let original = family.is_rec.then(|| goal.clone());
            let work_start = proof.work.len();
            self.eliminate_proof_goal_with_indices(
                proof,
                goal,
                &eliminate::EliminationSyntax::EmptyMatrix(fields),
                false,
                Some(&local.id),
                None,
            )?;
            if let Some(saved) = saved
                && proof.work[work_start..]
                    .iter()
                    .any(|work| matches!(work, Work::Goal(_)))
            {
                let consumed = self.txn.budget.heartbeats_consumed;
                *self = saved;
                self.txn.budget.heartbeats_consumed = consumed;
                proof.work.truncate(work_start);
                pending.push(EmptyTask::Split(
                    original.expect("recursive case snapshot"),
                    remaining,
                ));
                continue;
            }
            for work in proof.work.split_off(work_start) {
                self.tick()?;
                pending.push(match work {
                    Work::Goal(child) => {
                        let mut columns = remaining.clone();
                        // Other constructors' names do not occur in this
                        // branch. Solved fields have become let aliases; the
                        // pin substitutes and drops those non-variable columns.
                        for name in ordered_fields.iter().rev() {
                            self.tick()?;
                            if child
                                .lctx
                                .find_by_user_name(name)
                                .is_some_and(|local| local.value.is_none())
                            {
                                columns.push_front(name.clone());
                            }
                        }
                        EmptyTask::Split(child, columns)
                    }
                    Work::Close(parent, value) => EmptyTask::Close(parent, value),
                    _ => return Err(failure(SourceInferenceError::Scope)),
                });
            }
        }
        Ok(())
    }
}
