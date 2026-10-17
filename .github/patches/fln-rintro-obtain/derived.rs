//! Introduction and obtained witnesses share the checked recursive-case planner.
use super::*;
use fln_syntax::source::SourceInfo;

fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), args)
}
fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}
fn annotation(syntax: &Syntax) -> Result<Option<&Syntax>, NatDefinitionElabError> {
    match expect_null_args(syntax, "recursive introduction annotation")? {
        [] => Ok(None),
        [colon, type_] => {
            expect_atom(colon, ":", "recursive introduction annotation")?;
            Ok(Some(type_))
        }
        _ => Err(malformed()),
    }
}

enum IntroStep<'a> {
    Introduce(ProofGoal, usize),
    Emit(Work<'a>),
}

impl Context {
    pub(in crate::source::tactics) fn rintro_proof_goal<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, patterns, type_] = args else { return Err(malformed()); };
        expect_atom(keyword, "rintro", "recursive introduction")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "rintro"])?;
        let inherited = annotation(type_)?;
        let mut input = expect_null_args(patterns, "rintro patterns")?
            .iter().rev().map(|s| (s, inherited)).collect::<Vec<_>>();
        let mut arena = vec![Pattern::One(None)];
        let mut patterns = Vec::new();
        while let Some((syntax, inherited)) = input.pop() {
            self.tick()?;
            let Syntax::Node { kind: node, args, .. } = syntax else { return Err(malformed()); };
            if node == &kind(&["rintroPat", "one"]) {
                let [pattern] = args.as_slice() else { return Err(malformed()); };
                let mut pattern = self.parse_rcases_pattern(pattern, &mut arena)?;
                if let Some(type_) = inherited {
                    let next = arena.len();
                    arena.push(Pattern::Typed(pattern, type_));
                    pattern = next;
                }
                patterns.push(pattern);
            } else if node == &kind(&["rintroPat", "binder"]) {
                let [open, patterns, type_, close] = args.as_slice() else { return Err(malformed()); };
                expect_atom(open, "(", "rintro group")?;
                expect_atom(close, ")", "rintro group")?;
                let inherited = annotation(type_)?.or(inherited);
                input.extend(expect_null_args(patterns, "rintro group patterns")?.iter().rev().map(|s| (s, inherited)));
            } else {
                return Err(error(TacticError::UnsupportedTactic(node.clone())));
            }
        }
        if patterns.is_empty() { return Err(malformed()); }
        let mut pending = vec![IntroStep::Introduce(goal, 0)];
        let mut output = Vec::new();
        while let Some(step) = pending.pop() {
            self.tick()?;
            let (mut goal, index) = match step {
                IntroStep::Emit(work) => { output.push(work); continue; }
                IntroStep::Introduce(goal, index) => (goal, index),
            };
            let Some(&pattern) = patterns.get(index) else {
                output.push(Work::Goal(goal));
                continue;
            };
            self.txn.lctx = goal.lctx.clone();
            let name = self.fresh_name()?;
            self.introduce_proof_binder(&mut goal, name.clone())?;
            goal.lctx = self.txn.lctx.clone();
            let start = proof.work.len();
            self.run_rcases_patterns(proof, goal, arena.clone(), vec![Subject { name, pattern, rename: true }])?;
            for work in proof.work.split_off(start) {
                pending.push(match work {
                    Work::Goal(child) => IntroStep::Introduce(child, index + 1),
                    work @ Work::Close(..) => IntroStep::Emit(work),
                    _ => return Err(malformed()),
                });
            }
        }
        proof.work.extend(output.into_iter().rev());
        Ok(())
    }

    pub(in crate::source::tactics) fn obtain_proof_goal<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        mut goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, pattern, type_, values] = args else { return Err(malformed()); };
        expect_atom(keyword, "obtain", "obtained witness")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "obtain"])?;
        let pattern = match expect_null_args(pattern, "obtain pattern")? {
            [] => None,
            [pattern] => Some(pattern),
            _ => return Err(malformed()),
        };
        let type_syntax = annotation(type_)?;
        match expect_null_args(values, "obtain values")? {
            [assignment, values] => {
                expect_atom(assignment, ":=", "obtain assignment")?;
                let targets = separated(values, ",")?;
                if targets.len() != 1 {
                    return Err(error(TacticError::UnsupportedTactic(kind(&["obtain"]))));
                }
                let pattern = pattern.cloned().unwrap_or_else(|| Syntax::node(kind(&["rcasesPat", "ignore"]), vec![atom("_")]));
                let pattern = Syntax::node(kind(&["rcasesPatLo"]), vec![
                    if pattern.kind() == Some(&kind(&["rcasesPatMed"])) { pattern } else {
                        Syntax::node(kind(&["rcasesPatMed"]), vec![null(vec![pattern])])
                    },
                    type_.clone(),
                ]);
                let args = vec![atom("rcases"), null(vec![Syntax::node(kind(&["elimTarget"]), vec![null(vec![]), targets[0].clone()])]), null(vec![atom("with"), pattern])];
                self.rcases_proof_goal(proof, goal, &args)
            }
            [] => {
                let type_syntax = type_syntax.ok_or_else(malformed)?;
                let mut arena = vec![Pattern::One(None)];
                let pattern = match pattern {
                    Some(pattern) => self.parse_rcases_pattern(pattern, &mut arena)?,
                    None => {
                        arena.push(Pattern::One(Some(Name::from_components(["this"]))));
                        1
                    }
                };
                self.txn.lctx = goal.lctx.clone();
                let type_ = self.type_term(type_syntax)?;
                let (value, witness) = self.proof_goal(type_.clone())?;
                let name = self.fresh_name()?;
                let id = FVarId(self.fresh_name()?);
                // The witness is opaque while its continuation is elaborated.
                // Its ordinary let retains the separately checked proof, and the
                // witness goal's old context cannot see this new assumption.
                let local = LocalDecl {
                    id: id.clone(), user_name: name.clone(), type_: type_.clone(),
                    value: Some(value), binder_info: BinderInfo::Default,
                    index: self.txn.lctx.len(),
                };
                self.txn.lctx.add_param(id, name.clone(), type_, BinderInfo::Default);
                goal.introduced.push(local);
                goal.lctx = self.txn.lctx.clone();
                self.run_rcases_patterns(proof, goal, arena, vec![Subject { name, pattern, rename: true }])?;
                // LIFO: prove the witness before any branch can use it.
                proof.work.push(Work::Goal(witness));
                Ok(())
            }
            _ => Err(malformed()),
        }
    }
}
