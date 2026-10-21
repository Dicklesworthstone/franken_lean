//! Shared introductions for ordinary binders and checked term patterns.
//! Tuple patterns reuse the lambda/match compiler and scoped refinement holes;
//! annotations are elaborated before a new name can shadow their context.
use super::*;
use fln_syntax::source::SourceInfo;

fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}
fn null(items: Vec<Syntax>) -> Syntax {
    Syntax::node(Name::from_components(["null"]), items)
}
fn simple(syntax: &Syntax) -> Option<Option<Name>> {
    match syntax {
        Syntax::Ident { val, .. } => Some(Some(val.clone())),
        Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Term", "hole"])
                && matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "_") =>
        {
            Some(None)
        }
        _ => None,
    }
}

pub(super) fn frame(goal: &ProofGoal) -> ProofState<'static> {
    ProofState {
        extent: None,
        saved: goal.lctx.clone(),
        target: goal.target.clone(),
        root: Expr::mvar(goal.id.clone()),
        instructions: Vec::new(),
        cursor: 0,
        work: Vec::new(),
        controls: Vec::new(),
    }
}

impl Context {
    pub(super) fn intro_proof_patterns(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        patterns: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let snapshot = self.clone();
        let result = self.intro_pattern_frontier(goal, patterns);
        match result {
            Ok(work) => {
                proof.work.extend(work);
                Ok(())
            }
            Err(problem) => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = snapshot;
                self.txn.budget.heartbeats_consumed = spent;
                Err(problem)
            }
        }
    }

    /// `intros` (`evalIntros`, vendored src/Lean/Elab/Tactic/BuiltinTactic.lean). With no
    /// names it introduces every binder `getIntrosSize` counts — the leading `∀` and `let`
    /// binders, through metadata, without unfolding — each under an inaccessible name;
    /// otherwise one binder per name (`introN`), a `_` leaving that one inaccessible.
    pub(super) fn intros_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        names: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "intros"])?;
        self.txn.lctx = goal.lctx.clone();
        let count = if names.is_empty() {
            let mut target = self.instantiate(&goal.target)?;
            let mut count = 0usize;
            loop {
                self.tick()?;
                target = match target.node() {
                    ExprNode::ForallE { body, .. } | ExprNode::LetE { body, .. } => {
                        count += 1;
                        body.clone()
                    }
                    ExprNode::MData { expr, .. } => expr.clone(),
                    _ => break,
                };
            }
            count
        } else {
            names.len()
        };
        for index in 0..count {
            self.tick()?;
            let name = match names.get(index).map(simple) {
                None | Some(Some(None)) => self.fresh_name()?,
                Some(Some(Some(name))) => name,
                Some(None) => return Err(error(TacticError::MalformedScript)),
            };
            self.introduce_proof_binder(&mut goal, name)?;
        }
        goal.lctx = self.txn.lctx.clone();
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    fn intro_pattern_frontier(
        &mut self,
        goal: ProofGoal,
        patterns: &[Syntax],
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        let mut pending = vec![(Work::Goal(goal), 0)];
        let mut result = Vec::new();
        while let Some((work, index)) = pending.pop() {
            self.tick()?;
            match work {
                Work::Goal(goal) if index < patterns.len().max(1) => {
                    for work in self.introduce_proof_pattern(goal, patterns.get(index))? {
                        pending.push((work, index + 1));
                    }
                }
                work @ (Work::Goal(_) | Work::Close(..)) => result.push(work),
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
        result.reverse();
        Ok(result)
    }

    pub(super) fn introduce_proof_pattern(
        &mut self,
        mut goal: ProofGoal,
        pattern: Option<&Syntax>,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        self.tick()?;
        self.txn.lctx = goal.lctx.clone();
        let mut annotation = None;
        let name = match pattern {
            None => Some(None),
            Some(syntax) if syntax.kind() == Some(&parser_kind(&["Term", "typeAscription"])) => {
                let [open, inner, colon, type_, close] = expect_node(
                    syntax,
                    &parser_kind(&["Term", "typeAscription"]),
                    5,
                    "typed introduction",
                )?
                else {
                    return Err(error(TacticError::MalformedScript));
                };
                let paren = Syntax::node(
                    parser_kind(&["Term", "paren"]),
                    vec![open.clone(), inner.clone(), close.clone()],
                );
                parenthesized_inner(&paren)?;
                expect_atom(colon, ":", "introduction annotation")?;
                let name = simple(inner).ok_or_else(|| error(TacticError::MalformedScript))?;
                annotation = match expect_null_args(type_, "introduction annotation")? {
                    [] => None,
                    [syntax] => Some(self.type_term(syntax)?),
                    _ => return Err(error(TacticError::MalformedScript)),
                };
                Some(name)
            }
            Some(syntax) => simple(syntax),
        };
        if let Some(name) = name {
            let name = match name {
                Some(name) => name,
                None => self.fresh_name()?,
            };
            self.introduce_proof_binder(&mut goal, name)?;
            goal.lctx = self.txn.lctx.clone();
            if let Some(annotation) = annotation {
                let local = goal
                    .introduced
                    .last()
                    .cloned()
                    .ok_or_else(|| error(TacticError::MalformedScript))?;
                let mut budget = UnificationBudget::new(self.kernel);
                budget.transparency = UnificationTransparency::Default;
                if !self.proof_types_match_with_budget(&local.type_, &annotation, budget)? {
                    return Err(error(TacticError::ApplyMismatch));
                }
                self.resolve_instances_with_defaults()?;
                self.flush(false)?;
                let annotation = self.instantiate(&annotation)?;
                self.require_resolved(std::slice::from_ref(&annotation))?;
                let mut context = LocalContext::new();
                for old in goal.lctx.decls() {
                    self.tick()?;
                    let mut updated = old.clone();
                    if updated.id == local.id {
                        updated.type_ = annotation.clone();
                    }
                    eliminate::add_local(&mut context, &updated);
                }
                self.txn.lctx = context.clone();
                goal.lctx = context;
                goal.introduced.last_mut().expect("introduced binder").type_ = annotation;
            }
            return Ok(vec![Work::Goal(goal)]);
        }
        let pattern = pattern.expect("a nontrivial introduction has a pattern");
        self.validate_intro_pattern(pattern)?;
        let lambda = Syntax::node(
            parser_kind(&["Term", "fun"]),
            vec![
                atom("fun"),
                Syntax::node(
                    parser_kind(&["Term", "basicFun"]),
                    vec![
                        null(vec![pattern.clone()]),
                        null(Vec::new()),
                        atom("=>"),
                        Syntax::node(
                            parser_kind(&["Term", "syntheticHole"]),
                            vec![atom("?"), atom("_")],
                        ),
                    ],
                ),
            ],
        );
        let depth = self.begin_refinement();
        let term = self.term(&lambda, Some(goal.target.clone()))?;
        let mut proof = frame(&goal);
        self.finish_refinement(&mut proof, goal, term, depth)?;
        Ok(proof.work)
    }

    fn validate_intro_pattern(&mut self, syntax: &Syntax) -> Result<(), NatDefinitionElabError> {
        let mut pending = vec![syntax];
        while let Some(syntax) = pending.pop() {
            self.tick()?;
            if simple(syntax).is_some() {
                continue;
            }
            let Syntax::Node { kind, args, .. } = syntax else {
                return Err(error(TacticError::MalformedScript));
            };
            if kind == &parser_kind(&["Term", "app"])
                && matches!(args.as_slice(), [Syntax::Ident { val, .. }, _]
                    if *val == Name::from_components(["_root_", "Prod", "mk"]))
            {
                // The inside-out source pass has already expanded tuple
                // syntax to the pin's definition-site-qualified constructor.
                let fields = expect_null_args(&args[1], "expanded tuple introduction")?;
                if fields.len() != 2 {
                    return Err(error(TacticError::MalformedScript));
                }
                pending.extend(fields.iter().rev());
            } else if kind == &parser_kind(&["Term", "paren"]) {
                let inner = parenthesized_inner(syntax)?
                    .ok_or_else(|| error(TacticError::MalformedScript))?;
                pending.push(inner);
            } else if kind == &parser_kind(&["Term", "tuple"]) && args.len() == 3 {
                let parts = expect_null_args(&args[1], "tuple introduction")?;
                let [first, comma, rest] = parts else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(comma, ",", "tuple introduction separator")?;
                pending.push(first);
                let rest = expect_null_args(rest, "tuple introduction fields")?;
                if rest.is_empty() {
                    return Err(error(TacticError::MalformedScript));
                }
                for (index, child) in rest.iter().enumerate() {
                    self.tick()?;
                    if index % 2 == 0 {
                        pending.push(child);
                    } else {
                        expect_atom(child, ",", "tuple introduction separator")?;
                    }
                }
            } else if kind == &parser_kind(&["Term", "anonymousCtor"]) && args.len() == 3 {
                expect_atom(&args[0], "⟨", "constructor introduction")?;
                expect_atom(&args[2], "⟩", "constructor introduction")?;
                let items = expect_null_args(&args[1], "constructor introduction fields")?;
                if !items.is_empty() && items.len() % 2 == 0 {
                    return Err(error(TacticError::MalformedScript));
                }
                for (index, child) in items.iter().enumerate() {
                    self.tick()?;
                    if index % 2 == 0 {
                        pending.push(child);
                    } else {
                        expect_atom(child, ",", "constructor introduction separator")?;
                    }
                }
            } else {
                return Err(error(TacticError::UnsupportedTactic(kind.clone())));
            }
        }
        Ok(())
    }
}
