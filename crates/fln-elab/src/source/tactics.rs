//! Native proof-state execution. Tactics construct candidate terms, not verdicts.
//!
//! `intro` records binders and closes them only after descendant goals are
//! solved. Abstracting a lambda around an unassigned child hole would hide its
//! context variables from substitution and leak free variables. Both tactic
//! sequences and application continuations use heap worklists instead.

use super::*;
mod rewrite;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TacticError {
    ExpectedGoal,
    NoGoals,
    UnsolvedGoals { count: usize },
    NoMatchingAssumption,
    ApplyMismatch,
    MalformedScript,
    ExpectedEquality,
    RewriteNoMatch,
    SimplificationNoProgress,
    SimplificationCycle,
}
impl std::fmt::Display for TacticError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ExpectedGoal => write!(f, "by proof requires an expected type"),
            Self::NoGoals => write!(f, "tactic has no remaining goal"),
            Self::UnsolvedGoals { count } => write!(f, "proof script left {count} unsolved goals"),
            Self::NoMatchingAssumption => write!(f, "no local assumption matches the goal"),
            Self::ApplyMismatch => write!(f, "apply conclusion does not match the goal"),
            Self::ExpectedEquality => write!(f, "rewrite requires an instantiated equality proof"),
            Self::RewriteNoMatch => write!(f, "rewrite found no matching occurrence in the goal"),
            Self::SimplificationNoProgress => write!(f, "simp only made no progress"),
            Self::SimplificationCycle => write!(f, "simp only encountered a rewrite cycle"),
            Self::MalformedScript => write!(f, "unsupported or malformed native proof script"),
        }
    }
}
fn error(reason: TacticError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Tactic(reason))
}

pub(super) struct ProofGoal {
    id: MVarId,
    pub(super) target: Expr,
    pub(super) lctx: LocalContext,
    introduced: Vec<LocalDecl>,
}
enum Work<'a> {
    Rewrite(ProofGoal, std::collections::VecDeque<RewriteRule<'a>>, bool),
    Goal(ProofGoal),
    Close(ProofGoal, Expr),
}
pub(super) struct ProofState<'a> {
    saved: LocalContext,
    target: Expr,
    root: Expr,
    instructions: Vec<&'a Syntax>,
    cursor: usize,
    work: Vec<Work<'a>>,
}
pub(super) struct RewriteRule<'a> {
    pub(super) syntax: &'a Syntax,
    pub(super) reverse: bool,
}

pub(super) enum ProofAction<'a> {
    Rewrite {
        goal: ProofGoal,
        rule: RewriteRule<'a>,
        remaining: std::collections::VecDeque<RewriteRule<'a>>,
        close: bool,
    },
    Term {
        syntax: &'a Syntax,
        goal: ProofGoal,
        apply: bool,
    },
    Complete(Typed),
}

impl Context {
    fn proof_goal(&mut self, target: Expr) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        let hole = self.hole(target.clone())?;
        let ExprNode::MVar { id } = hole.node() else {
            unreachable!("fresh hole");
        };
        let goal = ProofGoal {
            id: id.clone(),
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        Ok((hole, goal))
    }

    pub(super) fn start_proof<'a>(
        &mut self,
        syntax: &'a Syntax,
        expected: Option<Expr>,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        let target = expected.ok_or_else(|| error(TacticError::ExpectedGoal))?;
        let parts = expect_node(syntax, &parser_kind(&["Term", "byTactic"]), 2, "by proof")?;
        expect_atom(&parts[0], "by", "by keyword")?;
        let sequence = expect_node(
            &parts[1],
            &parser_kind(&["Tactic", "tacticSeq"]),
            1,
            "tactic sequence",
        )?;
        let sequence = expect_node(
            &sequence[0],
            &parser_kind(&["Tactic", "tacticSeq1Indented"]),
            1,
            "flat tactic sequence",
        )?;
        let rows = expect_null_args(&sequence[0], "tactic sequence rows")?;
        let mut instructions = Vec::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 0 {
                instructions.push(row);
            } else if !row.is_missing() && !matches!(row, Syntax::Atom { val, .. } if val == ";") {
                return Err(error(TacticError::MalformedScript));
            }
        }
        let (root, goal) = self.proof_goal(target.clone())?;
        Ok(ProofState {
            saved: self.txn.lctx.clone(),
            target,
            root,
            instructions,
            cursor: 0,
            work: vec![Work::Goal(goal)],
        })
    }

    /// Try equality transactionally; a failed candidate retains no assignment.
    /// Inconclusive/resource/internal outcomes never mean "try another proof".
    fn proof_types_match(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        match self
            .txn
            .unify(left, right, UnificationBudget::new(self.kernel))
        {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(_)) => Ok(false),
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(false)
            }
            Err(error) => Err(failure(SourceInferenceError::Unification(Box::new(error)))),
        }
    }

    pub(super) fn close_proof_goal(
        &mut self,
        goal: ProofGoal,
        value: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx;
        self.flush(false)?;
        let mut value = self.instantiate(&value)?;
        for local in goal.introduced.into_iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value = Expr::lam(local.user_name, domain, value, local.binder_info);
        }
        // This is candidate construction in a private transaction, not a
        // kernel acceptance. The complete command still goes through K1.
        self.txn
            .assign_mvar(
                goal.id,
                value,
                AssignmentJustification::Tactic {
                    tactic_name: Name::from_components(["native_source_proof"]),
                },
            )
            .map_err(|e| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Metavariable(e),
                )))
            })?;
        Ok(())
    }

    pub(super) fn advance_proof<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
    ) -> Result<ProofAction<'a>, NatDefinitionElabError> {
        loop {
            self.tick()?;
            let Some(work) = proof.work.pop() else {
                if proof.cursor != proof.instructions.len() {
                    return Err(error(TacticError::NoGoals));
                }
                self.txn.lctx = proof.saved.clone();
                let value = self.instantiate(&proof.root)?;
                return Ok(ProofAction::Complete(Typed {
                    value,
                    type_: proof.target.clone(),
                }));
            };
            let mut goal = match work {
                Work::Rewrite(goal, mut remaining, close) => {
                    self.txn.lctx = goal.lctx.clone();
                    if let Some(rule) = remaining.pop_front() {
                        return Ok(ProofAction::Rewrite {
                            goal,
                            rule,
                            remaining,
                            close,
                        });
                    }
                    if close && self.rewrite_reflexivity(&goal)? {
                        continue;
                    }
                    goal
                }
                Work::Close(goal, term) => {
                    self.close_proof_goal(goal, term)?;
                    continue;
                }
                Work::Goal(goal) => goal,
            };
            if self.txn.mvars.is_assigned(&goal.id) {
                continue;
            }
            self.txn.lctx = goal.lctx.clone();
            goal.target = self.instantiate(&goal.target)?;
            let Some(instruction) = proof.instructions.get(proof.cursor) else {
                let count = 1 + proof.work.iter().filter(|row| matches!(row, Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id))).count();
                return Err(error(TacticError::UnsolvedGoals { count }));
            };
            proof.cursor += 1;
            let Syntax::Node { kind, args, .. } = instruction else {
                return Err(error(TacticError::MalformedScript));
            };
            if kind == &parser_kind(&["Tactic", "simp"]) {
                self.simplify_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "rwSeq"])
                || kind == &parser_kind(&["Tactic", "rewriteSeq"])
            {
                let close = kind == &parser_kind(&["Tactic", "rwSeq"]);
                let rules = self.rewrite_rules(args, close)?;
                proof.work.push(Work::Rewrite(goal, rules, close));
            } else if kind == &parser_kind(&["Tactic", "intro"]) {
                let [keyword, names] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "intro", "intro keyword")?;
                let names = expect_null_args(names, "intro names")?;
                for index in 0..names.len().max(1) {
                    self.tick()?;
                    let name = match names.get(index) {
                        Some(Syntax::Ident { val, .. }) => val.clone(),
                        Some(Syntax::Node { kind, args, .. })
                            if kind == &parser_kind(&["Term", "hole"])
                                && matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "_") =>
                        {
                            self.fresh_name()?
                        }
                        None => self.fresh_name()?,
                        _ => return Err(error(TacticError::MalformedScript)),
                    };
                    let ty = self.whnf(&goal.target)?;
                    let ExprNode::ForallE {
                        binder_type,
                        body,
                        binder_info,
                        ..
                    } = ty.node()
                    else {
                        return Err(failure(SourceInferenceError::ExpectedFunction));
                    };
                    let id = FVarId(self.fresh_name()?);
                    goal.target = self.substitute(body, &Expr::fvar(id.clone()))?;
                    self.txn
                        .lctx
                        .add_param(id.clone(), name, binder_type.clone(), *binder_info);
                    goal.introduced
                        .push(self.txn.lctx.find(&id).expect("introduced local").clone());
                }
                goal.lctx = self.txn.lctx.clone();
                proof.work.push(Work::Goal(goal));
            } else if kind == &parser_kind(&["Tactic", "rfl"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "rfl", "reflexivity tactic")?;
                let target = self.whnf(&goal.target)?;
                let (level, alpha, left, right) =
                    equality_target(&target).ok_or_else(|| error(TacticError::ApplyMismatch))?;
                self.constrain(&left, &right)?;
                let value = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                        alpha,
                    ),
                    left,
                );
                self.close_proof_goal(goal, value)?;
            } else if kind == &parser_kind(&["Tactic", "assumption"]) {
                let [keyword] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "assumption", "assumption keyword")?;
                let mut matched = None;
                for local in goal.lctx.decls().iter().rev() {
                    self.tick()?;
                    if self.proof_types_match(&local.type_, &goal.target)? {
                        matched = Some(Expr::fvar(local.id.clone()));
                        break;
                    }
                }
                let value = matched.ok_or_else(|| error(TacticError::NoMatchingAssumption))?;
                self.close_proof_goal(goal, value)?;
            } else {
                let apply = kind == &parser_kind(&["Tactic", "apply"]);
                if !apply && kind != &parser_kind(&["Tactic", "exact"]) {
                    return Err(error(TacticError::MalformedScript));
                }
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if apply { "apply" } else { "exact" },
                    "tactic keyword",
                )?;
                return Ok(ProofAction::Term {
                    syntax: term,
                    goal,
                    apply,
                });
            }
        }
    }

    pub(super) fn apply_proof_term(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        mut term: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            if self.proof_types_match(&term.type_, &goal.target)? {
                break;
            }
            term.type_ = self.whnf(&term.type_)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = term.type_.node()
            else {
                return Err(error(TacticError::ApplyMismatch));
            };
            if *binder_info == BinderInfo::InstImplicit {
                return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
            }
            let domain = binder_type.clone();
            let body = body.clone();
            let (argument, subgoal) = self.proof_goal(domain)?;
            term.value = Expr::app(term.value, argument.clone());
            term.type_ = self.substitute(&body, &argument)?;
            arguments.push(subgoal);
        }
        proof.work.push(Work::Close(goal, term.value));
        // Dependency-producing parameters precede later parameters. Metavariables
        // already inferred while matching the conclusion are skipped by advance.
        proof
            .work
            .extend(arguments.into_iter().rev().map(Work::Goal));
        Ok(())
    }
}

/// Decode only the ordinary homogeneous equality head; no lookalike names or
/// Boolean comparisons count as equality propositions.
fn equality_target(target: &Expr) -> Option<(Level, Expr, Expr, Expr)> {
    let ExprNode::App { f, a: right } = target.node() else {
        return None;
    };
    let ExprNode::App { f, a: left } = f.node() else {
        return None;
    };
    let ExprNode::App { f, a: alpha } = f.node() else {
        return None;
    };
    let ExprNode::Const { name, levels } = f.node() else {
        return None;
    };
    if name != &Name::from_components(["Eq"]) {
        return None;
    }
    let [level] = levels.as_slice() else {
        return None;
    };
    Some((level.clone(), alpha.clone(), left.clone(), right.clone()))
}
