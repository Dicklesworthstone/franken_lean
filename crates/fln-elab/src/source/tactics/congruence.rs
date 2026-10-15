//! Native congruence builds ordinary Eq.rec proofs, never equality verdicts.
//!
//! One depth step decomposes an entire application spine, not one curried App.
//! Independent arguments use a small homogeneous proof. Dependent telescopes
//! use a generated heterogeneous theorem with complete suffix motives; neither
//! lane changes the kernel's conversion rules or admits unchecked evidence.
use super::*;
mod dependent;
#[cfg(test)]
mod tests;

struct Equation {
    level: Level,
    domain: Expr,
    left: Expr,
    right: Expr,
}
impl Equation {
    fn target(&self) -> Expr {
        equality::equation(
            self.level.clone(),
            self.domain.clone(),
            self.left.clone(),
            self.right.clone(),
        )
    }
}

fn restore(context: &mut Context, before: &Context) {
    let spent = context.txn.budget.heartbeats_consumed;
    *context = before.clone();
    context.txn.budget.heartbeats_consumed = spent;
}

impl Context {
    pub(super) fn congruence_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "congr"])?;
        let [keyword, optional] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "congr", "congruence tactic")?;
        let depth = match expect_null_args(optional, "congruence depth")? {
            [] => 1_000_000,
            [numeral] => {
                let [Syntax::Atom { val, .. }] = expect_node(
                    numeral,
                    &Name::from_components(["num"]),
                    1,
                    "congruence depth numeral",
                )?
                else {
                    return Err(error(TacticError::MalformedScript));
                };
                for _ in val.bytes() {
                    self.tick()?;
                }
                let Literal::Nat(n) = decode_natural(val)? else {
                    return Err(error(TacticError::MalformedScript));
                };
                // An unrepresentably large depth is never a small wrapped bound.
                // The ordinary heartbeat limit still bounds the actual traversal.
                match n.limbs_le() {
                    [] => 0,
                    [n] => usize::try_from(*n).unwrap_or(usize::MAX),
                    _ => usize::MAX,
                }
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let before = Box::new(self.clone());
        match self.congruence_frontier(goal, depth) {
            Ok(work) => {
                proof.work.extend(work.into_iter().rev());
                Ok(())
            }
            Err(problem) => {
                restore(self, &before);
                Err(problem)
            }
        }
    }

    fn congruence_frontier(
        &mut self,
        goal: ProofGoal,
        depth: usize,
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        let mut pending = vec![(Work::Goal(goal), depth)];
        let mut remaining = Vec::new();
        while let Some((work, depth)) = pending.pop() {
            self.tick()?;
            let Work::Goal(mut goal) = work else {
                // Parent terms close only after every surviving descendant goal.
                // In particular no lambda is abstracted around an open child hole.
                remaining.push(work);
                continue;
            };
            if self.txn.mvars.is_assigned(&goal.id) {
                continue;
            }
            self.txn.lctx = goal.lctx.clone();
            goal.target = self.instantiate(&goal.target)?;
            if let Some(value) =
                self.congruence_close(&goal, UnificationTransparency::Abbreviations)?
            {
                self.close_proof_goal(goal, value)?;
                continue;
            }
            if depth != 0 {
                let before = Box::new(self.clone());
                match self.congruence_step(&goal) {
                    Ok(Some((value, children))) => {
                        pending.push((Work::Close(goal, value), depth));
                        pending.extend(
                            children
                                .into_iter()
                                .rev()
                                .map(|g| (Work::Goal(g), depth - 1)),
                        );
                        continue;
                    }
                    Ok(None) => restore(self, &before),
                    Err(problem) => {
                        restore(self, &before);
                        return Err(problem);
                    }
                }
            }
            if let Some(value) = self.congruence_close(&goal, UnificationTransparency::Default)? {
                self.close_proof_goal(goal, value)?;
            } else {
                remaining.push(Work::Goal(goal));
            }
        }
        Ok(remaining)
    }

    /// The two congrPre phases have deliberately different transparency.
    /// A failed comparison is transactional and a resource stop is not false.
    fn congruence_close(
        &mut self,
        goal: &ProofGoal,
        transparency: UnificationTransparency,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        if transparency == UnificationTransparency::Abbreviations
            && let Some(value) = self.automatic_reflexivity_candidate(goal, true)?
        {
            return Ok(Some(value));
        }
        let target = self.whnf_with_transparency(&goal.target, transparency, true)?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = transparency;
        if let Some((u, alpha, left, right)) = equality_target(&target) {
            if self.proof_types_match_with_budget(&left, &right, budget)? {
                return Ok(Some(equality::reflexivity(u, alpha, left)));
            }
        } else if let Some((u, alpha, left, beta, right)) = equality::heterogeneous_target(&target)
            && self.proof_types_match_with_budget(&alpha, &beta, budget)?
            && self.proof_types_match_with_budget(&left, &right, budget)?
        {
            return Ok(Some([alpha, left].into_iter().fold(
                Expr::const_(Name::from_components(["HEq", "refl"]), vec![u]),
                Expr::app,
            )));
        }
        for local in goal.lctx.decls().iter().rev() {
            self.tick()?;
            if !self.is_matrix_hypothesis(local)
                && self.proof_types_match_with_budget(&local.type_, &target, budget)?
            {
                return Ok(Some(Expr::fvar(local.id.clone())));
            }
        }
        Ok(None)
    }

    fn congruence_spine(
        &mut self,
        expression: &Expr,
    ) -> Result<(Expr, Vec<Expr>), NatDefinitionElabError> {
        let mut head = expression.clone();
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::MData { expr, .. } => head = expr.clone(),
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f.clone();
                }
                _ => {
                    arguments.reverse();
                    return Ok((head, arguments));
                }
            }
        }
    }

    fn congruence_sort(&mut self, type_: &Expr) -> Result<Level, NatDefinitionElabError> {
        let sort = self
            .known_type(type_)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let sort = self.whnf(&sort)?;
        let ExprNode::Sort { level } = sort.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        Ok(level.clone())
    }

    /// J into Prop. The caller supplies a proposition with an open endpoint,
    /// and a proof at the left endpoint; the result retains the actual witness.
    fn congruence_transport(
        &mut self,
        equation: &Equation,
        witness: Expr,
        conclusion: impl FnOnce(Expr) -> Expr,
        minor: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.tick()?;
        let endpoint = FVarId(self.fresh_name()?);
        let variable = Expr::fvar(endpoint.clone());
        let witness_type = equality::equation(
            equation.level.clone(),
            equation.domain.clone(),
            equation.left.clone(),
            variable.clone(),
        );
        let inner = Expr::lam(
            Name::anonymous(),
            witness_type,
            conclusion(variable),
            BinderInfo::Default,
        )
        .abstract_fvar(&endpoint, 0)
        .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(
            endpoint.0,
            equation.domain.clone(),
            inner,
            BinderInfo::Default,
        );
        Ok([
            equation.domain.clone(),
            equation.left.clone(),
            motive,
            minor,
            equation.right.clone(),
            witness,
        ]
        .into_iter()
        .fold(
            Expr::const_(
                Name::from_components(["Eq", "rec"]),
                vec![Level::zero(), equation.level.clone()],
            ),
            Expr::app,
        ))
    }

    fn congruence_step(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<(Expr, Vec<ProofGoal>)>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.whnf(&goal.target)?;
        let (u, alpha, left, right, heterogeneous) =
            if let Some((u, a, l, r)) = equality_target(&target) {
                (u, a, l, r, false)
            } else if let Some((u, a, l, _, r)) = equality::heterogeneous_target(&target) {
                (u, a, l, r, true)
            } else {
                return Ok(None);
            };
        let before = Box::new(self.clone());
        let (mut value, children) = match self.congruence_application(&left, &right)? {
            Some(result) => result,
            None => {
                restore(self, &before);
                let Some((value, children)) =
                    self.congruence_dependent_application(&left, &right)?
                else {
                    return Ok(None);
                };
                let value = if heterogeneous {
                    value
                } else {
                    [alpha, left, right, value].into_iter().fold(
                        Expr::const_(Name::from_components(["eq_of_heq"]), vec![u]),
                        Expr::app,
                    )
                };
                return Ok(Some((value, children)));
            }
        };
        if heterogeneous {
            let equation = Equation {
                level: u.clone(),
                domain: alpha.clone(),
                left: left.clone(),
                right,
            };
            let minor = [alpha.clone(), left.clone()].into_iter().fold(
                Expr::const_(Name::from_components(["HEq", "refl"]), vec![u.clone()]),
                Expr::app,
            );
            value = self.congruence_transport(
                &equation,
                value,
                |right| {
                    [alpha.clone(), left.clone(), alpha.clone(), right]
                        .into_iter()
                        .fold(
                            Expr::const_(Name::from_components(["HEq"]), vec![u.clone()]),
                            Expr::app,
                        )
                },
                minor,
            )?;
        }
        Ok(Some((value, children)))
    }

    fn congruence_application(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<Option<(Expr, Vec<ProofGoal>)>, NatDefinitionElabError> {
        let (mut left, left_args) = self.congruence_spine(left)?;
        let (mut right, right_args) = self.congruence_spine(right)?;
        if left_args.is_empty() || left_args.len() != right_args.len() {
            return Ok(None);
        }
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::Default;
        if !self.proof_types_match_with_budget(&left, &right, budget)? {
            return Ok(None);
        }
        let mut type_ = self
            .known_type(&left)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let mut level = self.congruence_sort(&type_)?;
        let mut value = equality::reflexivity(level.clone(), type_.clone(), left.clone());
        let mut children = Vec::new();
        for (a, b) in left_args.into_iter().zip(right_args) {
            self.tick()?;
            let function_type = self.whnf(&type_)?;
            let ExprNode::ForallE {
                binder_type: domain,
                body,
                ..
            } = function_type.node()
            else {
                return Ok(None);
            };
            let same = self.proof_types_match_with_budget(&a, &b, budget)?;
            // Varying a dependent argument requires heterogeneous transport of
            // later arguments/results. Never manufacture an Eq at unequal types.
            if !same && body.has_loose_bvars() {
                return Ok(None);
            }
            let range = self.substitute(body, &a)?;
            let range_level = self.congruence_sort(&range)?;
            let next_left = Expr::app(left.clone(), a.clone());
            let function_equation = Equation {
                level,
                domain: type_.clone(),
                left,
                right: right.clone(),
            };
            let minor =
                equality::reflexivity(range_level.clone(), range.clone(), next_left.clone());
            value = self.congruence_transport(
                &function_equation,
                value,
                |f| {
                    equality::equation(
                        range_level.clone(),
                        range.clone(),
                        next_left.clone(),
                        Expr::app(f, a.clone()),
                    )
                },
                minor,
            )?;
            if !same {
                let equation = Equation {
                    level: self.congruence_sort(domain)?,
                    domain: domain.clone(),
                    left: a,
                    right: b.clone(),
                };
                let (witness, child) = self.proof_goal(equation.target())?;
                children.push(child);
                value = self.congruence_transport(
                    &equation,
                    witness,
                    |argument| {
                        equality::equation(
                            range_level.clone(),
                            range.clone(),
                            next_left.clone(),
                            Expr::app(right.clone(), argument),
                        )
                    },
                    value,
                )?;
            }
            left = next_left;
            right = Expr::app(right, b);
            type_ = range;
            level = range_level;
        }
        Ok(Some((value, children)))
    }
}
