//! Function extensionality is derived from the already admitted quotient
//! primitives and Quot.sound, not introduced as a new axiom. The pointwise
//! goal remains open until the existing proof driver has real evidence.
use super::*;
#[cfg(test)]
mod tests;

struct FunctionEquation {
    function_type: Expr,
    universe: Level,
    left: Expr,
    right: Expr,
}

pub(super) fn is_empty(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Node { kind, args, .. }
        if kind == &Name::from_components(["tacticFunext___"])
        && matches!(args.as_slice(), [Syntax::Atom { val, .. }, Syntax::Node { kind, args, .. }]
            if val == "funext" && kind == &Name::from_components(["null"]) && args.is_empty()))
}

fn restore(context: &mut Context, before: &Context) {
    let spent = context.txn.budget.heartbeats_consumed;
    *context = before.clone();
    context.txn.budget.heartbeats_consumed = spent;
}
fn apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}
fn constant(name: &[&str], levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(name.iter().copied()), levels)
}

impl Context {
    pub(super) fn funext_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["tacticFunext___"])?;
        let [keyword, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "funext", "function extensionality")?;
        let names = expect_null_args(names, "function extensionality introductions")?;
        let before = Box::new(self.clone());
        match self.funext_frontier(goal, names) {
            Ok(work) => {
                proof.work.extend(work);
                Ok(())
            }
            Err(problem) => {
                restore(self, &before);
                Err(problem)
            }
        }
    }

    fn funext_frontier(
        &mut self,
        mut goal: ProofGoal,
        names: &[Syntax],
    ) -> Result<Vec<Work<'static>>, NatDefinitionElabError> {
        if !names.is_empty() {
            let mut pending = vec![(Work::Goal(goal), 0)];
            let mut output = Vec::new();
            while let Some((work, index)) = pending.pop() {
                self.tick()?;
                match work {
                    Work::Goal(parent) if index < names.len() => {
                        let (value, child) = self.funext_step(&parent)?;
                        pending.push((Work::Close(parent, value), index + 1));
                        for work in self.introduce_proof_pattern(child, Some(&names[index]))? {
                            pending.push((work, index + 1));
                        }
                    }
                    work @ (Work::Goal(_) | Work::Close(..)) => output.push(work),
                    _ => return Err(error(TacticError::MalformedScript)),
                }
            }
            output.reverse();
            return Ok(output);
        }
        let mut work = Vec::new();
        loop {
            self.tick()?;
            // Bare funext is repeat (apply funext; intro): only the failed
            // iteration rolls back. Resource stops are never normal failure.
            let before = Box::new(self.clone());
            match self.funext_step(&goal) {
                Ok((value, mut child)) => {
                    let name = self.fresh_name()?;
                    self.introduce_proof_binder(&mut child, name)?;
                    child.lctx = self.txn.lctx.clone();
                    work.push(Work::Close(goal, value));
                    goal = child;
                }
                Err(problem) if backtrack::recoverable(&problem) => {
                    restore(self, &before);
                    break;
                }
                Err(problem) => return Err(problem),
            }
        }
        self.txn.lctx = goal.lctx.clone();
        work.push(Work::Goal(goal));
        Ok(work)
    }

    pub(super) fn funext_step(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let target = self.whnf(&goal.target)?;
        let (universe, function_type, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let function_type = self.whnf(&function_type)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = function_type.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        // Do not instantiate an unknown equality carrier into a function.
        // Repetition must decrease an existing telescope, not invent one.
        let mut argument = self.equality_local(binder_type.clone())?;
        argument.user_name = binder_name.clone();
        let x = Expr::fvar(argument.id.clone());
        eliminate::add_local(&mut self.txn.lctx, &argument);
        let codomain = self.substitute(body, &x)?;
        let sort = self
            .known_type(&codomain)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let result_level = self.sort_level(&Typed {
            value: codomain.clone(),
            type_: sort,
        })?;
        self.txn.lctx = goal.lctx.clone();
        let pointwise = equality::equation(
            result_level.clone(),
            codomain.clone(),
            Expr::app(left.clone(), x.clone()),
            Expr::app(right.clone(), x),
        );
        let pointwise = self.close_equality_binder(&argument, pointwise, false)?;
        let (witness, child) = self.proof_goal(pointwise)?;
        let equation = FunctionEquation {
            function_type,
            universe,
            left,
            right,
        };
        let value =
            self.quotient_funext(&equation, &argument, &codomain, &result_level, witness)?;
        Ok((value, child))
    }

    fn quotient_funext(
        &mut self,
        equation: &FunctionEquation,
        argument: &LocalDecl,
        codomain: &Expr,
        result_level: &Level,
        witness: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let FunctionEquation {
            function_type,
            universe,
            left,
            right,
        } = equation;
        for name in ["Quot", "Quot.mk", "Quot.lift", "Quot.sound"] {
            self.tick()?;
            let name = Name::from_components(name.split('.'));
            if !self.txn.env.contains(&name) {
                return Err(failure(SourceInferenceError::UnknownConstant(name)));
            }
        }
        // eqv := fun f g => forall x, f x = g x
        let f = self.equality_local(function_type.clone())?;
        let g = self.equality_local(function_type.clone())?;
        let fv = Expr::fvar(f.id.clone());
        let gv = Expr::fvar(g.id.clone());
        let x = Expr::fvar(argument.id.clone());
        let pointwise = equality::equation(
            result_level.clone(),
            codomain.clone(),
            Expr::app(fv.clone(), x.clone()),
            Expr::app(gv.clone(), x.clone()),
        );
        let pointwise = self.close_equality_binder(argument, pointwise, false)?;
        let mut relation = self.close_equality_binder(&g, pointwise.clone(), true)?;
        relation = self.close_equality_binder(&f, relation, true)?;
        let quotient = apps(
            constant(&["Quot"], vec![universe.clone()]),
            [function_type.clone(), relation.clone()],
        );
        let q = self.equality_local(quotient.clone())?;
        // extfunApp q x := Quot.lift (fun f => f x) (fun f g h => h x) q
        // The lift's result is constant in f, but may depend on x.
        let evaluate = self.close_equality_binder(&f, Expr::app(fv, x.clone()), true)?;
        let h = self.equality_local(pointwise)?;
        let mut respects = Expr::app(Expr::fvar(h.id.clone()), x);
        for local in [&h, &g, &f] {
            respects = self.close_equality_binder(local, respects, true)?;
        }
        let mut selector = apps(
            constant(
                &["Quot", "lift"],
                vec![universe.clone(), result_level.clone()],
            ),
            [
                function_type.clone(),
                relation.clone(),
                codomain.clone(),
                evaluate,
                respects,
                Expr::fvar(q.id.clone()),
            ],
        );
        selector = self.close_equality_binder(argument, selector, true)?;
        selector = self.close_equality_binder(&q, selector, true)?;
        let mk = |value| {
            apps(
                constant(&["Quot", "mk"], vec![universe.clone()]),
                [function_type.clone(), relation.clone(), value],
            )
        };
        let equality = Typed {
            type_: equality::equation(
                universe.clone(),
                quotient,
                mk(left.clone()),
                mk(right.clone()),
            ),
            value: apps(
                constant(&["Quot", "sound"], vec![universe.clone()]),
                [
                    function_type.clone(),
                    relation,
                    left.clone(),
                    right.clone(),
                    witness,
                ],
            ),
        };
        // Quot.lift computation and function eta identify these endpoints
        // with f and g. Both checkers independently check the full transport.
        Ok(self
            .selector_congruence(&equality, function_type, universe, &selector)?
            .value)
    }
}
