//! Goal rewriting by explicit equality proofs. The result is an Eq.rec term,
//! never an unchecked change of the goal's type or a new equality axiom.
mod matching;
mod simplify;

use super::*;
use fln_core::level::LevelView;
use std::collections::{HashMap, HashSet, VecDeque};

impl Context {
    pub(super) fn rewrite_rules<'a>(
        &mut self,
        args: &'a [Syntax],
        close: bool,
    ) -> Result<VecDeque<RewriteRule<'a>>, NatDefinitionElabError> {
        let [keyword, config, sequence, location] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(
            keyword,
            if close { "rw" } else { "rewrite" },
            "rewrite keyword",
        )?;
        expect_empty_null(config, "default rewrite configuration")?;
        expect_empty_null(location, "goal-only rewrite location")?;
        let parts = expect_node(
            sequence,
            &parser_kind(&["Tactic", "rwRuleSeq"]),
            3,
            "rewrite rule sequence",
        )?;
        expect_atom(&parts[0], "[", "rewrite rule opener")?;
        expect_atom(&parts[2], "]", "rewrite rule closer")?;
        let rows = expect_null_args(&parts[1], "rewrite rules")?;
        if rows.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let mut rules = VecDeque::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "rewrite rule separator")?;
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "rwRule"]), 2, "rewrite rule")?;
            let direction = expect_null_args(&parts[0], "rewrite direction")?;
            let reverse = match direction {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            rules.push_back(RewriteRule {
                syntax: &parts[1],
                reverse,
            });
        }
        Ok(rules)
    }

    pub(super) fn rewrite_reflexivity(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        let Some(value) = self.automatic_reflexivity_candidate(goal)? else {
            return Ok(false);
        };
        // Each rewrite created a separate child. Its parent's introduced-binder
        // closure remains below it on the work stack.
        self.txn
            .assign_mvar(
                goal.id.clone(),
                value,
                AssignmentJustification::Tactic {
                    tactic_name: Name::from_components(["rw", "rfl"]),
                },
            )
            .map_err(|e| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Metavariable(e),
                )))
            })?;
        Ok(true)
    }

    /// Automatic tactic closure uses reducible transparency for both the goal
    /// head and its operands. Ordinary `rfl` retains its separate, wider policy.
    fn automatic_reflexivity_candidate(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let transparency = UnificationTransparency::Abbreviations;
        let target = self.whnf_with_transparency(&goal.target, transparency)?;
        let Some((level, alpha, left, right)) = equality_target(&target) else {
            return Ok(None);
        };
        let left = self.whnf_with_transparency(&left, transparency)?;
        let right = self.whnf_with_transparency(&right, transparency)?;
        if !self.proof_types_match(&left, &right)?
            && !self.rewrite_arithmetic_reflexivity(goal, &left, &right)?
        {
            return Ok(None);
        }
        Ok(Some(app(
            Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
            [alpha, left],
        )))
    }

    /// The source unifier has no literal arithmetic reducer. Reuse K1 only
    /// for closed arithmetic over the exact seed primitives: unrestricted
    /// kernel conversion would also unfold ordinary definitions, exceeding
    /// automatic closure's reducible transparency. Final admission checks both seats.
    fn rewrite_arithmetic_reflexivity(
        &mut self,
        goal: &ProofGoal,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        let mut work = vec![&left, &right];
        let mut seen = HashSet::new();
        while let Some(term) = work.pop() {
            if !seen.insert(term.allocation_identity()) {
                continue;
            }
            self.tick()?;
            match term.node() {
                ExprNode::Lit {
                    literal: Literal::Nat(_),
                } => {}
                ExprNode::App { f, a } => work.extend([f, a]),
                ExprNode::MData { expr, .. } => work.push(expr),
                ExprNode::Const { name, levels } if levels.is_empty() => {
                    let Some(Declaration::Axiom(expected)) =
                        crate::seed::source_intrinsic_seed_declaration(name)
                    else {
                        return Ok(false);
                    };
                    let mut result = &expected.base.type_;
                    while let ExprNode::ForallE { body, .. } = result.node() {
                        result = body;
                    }
                    if !matches!(result.node(), ExprNode::Const { name, levels }
                        if name == &Name::from_components(["Nat"]) && levels.is_empty())
                        || self.txn.env.find(name)
                            != Some(&fln_env::constants::ConstantInfo::Axiom(expected))
                    {
                        return Ok(false);
                    }
                }
                _ => return Ok(false),
            }
        }
        match fln_kernel::check_def_eq(&self.txn.env, &[], &left, &right, self.kernel) {
            Outcome::Complete(Verdict::Accepted { .. }) => Ok(true),
            Outcome::Complete(Verdict::Rejected { .. }) => Ok(false),
            outcome => Err(failure(SourceInferenceError::Unification(Box::new(
                UnificationError::AssignmentCheck {
                    id: goal.id.clone(),
                    outcome: Box::new(outcome),
                },
            )))),
        }
    }

    pub(in crate::source) fn rewrite_proof_term<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        rule: Typed,
        reverse: bool,
        remaining: VecDeque<RewriteRule<'a>>,
        close: bool,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let original_target = self.instantiate(&goal.target)?;
        let (rule, occurrence) = self
            .instantiate_rewrite_rule(rule, &original_target, reverse, false)?
            .ok_or_else(|| error(TacticError::RewriteNoMatch))?;
        let (next_goal, value) = self.rewrite_transport(&goal, rule, &occurrence, reverse)?;
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Rewrite(next_goal, remaining, close));
        Ok(())
    }

    /// Build one ordinary conversion/equality transport. The caller owns the
    /// continuation and must close introduced binders only after its child.
    fn rewrite_transport(
        &mut self,
        goal: &ProofGoal,
        rule: Typed,
        occurrence: &Expr,
        reverse: bool,
    ) -> Result<(ProofGoal, Expr), NatDefinitionElabError> {
        let rule_type = self.whnf(&rule.type_)?;
        let (u, alpha, from, to) =
            equality_target(&rule_type).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let target = self.instantiate(&goal.target)?;
        let from = self.instantiate(&from)?;
        let to = self.instantiate(&to)?;
        let alpha = self.instantiate(&alpha)?;
        let rule_value = self.instantiate(&rule.value)?;
        let pattern = occurrence;
        let replacement = if reverse { &from } else { &to };
        if pattern.has_expr_mvar() || pattern.has_level_mvar() || pattern.has_loose_bvars() {
            return Err(error(TacticError::ExpectedEquality));
        }
        let marker = FVarId(self.fresh_name()?);
        let (template, matched) =
            self.rewrite_template(&target, pattern, &Expr::fvar(marker.clone()))?;
        if !matched {
            return Err(error(TacticError::RewriteNoMatch));
        }
        let abstracted = template
            .abstract_fvar(&marker, 0)
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        let next_target = self.substitute(&abstracted, replacement)?;
        let universe = self
            .known_type(&target)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let universe = self.whnf(&universe)?;
        let ExprNode::Sort { level: v } = universe.node() else {
            return Err(failure(SourceInferenceError::ExpectedType));
        };
        let (child, next_goal) = self.proof_goal(next_target)?;
        // Definitionally identical endpoints need no equality elimination.
        // Keep the requested syntactic target, but avoid an unnecessary dependent
        // transport. Final admission still checks the original goal by conversion.
        let reduced_from = self.whnf(&from)?;
        let reduced_to = self.whnf(&to)?;
        if self.proof_types_match(&reduced_from, &reduced_to)? {
            return Ok((next_goal, child));
        }
        let eq_domain = app(
            Expr::const_(Name::from_components(["Eq"]), vec![u.clone()]),
            [alpha.clone(), from.clone(), Expr::fvar(marker.clone())],
        );
        // Forward: Eq.rec (fun z _ => T z -> T a) id h : T b -> T a.
        // Backward: Eq.rec (fun z _ => T z) child h : T b.
        // Both directions retain the actual equality proof.
        let (motive_body, minor) = if reverse {
            (template, child.clone())
        } else {
            (
                Expr::forall_e(
                    Name::anonymous(),
                    template,
                    target.clone(),
                    BinderInfo::Default,
                ),
                Expr::lam(
                    Name::anonymous(),
                    target,
                    Expr::bvar(0).expect("fixed identity binder"),
                    BinderInfo::Default,
                ),
            )
        };
        let motive_body = Expr::lam(
            Name::from_components(["t"]),
            eq_domain,
            motive_body,
            BinderInfo::Default,
        )
        .abstract_fvar(&marker, 0)
        .map_err(|_| failure(SourceInferenceError::Scope))?;
        let motive = Expr::lam(marker.0, alpha.clone(), motive_body, BinderInfo::Default);
        let transport = app(
            Expr::const_(Name::from_components(["Eq", "rec"]), vec![v.clone(), u]),
            [alpha, from, motive, minor, to, rule_value],
        );
        let value = if reverse {
            transport
        } else {
            Expr::app(transport, child)
        };
        Ok((next_goal, value))
    }

    /// Allocation-memoized replacement of exact elaborated occurrences. The
    /// rule has no loose bvars, so no binder-dependent lift of it is required.
    fn rewrite_template(
        &mut self,
        target: &Expr,
        pattern: &Expr,
        replacement: &Expr,
    ) -> Result<(Expr, bool), NatDefinitionElabError> {
        let mut done = HashMap::<usize, (Expr, bool)>::new();
        let mut work = vec![(target, false)];
        while let Some((term, exit)) = work.pop() {
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            self.tick()?;
            if !exit {
                if self.rewrite_same(term, pattern)? {
                    done.insert(key, (replacement.clone(), true));
                    continue;
                }
                work.push((term, true));
                work.extend(
                    children(term)
                        .into_iter()
                        .flatten()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let child = |e: &Expr| {
                done.get(&e.allocation_identity())
                    .expect("postorder child")
                    .0
                    .clone()
            };
            let changed = children(term)
                .into_iter()
                .flatten()
                .any(|e| done[&e.allocation_identity()].1);
            let value = if !changed {
                term.clone()
            } else {
                match term.node() {
                    ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                    ExprNode::Lam {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => Expr::lam(
                        binder_name.clone(),
                        child(binder_type),
                        child(body),
                        *binder_info,
                    ),
                    ExprNode::ForallE {
                        binder_name,
                        binder_type,
                        body,
                        binder_info,
                    } => Expr::forall_e(
                        binder_name.clone(),
                        child(binder_type),
                        child(body),
                        *binder_info,
                    ),
                    ExprNode::LetE {
                        decl_name,
                        type_,
                        value,
                        body,
                        non_dep,
                    } => Expr::let_e(
                        decl_name.clone(),
                        child(type_),
                        child(value),
                        child(body),
                        *non_dep,
                    ),
                    ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                    _ => term.clone(),
                }
            };
            done.insert(key, (value, changed));
        }
        Ok(done
            .remove(&target.allocation_identity())
            .expect("finished rewrite root"))
    }

    /// A sufficient syntactic match, with pair memoization and metered visits;
    /// no recursive Expr equality over an exponentially shared input graph.
    fn rewrite_same(&mut self, left: &Expr, right: &Expr) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![(left, right)];
        let mut seen = HashSet::new();
        while let Some((a, b)) = work.pop() {
            if !seen.insert((a.allocation_identity(), b.allocation_identity())) {
                continue;
            }
            self.tick()?;
            if a.allocation_identity() == b.allocation_identity() {
                continue;
            }
            if a.hash() != b.hash() {
                return Ok(false);
            }
            match (a.node(), b.node()) {
                (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
                (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
                (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
                (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
                (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                    if !self.rewrite_levels_same(a, b)? {
                        return Ok(false);
                    }
                }
                (
                    ExprNode::Const { name: a, levels: x },
                    ExprNode::Const { name: b, levels: y },
                ) if a == b && x.len() == y.len() => {
                    for (a, b) in x.iter().zip(y) {
                        if !self.rewrite_levels_same(a, b)? {
                            return Ok(false);
                        }
                    }
                }
                (ExprNode::App { f: a, a: b }, ExprNode::App { f: c, a: d }) => {
                    work.push((a, c));
                    work.push((b, d));
                }
                (
                    ExprNode::Lam {
                        binder_type: a,
                        body: b,
                        ..
                    },
                    ExprNode::Lam {
                        binder_type: c,
                        body: d,
                        ..
                    },
                )
                | (
                    ExprNode::ForallE {
                        binder_type: a,
                        body: b,
                        ..
                    },
                    ExprNode::ForallE {
                        binder_type: c,
                        body: d,
                        ..
                    },
                ) => {
                    work.push((a, c));
                    work.push((b, d));
                }
                (
                    ExprNode::LetE {
                        type_: a,
                        value: b,
                        body: c,
                        ..
                    },
                    ExprNode::LetE {
                        type_: d,
                        value: e,
                        body: f,
                        ..
                    },
                ) => {
                    work.push((a, d));
                    work.push((b, e));
                    work.push((c, f));
                }
                (ExprNode::MData { data: a, expr: x }, ExprNode::MData { data: b, expr: y })
                    if a == b =>
                {
                    work.push((x, y))
                }
                (
                    ExprNode::Proj {
                        struct_name: a,
                        idx: i,
                        expr: x,
                    },
                    ExprNode::Proj {
                        struct_name: b,
                        idx: j,
                        expr: y,
                    },
                ) if a == b && i == j => work.push((x, y)),
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
    fn rewrite_levels_same(
        &mut self,
        left: &Level,
        right: &Level,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![(left, right)];
        let mut seen = HashSet::new();
        while let Some((a, b)) = work.pop() {
            if !seen.insert((std::ptr::from_ref(a), std::ptr::from_ref(b))) {
                continue;
            }
            self.tick()?;
            match (a.view(), b.view()) {
                (LevelView::Zero, LevelView::Zero) => {}
                (LevelView::Param(a), LevelView::Param(b)) if a == b => {}
                (LevelView::MVar(a), LevelView::MVar(b)) if a == b => {}
                (LevelView::Succ(a), LevelView::Succ(b)) => work.push((a, b)),
                (LevelView::Max(a, b), LevelView::Max(c, d))
                | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                    work.push((a, c));
                    work.push((b, d));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
}
fn app<const N: usize>(head: Expr, args: [Expr; N]) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn children(expr: &Expr) -> [Option<&Expr>; 3] {
    match expr.node() {
        ExprNode::App { f, a } => [Some(f), Some(a), None],
        ExprNode::Lam {
            binder_type, body, ..
        }
        | ExprNode::ForallE {
            binder_type, body, ..
        } => [Some(binder_type), Some(body), None],
        ExprNode::LetE {
            type_, value, body, ..
        } => [Some(type_), Some(value), Some(body)],
        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
        _ => [None, None, None],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn shared_rewrite_templates_remain_shared_and_fit_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(64 * 1024));
                let x = Expr::fvar(FVarId(Name::from_components(["x"])));
                let y = Expr::fvar(FVarId(Name::from_components(["y"])));
                let mut target = x.clone();
                for _ in 0..60 {
                    target = Expr::app(target.clone(), target);
                }
                let (mut output, changed) = ctx.rewrite_template(&target, &x, &y).unwrap();
                assert!(changed);
                for _ in 0..60 {
                    let ExprNode::App { f, a } = output.node() else {
                        panic!("shared application");
                    };
                    assert_eq!(f.allocation_identity(), a.allocation_identity());
                    output = f.clone();
                }
                assert_eq!(output, y);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn rewrite_matching_respects_work_limits() {
        let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(1024 * 1024));
        ctx.txn.budget.max_heartbeats = 1;
        let x = Expr::fvar(FVarId(Name::from_components(["x"])));
        let y = Expr::fvar(FVarId(Name::from_components(["y"])));
        assert!(
            ctx.rewrite_template(&Expr::app(x.clone(), x.clone()), &x, &y)
                .is_err()
        );
        assert!(ctx.txn.mvars.is_empty());
    }
}
