//! Conversion mode: the `conv` tactic and the conv tactics (vendored
//! `Lean/Elab/Tactic/Conv/*.lean`, syntax and macros in `Init/Conv.lean`).
//!
//! A conv goal is an ordinary goal `lhs = ?rhs`, `?rhs` a fresh metavariable, recorded in
//! [`Context::conv_goals`] so a goal display shows it as `| lhs` (the pin's `mkLHSGoalRaw`
//! annotation). Each conv tactic replaces the main conv goal by goals that close it with an
//! equality proof built from checked lemmas (`Eq.trans`, `congrArg`, `congrFun`, the generated
//! congruence theorem of `mkCongrSimpCore?`, `funext`, `forall_congr`, …); when the block ends,
//! the goals left are closed by reflexivity and the original goal is replaced through `Eq.mpr`
//! (or the hypothesis through `Eq.mp`). Every term goes through ordinary admission.
//!
//! A goal under a binder the tactic entered (`ext`, `arg` on a `∀`, `pattern` under a `fun`)
//! lives in a context extending its parent's. Its parent's proof and right-hand side abstract
//! that binder, which is only sound once the child is solved; so they are recorded as
//! metavariables of the parent's context, each assigned by a deferred close of a goal that
//! abstracts the binder ([`Context::conv_lift`]), the worklist's rule for `intro`.
//!
//! Conv tactics this engine does not run are refused, typed, never approximated and never
//! caught by `first`/`try` (`TacticError::UnsupportedTactic`, `TacticError::ConvUnsupported`).
use super::*;
mod congr;
mod pattern;

pub(super) fn conv_kind(name: &str) -> Name {
    parser_kind(&["Tactic", "Conv", name])
}

/// Whether `kind` is a conv tactic's (or the `conv` tactic's) syntax kind.
pub(super) fn is_conv_kind(kind: &Name) -> bool {
    kind.parent() == parser_kind(&["Tactic", "Conv"])
        || kind == &Name::from_components(["Lean", "convCalc_"])
}

fn app<const N: usize>(head: Expr, args: [Expr; N]) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// `e.isAppOf c`.
fn is_app_of(expr: &Expr, name: &[&str]) -> bool {
    let mut head = expr;
    while let ExprNode::App { f, .. } = head.node() {
        head = f;
    }
    matches!(head.node(), ExprNode::Const { name: actual, .. }
        if actual == &Name::from_components(name.iter().copied()))
}

/// `Expr.cleanupAnnotations`: the expression under its metadata.
fn cleanup(expr: &Expr) -> Expr {
    let mut expr = expr.clone();
    while let ExprNode::MData { expr: inner, .. } = expr.node() {
        expr = inner.clone();
    }
    expr
}

/// An application's head and its arguments, in order (`Expr.withApp`).
fn spine(expr: &Expr) -> (Expr, Vec<Expr>) {
    let mut head = expr;
    let mut args = Vec::new();
    while let ExprNode::App { f, a } = head.node() {
        args.push(a.clone());
        head = f;
    }
    args.reverse();
    (head.clone(), args)
}

/// `Name.appendBefore`: `pre` before the last string component of the name's base (its macro
/// scopes, if any, kept).
fn append_before(name: &Name, pre: &str) -> Name {
    let mut parts = Vec::new();
    let mut current = name.clone();
    while !current.is_anonymous() {
        parts.push(current.clone());
        current = current.parent();
    }
    parts.reverse();
    // `parts[i]` is the prefix of `name` with `i + 1` components; the base ends before `_@`.
    let base_end = parts
        .iter()
        .position(|part| matches!(part.leaf_view(), LeafView::Str(s) if s == "_@"))
        .unwrap_or(parts.len());
    if base_end == 0 {
        return Name::str(Name::anonymous(), pre);
    }
    let last = &parts[base_end - 1];
    let renamed = match last.leaf_view() {
        LeafView::Str(s) => Name::str(last.parent(), format!("{pre}{s}")),
        _ => Name::str(last.clone(), pre),
    };
    // Re-append the components after the base.
    let mut result = renamed;
    for part in &parts[base_end..] {
        result = match part.leaf_view() {
            LeafView::Str(s) => Name::str(result, s),
            LeafView::Num(n) => Name::num(result, n),
            LeafView::Anonymous => result,
        };
    }
    result
}

/// What a conversion frame does with the goals its sequence leaves.
#[derive(Clone)]
pub(super) enum Finish {
    /// `conv (at h)? => …` (`evalConv`): the goals left are closed by reflexivity (`convert`),
    /// then the goal's target (`replaceTargetEq` and `try with_reducible rfl`) or the hypothesis
    /// `local` (`replaceLocalDecl`) is replaced.
    Target {
        goal: ProofGoal,
        local: Option<FVarId>,
        lhs: Expr,
        rhs: Expr,
        root: MVarId,
    },
    /// A conv tactic `conv => …` (`evalConvConvSeq`): `convert`, then `updateLhs` on `goal`.
    Nested {
        goal: ProofGoal,
        rhs: Expr,
        root: MVarId,
    },
    /// `{ … }` and `· …` (`evalConvSeqBracketed`): `all_goals (try with_reducible rfl)`, then
    /// `closeUsingOrAdmit`'s requirement that no goal is left.
    Bracketed,
    /// `tactic => …` (`evalNestedTactic`): the goals left of shape `_ = ?m …` become conv goals
    /// again (`remarkAsConvGoal`).
    Tactic,
}

impl Context {
    /// The universe of `type_`, a type in the current local context.
    fn conv_level(&mut self, type_: &Expr) -> Result<Level, NatDefinitionElabError> {
        let sort = self
            .known_type(type_)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        self.sort_level(&Typed {
            value: type_.clone(),
            type_: sort,
        })
    }

    /// The type of `expr` in the current local context, instantiated.
    fn conv_type(&mut self, expr: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let type_ = self
            .known_type(expr)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        self.instantiate(&type_)
    }

    /// `isProp e`: whether `e`'s type is `Prop`.
    fn conv_is_prop(&mut self, expr: &Expr) -> Result<bool, NatDefinitionElabError> {
        let Some(type_) = self.known_type(expr)? else {
            return Ok(false);
        };
        let type_ = self.whnf(&type_)?;
        Ok(matches!(type_.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()))
    }

    /// A constant the conv proofs name; a world without it is a typed refusal.
    fn conv_constant(
        &mut self,
        name: &[&str],
        levels: Vec<Level>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let constant_name = Name::from_components(name.iter().copied());
        if !self.txn.env.contains(&constant_name) {
            return Err(failure(SourceInferenceError::UnknownConstant(
                constant_name,
            )));
        }
        Ok(Expr::const_(constant_name, levels))
    }

    /// A conv goal's sides: `(u, α, lhs, rhs)` of its target `@Eq.{u} α lhs rhs`.
    fn conv_sides(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<(Level, Expr, Expr, Expr), NatDefinitionElabError> {
        let target = self.instantiate(&goal.target)?;
        if let Some(sides) = equality_target(&cleanup(&target)) {
            return Ok(sides);
        }
        let target =
            self.whnf_with_transparency(&target, UnificationTransparency::Abbreviations, false)?;
        equality_target(&target).ok_or_else(|| error(TacticError::ConvInvalidGoal))
    }

    /// `mkConvGoalFor lhs tag`: a fresh `?rhs` and the conv goal `lhs = ?rhs`, in the current
    /// local context. Returns `?rhs`, the goal's metavariable and the goal.
    fn conv_goal_for(
        &mut self,
        lhs: &Expr,
        tag: &Name,
    ) -> Result<(Expr, Expr, ProofGoal), NatDefinitionElabError> {
        let alpha = self.conv_type(lhs)?;
        let level = self.conv_level(&alpha)?;
        let rhs = self.hole(alpha.clone())?;
        let target = equality::equation(level, alpha, lhs.clone(), rhs.clone());
        let (hole, goal) = self.proof_goal(target)?;
        self.conv_goals.insert(goal.id.clone());
        if !tag.is_anonymous() {
            self.goal_tags.insert(goal.id.clone(), tag.clone());
        }
        Ok((rhs, hole, goal))
    }

    /// `isDefEq rhs value` where `rhs` is a conv goal's right-hand side: a still unknown `?rhs`
    /// is assigned, anything else is compared.
    fn conv_resolve_rhs(
        &mut self,
        rhs: &Expr,
        value: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let rhs = self.instantiate(rhs)?;
        if let ExprNode::MVar { id } = rhs.node()
            && !self.txn.mvars.is_assigned(id)
        {
            let value = self.instantiate(value)?;
            if self.txn.mvars.collect_mvars(&value).contains(id) {
                return Ok(false);
            }
            self.txn
                .assign_mvar(
                    id.clone(),
                    value,
                    AssignmentJustification::Tactic {
                        tactic_name: Name::from_components(["conv"]),
                    },
                )
                .map_err(|e| {
                    failure(SourceInferenceError::Unification(Box::new(
                        UnificationError::Metavariable(e),
                    )))
                })?;
            return Ok(true);
        }
        self.proof_types_match(&rhs, value)
    }

    /// A new goal standing for `parent`, of target `target`, in `parent`'s context and with its
    /// tag, marked as a conv goal.
    fn conv_successor(
        &mut self,
        parent: &ProofGoal,
        target: Expr,
    ) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        self.txn.lctx = parent.lctx.clone();
        let (hole, goal) = self.proof_goal(target)?;
        self.conv_goals.insert(goal.id.clone());
        if let Some(tag) = self.goal_tags.get(&parent.id).cloned() {
            self.goal_tags.insert(goal.id.clone(), tag);
        }
        Ok((hole, goal))
    }

    /// `Meta.mkEqTrans h₁ h₂` for `h₁ : a = b` and `h₂ : b = c`.
    fn conv_eq_trans(
        &mut self,
        level: &Level,
        alpha: &Expr,
        [a, b, c]: [&Expr; 3],
        first: Expr,
        second: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if is_app_of(&first, &["Eq", "refl"]) {
            return Ok(second);
        }
        if is_app_of(&second, &["Eq", "refl"]) {
            return Ok(first);
        }
        Ok(app(
            self.conv_constant(&["Eq", "trans"], vec![level.clone()])?,
            [
                alpha.clone(),
                a.clone(),
                b.clone(),
                c.clone(),
                first,
                second,
            ],
        ))
    }

    /// `Meta.mkEqRefl a`.
    fn conv_eq_refl(&mut self, value: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let alpha = self.conv_type(value)?;
        let level = self.conv_level(&alpha)?;
        Ok(app(
            self.conv_constant(&["Eq", "refl"], vec![level])?,
            [alpha, value.clone()],
        ))
    }

    /// `updateLhs lhs' h`: `⊢ lhs = rhs` becomes `⊢ lhs' = rhs`, closed by `Eq.trans h ?new`.
    fn conv_update_lhs(
        &mut self,
        goal: ProofGoal,
        lhs_new: Expr,
        proof: Expr,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let (level, alpha, lhs, rhs) = self.conv_sides(&goal)?;
        let target = equality::equation(level.clone(), alpha.clone(), lhs_new.clone(), rhs.clone());
        let (hole, next) = self.conv_successor(&goal, target)?;
        let value = self.conv_eq_trans(&level, &alpha, [&lhs, &lhs_new, &rhs], proof, hole)?;
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, value)?;
        Ok(next)
    }

    /// Assign a conv goal a proof that may still read its successors' metavariables. A goal
    /// with binders of its own to abstract (`intro` inside `tactic =>`) would abstract them
    /// around those unsolved holes, so such a goal is refused rather than closed.
    fn conv_close(&mut self, goal: ProofGoal, value: Expr) -> Result<(), NatDefinitionElabError> {
        if !goal.introduced.is_empty() {
            return Err(error(TacticError::ConvUnsupported(
                "a conv tactic on a goal with binders of its own to close",
            )));
        }
        self.close_proof_goal(goal, value)
    }

    /// `changeLhs lhs'`: `lhs'` definitionally equal to the goal's `lhs` replaces it
    /// (`replaceTargetDefEq`, with its `id` type hint).
    fn conv_change_lhs(
        &mut self,
        goal: ProofGoal,
        lhs_new: Expr,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let (level, alpha, lhs, rhs) = self.conv_sides(&goal)?;
        let lhs_new = self.instantiate(&lhs_new)?;
        if self.rewrite_same(&lhs, &lhs_new)? {
            return Ok(goal);
        }
        let old_target = equality::equation(level.clone(), alpha.clone(), lhs, rhs.clone());
        let target = equality::equation(level, alpha, lhs_new, rhs);
        let (hole, next) = self.conv_successor(&goal, target)?;
        let value = app(
            self.conv_constant(&["id"], vec![Level::zero()])?,
            [old_target, hole],
        );
        self.conv_goals.remove(&goal.id);
        self.conv_close(goal, value)?;
        Ok(next)
    }

    /// A metavariable of the current context standing for `fun locals => inner`, where `inner`
    /// lives in the current context extended by `locals` (`extended`): its assignment is a
    /// deferred close, pushed onto `deferred`, which runs once `inner`'s goals are solved.
    /// `type_` is its type, already abstracted.
    fn conv_lift<'w>(
        &mut self,
        deferred: &mut Vec<Work<'w>>,
        extended: &LocalContext,
        locals: &[LocalDecl],
        inner: Expr,
        type_: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        if locals.is_empty() {
            return Ok(inner);
        }
        let hole = self.hole(type_.clone())?;
        let ExprNode::MVar { id } = hole.node() else {
            unreachable!("fresh hole");
        };
        deferred.push(Work::Close(
            ProofGoal {
                id: id.clone(),
                target: type_,
                lctx: extended.clone(),
                introduced: locals.to_vec(),
                no_implicit_lambda: false,
            },
            inner,
        ));
        Ok(hole)
    }

    /// `mkForallFVars`/`mkLambdaFVars` over `locals` (in order), from their declarations.
    fn conv_close_binders(
        &mut self,
        locals: &[LocalDecl],
        body: Expr,
        lambda: bool,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut result = body;
        for local in locals.iter().rev() {
            self.tick()?;
            let abstracted = result
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            result = if lambda {
                Expr::lam(
                    local.user_name.clone(),
                    local.type_.clone(),
                    abstracted,
                    local.binder_info,
                )
            } else {
                Expr::forall_e(
                    local.user_name.clone(),
                    local.type_.clone(),
                    abstracted,
                    local.binder_info,
                )
            };
        }
        Ok(result)
    }

    /// A fresh local `name : type_` (`withLocalDecl`), added to the current context.
    fn conv_local(
        &mut self,
        name: Name,
        type_: Expr,
        binder_info: BinderInfo,
    ) -> Result<LocalDecl, NatDefinitionElabError> {
        let id = FVarId(self.fresh_name()?);
        self.txn
            .lctx
            .add_param(id.clone(), name, type_, binder_info);
        Ok(self.txn.lctx.find(&id).cloned().expect("added conv local"))
    }

    /// The instructions of a `convSeq`: a bracketed one is the single instruction that runs it,
    /// parentheses (`Conv.paren`, pure grouping) are read through.
    pub(super) fn conv_instructions<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Vec<&'a Syntax>, NatDefinitionElabError> {
        let [inner] = expect_node(syntax, &conv_kind("convSeq"), 1, "conv sequence")? else {
            return Err(error(TacticError::MalformedScript));
        };
        if inner.kind() == Some(&conv_kind("convSeqBracketed")) {
            return Ok(vec![inner]);
        }
        let [rows] = expect_node(
            inner,
            &conv_kind("convSeq1Indented"),
            1,
            "conv sequence rows",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let mut instructions = Vec::new();
        let mut pending = vec![rows];
        while let Some(rows) = pending.pop() {
            for (index, row) in expect_null_args(rows, "conv rows")?.iter().enumerate() {
                self.tick()?;
                if index % 2 == 1 {
                    if !matches!(row, Syntax::Atom { val, .. } if val == ";") {
                        expect_empty_null(row, "conv separator")
                            .map_err(|_| error(TacticError::MalformedScript))?;
                    }
                    continue;
                }
                if row.kind() == Some(&conv_kind("paren")) {
                    let [open, sequence, close] =
                        expect_node(row, &conv_kind("paren"), 3, "conv parentheses")?
                    else {
                        return Err(error(TacticError::MalformedScript));
                    };
                    expect_atom(open, "(", "conv parenthesis")?;
                    expect_atom(close, ")", "conv parenthesis")?;
                    instructions.extend(self.conv_instructions(sequence)?);
                    continue;
                }
                instructions.push(row);
            }
        }
        if instructions.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        Ok(instructions)
    }

    /// One conv instruction (or the `conv` tactic itself) on `goal`, the main goal.
    pub(super) fn conv_instruction<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        instruction: &'a Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = instruction else {
            return Err(error(TacticError::MalformedScript));
        };
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "Conv", "conv"])?;
        self.txn.lctx = goal.lctx.clone();
        let short = match kind.leaf_view() {
            LeafView::Str(s) if kind.parent() == parser_kind(&["Tactic", "Conv"]) => s.to_owned(),
            _ if kind == &Name::from_components(["Lean", "convCalc_"]) => "calc".to_owned(),
            _ => return Err(error(TacticError::MalformedScript)),
        };
        match short.as_str() {
            "conv" => self.start_conv(proof, goal, args),
            "convConvSeq" => {
                let [keyword, arrow, sequence] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "conv", "nested conv keyword")?;
                expect_atom(arrow, "=>", "nested conv arrow")?;
                let (_, _, lhs, _) = self.conv_sides(&goal)?;
                let lhs = cleanup(&lhs);
                self.txn.lctx = goal.lctx.clone();
                let (rhs, _, root) = self.conv_goal_for(&lhs, &Name::anonymous())?;
                let body = self.conv_instructions(sequence)?;
                let finish = Finish::Nested {
                    goal,
                    rhs,
                    root: root.id.clone(),
                };
                self.start_conv_frame(proof, vec![Work::Goal(root)], body, finish)
            }
            "skip" => {
                proof.work.push(Work::Goal(goal));
                Ok(())
            }
            // `macro "rfl" : conv => `(conv| tactic => rfl)`.
            "convRfl" => {
                self.conv_goals.remove(&goal.id);
                self.rfl_proof_goal(goal)
            }
            // `macro "done" : conv => `(conv| tactic' => done)`: an unsolved goal fails it.
            "convDone" => {
                let count = 1 + proof
                    .work
                    .iter()
                    .filter(|row| {
                        matches!(row, Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id))
                    })
                    .count();
                Err(error(TacticError::UnsolvedGoals { count }))
            }
            // `macro "trace_state" : conv => `(conv| tactic' => trace_state)`.
            "convTrace_state" => {
                proof.work.push(Work::Goal(goal));
                self.trace_proof_state(proof, instruction)
            }
            "nestedTactic" => {
                let [keyword, arrow, sequence] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "tactic", "nested tactic keyword")?;
                expect_atom(arrow, "=>", "nested tactic arrow")?;
                let body = self.proof_instructions(sequence)?;
                // The goal is shown as `⊢ lhs = ?rhs` inside (`evalNestedTactic` strips the
                // annotation), and focused.
                self.conv_goals.remove(&goal.id);
                self.start_conv_frame(proof, vec![Work::Goal(goal)], body, Finish::Tactic)
            }
            "convApply_" => {
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "apply", "conv apply keyword")?;
                self.conv_apply(proof, goal, term)
            }
            "nestedConv" => {
                let [bracketed] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                self.start_conv_bracketed(proof, goal, bracketed)
            }
            "convSeqBracketed" => self.start_conv_bracketed(proof, goal, instruction),
            "conv·_" => {
                let [dot, sequence] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                if !matches!(dot, Syntax::Atom { val, .. } if val == "·" || val == ".") {
                    return Err(error(TacticError::MalformedScript));
                }
                let body = self.conv_instructions(sequence)?;
                self.start_conv_frame(proof, vec![Work::Goal(goal)], body, Finish::Bracketed)
            }
            "paren" => {
                let [open, sequence, close] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(open, "(", "conv parenthesis")?;
                expect_atom(close, ")", "conv parenthesis")?;
                let inner = self.conv_instructions(sequence)?;
                let at = proof.cursor - 1;
                proof.instructions.splice(at..=at, inner);
                proof.cursor = at;
                proof.work.push(Work::Goal(goal));
                Ok(())
            }
            "whnf" => {
                let (_, _, lhs, _) = self.conv_sides(&goal)?;
                let reduced = self.whnf(&lhs)?;
                let next = self.conv_change_lhs(goal, reduced)?;
                proof.work.push(Work::Goal(next));
                Ok(())
            }
            "zeta" => {
                let (_, _, lhs, _) = self.conv_sides(&goal)?;
                let reduced = self.conv_zeta_reduce(&lhs)?;
                let next = self.conv_change_lhs(goal, reduced)?;
                proof.work.push(Work::Goal(next));
                Ok(())
            }
            "change" => {
                let [keyword, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "change", "conv change keyword")?;
                self.conv_change(proof, goal, term)
            }
            "rewrite" | "convRw__" => {
                let [keyword, config, rules] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(
                    keyword,
                    if short == "rewrite" { "rewrite" } else { "rw" },
                    "conv rewrite keyword",
                )?;
                expect_default_config(config, "default conv rewrite configuration")?;
                self.conv_rewrite(proof, goal, rules)
            }
            "clear" => self.conv_clear(proof, goal, args),
            "simp" => self.conv_simp(proof, goal, args, false),
            "dsimp" => self.conv_simp(proof, goal, args, true),
            "unfold" => self.conv_unfold(proof, goal, args),
            "calc" => self.conv_calc(proof, goal, args),
            "lhs" | "rhs" | "convLeft" | "convRight" | "arg" | "congr" | "convArgs" | "fun"
            | "ext" | "convIntro___" | "enter" => self.conv_navigate(proof, goal, &short, args),
            "pattern" => {
                let [keyword, occs, term] = args.as_slice() else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "pattern", "pattern keyword")?;
                let work = self.conv_pattern(goal, occs, term)?;
                proof.work.extend(work.into_iter().rev());
                Ok(())
            }
            _ => Err(error(TacticError::UnsupportedTactic(kind.clone()))),
        }
    }

    /// `conv (at h)? (in (occs)? p)? => code` (`evalConv`): `code` runs on the conv goal
    /// `target = ?rhs` (or `type of h = ?rhs`), after `pattern (occs)? p` when given.
    fn start_conv<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        args: &'a [Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, at_slot, in_slot, arrow, sequence] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "conv", "conv keyword")?;
        expect_atom(arrow, "=>", "conv arrow")?;
        let local = match expect_null_args(at_slot, "conv location")? {
            [] => None,
            [at, Syntax::Ident { val, .. }] => {
                expect_atom(at, "at", "conv location keyword")?;
                // `getLocalDeclFromUserName`.
                let local = goal
                    .lctx
                    .find_by_user_name(val)
                    .filter(|local| !self.is_matrix_hypothesis(local))
                    .cloned()
                    .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
                Some(local)
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        self.txn.lctx = goal.lctx.clone();
        let lhs = match &local {
            None => self.instantiate(&goal.target)?,
            Some(local) => self.instantiate(&local.type_)?,
        };
        let (rhs, _, root) = self.conv_goal_for(&lhs, &Name::anonymous())?;
        let body = self.conv_instructions(sequence)?;
        let root_id = root.id.clone();
        let goals = match expect_null_args(in_slot, "conv pattern")? {
            [] => vec![Work::Goal(root)],
            [keyword, occs, term] => {
                expect_atom(keyword, "in", "conv pattern keyword")?;
                self.conv_pattern(root, occs, term)?
            }
            _ => return Err(error(TacticError::MalformedScript)),
        };
        let finish = Finish::Target {
            goal,
            local: local.map(|local| local.id),
            lhs,
            rhs,
            root: root_id,
        };
        self.start_conv_frame(proof, goals, body, finish)
    }

    /// `{ … }` (`Conv.nestedConv`, `evalConvSeqBracketed`) on the main goal.
    fn start_conv_bracketed<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        bracketed: &'a Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let [open, rows, close] = expect_node(
            bracketed,
            &conv_kind("convSeqBracketed"),
            3,
            "bracketed conv sequence",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(open, "{", "conv brace")?;
        expect_atom(close, "}", "conv brace")?;
        let mut body = Vec::new();
        for (index, row) in expect_null_args(rows, "bracketed conv rows")?
            .iter()
            .enumerate()
        {
            self.tick()?;
            if index % 2 == 0 {
                body.push(row);
            }
        }
        if body.is_empty() {
            // `{}`: nothing runs; the goal must still be closed by `try with_reducible rfl`.
            if !self.conv_try_reducible_rfl(&goal)? {
                return Err(error(TacticError::UnsolvedGoals { count: 1 }));
            }
            return Ok(());
        }
        self.start_conv_frame(proof, vec![Work::Goal(goal)], body, Finish::Bracketed)
    }

    /// The end of a conversion frame: `pending` is what its sequence left, in worklist order
    /// (the next to run last). The frame's suspended work is back in `proof.work`.
    pub(super) fn finish_conv<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        finish: Finish,
        pending: Vec<Work<'a>>,
    ) -> Result<(), NatDefinitionElabError> {
        match finish {
            Finish::Tactic => {
                // `remarkAsConvGoal`.
                for work in &pending {
                    self.tick()?;
                    if let Work::Goal(goal) = work
                        && !self.txn.mvars.is_assigned(&goal.id)
                    {
                        self.txn.lctx = goal.lctx.clone();
                        let target = self.instantiate(&goal.target)?;
                        if let Some((.., rhs)) = equality_target(&target) {
                            let (head, _) = spine(&rhs);
                            if matches!(head.node(), ExprNode::MVar { id } if !self.txn.mvars.is_assigned(id))
                            {
                                self.conv_goals.insert(goal.id.clone());
                            }
                        }
                    }
                }
                proof.work.extend(pending);
                Ok(())
            }
            Finish::Bracketed => {
                let mut unsolved = 0usize;
                for work in pending.into_iter().rev() {
                    self.tick()?;
                    match work {
                        Work::Goal(goal) => {
                            if self.txn.mvars.is_assigned(&goal.id) {
                                continue;
                            }
                            if !self.conv_try_reducible_rfl(&goal)? {
                                unsolved += 1;
                            }
                        }
                        Work::Close(goal, value) => {
                            if unsolved == 0 {
                                self.close_proof_goal(goal, value)?;
                            }
                        }
                        _ => return Err(error(TacticError::MalformedScript)),
                    }
                }
                if unsolved != 0 {
                    return Err(error(TacticError::UnsolvedGoals { count: unsolved }));
                }
                Ok(())
            }
            Finish::Target {
                goal,
                local,
                lhs,
                rhs,
                root,
            } => {
                self.conv_close_remaining(pending)?;
                let rhs = self.instantiate(&rhs)?;
                let equality = self.instantiate(&Expr::mvar(root))?;
                self.txn.lctx = goal.lctx.clone();
                let level = self.conv_level(&lhs)?;
                match local {
                    None => {
                        // `replaceTargetEq` and `try with_reducible rfl`.
                        let (hole, next) = {
                            let (hole, next) = self.proof_goal(rhs.clone())?;
                            if let Some(tag) = self.goal_tags.get(&goal.id).cloned() {
                                self.goal_tags.insert(next.id.clone(), tag);
                            }
                            (hole, next)
                        };
                        let statement = equality::equation(
                            Level::succ(level.clone())
                                .map_err(|_| failure(SourceInferenceError::Scope))?,
                            Expr::sort(level.clone()),
                            lhs.clone(),
                            rhs.clone(),
                        );
                        let hint = app(
                            self.conv_constant(&["id"], vec![Level::zero()])?,
                            [statement, equality],
                        );
                        let value = app(
                            self.conv_constant(&["Eq", "mpr"], vec![level])?,
                            [lhs, rhs, hint, hole],
                        );
                        // The goal's own binders close once the new goal is solved.
                        proof.work.push(Work::Close(goal, value));
                        if !self.conv_try_reducible_rfl(&next)? {
                            proof.work.push(Work::Goal(next));
                        }
                        Ok(())
                    }
                    Some(local) => {
                        // `replaceLocalDecl`.
                        let declaration = goal
                            .lctx
                            .find(&local)
                            .cloned()
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
                        let value = app(
                            self.conv_constant(&["Eq", "mp"], vec![level])?,
                            [lhs, rhs.clone(), equality, Expr::fvar(local)],
                        );
                        let (next, parent, child) = self.replace_rewritten_hypothesis(
                            goal,
                            &declaration,
                            Typed { value, type_: rhs },
                            false,
                        )?;
                        proof.work.push(Work::Close(parent, child));
                        proof.work.push(Work::Goal(next));
                        Ok(())
                    }
                }
            }
            Finish::Nested { goal, rhs, root } => {
                self.conv_close_remaining(pending)?;
                let rhs = self.instantiate(&rhs)?;
                let equality = self.instantiate(&Expr::mvar(root))?;
                let next = self.conv_update_lhs(goal, rhs, equality)?;
                proof.work.push(Work::Goal(next));
                Ok(())
            }
        }
    }

    /// `convert`'s end: each goal left is closed by `refl`, else by `inferInstance`, else the
    /// conversion fails ("There are unsolved goals"). Deferred closes run in order.
    fn conv_close_remaining(
        &mut self,
        pending: Vec<Work<'_>>,
    ) -> Result<(), NatDefinitionElabError> {
        let mut unsolved = 0usize;
        for work in pending.into_iter().rev() {
            self.tick()?;
            match work {
                Work::Goal(goal) => {
                    if self.txn.mvars.is_assigned(&goal.id) {
                        continue;
                    }
                    if !self.conv_refl(&goal)? && !self.conv_infer_instance(&goal)? {
                        unsolved += 1;
                    }
                }
                Work::Close(goal, value) => {
                    if unsolved == 0 {
                        self.close_proof_goal(goal, value)?;
                    }
                }
                _ => return Err(error(TacticError::MalformedScript)),
            }
        }
        if unsolved != 0 {
            return Err(error(TacticError::ConvUnsolvedGoals { count: unsolved }));
        }
        Ok(())
    }

    /// `MVarId.refl`: an `Eq` goal whose sides are definitionally equal closes by `Eq.refl`.
    fn conv_refl(&mut self, goal: &ProofGoal) -> Result<bool, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let Some((level, alpha, left, right)) = equality_target(&cleanup(&target)) else {
            return Ok(false);
        };
        if !self.proof_types_match(&left, &right)? {
            // A closed equation the unifier leaves open (native `Nat` arithmetic, say) is
            // decided by the same Default conversion `change` uses.
            let before = Box::new(self.clone());
            let decided = self.coercion_eq(&left, &right);
            match decided {
                Ok(true) => {}
                Ok(false) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = *before;
                    self.txn.budget.heartbeats_consumed = spent;
                    return Ok(false);
                }
                Err(problem) if super::backtrack::recoverable(&problem) => {
                    let spent = self.txn.budget.heartbeats_consumed;
                    *self = *before;
                    self.txn.budget.heartbeats_consumed = spent;
                    return Ok(false);
                }
                Err(problem) => return Err(problem),
            }
        }
        let value = equality::reflexivity(level, alpha, left);
        self.conv_goals.remove(&goal.id);
        self.close_proof_goal(goal.clone(), value)?;
        Ok(true)
    }

    /// `MVarId.inferInstance`, failing quietly (`<|> pure ()`).
    fn conv_infer_instance(&mut self, goal: &ProofGoal) -> Result<bool, NatDefinitionElabError> {
        let before = Box::new(self.clone());
        let attempt = (|| -> Result<bool, NatDefinitionElabError> {
            self.txn.lctx = goal.lctx.clone();
            let target = self.instantiate(&goal.target)?;
            if self.validate_instance_binder(&target).is_err() {
                return Ok(false);
            }
            let value = self.instance_hole(target)?;
            self.resolve_instances(true)?;
            let value = self.instantiate(&value)?;
            if value.has_expr_mvar() {
                return Ok(false);
            }
            self.close_proof_goal(goal.clone(), value)?;
            Ok(true)
        })();
        match attempt {
            Ok(true) => Ok(true),
            Ok(false) => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = *before;
                self.txn.budget.heartbeats_consumed = spent;
                Ok(false)
            }
            Err(problem) if super::backtrack::recoverable(&problem) => {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = *before;
                self.txn.budget.heartbeats_consumed = spent;
                Ok(false)
            }
            Err(problem) => Err(problem),
        }
    }

    /// `try with_reducible rfl` on `goal`: an `Eq`, `HEq` or `Iff` whose sides are equal at
    /// reducible transparency closes.
    fn conv_try_reducible_rfl(&mut self, goal: &ProofGoal) -> Result<bool, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let target = self.whnf_with_transparency(
            &cleanup(&target),
            UnificationTransparency::Abbreviations,
            true,
        )?;
        let (head, args) = spine(&target);
        if matches!(head.node(), ExprNode::Const { name, .. } if name == &Name::from_components(["Iff"]))
            && args.len() == 2
        {
            let mut budget = UnificationBudget::new(self.kernel);
            budget.transparency = UnificationTransparency::Abbreviations;
            let before = Box::new(self.clone());
            if !self.proof_types_match_with_budget(&args[0], &args[1], budget)? {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = *before;
                self.txn.budget.heartbeats_consumed = spent;
                return Ok(false);
            }
            let value = Expr::app(
                self.conv_constant(&["Iff", "refl"], Vec::new())?,
                args[0].clone(),
            );
            self.conv_goals.remove(&goal.id);
            self.close_proof_goal(goal.clone(), value)?;
            return Ok(true);
        }
        let mut plain = goal.clone();
        plain.target = target;
        let Some(value) = self.automatic_reflexivity_candidate(&plain, true)? else {
            return Ok(false);
        };
        self.conv_goals.remove(&goal.id);
        self.close_proof_goal(goal.clone(), value)?;
        Ok(true)
    }

    /// `apply e` (`macro "apply " e:term : conv => `(conv| tactic => apply $e)`): the goal is
    /// focused without its annotation, `apply e` runs, and the goals it leaves of shape
    /// `_ = ?m …` are conv goals again.
    fn conv_apply(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        term: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        self.conv_goals.remove(&goal.id);
        self.txn.lctx = goal.lctx.clone();
        let instance_start = self.instance_goals.len();
        let value = self.term(term, None)?;
        let start = proof.work.len();
        self.apply_proof_term(proof, goal, value, instance_start)?;
        let produced: Vec<ProofGoal> = proof.work[start..]
            .iter()
            .filter_map(|work| match work {
                Work::Goal(goal) => Some(goal.clone()),
                _ => None,
            })
            .collect();
        for new in produced {
            self.tick()?;
            if self.txn.mvars.is_assigned(&new.id) {
                continue;
            }
            let id = new.id.clone();
            let target = self.instantiate(&new.target)?;
            if let Some((.., rhs)) = equality_target(&target) {
                let (head, _) = spine(&rhs);
                if matches!(head.node(), ExprNode::MVar { id } if !self.txn.mvars.is_assigned(id)) {
                    self.conv_goals.insert(id);
                }
            }
        }
        Ok(())
    }

    /// `change e` (`Conv.evalChange`): `e`, elaborated at the type of `lhs`, must be
    /// definitionally equal to it, and becomes the new `lhs`.
    fn conv_change(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        term: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let (_, alpha, lhs, _) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let old = self.txn.mvars.collect_mvars(&lhs);
        let replacement = self.term(term, Some(alpha))?;
        // As the tactic `change` (`change_proof_goal`): the pin's `elabChange` retries its
        // `isDefEq` after pending synthesis and default instances.
        self.resolve_instances(false)?;
        self.flush(false)?;
        if !self.coercion_eq(&replacement.value, &lhs)? {
            self.resolve_instances_with_defaults()?;
            self.flush(false)?;
            if !self.coercion_eq(&replacement.value, &lhs)? {
                return Err(error(TacticError::ChangeMismatch));
            }
        }
        let replacement = self.instantiate(&replacement.value)?;
        // `logUnassignedAndAbort` over the metavariables the term made.
        let made = self
            .txn
            .mvars
            .collect_mvars(&replacement)
            .into_iter()
            .filter(|id| !old.contains(id))
            .count();
        if made != 0 {
            return Err(failure(SourceInferenceError::UnresolvedHoles {
                count: made,
            }));
        }
        let next = self.conv_change_lhs(goal, replacement)?;
        proof.work.push(Work::Goal(next));
        Ok(())
    }

    /// `rw [rules]` and `rewrite [rules]` (`Conv.evalRewrite`): each rule rewrites `lhs`
    /// (`MVarId.rewrite`), the new `lhs` replacing it through `updateLhs`; the rule's remaining
    /// hypotheses follow the goal.
    fn conv_rewrite(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        rules: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let parts = expect_node(
            rules,
            &parser_kind(&["Tactic", "rwRuleSeq"]),
            3,
            "conv rewrite rules",
        )?;
        expect_atom(&parts[0], "[", "rewrite rule opener")?;
        expect_atom(&parts[2], "]", "rewrite rule closer")?;
        let rows = expect_null_args(&parts[1], "rewrite rules")?;
        if rows.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let mut premises = Vec::new();
        for (index, row) in rows.iter().enumerate() {
            self.tick()?;
            if index % 2 == 1 {
                expect_atom(row, ",", "rewrite rule separator")?;
                continue;
            }
            let parts = expect_node(row, &parser_kind(&["Tactic", "rwRule"]), 2, "rewrite rule")?;
            let reverse = match expect_null_args(&parts[0], "rewrite direction")? {
                [] => false,
                [Syntax::Atom { val, .. }] if val == "←" || val == "<-" => true,
                _ => return Err(error(TacticError::MalformedScript)),
            };
            let (_, _, lhs, _) = self.conv_sides(&goal)?;
            self.txn.lctx = goal.lctx.clone();
            let rule = self.term(&parts[1], None)?;
            let (lhs_new, equality, rule_premises) =
                self.conv_rewrite_expression(&lhs, rule, reverse)?;
            goal = self.conv_update_lhs(goal, lhs_new, equality)?;
            premises.extend(rule_premises);
        }
        // The main goal first, then the rules' hypotheses in order.
        proof
            .work
            .extend(premises.into_iter().rev().map(Work::Goal));
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// `clear h₁ … hₙ` (`Conv.evalClear`): the locals leave the conv goal, the latest first
    /// (`convClear`), unless something left still reads them.
    fn conv_clear(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "clear", "conv clear keyword")?;
        let names = expect_null_args(names, "conv cleared names")?;
        let mut removed = std::collections::HashSet::new();
        for name in names {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Err(error(TacticError::MalformedScript));
            };
            let local = goal
                .lctx
                .find_by_user_name(val)
                .filter(|local| !self.is_matrix_hypothesis(local))
                .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
            if !removed.insert(local.id.clone()) {
                return Err(failure(SourceInferenceError::UnknownConstant(val.clone())));
            }
        }
        if let Some(blocked) = self.clear_blocker(&goal, &removed)? {
            return Err(error(blocked));
        }
        let child = self.cleared_proof_goal(proof, goal, &removed)?;
        self.conv_goals.insert(child.id.clone());
        proof.work.push(Work::Goal(child));
        Ok(())
    }

    /// `simp …` and `dsimp …` (`Conv.evalSimp`, `Conv.evalDSimp`): `lhs` simplified, the result
    /// replacing it through `updateLhs` (or `changeLhs` when definitional).
    fn conv_simp(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
        definitional: bool,
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, config, discharger, only, rules] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        // The tactic's slots, with no location.
        let slots = vec![
            keyword.clone(),
            config.clone(),
            discharger.clone(),
            only.clone(),
            rules.clone(),
            Syntax::node(Name::str(Name::anonymous(), "null"), Vec::new()),
        ];
        let (_, _, lhs, _) = self.conv_sides(&goal)?;
        self.txn.lctx = goal.lctx.clone();
        let next = if definitional {
            let reduced = self.dsimp_expression_with(&slots, &lhs)?;
            self.conv_change_lhs(goal, reduced)?
        } else {
            match self.simp_expression_with(&slots, &lhs)? {
                (result, None) => self.conv_change_lhs(goal, result)?,
                (result, Some(equality)) => self.conv_update_lhs(goal, result, equality)?,
            }
        };
        proof.work.push(Work::Goal(next));
        Ok(())
    }

    /// `unfold f₁ … fₙ` (`Conv.evalUnfold`): each name unfolded in `lhs` in turn, never failing
    /// for want of an occurrence.
    fn conv_unfold(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "unfold", "conv unfold keyword")?;
        let names = expect_null_args(names, "conv unfold names")?;
        if names.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let mut goal = goal;
        for index in 0..names.len() {
            self.tick()?;
            let (_, _, lhs, _) = self.conv_sides(&goal)?;
            self.txn.lctx = goal.lctx.clone();
            let lhs = self.instantiate(&lhs)?;
            let (unfolded, _) = self.unfold_tactic_expression(&names[index..=index], &lhs)?;
            goal = self.conv_change_lhs(goal, unfolded)?;
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// `calc …` (`macro tk:"calc" steps:calcSteps : conv => `(conv| tactic => calc%$tk $steps)`).
    fn conv_calc(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        self.require_declared_tactic(&["Lean", "convCalc_"])?;
        let calculation =
            Syntax::node(Name::from_components(["Lean", "calcTactic"]), args.to_vec());
        self.conv_goals.remove(&goal.id);
        self.txn.lctx = goal.lctx.clone();
        let target = self.instantiate(&goal.target)?;
        let value = self.term(&calculation, Some(target))?;
        self.close_proof_goal(goal, value.value)?;
        let _ = proof;
        Ok(())
    }

    /// `zetaReduce e` (vendored `Lean/Meta/Transform.lean`): every `let` of `e` and every
    /// local definition it reads is replaced by its value, beta-reducing what that exposes.
    fn conv_zeta_reduce(&mut self, root: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let root = self.instantiate(root)?;
        // Every visited term stays alive, so an allocation identity is never reused.
        let mut done = std::collections::HashMap::<usize, Expr>::new();
        let mut keep = Vec::new();
        let mut work = vec![(root.clone(), false)];
        while let Some((term, exit)) = work.pop() {
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            self.tick()?;
            let children: Vec<Expr> = match term.node() {
                ExprNode::FVar { id } => self
                    .txn
                    .lctx
                    .find(id)
                    .and_then(|local| local.value.clone())
                    .into_iter()
                    .collect(),
                ExprNode::App { f, a } => vec![f.clone(), a.clone()],
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => vec![binder_type.clone(), body.clone()],
                ExprNode::LetE {
                    type_, value, body, ..
                } => vec![type_.clone(), value.clone(), body.clone()],
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => vec![expr.clone()],
                _ => Vec::new(),
            };
            if !exit
                && children
                    .iter()
                    .any(|c| !done.contains_key(&c.allocation_identity()))
            {
                work.push((term.clone(), true));
                for child in children.into_iter().rev() {
                    work.push((child, false));
                }
                continue;
            }
            let get = |e: &Expr| done[&e.allocation_identity()].clone();
            let result = match term.node() {
                ExprNode::App { f, a } => {
                    let reduced = Expr::app(get(f), get(a));
                    // `.beta e.getAppArgs` where the head was a local definition.
                    let (head, _) = spine(&term);
                    let unfolded = matches!(head.node(), ExprNode::FVar { id }
                        if self.txn.lctx.find(id).is_some_and(|local| local.value.is_some()));
                    if unfolded {
                        self.head_beta(reduced)?
                    } else {
                        reduced
                    }
                }
                ExprNode::Lam {
                    binder_name,
                    binder_info,
                    binder_type,
                    body,
                } => Expr::lam(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_info,
                    binder_type,
                    body,
                } => Expr::forall_e(
                    binder_name.clone(),
                    get(binder_type),
                    get(body),
                    *binder_info,
                ),
                ExprNode::LetE { value, body, .. } => {
                    let body = get(body);
                    let value = get(value);
                    self.substitute(&body, &value)?
                }
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), get(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, get(expr)),
                ExprNode::FVar { id } => {
                    match self.txn.lctx.find(id).and_then(|local| local.value.clone()) {
                        Some(value) => get(&value),
                        None => term.clone(),
                    }
                }
                _ => term.clone(),
            };
            done.insert(key, result);
            keep.push(term);
        }
        let reduced = done[&root.allocation_identity()].clone();
        self.instantiate(&reduced)
    }
}
