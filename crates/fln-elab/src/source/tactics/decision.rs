//! Constructive proof control over ordinary admitted Decidable dictionaries.
//! Case branches are checked functions; an evaluated dictionary never permits
//! an unselected source branch or written annotation to disappear.
use super::*;

pub(super) fn constant(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), levels)
}
pub(super) fn apps(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

/// The pin's `DeclNameGenerator` (vendored Lean/CoreM.lean:74-141) for the declaration being
/// elaborated: `withDeclNameForAuxNaming` sets the prefix to its name
/// (Lean/Elab/Term/TermElabM.lean:679-683), and a theorem's body runs in the child generator
/// `elabAsync` forks (`mkChild`, Lean/Elab/MutualDef.lean:1237-1243, 1314-1318).
#[derive(Clone, Debug)]
pub(in crate::source) struct AuxNames {
    prefix: Name,
    idx: u64,
    /// `parentIdxs`, the most recent fork first.
    parents: Vec<u64>,
}

impl AuxNames {
    pub(in crate::source) fn new(prefix: Name, child: bool) -> Self {
        Self {
            prefix,
            idx: 1,
            parents: if child { vec![1] } else { Vec::new() },
        }
    }

    /// `curr`: `<prefix>.<infix>`, then each parent index and the current one, outermost first,
    /// each appended to the last component as `_<index>` (`Name.appendIndexAfter`).
    fn current(&self, base: &Name) -> Name {
        self.parents
            .iter()
            .rev()
            .chain(std::iter::once(&self.idx))
            .fold(base.clone(), |name, index| match name.leaf_view() {
                LeafView::Str(last) => Name::str(name.parent(), format!("{last}_{index}")),
                _ => Name::str(name, format!("_{index}")),
            })
    }
}

/// The universe parameters of `expr` in the order the pin's `collectLevelParams` meets them
/// (vendored Lean/Util/CollectLevelParams.lean): function before argument, binder domain before
/// body, a constant's levels left to right; each name once.
fn level_params_in_order(
    expr: &Expr,
    mut tick: impl FnMut() -> Result<(), NatDefinitionElabError>,
) -> Result<Vec<Name>, NatDefinitionElabError> {
    use fln_core::level::LevelView;
    use std::collections::HashSet;

    let mut found = Vec::new();
    let mut seen_names = HashSet::new();
    let mut seen_expressions = HashSet::new();
    let mut expressions = vec![expr];
    while let Some(expression) = expressions.pop() {
        tick()?;
        if !expression.has_level_param()
            || !seen_expressions.insert(expression.allocation_identity())
        {
            continue;
        }
        let mut levels: Vec<&Level> = Vec::new();
        match expression.node() {
            ExprNode::Sort { level } => levels.push(level),
            ExprNode::Const {
                levels: arguments, ..
            } => levels.extend(arguments.iter().rev()),
            // Pushed in reverse, so the first child is visited first.
            ExprNode::App { f, a } => expressions.extend([a, f]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => expressions.extend([body, binder_type]),
            ExprNode::LetE {
                type_, value, body, ..
            } => expressions.extend([body, value, type_]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => expressions.push(expr),
            _ => {}
        }
        while let Some(level) = levels.pop() {
            tick()?;
            match level.view() {
                LevelView::Param(name) => {
                    if seen_names.insert(name.clone()) {
                        found.push(name.clone());
                    }
                }
                LevelView::Succ(inner) => levels.push(inner),
                LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                    levels.extend([right, left]);
                }
                _ => {}
            }
        }
    }
    Ok(found)
}

impl Context {
    pub(super) fn decide_proof_goal(
        &mut self,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let sort = self
            .known_type(&goal.target)?
            .ok_or_else(|| error(TacticError::ExpectedProposition))?;
        if !self.proof_types_match(&sort, &Expr::sort(Level::zero()))? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let proposition = self.instantiate(&goal.target)?;
        self.require_resolved(std::slice::from_ref(&proposition))?;
        // The pin's `preprocessPropToDecide` (Lean/Elab/Tactic/Decide.lean): let-bound locals are
        // unfolded, and a goal that still mentions a local is refused, even where a local
        // dictionary would decide it.
        if self.zeta_locals(&proposition)?.has_fvar() {
            return Err(error(TacticError::DecideFreeVariables));
        }
        let dictionary = self.decision_dictionary(&proposition)?;
        let computation = apps(
            self.decide_constant(),
            [proposition.clone(), dictionary.clone()],
        );
        if !self.decision_computes_true(computation.clone())? {
            return Err(error(TacticError::DecisionNotTrue));
        }
        let reflexive = apps(
            constant("Eq.refl", vec![Level::one()]),
            [constant("Bool", vec![]), constant("Bool.true", vec![])],
        );
        // `mkDecideProof` (vendored `Lean/Meta/AppBuilder.lean:593-598`): the reflexivity proof
        // carries its expected type, `@id (decide p = true) rfl` (`mkExpectedPropHint`); `#print`
        // shows it as `of_decide_eq_true (id (Eq.refl true))`. The seed dialect has no `id`.
        let reflexive = if self.txn.env.contains(&Name::from_components(["id"])) {
            let equation = apps(
                constant("Eq", vec![Level::one()]),
                [
                    constant("Bool", vec![]),
                    computation,
                    constant("Bool.true", vec![]),
                ],
            );
            apps(constant("id", vec![Level::zero()]), [equation, reflexive])
        } else {
            reflexive
        };
        let value = apps(
            constant("of_decide_eq_true", vec![]),
            [proposition, dictionary, reflexive],
        );
        // Both checkers must justify the Boolean conversion independently.
        // In particular the actual dictionary and its arguments are retained;
        // successful tactic conversion is not an admission certificate.
        self.close_proof_goal(goal, value)
    }

    /// `mkAuxDeclName infix` (vendored Lean/CoreM.lean:149-153): the generator's next name that
    /// no constant has, keeping the index it reached.
    fn aux_decl_name(&mut self, infix: &Name) -> Result<Name, NatDefinitionElabError> {
        let mut names = self
            .aux_names
            .clone()
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        let base = names.prefix.append_core(infix);
        loop {
            self.tick()?;
            let name = names.current(&base);
            if !self.txn.env.contains(&name) {
                self.aux_names = Some(names);
                return Ok(name);
            }
            names.idx = names
                .idx
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        }
    }

    /// `native_decide`, and `decide +native` (`evalDecideCore` with `native`, vendored
    /// Lean/Elab/Tactic/Decide.lean:70-100; `elabNativeDecideCore`, :57-68): the decision
    /// `Decidable.decide p inst` is compiled and run by the engine's evaluator (`nativeEqTrue`,
    /// Lean/Meta/Native.lean). When it returns `true`, the axiom
    /// `<decl>._native.<tactic>.ax_… : @Eq Bool (Decidable.decide p inst) true` is added and
    /// the goal closed by `of_decide_eq_true p inst ax`.
    pub(super) fn native_decide_proof_goal(
        &mut self,
        goal: ProofGoal,
        tactic: &str,
    ) -> Result<(), NatDefinitionElabError> {
        use crate::native::{NativeEvaluation, NativeEvaluationError};
        use fln_env::constants::{
            AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
        };

        let tactic_name = Name::from_components([tactic]);
        self.txn.lctx = goal.lctx.clone();
        let sort = self
            .known_type(&goal.target)?
            .ok_or_else(|| error(TacticError::ExpectedProposition))?;
        if !self.proof_types_match(&sort, &Expr::sort(Level::zero()))? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let proposition = self.instantiate(&goal.target)?;
        self.require_resolved(std::slice::from_ref(&proposition))?;
        // `preprocessPropToDecide`: let-bound locals are unfolded, and the unfolded proposition
        // is the one decided; one that still mentions a local is refused.
        let proposition = self.zeta_locals(&proposition)?;
        if proposition.has_fvar() {
            return Err(error(TacticError::DecideFreeVariables));
        }
        let unavailable = || {
            failure(SourceInferenceError::NativeEvaluation(
                NativeEvaluationError::Unavailable,
            ))
        };
        let provider = self.native.clone().ok_or_else(unavailable)?;
        if self.aux_names.is_none() {
            return Err(unavailable());
        }
        // `mkDecide` (vendored Lean/Meta/AppBuilder.lean:589-590).
        let dictionary = self.decision_dictionary(&proposition)?;
        let dictionary = self.instantiate(&dictionary)?;
        let decision = apps(
            self.decide_constant(),
            [proposition.clone(), dictionary.clone()],
        );
        // `nativeEqTrue` (Lean/Meta/Native.lean:38-41): a dictionary from the local context
        // leaves a local in the decision.
        if decision.has_fvar() || decision.has_expr_mvar() || decision.has_level_mvar() {
            return Err(error(TacticError::NativeDecideOpen {
                tactic: tactic_name,
                metavariables: !decision.has_fvar(),
                decision,
            }));
        }
        let levels = level_params_in_order(&decision, || self.tick())?;
        let native = Name::from_components(["_native", tactic]);
        let definition_name =
            self.aux_decl_name(&native.append_core(&Name::from_components(["decl"])))?;
        let definition = DefinitionVal {
            base: ConstantVal {
                name: definition_name.clone(),
                level_params: levels.clone(),
                type_: constant("Bool", vec![]),
            },
            value: decision.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![definition_name],
        };
        match provider.0.evaluate_bool(&definition) {
            NativeEvaluation::Value(true) => {}
            NativeEvaluation::Value(false) => {
                return Err(error(TacticError::NativeDecideFalse {
                    tactic: tactic_name,
                    proposition,
                }));
            }
            NativeEvaluation::Unsupported(reason) => {
                return Err(failure(SourceInferenceError::NativeEvaluation(
                    NativeEvaluationError::Unsupported(reason),
                )));
            }
            NativeEvaluation::Inconclusive(reason) => {
                return Err(failure(SourceInferenceError::NativeEvaluationInconclusive(
                    Box::new(reason),
                )));
            }
            NativeEvaluation::InternalFault(fault) => {
                return Err(failure(SourceInferenceError::NativeEvaluation(
                    NativeEvaluationError::Fault(fault),
                )));
            }
        }
        let axiom_name = self.aux_decl_name(&native.append_core(&Name::from_components(["ax"])))?;
        let axiom = AxiomVal {
            base: ConstantVal {
                name: axiom_name.clone(),
                level_params: levels.clone(),
                type_: apps(
                    constant("Eq", vec![Level::one()]),
                    [
                        constant("Bool", vec![]),
                        decision,
                        constant("Bool.true", vec![]),
                    ],
                ),
            },
            is_unsafe: false,
        };
        // Later elaboration in this declaration sees the axiom, as the pin's `addDecl` makes it
        // visible. It is admitted, through both checkers, before the declaration citing it.
        self.txn.env = self
            .txn
            .env
            .add_decl(ConstantInfo::Axiom(axiom.clone()))
            .map_err(|_| failure(SourceInferenceError::Scope))?;
        self.native_axioms.push(Declaration::Axiom(axiom));
        // `addDecl` checks the axiom in a task forked from the generator when `Elab.async`
        // holds (vendored Lean/AddDecl.lean:167-169), which advances its index (`mkChild`).
        if self
            .txn
            .options
            .get_bool(&Name::from_components(["Elab", "async"]), true)
            && let Some(names) = &mut self.aux_names
        {
            names.idx = names
                .idx
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        }
        let evidence = Expr::const_(axiom_name, levels.into_iter().map(Level::param).collect());
        let value = apps(
            constant("of_decide_eq_true", vec![]),
            [proposition, dictionary, evidence],
        );
        self.close_proof_goal(goal, value)
    }

    /// `decide`'s configuration (`Lean.Parser.Tactic.DecideConfig`): whether it asks for
    /// `+native`. Only `native` is read; any other item stays the typed refusal it was.
    pub(super) fn decide_native_config(
        &mut self,
        config: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        let [items] = expect_node(
            config,
            &parser_kind(&["Tactic", "optConfig"]),
            1,
            "decide config",
        )?
        else {
            return Err(error(TacticError::MalformedScript));
        };
        let native_field = Name::from_components(["native"]);
        let mut native = false;
        for item in expect_null_args(items, "decide config items")? {
            self.tick()?;
            let [item] = expect_node(
                item,
                &parser_kind(&["Tactic", "configItem"]),
                1,
                "decide config item",
            )?
            else {
                return Err(error(TacticError::MalformedScript));
            };
            let Syntax::Node { kind, args, .. } = item else {
                return Err(error(TacticError::MalformedScript));
            };
            native = match args.as_slice() {
                [
                    Syntax::Atom { val: sign, .. },
                    Syntax::Ident { val: field, .. },
                ] if field == &native_field
                    && ((kind == &parser_kind(&["Tactic", "posConfigItem"]) && sign == "+")
                        || (kind == &parser_kind(&["Tactic", "negConfigItem"]) && sign == "-")) =>
                {
                    sign == "+"
                }
                [
                    Syntax::Atom { val: open, .. },
                    Syntax::Ident { val: field, .. },
                    Syntax::Atom { val: assign, .. },
                    Syntax::Ident { val: value, .. },
                    Syntax::Atom { val: close, .. },
                ] if kind == &parser_kind(&["Tactic", "valConfigItem"])
                    && open == "("
                    && assign == ":="
                    && close == ")"
                    && field == &native_field
                    && (value == &Name::from_components(["true"])
                        || value == &Name::from_components(["false"])) =>
                {
                    value == &Name::from_components(["true"])
                }
                _ => return Err(error(TacticError::MalformedScript)),
            };
        }
        Ok(native)
    }

    /// `expr` with every let-bound local of the current context replaced by its value (the pin's
    /// `zetaReduce`). One pass from the newest local suffices: a value mentions only older ones.
    fn zeta_locals(&mut self, expr: &Expr) -> Result<Expr, NatDefinitionElabError> {
        let mut current = expr.clone();
        for local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            let Some(value) = &local.value else {
                continue;
            };
            let abstracted = current
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            if abstracted.has_loose_bvar(0) {
                let value = self.instantiate(value)?;
                current = abstracted
                    .subst_loose(0, std::slice::from_ref(&value))
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
            }
        }
        Ok(current)
    }

    /// The Boolean decision the tactic evaluates. The pin builds it with `mkDecide`,
    /// whose head is `Decidable.decide` (vendored Lean/Meta/AppBuilder.lean:589-590); a
    /// plain `decide` exists there only as an `export` alias, which is no
    /// constant at all. The frozen seed dialect has no `Decidable.decide` and
    /// names the same function `decide`, so the seed spelling is used only where
    /// the pin's constant is absent; it goes when the seed is retired
    /// (franken_lean-z8j.1.8).
    pub(in crate::source) fn decide_constant(&self) -> Expr {
        let pinned = Name::from_components(["Decidable", "decide"]);
        if self.txn.env.contains(&pinned) {
            Expr::const_(pinned, vec![])
        } else {
            constant("decide", vec![])
        }
    }

    /// Recover the universe telescope of a closed conversion query, including
    /// levels occurring only in local binder types or let-bound dictionaries.
    /// Expression closure does not close universe parameters. In particular,
    /// passing an empty telescope after closing a polymorphic local context
    /// makes a valid decision query look like an out-of-scope kernel term.
    ///
    /// This is syntax collection, not universe inference or proof admission.
    /// Callers must instantiate and check for unresolved holes first; the final
    /// declaration still has to pass both ordinary checkers at its own telescope.
    fn decision_level_params(
        &mut self,
        terms: &[&Expr],
    ) -> Result<Vec<Name>, NatDefinitionElabError> {
        use fln_core::level::LevelView;
        use std::collections::{BTreeSet, HashSet};

        let mut parameters = BTreeSet::new();
        let mut expressions = terms.to_vec();
        let mut seen_expressions = HashSet::new();
        let mut levels = Vec::new();
        while let Some(expression) = expressions.pop() {
            self.tick()?;
            if !seen_expressions.insert(expression.allocation_identity()) {
                continue;
            }
            match expression.node() {
                ExprNode::Sort { level } => levels.push(level),
                ExprNode::Const {
                    levels: arguments, ..
                } => levels.extend(arguments),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    expressions.extend([binder_type, body]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    expressions.extend([type_, value, body]);
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    expressions.push(expr);
                }
                _ => {}
            }
        }
        let mut seen_levels = HashSet::new();
        while let Some(level) = levels.pop() {
            self.tick()?;
            if !seen_levels.insert(std::ptr::from_ref(level)) {
                continue;
            }
            match level.view() {
                LevelView::Param(name) => {
                    parameters.insert(name.clone());
                }
                LevelView::Succ(inner) => levels.push(inner),
                LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                    levels.extend([left, right]);
                }
                _ => {}
            }
        }
        Ok(parameters.into_iter().collect())
    }

    /// Source WHNF and the pattern unifier intentionally do not implement the
    /// complete kernel evaluator. Close the relevant local telescope and ask
    /// the existing K1 conversion query; this is tactic selection, not admission.
    /// Final admission retains the unmodified dictionary and checks both seats.
    fn decision_computes_true(
        &mut self,
        computation: Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.decision_computes(computation, "Bool.true")
    }

    /// The `false` direction of the same evaluation, for the pin's
    /// `contradiction` decide arm (Lean/Meta/Tactic/Contradiction.lean:199):
    /// a closed hypothesis whose decision computes `false` is refutable.
    pub(super) fn decision_computes_false(
        &mut self,
        computation: Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.decision_computes(computation, "Bool.false")
    }

    fn decision_computes(
        &mut self,
        mut computation: Expr,
        constructor: &str,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut truth = constant(constructor, vec![]);
        let mut needed = self.elimination_reads(&computation)?;
        for mut local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            if !needed.remove(&local.id) {
                continue;
            }
            local.type_ = self.instantiate(&local.type_)?;
            needed.extend(self.elimination_reads(&local.type_)?);
            if let Some(value) = &local.value {
                let value = self.instantiate(value)?;
                needed.extend(self.elimination_reads(&value)?);
                local.value = Some(value);
            }
            computation = self.close_equality_binder(&local, computation, true)?;
            truth = self.close_equality_binder(&local, truth, true)?;
        }
        if !needed.is_empty() || computation.has_fvar() || truth.has_fvar() {
            return Err(failure(SourceInferenceError::Scope));
        }
        self.require_resolved(&[computation.clone(), truth.clone()])?;
        let parameters = self.decision_level_params(&[&computation, &truth])?;
        let budget = &self.txn.budget;
        let remaining = if budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            budget
                .max_heartbeats
                .saturating_sub(budget.heartbeats_consumed)
        };
        let kernel = self
            .kernel
            .narrowed(self.kernel.steps.min(remaining), self.kernel.depth);
        match fln_kernel::check_def_eq(&self.txn.env, &parameters, &computation, &truth, kernel) {
            Outcome::Complete(verdict) => {
                let consumed = match &verdict {
                    Verdict::Accepted { consumption } | Verdict::Rejected { consumption, .. } => {
                        consumption.steps_used
                    }
                };
                self.txn.budget.heartbeats_consumed = self
                    .txn
                    .budget
                    .heartbeats_consumed
                    .checked_add(consumed)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                // Charge successful and failed conversions alike. Backtracking
                // may restore proof state but must not refund evaluation work.
                self.tick()?;
                Ok(verdict.is_accepted())
            }
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }

    pub(in crate::source) fn decision_dictionary(
        &mut self,
        proposition: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let domain = Expr::app(constant("Decidable", vec![]), proposition.clone());
        let dictionary = self.instance_hole(domain)?;
        self.resolve_instances(false)?;
        let dictionary = self.instantiate(&dictionary)?;
        // Resolve this tactic's dictionary only. Unrelated outer instance goals
        // may still depend on later fields or explicitly unsolved proof holes.
        if dictionary.has_expr_mvar() || dictionary.has_level_mvar() {
            return Err(failure(SourceInferenceError::InstanceSynthesisRequired));
        }
        Ok(dictionary)
    }

    fn decision_branch(
        &mut self,
        name: &Name,
        domain: Expr,
        target: &Expr,
    ) -> Result<(Expr, ProofGoal), NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let function_type = Expr::forall_e(
            name.clone(),
            domain.clone(),
            target.clone(),
            BinderInfo::Default,
        );
        let (value, mut goal) = self.proof_goal(function_type)?;
        let id = FVarId(self.fresh_name()?);
        self.txn
            .lctx
            .add_param(id.clone(), name.clone(), domain, BinderInfo::Default);
        goal.target = target.clone();
        goal.introduced
            .push(self.txn.lctx.find(&id).expect("case evidence").clone());
        goal.lctx = self.txn.lctx.clone();
        self.txn.lctx = saved;
        Ok((value, goal))
    }

    pub(in crate::source) fn split_decision_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        name: Name,
        proposition: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        if !self.proof_types_match(&proposition.type_, &Expr::sort(Level::zero()))? {
            return Err(error(TacticError::ExpectedProposition));
        }
        let proposition = self.instantiate(&proposition.value)?;
        // The pin's by_cases macro opens Classical while elaborating the
        // dependent conditional (Init/ByCases.lean). Activate its *registered*
        // scoped instances rather than manufacturing a propDecidable call:
        // ordinary priorities, local dictionaries and erasures still matter.
        // The scope ends before either branch, including after a failed search.
        self.tick()?;
        let mut scopes = self.source_scope.instance_scopes.clone();
        scopes
            .activate(&self.txn.env, &Name::from_components(["Classical"]))
            .map_err(instances::registry_error)?;
        let saved = std::mem::replace(&mut self.source_scope.instance_scopes, scopes);
        let dictionary = self.decision_dictionary(&proposition);
        self.source_scope.instance_scopes = saved;
        let dictionary = dictionary?;
        let target_type = self
            .known_type(&goal.target)?
            .ok_or_else(|| error(TacticError::ExpectedGoal))?;
        let universe = self.sort_level(&Typed {
            value: goal.target.clone(),
            type_: target_type,
        })?;
        let (yes, yes_goal) = self.decision_branch(&name, proposition.clone(), &goal.target)?;
        let negative = Expr::app(constant("Not", vec![]), proposition.clone());
        let (no, no_goal) = self.decision_branch(&name, negative, &goal.target)?;
        let value = apps(
            constant("dite", vec![universe]),
            [goal.target.clone(), proposition, dictionary, yes, no],
        );
        // The parent closes only after both branches, retaining even unused
        // branch obligations. LIFO publication exposes the positive case first.
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(no_goal));
        proof.work.push(Work::Goal(yes_goal));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }

    #[test]
    fn decision_collects_binder_and_constant_universes_from_both_endpoints() {
        let a = Name::from_components(["a"]);
        let z = Name::from_components(["z"]);
        let left = Expr::forall_e(
            Name::anonymous(),
            Expr::sort(Level::param(z.clone())),
            Expr::sort(Level::param(a.clone())),
            BinderInfo::Default,
        );
        let right = constant("polymorphic", vec![Level::param(z.clone())]);
        assert_eq!(
            context().decision_level_params(&[&left, &right]).unwrap(),
            vec![a, z]
        );
    }

    #[test]
    fn decision_collects_universes_used_only_by_a_let_value() {
        let u = Name::from_components(["u"]);
        let term = Expr::let_e(
            Name::anonymous(),
            Expr::sort(Level::one()),
            constant("dictionary", vec![Level::param(u.clone())]),
            Expr::sort(Level::zero()),
            false,
        );
        assert_eq!(context().decision_level_params(&[&term]).unwrap(), vec![u]);
    }

    #[test]
    fn decision_universe_collection_preserves_sharing_and_charges_work() {
        let u = Name::from_components(["u"]);
        let mut term = Expr::sort(Level::param(u.clone()));
        for _ in 0..24 {
            term = Expr::app(term.clone(), term);
        }
        let mut context = context();
        context.txn.budget.max_heartbeats = 200;
        assert_eq!(context.decision_level_params(&[&term]).unwrap(), vec![u]);
        assert!(context.txn.budget.heartbeats_consumed > 0);
        assert!(context.txn.budget.heartbeats_consumed < 200);
    }

    fn n(name: &str) -> Name {
        Name::from_components(name.split('.'))
    }

    /// The pin's names, measured with v4.32.0: `t1._native.native_decide.ax_1_1` for a theorem
    /// elaborated in a forked generator, `d1._native.native_decide.ax_1` for a definition.
    #[test]
    fn aux_names_append_parent_indices_before_their_own() {
        let base = n("t1._native.native_decide.ax");
        let mut child = AuxNames::new(n("t1"), true);
        assert_eq!(child.current(&base), n("t1._native.native_decide.ax_1_1"));
        child.idx = 3;
        assert_eq!(child.current(&base), n("t1._native.native_decide.ax_1_3"));
        let plain = AuxNames::new(n("d1"), false);
        assert_eq!(
            plain.current(&n("d1._native.decide.ax")),
            n("d1._native.decide.ax_1")
        );
    }

    #[test]
    fn aux_decl_name_skips_names_the_environment_has() {
        let taken = n("t._native.native_decide.ax_1");
        let env = Environment::new()
            .add_decl(fln_env::constants::ConstantInfo::Axiom(
                fln_env::constants::AxiomVal {
                    base: fln_env::constants::ConstantVal {
                        name: taken,
                        level_params: vec![],
                        type_: Expr::sort(Level::zero()),
                    },
                    is_unsafe: false,
                },
            ))
            .unwrap();
        let mut context = Context::new(&env, Budget::for_stack_bytes(2 * 1024 * 1024));
        context.aux_names = Some(AuxNames::new(n("t"), false));
        let infix = n("_native.native_decide.ax");
        assert_eq!(
            context.aux_decl_name(&infix).unwrap(),
            n("t._native.native_decide.ax_2")
        );
        // The generator keeps the index it reached.
        assert_eq!(
            context
                .aux_decl_name(&n("_native.native_decide.decl"))
                .unwrap(),
            n("t._native.native_decide.decl_2")
        );
        // No generator: the declaration's route did not name one.
        context.aux_names = None;
        assert!(context.aux_decl_name(&infix).is_err());
    }

    #[test]
    fn level_params_are_collected_in_the_pins_order_once_each() {
        let (u, v, w) = (n("u"), n("v"), n("w"));
        let head = constant(
            "f",
            vec![
                Level::param(v.clone()),
                Level::max(Level::param(u.clone()), Level::param(v.clone())).unwrap(),
            ],
        );
        let term = Expr::app(
            head,
            Expr::forall_e(
                Name::anonymous(),
                Expr::sort(Level::param(w.clone()).succ().unwrap()),
                Expr::sort(Level::param(u.clone())),
                BinderInfo::Default,
            ),
        );
        let mut ticks = 0;
        let found = level_params_in_order(&term, || {
            ticks += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(found, vec![v, u, w]);
        assert!(ticks > 0);
    }

    #[test]
    fn decision_universe_collection_cannot_bypass_the_source_budget() {
        let mut context = context();
        context.txn.budget.max_heartbeats = 1;
        let term = Expr::sort(Level::param(Name::from_components(["u"])));
        assert!(matches!(
            context.decision_level_params(&[&term]),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
