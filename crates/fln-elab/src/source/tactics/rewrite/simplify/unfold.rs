//! Selected-definition expansion and beta/zeta normalization on a shared DAG.
//! Only the named safe definition or local let is unfolded. Its actual body is
//! instantiated at each occurrence's universe arguments, never at guessed levels.

use super::*;
use fln_env::constants::{ConstantInfo, DefinitionVal};

#[derive(Clone)]
pub(super) enum Selection {
    Global(DefinitionVal),
    Local(FVarId, Expr),
}

pub(super) enum UnfoldResult {
    NotDefinition,
    Unchanged,
    Changed(Expr),
}

impl Context {
    pub(super) fn unfold_simp_rule(
        &mut self,
        rule: &SimpRule<'_>,
        target: &Expr,
    ) -> Result<UnfoldResult, NatDefinitionElabError> {
        // A `dsimproc`'s rewrite is definitional, as an unfolding is (`simproc.rs`).
        if let SimpRule::Simprocs(set) = rule {
            return self.simp_procedure_unfold(target, *set);
        }
        match self.simp_unfold_selection_for_rule(rule)? {
            Some(selection) => self.unfold_simp_selection(target, &selection),
            None => Ok(UnfoldResult::NotDefinition),
        }
    }

    /// Whether `simp_unfold_selection_for_rule` may select a definition for `rule`, or
    /// report its unknown constant. Deciding it charges nothing: a registered
    /// theorem and a local never unfold.
    pub(super) fn simp_rule_may_unfold(&self, rule: &SimpRule<'_>) -> bool {
        match rule {
            SimpRule::Explicit(_) => true,
            SimpRule::Local(_) | SimpRule::Arith | SimpRule::Decide | SimpRule::Simprocs(_) => {
                false
            }
            SimpRule::Global(rule) => {
                rule.proof.is_none()
                    && match self.txn.env.find(&rule.declaration) {
                        Some(ConstantInfo::Defn(definition)) => {
                            definition.safety == DefinitionSafety::Safe && !rule.reverse
                        }
                        Some(_) => false,
                        None => true,
                    }
            }
        }
    }

    pub(super) fn simp_unfold_selection_for_rule(
        &mut self,
        rule: &SimpRule<'_>,
    ) -> Result<Option<Selection>, NatDefinitionElabError> {
        match rule {
            SimpRule::Explicit(rule) => {
                self.simp_unfold_selection_for_term(rule.syntax, rule.reverse)
            }
            SimpRule::Local(_) | SimpRule::Arith | SimpRule::Decide | SimpRule::Simprocs(_) => {
                Ok(None)
            }
            SimpRule::Global(rule) => {
                self.tick()?;
                if rule.proof.is_some() {
                    return Ok(None);
                }
                match self.txn.env.find(&rule.declaration) {
                    Some(ConstantInfo::Defn(definition))
                        if definition.safety == DefinitionSafety::Safe && !rule.reverse =>
                    {
                        Ok(Some(Selection::Global(definition.clone())))
                    }
                    Some(_) => Ok(None),
                    None => Err(failure(SourceInferenceError::UnknownConstant(
                        rule.declaration.clone(),
                    ))),
                }
            }
        }
    }

    /// Selection respects local shadowing. A local proof/parameter with this
    /// name must not accidentally request expansion of a same-named global.
    /// Only a bare identifier is an unfolding request, as at the pin: `(f)` is a
    /// term rule (`simp_rule_global`).
    pub(super) fn unfold_simp_term(
        &mut self,
        syntax: &Syntax,
        reverse: bool,
        target: &Expr,
    ) -> Result<UnfoldResult, NatDefinitionElabError> {
        match self.simp_unfold_selection_for_term(syntax, reverse)? {
            Some(selection) => self.unfold_simp_selection(target, &selection),
            None => Ok(UnfoldResult::NotDefinition),
        }
    }

    fn simp_unfold_selection_for_term(
        &mut self,
        syntax: &Syntax,
        reverse: bool,
    ) -> Result<Option<Selection>, NatDefinitionElabError> {
        self.tick()?;
        let Syntax::Ident { val: name, .. } = syntax else {
            return Ok(None);
        };
        // The public IH remains a conditional parameter via a checked alias.
        // It was never an unfolding request. Avoid reconstructing its entire
        // dependent type just to rediscover that fact at every simp occurrence.
        if self.specialized_induction_rule(syntax)?.is_some() {
            return Ok(None);
        }
        let resolved = if self.txn.lctx.find_by_user_name(name).is_some() {
            name.clone()
        } else {
            self.resolve_source_name(name)?
                .unwrap_or_else(|| name.clone())
        };
        let name = &resolved;
        let selection = if let Some(local) = self
            .txn
            .lctx
            .decls()
            .iter()
            .rev()
            .find(|l| &l.user_name == name)
            .cloned()
        {
            // A checked local theorem remains a rewrite rule even when its
            // evidence is held in a let. Treating it as an unfolding request
            // would never apply its equality to the goal (the goal need not
            // contain the proof variable at all).
            if let Some(sort) = self.known_type(&local.type_)?
                && !sort.has_expr_mvar()
                && !sort.has_level_mvar()
                && self.proof_types_match(&sort, &Expr::sort(Level::zero()))?
            {
                return Ok(None);
            }
            match &local.value {
                Some(value) => Selection::Local(local.id.clone(), value.clone()),
                None => return Ok(None),
            }
        } else {
            match self.txn.env.find(name) {
                Some(ConstantInfo::Defn(definition))
                    if definition.safety == DefinitionSafety::Safe =>
                {
                    Selection::Global(definition.clone())
                }
                _ => return Ok(None),
            }
        };
        if reverse {
            return Err(error(TacticError::MalformedScript));
        }
        Ok(Some(selection))
    }

    fn unfold_simp_selection(
        &mut self,
        target: &Expr,
        selection: &Selection,
    ) -> Result<UnfoldResult, NatDefinitionElabError> {
        let result = self.simp_unfold_selected(target, Some(selection))?;
        // Unfolding normalizes every node it rebuilds, as the pin's simp beta- and
        // zeta-reduces. Removing a source ascription's `let` is not progress: the pin's
        // term has none, so `simp` on `(10 : USize) + 2 = x` makes no progress there.
        if self.simp_same_up_to_ascriptions(&result, target)? {
            Ok(UnfoldResult::Unchanged)
        } else {
            Ok(UnfoldResult::Changed(result))
        }
    }

    /// Equality after removing source ascriptions. This elaborator keeps `(e : T)` as
    /// `let _ : T := e; _` so the kernel checks the annotation; the pin's term has no `let`
    /// there. Its zeta reduction is therefore not progress: `dsimp only` on
    /// `(x : Nat) + 2 = 7`, or `simp` on `(10 : USize) + 2 = x`, makes none at the pin.
    pub(super) fn simp_same_up_to_ascriptions(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if self.rewrite_same(left, right)? {
            return Ok(true);
        }
        let left = self.without_source_ascriptions(left)?;
        let right = self.without_source_ascriptions(right)?;
        self.rewrite_same(&left, &right)
    }

    /// `expr` with every `let _ : T := e; _` that a non-`show` ascription elaborates to
    /// replaced by `e`.
    pub(in crate::source) fn without_source_ascriptions(
        &mut self,
        root: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut retained = Vec::new();
        let mut work = vec![(root.clone(), false)];
        while let Some((term, exit)) = work.pop() {
            self.tick()?;
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                work.push((term.clone(), true));
                work.extend(
                    children(&term)
                        .into_iter()
                        .rev()
                        .flatten()
                        .map(|child| (child.clone(), false)),
                );
                continue;
            }
            let child = |term: &Expr| done[&term.allocation_identity()].clone();
            let rebuilt = match term.node() {
                ExprNode::LetE {
                    decl_name,
                    value,
                    body,
                    non_dep: false,
                    ..
                } if decl_name.is_anonymous()
                    && matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                {
                    child(value)
                }
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
            };
            done.insert(key, rebuilt);
            // Keep every visited term alive: an allocation identity must not be reused.
            retained.push(term);
        }
        Ok(done[&root.allocation_identity()].clone())
    }

    /// `target` beta-, zeta- and iota-reduced at every node, as the pin's simp reduces before
    /// rewriting (`Simp.Config.beta`, `zeta`, `iota`, `proj`), or `None` where that changes
    /// nothing but source ascriptions. This happened here only while unfolding a selected
    /// definition, so `simp only []` made no progress on `(fun z => z) x + 2 = y`.
    pub(super) fn simp_normalize(
        &mut self,
        target: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let result = self.simp_unfold_selected(target, None)?;
        if self.simp_same_up_to_ascriptions(&result, target)? {
            Ok(None)
        } else {
            Ok(Some(result))
        }
    }

    pub(super) fn simp_unfold_selected(
        &mut self,
        root: &Expr,
        selection: Option<&Selection>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut work = vec![(root, false)];
        while let Some((term, exit)) = work.pop() {
            self.tick()?;
            let key = term.allocation_identity();
            if done.contains_key(&key) {
                continue;
            }
            if !exit {
                work.push((term, true));
                work.extend(
                    children(term)
                        .into_iter()
                        .rev()
                        .flatten()
                        .map(|child| (child, false)),
                );
                continue;
            }
            let child = |term: &Expr| done[&term.allocation_identity()].clone();
            let rebuilt = match term.node() {
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
                ExprNode::FVar { id } => match selection {
                    Some(Selection::Local(selected, value)) if selected == id => value.clone(),
                    _ => term.clone(),
                },
                _ => term.clone(),
            };
            let rebuilt = match selection {
                Some(Selection::Global(definition)) => {
                    self.unfold_selected_definition(&rebuilt, definition)?
                }
                _ => rebuilt,
            };
            // Metadata is kept, as the pin's `Simp.visit` keeps it (`mkMData m r.expr`): its child is
            // already reduced, and reducing the node again would only strip the annotation. A
            // `borrowed` mark that `Nat.add`'s `@&` binder leaves on a numeral's type then counted
            // as progress where the pin's `simp only` makes none.
            let normalized = if matches!(rebuilt.node(), ExprNode::MData { .. }) {
                rebuilt
            } else {
                self.simp_beta_zeta(&rebuilt)?
            };
            done.insert(key, normalized);
        }
        Ok(done
            .remove(&root.allocation_identity())
            .expect("selected unfolding finishes the root"))
    }

    /// Pure reduction only: no global delta or local-context lookup. Admitted
    /// recursors must reduce here so unfolding a selected recursive definition
    /// exposes the recursive calls to its induction hypotheses.
    fn simp_beta_zeta(&mut self, root: &Expr) -> Result<Expr, NatDefinitionElabError> {
        self.whnf_with_transparency(root, UnificationTransparency::None, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unfolding_selects_only_the_requested_global_even_below_binders() {
        let name = Name::from_components(["selected"]);
        let other = Name::from_components(["unselected"]);
        let ty = Expr::sort(Level::one());
        let body = Expr::lam(
            Name::anonymous(),
            ty.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        );
        let definition = DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: Vec::new(),
                type_: Expr::forall_e(
                    Name::anonymous(),
                    ty.clone(),
                    ty.clone(),
                    BinderInfo::Default,
                ),
            },
            value: body,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        };
        let selected = Expr::const_(name, Vec::new());
        let untouched = Expr::const_(other, Vec::new());
        let input = Expr::lam(
            Name::anonymous(),
            ty.clone(),
            Expr::app(
                untouched.clone(),
                Expr::app(selected, Expr::bvar(0).unwrap()),
            ),
            BinderInfo::Default,
        );
        let expected = Expr::lam(
            Name::anonymous(),
            ty,
            Expr::app(untouched, Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(1024 * 1024));
        assert_eq!(
            ctx.simp_unfold_selected(&input, Some(&Selection::Global(definition)))
                .unwrap(),
            expected
        );
    }

    #[test]
    fn selected_local_unfolding_preserves_shared_dags_and_respects_work_limits() {
        let id = FVarId(Name::from_components(["selected"]));
        let value = Expr::sort(Level::zero());
        let mut input = Expr::fvar(id.clone());
        for _ in 0..40 {
            input = Expr::app(input.clone(), input);
        }
        let selection = Selection::Local(id, value);
        let mut ctx = Context::new(&Environment::new(), Budget::for_stack_bytes(1024 * 1024));
        let mut output = ctx.simp_unfold_selected(&input, Some(&selection)).unwrap();
        for _ in 0..40 {
            let ExprNode::App { f, a } = output.node() else {
                panic!("application retained");
            };
            assert_eq!(f.allocation_identity(), a.allocation_identity());
            output = f.clone();
        }
        ctx.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            ctx.simp_unfold_selected(&input, Some(&selection)),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
