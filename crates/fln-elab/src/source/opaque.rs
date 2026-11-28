//! Checked logical witnesses for an omitted opaque value.
//!
//! The pin's `elabDefaultOrNonempty` (`Lean/Elab/Extra.lean:568–590`) tries
//! `Inhabited.default`, then `Classical.ofNonempty`. These are fixed constants,
//! not source names, and the second strategy does not grant executable code.
use super::*;
use fln_core::level::LevelView;
use std::collections::HashSet;

impl Context {
    pub(super) fn default_or_of_nonempty(
        &mut self,
        parts: &[Syntax],
        expected: Option<&Expr>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let [keyword, unsafe_slot] = parts else {
            return Err(failure(SourceInferenceError::Scope));
        };
        expect_atom(keyword, "default_or_ofNonempty%", "opaque witness builtin")?;
        let is_unsafe = match expect_null_args(unsafe_slot, "optional unsafe witness")? {
            [] => false,
            [keyword] => {
                expect_atom(keyword, "unsafe", "unsafe witness modifier")?;
                true
            }
            _ => return Err(failure(SourceInferenceError::Scope)),
        };
        let expected = expected.ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let expected = self.instantiate(expected)?;
        if matches!(expected.node(), ExprNode::MVar { .. }) {
            return Err(failure(SourceInferenceError::ExpectedType));
        }

        let mut missing = None;
        for components in [
            &["Inhabited", "default"][..],
            &["Classical", "ofNonempty"][..],
        ] {
            self.tick()?;
            let name = Name::from_components(components.iter().copied());
            if !self.txn.env.contains(&name) {
                missing.get_or_insert_with(|| failure(SourceInferenceError::UnknownConstant(name)));
                continue;
            }
            let saved = self.clone();
            let result = self.opaque_witness_application(&name, &expected);
            let spent = self.txn.budget.heartbeats_consumed;
            let next = self.next;
            *self = saved;
            self.txn.budget.heartbeats_consumed = spent;
            // Failed search never refunds work or reuses trial-local names.
            // Successful search exports only its fully instantiated witness.
            self.next = next;
            match result {
                Ok(term) => return Ok(term),
                Err(error)
                    if instances::nonmatch(&error)
                        || matches!(
                            error,
                            NatDefinitionElabError::Inference(
                                SourceInferenceError::InstanceSynthesisRequired(_)
                                    | SourceInferenceError::UnresolvedHoles { .. }
                                    | SourceInferenceError::UnresolvedUniverses
                            )
                        ) =>
                {
                    missing = Some(error)
                }
                // Exhaustion, broken metadata and kernel nonanswers are not
                // evidence that a different witness strategy should be tried.
                Err(error) => return Err(error),
            }
        }
        if is_unsafe {
            // The pin inserts a labeled sorry only after both searches fail.
            // This bounded profile requires a checked witness instead.
            return Err(NatDefinitionElabError::UnexpectedSyntax {
                expected: "an Inhabited or Nonempty instance for an unsafe omitted opaque value",
            });
        }
        Err(missing.unwrap_or_else(|| failure(SourceInferenceError::ExpectedType)))
    }

    /// `mkAppOptM f #[expected, none]` (`Lean/Meta/AppBuilder.lean:375–425`).
    /// The caller discards this scope even on success, as `withNewMCtxDepth`
    /// leaves no trial metavariables or unrelated synthetic obligations behind.
    fn opaque_witness_application(
        &mut self,
        name: &Name,
        expected: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.txn.mvars.restrict_assignments_to_new();
        self.txn.universes.restrict_assignments_to_new();
        self.equations.clear();
        self.stalled_flush = None;
        self.instance_goals.clear();
        self.instance_origins.clear();
        self.bound_metavars.clear();

        // AppBuilder names an admitted constant directly. A source recursive
        // placeholder or namespace resolution cannot redirect this operation.
        let info = self
            .txn
            .env
            .find(name)
            .cloned()
            .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(name.clone())))?;
        self.note_resolved_recursor(name, &info)?;
        let base = info.constant_val();
        let mut levels = Vec::new();
        for _ in &base.level_params {
            levels.push(self.level()?);
        }
        let function = Typed {
            value: Expr::const_(name.clone(), levels.clone()),
            type_: self.instantiate_params(&base.type_, &base.level_params, &levels)?,
        };
        let signature = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = signature.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let actual_sort = self
            .known_type(expected)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        self.check_scoped_equation(binder_type, &actual_sort)?;
        let remaining = self.substitute(body, expected)?;
        let remaining = self.whnf(&remaining)?;
        let ExprNode::ForallE {
            binder_type,
            body,
            binder_info: BinderInfo::InstImplicit,
            ..
        } = remaining.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        let registry = self
            .registry_cache
            .read_with_scopes(&self.txn.env, &self.source_scope.instance_scopes)
            .map_err(instances::registry_error)?;
        let dictionary = self.instance_hole(binder_type.clone())?;
        let ExprNode::MVar { id } = dictionary.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        let locals = self.txn.lctx.clone();
        let equations = std::mem::take(&mut self.equations);
        let result = self.search_instance(id.clone(), &registry);
        self.txn.lctx = locals;
        self.equations = equations;
        if result? != instances::SearchResult::Solved {
            return Err(self.instance_synthesis_failure(id)?);
        }
        let dictionary = self.instantiate(&dictionary)?;
        let type_ = self.substitute(body, &dictionary)?;
        self.check_scoped_equation(&type_, expected)?;
        let value = Expr::app(Expr::app(function.value, expected.clone()), dictionary);
        let value = self.instantiate(&value)?;
        let type_ = self.instantiate(&type_)?;
        self.require_opaque_witness_closed(&[value.clone(), type_.clone()])?;
        Ok(Typed { value, type_ })
    }

    /// `hasAssignableMVar` permits enclosing holes but not fresh holes that
    /// would escape the discarded application-builder scope. Walk shared DAGs
    /// once and charge each visit; declaration completion still resolves all
    /// enclosing term holes and generalizes its own universe parameters.
    fn require_opaque_witness_closed(
        &mut self,
        roots: &[Expr],
    ) -> Result<(), NatDefinitionElabError> {
        let mut expressions = roots.to_vec();
        let mut seen = HashSet::new();
        let mut levels = Vec::new();
        while let Some(expression) = expressions.pop() {
            self.tick()?;
            if (!expression.has_expr_mvar() && !expression.has_level_mvar())
                || !seen.insert(expression.allocation_identity())
            {
                continue;
            }
            match expression.node() {
                ExprNode::MVar { id } if self.txn.mvars.assignment_permitted(id) => {
                    return Err(failure(SourceInferenceError::UnresolvedHoles { count: 1 }));
                }
                ExprNode::Sort { level } => levels.push(level.clone()),
                ExprNode::Const { levels: args, .. } => levels.extend(args.iter().cloned()),
                ExprNode::App { f, a } => expressions.extend([f.clone(), a.clone()]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type.clone(), body.clone()]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_.clone(), value.clone(), body.clone()]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    expressions.push(expr.clone());
                }
                _ => {}
            }
        }
        let mut seen = HashSet::new();
        while let Some(level) = levels.pop() {
            self.tick()?;
            if !level.has_mvar() || !seen.insert(level.allocation_identity()) {
                continue;
            }
            match level.view() {
                LevelView::MVar(id) if self.txn.universes.assignment_permitted(id) => {
                    return Err(failure(SourceInferenceError::UnresolvedUniverses));
                }
                LevelView::Succ(inner) => levels.push(inner.clone()),
                LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                    levels.extend([a.clone(), b.clone()]);
                }
                _ => {}
            }
        }
        Ok(())
    }
}
