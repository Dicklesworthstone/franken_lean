//! Coercion insertion uses the ordinary instance engine and produces ordinary
//! projection applications. Neither finding a path nor reconstructing its type
//! grants proof authority: the final declaration still needs kernel admission.
use super::instances::{nonmatch, registry_error};
use super::*;
use crate::instances::InstanceRegistry;

impl Context {
    /// Expected function types expose domain/codomain universe constraints that
    /// a single sort equality can hide behind max/imax. Generate them inside
    /// the same speculative context as ordinary conversion, before coercions.
    fn constrain_expected_type(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        self.constrain_telescope_universes(actual, expected)?;
        self.constrain_type(actual, expected)
    }

    fn has_coercion_class(&self, name: &str) -> Result<bool, NatDefinitionElabError> {
        let name = Name::from_components([name]);
        if !self.txn.env.contains(&name) {
            return Ok(false);
        }
        Ok(InstanceRegistry::read(&self.txn.env)
            .map_err(registry_error)?
            .is_class(&name))
    }

    /// Probe one isolated equation without publishing a failed assignment or
    /// consuming the caller's unrelated suspended source equations.
    fn coercion_eq(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        // Keep named types when an unknown is assigned, just as constrain_type
        // does. Eager alias unfolding here would change later class selection.
        let actual = if matches!(expected.node(), ExprNode::MVar { .. })
            && matches!(
                actual.node(),
                ExprNode::Const { .. } | ExprNode::FVar { .. }
            ) {
            actual
        } else {
            self.whnf(&actual)?
        };
        let expected = if matches!(actual.node(), ExprNode::MVar { .. }) {
            expected
        } else {
            self.whnf(&expected)?
        };
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        match self.txn.unify(&actual, &expected, budget) {
            Ok(_) => Ok(true),
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if nonmatch(&error) {
                    self.coercion_kernel_eq(actual, expected)
                } else {
                    Err(error)
                }
            }
        }
    }

    /// The pattern unifier does not implement full arithmetic, proof
    /// irrelevance or polymorphic conversion. Before inserting a potentially
    /// observable conversion, ask the existing kernel equality query on closed
    /// terms. This grants no declaration authority and retains spent work.
    fn coercion_kernel_eq(
        &mut self,
        mut left: Expr,
        mut right: Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        if left.has_expr_mvar()
            || left.has_level_mvar()
            || right.has_expr_mvar()
            || right.has_level_mvar()
        {
            return Ok(false);
        }
        let mut needed = self.elimination_reads(&left)?;
        needed.extend(self.elimination_reads(&right)?);
        for local in self.txn.lctx.decls().to_vec().into_iter().rev() {
            self.tick()?;
            if !needed.remove(&local.id) {
                continue;
            }
            let domain = self.instantiate(&local.type_)?;
            let value = local
                .value
                .as_ref()
                .map(|v| self.instantiate(v))
                .transpose()?;
            if domain.has_expr_mvar()
                || domain.has_level_mvar()
                || value
                    .as_ref()
                    .is_some_and(|v| v.has_expr_mvar() || v.has_level_mvar())
            {
                return Ok(false);
            }
            needed.extend(self.elimination_reads(&domain)?);
            if let Some(value) = &value {
                needed.extend(self.elimination_reads(value)?);
            }
            for term in [&mut left, &mut right] {
                self.tick()?;
                let body = term
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                *term = match &value {
                    Some(value) => Expr::let_e(
                        local.user_name.clone(),
                        domain.clone(),
                        value.clone(),
                        body,
                        false,
                    ),
                    None => Expr::lam(
                        local.user_name.clone(),
                        domain.clone(),
                        body,
                        local.binder_info,
                    ),
                };
            }
        }
        if !needed.is_empty() || left.has_fvar() || right.has_fvar() {
            return Err(failure(SourceInferenceError::Scope));
        }
        let mut params = std::collections::BTreeSet::new();
        let mut expressions = vec![&left, &right];
        let mut seen = std::collections::HashSet::new();
        let mut levels = Vec::new();
        while let Some(expr) = expressions.pop() {
            self.tick()?;
            if !seen.insert(expr.allocation_identity()) {
                continue;
            }
            match expr.node() {
                ExprNode::Sort { level } => levels.push(level),
                ExprNode::Const { levels: ls, .. } => levels.extend(ls),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    expressions.push(expr)
                }
                _ => {}
            }
        }
        let mut seen = std::collections::HashSet::new();
        while let Some(level) = levels.pop() {
            self.tick()?;
            if !seen.insert(std::ptr::from_ref(level)) {
                continue;
            }
            match level.view() {
                fln_core::level::LevelView::Param(name) => {
                    params.insert(name.clone());
                }
                fln_core::level::LevelView::Succ(inner) => levels.push(inner),
                fln_core::level::LevelView::Max(a, b) | fln_core::level::LevelView::IMax(a, b) => {
                    levels.extend([a, b])
                }
                _ => {}
            }
        }
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
        };
        let kernel = self
            .kernel
            .narrowed(self.kernel.steps.min(remaining), self.kernel.depth);
        match fln_kernel::check_def_eq(
            &self.txn.env,
            &params.into_iter().collect::<Vec<_>>(),
            &left,
            &right,
            kernel,
        ) {
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
                self.tick()?;
                Ok(verdict.is_accepted())
            }
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }

    /// The last argument can constrain a polymorphic result, but this is only
    /// a hint. A rigidly different result may need a coercion after application.
    pub(in crate::source) fn constrain_result_hint(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !self.has_coercion_class("CoeT")? {
            return self.constrain_type(actual, expected);
        }
        self.coercion_eq(actual, expected).map(|_| ())
    }

    fn coercion_level(&mut self, type_: &Expr) -> Result<Option<Level>, NatDefinitionElabError> {
        let Some(sort) = self.known_type(type_)? else {
            return Ok(None);
        };
        let sort = self.whnf(&sort)?;
        Ok(match sort.node() {
            ExprNode::Sort { level } => Some(level.clone()),
            _ => None,
        })
    }

    /// Called only inside a speculative coercion context. The root's search
    /// can solve its own prerequisites without requiring unrelated dictionaries.
    fn coercion_instance(&mut self, target: Expr) -> Result<Option<Expr>, NatDefinitionElabError> {
        let registry = InstanceRegistry::read(&self.txn.env).map_err(registry_error)?;
        let saved = self.txn.lctx.clone();
        let suspended = std::mem::take(&mut self.equations);
        let hole = self.instance_hole(target)?;
        let ExprNode::MVar { id } = hole.node() else {
            unreachable!("instance hole");
        };
        let result = self.search_instance(id.clone(), &registry);
        self.txn.lctx = saved;
        self.equations = suspended;
        if result? {
            self.instantiate(&hole).map(Some)
        } else {
            Ok(None)
        }
    }

    fn coercion_projection(
        &mut self,
        class: &str,
        levels: Vec<Level>,
        args: Vec<Expr>,
        value: Option<Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        if !self.has_coercion_class(class)? {
            return Ok(None);
        }
        let target = args.iter().cloned().fold(
            Expr::const_(Name::from_components([class]), levels.clone()),
            Expr::app,
        );
        let Some(dict) = self.coercion_instance(target)? else {
            return Ok(None);
        };
        let mut term = args.into_iter().chain([dict]).fold(
            Expr::const_(Name::from_components([class, "coe"]), levels),
            Expr::app,
        );
        if let Some(value) = value {
            term = Expr::app(term, value);
        }
        term = self.instantiate(&term)?;
        let Some(type_) = self.known_type(&term)? else {
            return Ok(None);
        };
        Ok(Some(Typed {
            value: term,
            type_: self.whnf(&type_)?,
        }))
    }

    fn coerce_value(
        &mut self,
        term: &Typed,
        expected: &Expr,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let actual = self.instantiate(&term.type_)?;
        let expected = self.instantiate(expected)?;
        if actual.has_expr_mvar() || expected.has_expr_mvar() {
            return Ok(None);
        }
        let Some(u) = self.coercion_level(&actual)? else {
            return Ok(None);
        };
        let Some(v) = self.coercion_level(&expected)? else {
            return Ok(None);
        };
        let value = self.instantiate(&term.value)?;
        self.coercion_projection("CoeT", vec![u, v], vec![actual, value, expected], None)
    }

    fn coerce_shape(
        &mut self,
        term: &Typed,
        function: bool,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let actual = self.instantiate(&term.type_)?;
        if actual.has_expr_mvar() || actual.has_level_mvar() {
            return Ok(None);
        }
        let Some(u) = self.coercion_level(&actual)? else {
            return Ok(None);
        };
        let v = self.level()?;
        let output_type = if function {
            Expr::forall_e(
                Name::anonymous(),
                actual.clone(),
                Expr::sort(v.clone()),
                BinderInfo::Default,
            )
        } else {
            Expr::sort(v.clone())
        };
        let output = self.hole(output_type)?;
        let result = self.coercion_projection(
            if function { "CoeFun" } else { "CoeSort" },
            vec![u, v],
            vec![actual, output],
            Some(term.value.clone()),
        )?;
        Ok(result.filter(|result| {
            if function {
                matches!(result.type_.node(), ExprNode::ForallE { .. })
            } else {
                matches!(result.type_.node(), ExprNode::Sort { .. })
            }
        }))
    }

    pub(in crate::source) fn coerce_function(
        &mut self,
        mut term: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.resolve_instances(false)?;
        term.type_ = self.whnf(&term.type_)?;
        if matches!(term.type_.node(), ExprNode::ForallE { .. }) {
            return Ok(term);
        }
        let mut trial = self.clone();
        let result = trial.coerce_shape(&term, true);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match result? {
            Some(term) => {
                *self = trial;
                self.insert_implicits(term, ImplicitInsertion::ExplicitArgument)
            }
            None => Err(failure(SourceInferenceError::ExpectedFunction)),
        }
    }

    pub(in crate::source) fn coerce_expected(
        &mut self,
        term: Typed,
        expected: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        if !self.has_coercion_class("CoeT")? && !self.has_coercion_class("CoeSort")? {
            self.constrain_expected_type(&term.type_, expected)?;
            return Ok(term);
        }
        let mut trial = self.clone();
        let normal = (|| {
            trial.constrain_expected_type(&term.type_, expected)?;
            trial.resolve_instances(false)?;
            let actual = trial.instantiate(&term.type_)?;
            let target = trial.instantiate(expected)?;
            // Never guess an unknown target by asking for a coercion.
            // Preserve normal postponement of expression constraints.
            if actual.has_expr_mvar() || target.has_expr_mvar() {
                return Ok(true);
            }
            trial.coercion_eq(&actual, &target)
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match normal {
            Ok(true) => {
                *self = trial;
                return Ok(term);
            }
            Ok(false) => {}
            Err(error) if nonmatch(&error) => {}
            Err(error) => return Err(error),
        }
        let mut trial = self.clone();
        let result = (|| {
            let expected_head = trial.whnf(expected)?;
            let candidate = if matches!(expected_head.node(), ExprNode::Sort { .. }) {
                trial.coerce_shape(&term, false)?
            } else {
                trial.coerce_value(&term, expected)?
            };
            let Some(candidate) = candidate else {
                return Ok(None);
            };
            if !trial.coercion_eq(&candidate.type_, expected)? {
                return Ok(None);
            }
            Ok(Some(candidate))
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        if let Some(candidate) = result? {
            *self = trial;
            return Ok(candidate);
        }
        // No path: retain the original diagnostic boundary. Closed mismatches
        // still reach K1, while an unification/resource nonanswer stays typed.
        self.constrain_expected_type(&term.type_, expected)?;
        Ok(term)
    }
}
