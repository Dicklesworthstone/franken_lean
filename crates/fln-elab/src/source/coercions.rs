//! Coercion insertion uses the ordinary instance engine and produces ordinary
//! projection applications. Neither finding a path nor reconstructing its type
//! grants proof authority: the final declaration still needs kernel admission.
use super::instances::{nonmatch, registry_error};
use super::*;
use crate::instances::InstanceRegistry;
use fln_env::constants::ConstantInfo;

mod expand;
mod function;
mod monad;
mod result_hint;

/// A native probe can be blocked before a closed kernel query is possible.
/// Keep that distinct from a completed query's concrete conversion refusal.
pub(super) enum Conversion {
    Equal,
    Refuted(Verdict),
    Deferred,
}

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

    pub(in crate::source) fn has_coercion_class(
        &self,
        name: &str,
    ) -> Result<bool, NatDefinitionElabError> {
        let name = Name::from_components([name]);
        if !self.txn.env.contains(&name) {
            return Ok(false);
        }
        Ok(self.instance_registry()?.is_class(&name))
    }

    /// Probe one isolated equation without publishing a failed assignment or
    /// consuming the caller's unrelated suspended source equations.
    pub(in crate::source) fn coercion_eq(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        Ok(matches!(
            self.coercion_conversion(actual, expected)?,
            Conversion::Equal
        ))
    }

    pub(super) fn coercion_conversion(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Conversion, NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        // Ground equations need no assignments. Use the existing query under
        // Default's unfolding policy before entering the metavariable solver:
        // dependent recursor telescopes can otherwise be repeatedly rebuilt
        // by native conversion's type hints. The query sees original terms,
        // including native Nat operations, and retains the caller's budget.
        // A closure still mentioning a local type hole has not run a kernel
        // query; only that Deferred case proceeds to ordinary unification.
        if !actual.has_expr_mvar()
            && !actual.has_level_mvar()
            && !expected.has_expr_mvar()
            && !expected.has_level_mvar()
        {
            match self.coercion_kernel_conversion(actual.clone(), expected.clone())? {
                Conversion::Deferred => {}
                result => return Ok(result),
            }
        }
        // Compare the original terms with the ordinary Default reducer. Its
        // quick assignments preserve named carriers, and its native Nat rung
        // runs before delta (the pin's WHNF.lean). Source WHNF here would first
        // expand Nat.add's course-of-values body, hiding arithmetic from that
        // bounded evaluator and exhausting small nested reflexivity proofs.
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::Default;
        // The pin's `isDefEq` here synthesizes an instance its unification has
        // determined (`change 5 = 5` meets `(2 : Int) + 3 = 5` with `?α := Int`).
        match self.unify_pending(&[(actual.clone(), expected.clone())], budget)? {
            Ok(_) => Ok(Conversion::Equal),
            Err(error) => {
                let error = failure(SourceInferenceError::Unification(Box::new(error)));
                if nonmatch(&error) {
                    self.coercion_kernel_conversion(actual, expected)
                } else {
                    Err(error)
                }
            }
        }
    }

    /// Complete a closed conversion with the kernel's equality machinery under
    /// the same Default delta restrictions. Theorem bodies stay opaque too,
    /// matching Meta/GetUnfoldableConst.lean. This grants no declaration
    /// authority and retains spent work, including inconclusive outcomes.
    pub(in crate::source) fn coercion_kernel_eq(
        &mut self,
        left: Expr,
        right: Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        Ok(matches!(
            self.coercion_kernel_conversion(left, right)?,
            Conversion::Equal
        ))
    }

    fn coercion_kernel_conversion(
        &mut self,
        mut left: Expr,
        mut right: Expr,
    ) -> Result<Conversion, NatDefinitionElabError> {
        if left.has_expr_mvar()
            || left.has_level_mvar()
            || right.has_expr_mvar()
            || right.has_level_mvar()
        {
            return Ok(Conversion::Deferred);
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
                return Ok(Conversion::Deferred);
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
        let reducibility = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        match fln_kernel::check_def_eq_with_unfolding(
            &self.txn.env,
            &params.into_iter().collect::<Vec<_>>(),
            &left,
            &right,
            kernel,
            fln_kernel::DefEqUnfolding {
                opaque_definitions: reducibility.opaque_definitions(),
                unfold_theorems: false,
            },
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
                Ok(match verdict {
                    Verdict::Accepted { .. } => Conversion::Equal,
                    rejected @ Verdict::Rejected { .. } => Conversion::Refuted(rejected),
                })
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
        if !self.has_coercion_class("CoeT")?
            && !self.has_coercion_class("CoeFun")?
            && !self.has_coercion_class("MonadLiftT")?
            && !self.has_coercion_class("Monad")?
        {
            // Keep the written applications for ordinary unification. Reducing
            // `Id ?A` first exposes its hole and can assign the entire expected
            // `Id Nat` to it, changing later numeral/instance selection. The
            // original equation chooses `?A := Nat` before any delta retry.
            //
            // A result HINT runs before the remaining argument elaborates, so a
            // concrete refutation here must stay advisory: making it fatal
            // masked the argument's own diagnostic — `Nat.succ ·` reported a
            // NotDefEq conversion instead of the pin's "invalid occurrence of
            // `·` notation" (fln-ffce comment 3297) — and the coercion branch
            // below already drops a false equality. The equation is still
            // checked for real where the application completes and at the
            // declaration's ordinary K1 admission.
            match self.constrain(actual, expected) {
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ConversionRefused(_),
                )) => Ok(()),
                other => other,
            }?;
        } else if self.coercion_eq(actual, expected)? {
            return Ok(());
        }
        self.first_order_result_hint(actual, expected)
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
    pub(in crate::source) fn coercion_instance(
        &mut self,
        target: Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let registry =
            InstanceRegistry::read_with_scopes(&self.txn.env, &self.source_scope.instance_scopes)
                .map_err(registry_error)?;
        let saved = self.txn.lctx.clone();
        let suspended = std::mem::take(&mut self.equations);
        let hole = self.instance_hole(target)?;
        let ExprNode::MVar { id } = hole.node() else {
            unreachable!("instance hole");
        };
        let result = self.search_instance(id.clone(), &registry);
        self.txn.lctx = saved;
        self.equations = suspended;
        if result? == instances::SearchResult::Solved {
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
        term = self.expand_coercions(&term)?;
        let Some(type_) = self.known_type(&term)? else {
            return Ok(None);
        };
        Ok(Some(Typed {
            value: term,
            type_: self.whnf(&type_)?,
        }))
    }

    pub(in crate::source) fn coerce_value(
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
        // A later application argument may determine this carrier, including
        // a bundled value with its own CoeFun dictionary. Do not select that
        // carrier by coercion search before it is known.
        let mut head = &term.type_;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        if matches!(head.node(), ExprNode::MVar { .. }) {
            return Err(failure(SourceInferenceError::ExpectedFunction));
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
        if !self.has_coercion_class("CoeT")?
            && !self.has_coercion_class("CoeSort")?
            && !self.has_coercion_class("CoeFun")?
            && !self.has_coercion_class("MonadLiftT")?
            && !self.has_coercion_class("Monad")?
        {
            // No coercion can exist: a rigid mismatch is final here.
            self.refute_rigid_mismatch(&term.type_, expected)?;
            self.constrain_expected_type(&term.type_, expected)?;
            return Ok(term);
        }
        let mut trial = self.clone();
        let normal = (|| {
            trial.constrain_expected_type(&term.type_, expected)?;
            trial.resolve_instances(false)?;
            let actual = trial.instantiate(&term.type_)?;
            let target = trial.instantiate(expected)?;
            // Preserve normal postponement instead of repeatedly solving an
            // open equation. A known monad lift gets its own isolated attempt
            // below; unrelated holes must not start broader conversion work.
            if actual.has_expr_mvar() || target.has_expr_mvar() {
                return Ok(None);
            }
            trial.coercion_eq(&actual, &target).map(Some)
        })();
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match normal {
            Ok(Some(true)) => {
                *self = trial;
                return Ok(term);
            }
            Ok(None) => {
                // A known MonadLiftT m n can determine the result element in
                // n ?A even though direct equality with m A is stuck. The pin's
                // coerceMonadLift? deliberately handles this case before an
                // ordinary coercion search (Lean/Meta/Coe.lean). Start from the
                // original context, not the failed direct-typing equations.
                if let Some(lifted) = self.try_monad_lift(&term, expected)? {
                    return Ok(lifted);
                }
                // A CoeFun dictionary can likewise determine holes in an
                // expected Pi type. Its own shape/type probe is transactional;
                // a failed attempt must retain the original deferred equation.
                if let Some(function) = self.try_expected_function(&term, expected)? {
                    return Ok(function);
                }
                // No coercion: retain the original postponed typing obligations.
                // In particular, never select an unknown monad by search and
                // never refund the failed alternative's work.
                trial.txn.budget.heartbeats_consumed = self.txn.budget.heartbeats_consumed;
                *self = trial;
                return Ok(term);
            }
            Ok(Some(false)) => {}
            Err(error) if nonmatch(&error) => {}
            Err(error) => return Err(error),
        }
        // The pin tries a registered monad lift before ordinary value coercions.
        if let Some(lifted) = self.try_monad_lift(&term, expected)? {
            return Ok(lifted);
        }
        // Function-shape coercions precede CoeT, but only a matching function
        // type commits the speculative output-family assignments.
        if let Some(function) = self.try_expected_function(&term, expected)? {
            return Ok(function);
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
        // No path. A rigid mismatch is the pin's elaboration-time `Type mismatch`; any
        // other closed mismatch still reaches K1, while an unification/resource
        // nonanswer stays typed.
        self.refute_rigid_mismatch(&term.type_, expected)?;
        self.constrain_expected_type(&term.type_, expected)?;
        Ok(term)
    }

    /// Refuse, with the pin's `Type mismatch`, a term whose type is rigidly not its expected
    /// type (see [`Self::rigid_type_mismatch`]); any other pair is left to the caller.
    fn refute_rigid_mismatch(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        match self.rigid_type_mismatch(actual, expected)? {
            Some((actual, expected)) => Err(failure(SourceInferenceError::TypeMismatch {
                actual,
                expected,
            })),
            None => Ok(()),
        }
    }

    /// Whether `actual` and `expected` are certainly not definitionally equal, described for
    /// the message. They are when, with no metavariables, their weak head normal forms (safe
    /// definitions and local lets unfolded) have rigid heads that differ: two distinct
    /// constants that never reduce (inductive types and axioms), or two of a sort, a Π-type and
    /// such a constant. Once reduction reaches
    /// such a head the kernel's own reduction ends at the same head, and distinct rigid heads
    /// are never definitionally equal, so every pair refuted here is one K1 would reject too:
    /// refutation moves the refusal to elaboration and never changes a verdict. Anything else,
    /// a `Sort u` against a `Sort v` or a head that is not rigid, is `None`.
    pub(in crate::source) fn rigid_type_mismatch(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<Option<(String, String)>, NatDefinitionElabError> {
        let actual = self.instantiate(actual)?;
        let expected = self.instantiate(expected)?;
        if [&actual, &expected]
            .iter()
            .any(|type_| type_.has_expr_mvar() || type_.has_level_mvar())
        {
            return Ok(None);
        }
        let actual = self.whnf(&actual)?;
        let expected = self.whnf(&expected)?;
        if [&actual, &expected]
            .iter()
            .any(|type_| type_.has_expr_mvar() || type_.has_level_mvar())
        {
            return Ok(None);
        }
        let (Some(left), Some(right)) = (self.rigid_shape(&actual), self.rigid_shape(&expected))
        else {
            return Ok(None);
        };
        let distinct = match (&left, &right) {
            (RigidShape::Constant(a, _), RigidShape::Constant(b, _)) => a != b,
            (RigidShape::Sort, RigidShape::Sort) | (RigidShape::Pi, RigidShape::Pi) => false,
            _ => true,
        };
        Ok(distinct.then(|| (left.describe(), right.describe())))
    }

    fn rigid_shape(&self, type_: &Expr) -> Option<RigidShape> {
        match type_.node() {
            ExprNode::Sort { .. } => return Some(RigidShape::Sort),
            ExprNode::ForallE { .. } => return Some(RigidShape::Pi),
            _ => {}
        }
        let mut head = type_;
        let mut applied = false;
        while let ExprNode::App { f, .. } = head.node() {
            head = f;
            applied = true;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return None;
        };
        // An inductive type or an axiom (the source seed's `String`) never reduces. Anything
        // else (a definition whnf stopped at, an opaque, a quotient) is left undecided.
        matches!(
            self.txn.env.find(name),
            Some(ConstantInfo::Induct(_) | ConstantInfo::Axiom(_))
        )
        .then(|| RigidShape::Constant(name.clone(), applied))
    }
}

/// A type's head after reduction, when it is rigid: no reduction can change it.
enum RigidShape {
    Sort,
    Pi,
    /// An inductive type or an axiom, and whether it is applied to arguments.
    Constant(Name, bool),
}

impl RigidShape {
    fn describe(&self) -> String {
        match self {
            Self::Sort => "Sort …".to_owned(),
            Self::Pi => "… → …".to_owned(),
            Self::Constant(name, false) => name.to_display_string(),
            Self::Constant(name, true) => format!("{} …", name.to_display_string()),
        }
    }
}
