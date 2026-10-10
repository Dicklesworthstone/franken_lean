//! Primitive structural recursion, compiled into the match recursor's hypotheses.
//!
//! A recursive name is a private local marker, never an environment declaration.
//! Only calls on an immediate recursive constructor field, fully applied when
//! function-valued, may replace that marker.
//! The recursor computes the entire body: binder-free contexts around a selected
//! match are distributed into its hygienic branches before motive construction.
//! An inner subexpression's hypothesis cannot stand for the whole function. Arguments retained
//! as fixed must be the original locals or their domain-checked eta expansions;
//! changed arguments are generalized without conversion erasing their contents.
use super::*;
mod constrained;
mod context;
mod lambdas;
mod matrix;
mod obligation;
pub(super) use constrained::ConstrainedBranch;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecursionError {
    ResultTypeRequired,
    RootMatchRequired,
    ExplicitParameterRequired,
    NotDecreasing,
    ChangedParameter,
    /// Internal request to rebuild this candidate's motive. The header local
    /// identifies its owner across nested local-function/proof checkpoints.
    GeneralizeParameter {
        owner: FVarId,
        position: usize,
    },
    ChangedIndex,
    PartialApplication,
    StructuralMeasureNotParameter,
    StructuralParameterNotInductive,
    TerminationBinderCount {
        bound: usize,
        available: usize,
    },
}
impl std::fmt::Display for RecursionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::TerminationBinderCount { bound, available } => {
                return write!(
                    f,
                    "{bound} parameters bound in `termination_by`, but the function body only binds {available} parameters"
                );
            }
            Self::ResultTypeRequired => "recursive definition requires an explicit result type",
            Self::RootMatchRequired => {
                "structural recursion requires a body matching a function parameter"
            }
            Self::ExplicitParameterRequired => {
                "structural recursion requires an explicit decreasing parameter"
            }
            Self::NotDecreasing => {
                "recursive call is not on an immediate recursive constructor field"
            }
            Self::ChangedParameter => "recursive call changes a fixed parameter",
            Self::GeneralizeParameter { .. } => "recursive parameter requires generalization",
            Self::ChangedIndex => "recursive call indices do not match its structural child's type",
            Self::PartialApplication => {
                "recursive function escapes without its structural argument"
            }
            Self::StructuralMeasureNotParameter => {
                "the termination measure of a structurally recursive function must be one of its parameters"
            }
            Self::StructuralParameterNotInductive => {
                "cannot use specified measure for structural recursion: its type is not an inductive"
            }
        })
    }
}
fn error(reason: RecursionError) -> NatDefinitionElabError {
    failure(SourceInferenceError::Recursion(reason))
}

/// The pin's `TerminationBy`: aliases bind only parameters after the declaration
/// colon. The measure remains source syntax until a surviving recursive call
/// actually needs it; a nonrecursive declaration does not elaborate its hint.
#[derive(Clone)]
pub(super) struct StructuralHint<'a> {
    aliases: Vec<Option<Name>>,
    measure: &'a Syntax,
}

/// Read the supported structural clause, never silently discard a well-founded
/// measure or a `decreasing_by` proof. Shape checks match `elabTerminationHints`
/// in the pinned `Lean/Elab/PreDefinition/TerminationHint.lean`.
pub(super) fn structural_hint(
    syntax: &Syntax,
) -> Result<Option<StructuralHint<'_>>, NatDefinitionElabError> {
    let parts = expect_node(
        syntax,
        &parser_kind(&["Termination", "suffix"]),
        2,
        "termination suffix",
    )?;
    expect_empty_null(&parts[1], "absent decreasing_by clause")?;
    let clause = match expect_null_args(&parts[0], "termination clause")? {
        [] => return Ok(None),
        [clause] => clause,
        _ => return Err(failure(SourceInferenceError::Scope)),
    };
    let clause = expect_node(
        clause,
        &parser_kind(&["Termination", "terminationBy"]),
        4,
        "structural termination clause",
    )?;
    expect_atom(&clause[0], "termination_by", "termination keyword")?;
    let [structural] = expect_null_args(&clause[1], "structural termination marker")? else {
        return Err(NatDefinitionElabError::UnexpectedSyntax {
            expected: "termination_by structural parameter",
        });
    };
    expect_atom(structural, "structural", "structural termination marker")?;
    let mut aliases = Vec::new();
    match expect_null_args(&clause[2], "termination parameter aliases")? {
        [] => {}
        [binders, arrow] => {
            expect_atom(arrow, "=>", "termination parameter arrow")?;
            let binders = expect_null_args(binders, "termination parameters")?;
            if binders.is_empty() {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "termination parameter before =>",
                });
            }
            for binder in binders {
                match binder {
                    Syntax::Ident { val, .. } if !val.is_anonymous() => {
                        aliases.push(Some(val.clone()));
                    }
                    _ => {
                        let [hole] = expect_node(
                            binder,
                            &parser_kind(&["Term", "hole"]),
                            1,
                            "termination parameter or underscore",
                        )?
                        else {
                            return Err(failure(SourceInferenceError::Scope));
                        };
                        expect_atom(hole, "_", "termination parameter underscore")?;
                        aliases.push(None);
                    }
                }
            }
        }
        _ => return Err(failure(SourceInferenceError::Scope)),
    }
    Ok(Some(StructuralHint {
        aliases,
        measure: &clause[3],
    }))
}

#[derive(Clone)]
pub(super) struct Recursion {
    pub(super) name: Name,
    pub(super) reference: Typed,
    pub(super) marker: FVarId,
    pub(super) parameters: Vec<LocalDecl>,
    pub(super) decreasing: usize,
    /// Source matrix column chosen for the structural split; arguments keep
    /// their original function-telescope order.
    pub(super) column: usize,
    /// Other explicitly matched inputs may vary, even before the decreasing
    /// parameter. Actual uniform family parameters remain fixed.
    matched_parameters: HashSet<usize>,
    pub(super) generalized_parameters: HashSet<usize>,
    pub(super) pending: bool,
    pub(super) matrix: bool,
    matrix_hypotheses: Vec<(Name, Name)>,
    matrix_hidden: HashSet<Name>,
    /// Family-ordered index binders, each pointing into the source telescope.
    indices: Vec<usize>,
    /// Source-ordered arguments universally quantified in each hypothesis.
    varying: Vec<usize>,
    family: Option<(Name, usize)>,
    contextual_capture: Option<context::Capture>,
    pub(super) equation_goals: HashMap<MVarId, ConstrainedBranch>,
}
impl Context {
    /// Elaborate the measure in the header-plus-alias scope, as the pin's
    /// `TerminationMeasure.elab` does. The result must be the actual free
    /// variable, not merely definitionally equal to one. Restore all speculative
    /// state and generated identities, retaining only the consumed work.
    pub(super) fn structural_hint_parameter(
        &mut self,
        hint: &StructuralHint<'_>,
        parameters: &[LocalDecl],
        header_parameters: usize,
    ) -> Result<usize, NatDefinitionElabError> {
        let extra = parameters
            .get(header_parameters..)
            .ok_or_else(|| failure(SourceInferenceError::Scope))?;
        if hint.aliases.len() > extra.len() {
            return Err(error(RecursionError::TerminationBinderCount {
                bound: hint.aliases.len(),
                available: extra.len(),
            }));
        }
        let snapshot = self.clone();
        let result = (|| {
            let mut extra_names = HashMap::new();
            for (index, parameter) in extra.iter().enumerate() {
                self.tick()?;
                extra_names.insert(parameter.id.clone(), hint.aliases.get(index).cloned());
            }
            let mut locals = LocalContext::new();
            for local in snapshot.txn.lctx.decls() {
                self.tick()?;
                let mut local = local.clone();
                if let Some(alias) = extra_names.get(&local.id) {
                    let Some(alias) = alias else {
                        // Lambda-body names do not scope over a termination
                        // clause. Unaliased later parameters are not in its
                        // context at all, even for tactics such as assumption.
                        continue;
                    };
                    local.user_name = alias.clone().unwrap_or_else(Name::anonymous);
                }
                tactics::eliminate::add_local(&mut locals, &local);
            }
            self.txn.lctx = locals;
            self.recursion = None;
            self.defining = None;
            self.attempt_depth = self
                .attempt_depth
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            let measure = self.term(hint.measure, None)?;
            let measure = self.finish(measure)?;
            self.check_structural_measure(&measure)?;
            // The native source driver retains ascriptions as identity lets
            // so later reduction cannot erase an unchecked annotation. The
            // check above has now validated their original, unreduced terms.
            // Peel only that encoding, as the pin's elaborator emits its inner
            // expression directly. A source let or reducible application is
            // still not a structural parameter.
            let mut value = &measure.value;
            loop {
                self.tick()?;
                match value.node() {
                    ExprNode::MData { expr, .. } => value = expr,
                    ExprNode::LetE {
                        decl_name,
                        value: inner,
                        body,
                        ..
                    } if decl_name.is_anonymous()
                        && matches!(body.node(), ExprNode::BVar { idx: 0 }) =>
                    {
                        value = inner
                    }
                    _ => break,
                }
            }
            let ExprNode::FVar { id } = value.node() else {
                return Err(error(RecursionError::StructuralMeasureNotParameter));
            };
            for (position, parameter) in parameters
                .iter()
                .take(header_parameters + hint.aliases.len())
                .enumerate()
            {
                self.tick()?;
                if &parameter.id == id {
                    self.structural_parameter_domain(parameter)?;
                    return Ok(position);
                }
            }
            Err(error(RecursionError::StructuralMeasureNotParameter))
        })();
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        result
    }

    /// Explicit structural recursion has the pin's `getRecArgInfo` domain
    /// restriction: an inductive application with distinct variable indices.
    /// In particular it must not enter native constrained-index recursion just
    /// because an automatically selected recursor could prove that program.
    fn structural_parameter_domain(
        &mut self,
        parameter: &LocalDecl,
    ) -> Result<(), NatDefinitionElabError> {
        let type_ = self.whnf(&parameter.type_)?;
        let mut head = &type_;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            match head.node() {
                ExprNode::App { f, a } => {
                    arguments.push(a.clone());
                    head = f;
                }
                ExprNode::MData { expr, .. } => head = expr,
                _ => break,
            }
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Err(error(RecursionError::StructuralParameterNotInductive));
        };
        let Some(fln_env::constants::ConstantInfo::Induct(family)) = self.txn.env.find(name) else {
            return Err(error(RecursionError::StructuralParameterNotInductive));
        };
        let parameters = family.num_params as usize;
        if arguments.len() != parameters + family.num_indices as usize {
            return Err(error(RecursionError::StructuralParameterNotInductive));
        }
        arguments.reverse();
        self.elimination_index_locals(&arguments[parameters..])?;
        Ok(())
    }

    /// Check the original measure before its annotation encoding is inspected.
    /// The axiom's type contains an ordinary checked let initializer and is
    /// closed over the actual local telescope; nothing is admitted to the
    /// environment. Every kernel step is charged to the same source budget.
    fn check_structural_measure(&mut self, measure: &Typed) -> Result<(), NatDefinitionElabError> {
        let mut type_ = Expr::let_e(
            Name::anonymous(),
            measure.type_.clone(),
            measure.value.clone(),
            Expr::sort(Level::zero()),
            false,
        );
        for local in self.txn.lctx.clone().decls().iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            let body = type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            type_ = if let Some(value) = &local.value {
                Expr::let_e(
                    local.user_name.clone(),
                    domain,
                    self.instantiate(value)?,
                    body,
                    false,
                )
            } else {
                Expr::forall_e(local.user_name.clone(), domain, body, local.binder_info)
            };
        }
        let name = loop {
            let name = self.fresh_name()?;
            if !self.txn.env.contains(&name) {
                break name;
            }
        };
        let declaration = Declaration::Axiom(fln_env::constants::AxiomVal {
            base: ConstantVal {
                name,
                level_params: self.level_params.clone(),
                type_,
            },
            is_unsafe: false,
        });
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
        };
        let budget = self
            .kernel
            .narrowed(self.kernel.steps.min(remaining), self.kernel.depth);
        let outcome = check(&self.txn.env, &declaration, budget);
        if let Outcome::Complete(verdict) = &outcome {
            let consumed = match verdict {
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
        }
        match outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => Ok(()),
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }

    /// A synthetic argument's selected termination failure must reach the
    /// enclosing candidate driver after tactic alternatives finish. Earlier
    /// diagnostics belong to an outer body; explicit failure restores the
    /// existing diagnostic vector along with its argument/proof checkpoint.
    pub(super) fn require_no_postponed_recursion_since(
        &mut self,
        start: usize,
    ) -> Result<(), NatDefinitionElabError> {
        if start > self.postponed_application_errors.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        for index in start..self.postponed_application_errors.len() {
            self.tick()?;
            let problem = &self.postponed_application_errors[index];
            if matches!(
                problem,
                NatDefinitionElabError::Inference(SourceInferenceError::Recursion(_))
            ) {
                return Err(problem.clone());
            }
        }
        Ok(())
    }

    /// Implicit higher-order inference can produce `fun x => P x` for the fixed
    /// parameter `P`. Recognize only that exact eta shape, checking every domain
    /// against P's dependent function telescope. Unlike general conversion this
    /// cannot erase a let, application argument, annotation, or recursive call.
    fn fixed_recursive_argument(
        &mut self,
        argument: &Expr,
        parameter: &LocalDecl,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut body = argument;
        let type_ = self.instantiate(&parameter.type_)?;
        let mut domain = &type_;
        let mut arity = 0u32;
        while let ExprNode::Lam {
            binder_type,
            body: inner,
            ..
        } = body.node()
        {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type: expected,
                body: result,
                ..
            } = domain.node()
            else {
                return Ok(false);
            };
            if binder_type != expected {
                return Ok(false);
            }
            arity = arity
                .checked_add(1)
                .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
            body = inner;
            domain = result;
        }
        for index in 0..arity {
            self.tick()?;
            let ExprNode::App { f, a } = body.node() else {
                return Ok(false);
            };
            if !matches!(a.node(), ExprNode::BVar { idx } if *idx == index) {
                return Ok(false);
            }
            body = f;
        }
        Ok(matches!(body.node(), ExprNode::FVar { id } if id == &parameter.id))
    }

    /// Retry only an actual unresolved self-reference. Candidate selection is
    /// source-ordered and transactional. Failed candidates retain spent work,
    /// but no assignments, generated identities, local facts or matrix state.
    /// Changed earlier arguments expand a candidate's generalization mask;
    /// strict growth bounds these retries by the size of its header telescope.
    pub(super) fn definition_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hint: Option<&StructuralHint<'_>>,
        header_parameters: usize,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.defining = Some(name.clone());
        let snapshot = self.clone();
        match self.term(syntax, expected.clone()) {
            Err(NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(
                found,
            ))) if (&found == name
                || self.source_scope.declaration_name(&found).as_ref() == Ok(name))
                && !self.txn.env.contains(name) => {}
            Ok(body) => {
                // A resumed callback reports its failure as a delayed source
                // diagnostic. Let tactic alternatives finish and roll back
                // first: an explicit `fail` may discard the self reference.
                // A surviving reference selects the same ordinary recursion
                // retry before later hole equations can obscure its cause.
                let mut discovered = false;
                if !self.txn.env.contains(name) {
                    for index in snapshot.postponed_application_errors.len()
                        ..self.postponed_application_errors.len()
                    {
                        self.tick()?;
                        if matches!(
                            &self.postponed_application_errors[index],
                            NatDefinitionElabError::Inference(SourceInferenceError::UnknownConstant(found))
                                if found == name
                                    || self.source_scope.declaration_name(found).as_ref() == Ok(name)
                        ) {
                            discovered = true;
                            break;
                        }
                    }
                }
                if !discovered {
                    return Ok(body);
                }
            }
            result => return result,
        }
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot.clone();
        self.txn.budget.heartbeats_consumed = spent;
        let mut parameters = parameters.to_vec();
        let result = (|| {
            let (body, expected, lambdas) =
                self.open_recursive_lambdas(syntax, expected, &mut parameters)?;
            let selected = hint
                .map(|hint| self.structural_hint_parameter(hint, &parameters, header_parameters))
                .transpose()?;
            let body =
                self.structural_definition_body(name, &parameters, body, expected, selected)?;
            self.close_recursive_lambdas(&lambdas, body)
        })();
        if result.is_err() {
            let spent = self.txn.budget.heartbeats_consumed;
            *self = snapshot;
            self.txn.budget.heartbeats_consumed = spent;
        }
        result
    }

    /// The body after the source's leading lambdas have introduced their real
    /// parameters. The original-body obligation and structural call checks are
    /// identical for header parameters and these written lambda binders.
    fn structural_definition_body(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        syntax: &Syntax,
        expected: Option<Expr>,
        hinted_parameter: Option<usize>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let snapshot = self.clone();
        let (selected, context) = self.contextual_recursive_match(parameters, syntax)?;
        let columns = self.recursion_columns(parameters, selected)?;
        let matched: Vec<_> = columns.iter().map(|(_, position)| *position).collect();
        let mut first_error = None;
        for (column, decreasing) in columns {
            if hinted_parameter.is_some_and(|position| position != decreasing) {
                continue;
            }
            let mut generalized = HashSet::new();
            loop {
                let spent = self.txn.budget.heartbeats_consumed;
                *self = snapshot.clone();
                self.txn.budget.heartbeats_consumed = spent;
                let result = self
                    .prepare_recursion(
                        name,
                        parameters,
                        selected,
                        expected.as_ref(),
                        column,
                        &matched,
                    )
                    .and_then(|()| {
                        self.recursion
                            .as_mut()
                            .expect("prepared structural candidate")
                            .generalized_parameters = generalized.clone();
                        if context.is_empty() {
                            let obligation =
                                self.original_recursive_body_obligation(syntax, expected.clone())?;
                            let mut value = self.term(syntax, expected.clone())?;
                            value.value = Expr::let_e(
                                Name::anonymous(),
                                obligation.type_,
                                obligation.value,
                                value.value,
                                false,
                            );
                            Ok(value)
                        } else {
                            let build = self.prepare_contextual_recursion(
                                syntax,
                                &context,
                                expected.clone(),
                            )?;
                            let body =
                                self.distribute_recursive_context(selected, column, &build)?;
                            let mut value = self.term(&body, expected.clone())?;
                            value.value = value
                                .value
                                .abstract_fvar(&build.helper.id, 0)
                                .map_err(|_| failure(SourceInferenceError::Scope))?;
                            value.value = Expr::let_e(
                                Name::anonymous(),
                                build.helper.type_,
                                build.helper.value.expect("typed context helper"),
                                value.value,
                                false,
                            );
                            value.value = Expr::let_e(
                                Name::anonymous(),
                                build.obligation.type_,
                                build.obligation.value,
                                value.value,
                                false,
                            );
                            Ok(value)
                        }
                    })
                    .and_then(|value| {
                        self.require_no_postponed_recursion_since(
                            snapshot.postponed_application_errors.len(),
                        )?;
                        Ok(value)
                    });
                match result {
                    Ok(value) => return Ok(value),
                    Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                        RecursionError::GeneralizeParameter { owner, position },
                    ))) if owner == parameters[decreasing].id
                        && position < decreasing
                        && generalized.insert(position) => {}
                    Err(
                        problem @ NatDefinitionElabError::Inference(
                            SourceInferenceError::Recursion(
                                RecursionError::NotDecreasing
                                | RecursionError::ChangedParameter
                                | RecursionError::ChangedIndex
                                | RecursionError::RootMatchRequired
                                | RecursionError::ExplicitParameterRequired
                                | RecursionError::PartialApplication,
                            ),
                        ),
                    ) => {
                        first_error.get_or_insert(problem);
                        break;
                    }
                    Err(problem) => {
                        let spent = self.txn.budget.heartbeats_consumed;
                        *self = snapshot;
                        self.txn.budget.heartbeats_consumed = spent;
                        return Err(problem);
                    }
                }
            }
        }
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        Err(first_error.unwrap_or_else(|| error(RecursionError::RootMatchRequired)))
    }

    /// A structural candidate must be an actual explicit header parameter, not
    /// a computed expression. Each input identity is enumerated once; motive
    /// discovery can retry it with more generalized parameters. The pattern
    /// matrix still checks every source discriminant and every row.
    pub(super) fn recursion_columns(
        &mut self,
        parameters: &[LocalDecl],
        mut syntax: &Syntax,
    ) -> Result<Vec<(usize, usize)>, NatDefinitionElabError> {
        while let Some(inner) = parenthesized_inner(syntax)? {
            self.tick()?;
            syntax = inner;
        }
        if syntax.kind() != Some(&parser_kind(&["Term", "match"])) {
            return Err(error(RecursionError::RootMatchRequired));
        }
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "match"]),
            6,
            "recursive root match",
        )?;
        let discriminants = expect_null_args(&parts[3], "recursive discriminants")?;
        if discriminants.is_empty() || discriminants.len() % 2 == 0 {
            return Err(error(RecursionError::RootMatchRequired));
        }
        let mut columns = Vec::new();
        let mut seen = HashSet::new();
        for (position, discriminant) in discriminants.iter().enumerate() {
            self.tick()?;
            if position % 2 != 0 {
                expect_atom(discriminant, ",", "recursive discriminant separator")?;
                continue;
            }
            let parts = expect_node(
                discriminant,
                &parser_kind(&["Term", "matchDiscr"]),
                2,
                "recursive discriminant",
            )?;
            let mut value = &parts[1];
            while let Some(inner) = parenthesized_inner(value)? {
                self.tick()?;
                value = inner;
            }
            if let Syntax::Ident { val, .. } = value
                && let Some((position_in_header, parameter)) = parameters
                    .iter()
                    .enumerate()
                    .rev()
                    .find(|(_, p)| &p.user_name == val)
                && parameter.binder_info == BinderInfo::Default
                && seen.insert(parameter.id.clone())
            {
                columns.push((position / 2, position_in_header));
            }
        }
        Ok(columns)
    }

    pub(super) fn prepare_recursion(
        &mut self,
        name: &Name,
        parameters: &[LocalDecl],
        mut syntax: &Syntax,
        expected: Option<&Expr>,
        column: usize,
        matched: &[usize],
    ) -> Result<(), NatDefinitionElabError> {
        let expected = expected.ok_or_else(|| error(RecursionError::ResultTypeRequired))?;
        while let Some(inner) = parenthesized_inner(syntax)? {
            self.tick()?;
            syntax = inner;
        }
        if !matches!(syntax, Syntax::Node { kind, .. } if kind == &parser_kind(&["Term", "match"]))
        {
            return Err(error(RecursionError::RootMatchRequired));
        }
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "match"]),
            6,
            "recursive root match",
        )?;
        let discriminants = expect_null_args(&parts[3], "recursive discriminants")?;
        let first = discriminants
            .get(column * 2)
            .ok_or_else(|| error(RecursionError::RootMatchRequired))?;
        let first = expect_node(
            first,
            &parser_kind(&["Term", "matchDiscr"]),
            2,
            "recursive discriminant",
        )?;
        let mut discriminant = &first[1];
        while let Some(inner) = parenthesized_inner(discriminant)? {
            self.tick()?;
            discriminant = inner;
        }
        let Syntax::Ident { val, .. } = discriminant else {
            return Err(error(RecursionError::RootMatchRequired));
        };
        let decreasing = parameters
            .iter()
            .rposition(|local| &local.user_name == val)
            .ok_or_else(|| error(RecursionError::RootMatchRequired))?;
        if parameters[decreasing].binder_info != BinderInfo::Default {
            return Err(error(RecursionError::ExplicitParameterRequired));
        }
        let mut full_type = self.instantiate(expected)?;
        for local in parameters.iter().rev() {
            self.tick()?;
            full_type = full_type
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            full_type = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                full_type,
                local.binder_info,
            );
        }
        let marker = FVarId(self.fresh_name()?);
        self.txn.lctx.add_param(
            marker.clone(),
            Name::anonymous(),
            full_type.clone(),
            BinderInfo::Default,
        );
        self.recursion = Some(Recursion {
            name: name.clone(),
            reference: Typed {
                value: Expr::fvar(marker.clone()),
                type_: full_type,
            },
            marker,
            parameters: parameters.to_vec(),
            decreasing,
            column,
            matched_parameters: matched.iter().copied().collect(),
            generalized_parameters: HashSet::new(),
            pending: true,
            matrix: false,
            matrix_hypotheses: Vec::new(),
            matrix_hidden: HashSet::new(),
            indices: Vec::new(),
            varying: (decreasing + 1..parameters.len()).collect(),
            family: None,
            contextual_capture: None,
            equation_goals: HashMap::new(),
        });
        Ok(())
    }

    /// Separate fixed family parameters from indices that change at each child.
    /// Earlier arguments depending on an index must vary too; capturing them
    /// would give a recursive hypothesis a value at the *outer* index. Index
    /// domains may depend on preceding indices, but never on a generalized
    /// ordinary argument or a later index.
    pub(super) fn recursive_indices(
        &mut self,
        family: &Name,
        parameters: &[Expr],
        indices: &[LocalDecl],
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match specification");
        let mut positions = Vec::new();
        let mut removed: HashSet<_> = indices.iter().map(|local| local.id.clone()).collect();
        for local in indices {
            self.tick()?;
            let position = recursion
                .parameters
                .iter()
                .position(|param| param.id == local.id)
                .filter(|position| *position < recursion.decreasing)
                .ok_or_else(|| {
                    failure(SourceInferenceError::Match(
                        matching::MatchError::UnrefinedIndices,
                    ))
                })?;
            positions.push(position);
        }
        removed.insert(recursion.parameters[recursion.decreasing].id.clone());
        let mut uniform = HashSet::new();
        for parameter in parameters {
            uniform.extend(self.elimination_reads(parameter)?);
        }
        // Telescope domains may depend on earlier parameters. Keep that entire
        // dependency closure fixed, not just the syntactically visible argument.
        for local in recursion.parameters.iter().rev() {
            self.tick()?;
            if uniform.contains(&local.id) {
                uniform.extend(self.elimination_reads(&local.type_)?);
            }
        }
        let mut varying = Vec::new();
        for (position, local) in recursion.parameters.iter().enumerate() {
            self.tick()?;
            if position != recursion.decreasing
                && !positions.contains(&position)
                && (position > recursion.decreasing
                    || recursion.generalized_parameters.contains(&position)
                    || (recursion.matched_parameters.contains(&position)
                        && !uniform.contains(&local.id))
                    || !self.elimination_reads(&local.type_)?.is_disjoint(&removed))
            {
                varying.push(position);
                removed.insert(local.id.clone());
            }
        }
        for parameter in parameters {
            if !self.elimination_reads(parameter)?.is_disjoint(&removed) {
                return Err(error(RecursionError::ChangedParameter));
            }
        }
        let mut preceding = HashSet::new();
        for index in indices {
            if self
                .elimination_reads(&index.type_)?
                .iter()
                .any(|id| removed.contains(id) && !preceding.contains(id))
            {
                return Err(failure(SourceInferenceError::Match(
                    matching::MatchError::UnrefinedIndices,
                )));
            }
            preceding.insert(index.id.clone());
        }
        let recursion = self
            .recursion
            .as_mut()
            .expect("recursive match specification");
        recursion.indices = positions;
        recursion.varying = varying;
        recursion.family = Some((family.clone(), parameters.len()));
        Ok(())
    }

    pub(super) fn is_recursive_match(&self, major: &Expr) -> bool {
        self.recursion.as_ref().is_some_and(|recursion| {
            recursion.pending
                && *major == Expr::fvar(recursion.parameters[recursion.decreasing].id.clone())
        })
    }

    pub(super) fn recursive_match(&mut self, major: &Expr) -> bool {
        if self.is_recursive_match(major) {
            self.recursion
                .as_mut()
                .expect("selected recursive match")
                .pending = false;
            true
        } else {
            false
        }
    }

    /// Abstract trailing arguments into the motive, so the induction hypothesis
    /// is a function of their *new* values, rather than a result at captured
    /// values from the original call. Domains may depend on the major and on
    /// preceding trailing arguments.
    pub(super) fn recursive_target(
        &mut self,
        target: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive target specification");
        let mut target = self.instantiate(target)?;
        for position in recursion.varying.iter().rev() {
            let local = &recursion.parameters[*position];
            self.tick()?;
            target = target
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            target = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                target,
                local.binder_info,
            );
        }
        Ok(target)
    }

    pub(super) fn recursive_arguments(&self) -> Vec<Expr> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("recursive result specification");
        recursion
            .varying
            .iter()
            .map(|position| Expr::fvar(recursion.parameters[*position].id.clone()))
            .collect()
    }

    pub(super) fn recursive_parameters(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        mut target: Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive branch specification");
        for position in &recursion.varying {
            let parameter = &recursion.parameters[*position];
            self.tick()?;
            target = self.whnf(&target)?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = target.node()
            else {
                return Err(failure(SourceInferenceError::ExpectedFunction));
            };
            // A pattern binder shadows an equally named header parameter. The
            // generalized parameter still exists but is not name-resolvable.
            let name = if locals
                .iter()
                .any(|local| local.user_name == parameter.user_name)
            {
                Name::anonymous()
            } else {
                parameter.user_name.clone()
            };
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("generalized argument")
                    .clone(),
            );
            target = self.substitute(body, &Expr::fvar(id))?;
        }
        Ok(target)
    }

    /// The original major must not remain captured in a recursive minor: its
    /// value at smaller arguments is the constructor currently being inspected.
    pub(super) fn recursive_branch_context(&mut self) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match has a specification");
        let removed: HashSet<_> = recursion
            .indices
            .iter()
            .chain(&recursion.varying)
            .map(|position| recursion.parameters[*position].id.clone())
            .chain([recursion.parameters[recursion.decreasing].id.clone()])
            .collect();
        let previous = self.txn.lctx.clone();
        self.txn.lctx = LocalContext::new();
        for local in previous.decls() {
            self.tick()?;
            if !removed.contains(&local.id) {
                if let Some(value) = &local.value {
                    self.txn.lctx.add_let(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        value.clone(),
                    );
                } else {
                    self.txn.lctx.add_param(
                        local.id.clone(),
                        local.user_name.clone(),
                        local.type_.clone(),
                        local.binder_info,
                    );
                }
            }
        }
        // Preserve a local recursive self binder's lexical position and name.
        // Replacing it by an anonymous marker would resolve a recursive call
        // to an outer binding with the same name. Its type is already closed
        // over the function parameters, so it does not capture the old major.
        if !self.txn.lctx.contains(&recursion.marker) {
            self.txn.lctx.add_param(
                recursion.marker.clone(),
                Name::anonymous(),
                recursion.reference.type_.clone(),
                BinderInfo::Default,
            );
        }
        Ok(())
    }

    /// Rebind source index names to this branch's constructor result, just as
    /// the original major is rebound to the constructor. Pattern names shadow
    /// these aliases, but core identities never do. Domains are specialized in
    /// family order for genuinely dependent index telescopes.
    pub(super) fn recursive_index_aliases(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        constructor_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .clone()
            .expect("recursive match specification");
        let (family, parameters) = recursion
            .family
            .as_ref()
            .expect("recursive family classified");
        let values = self.elimination_result_indices(
            constructor_type,
            family,
            *parameters,
            recursion.indices.len(),
        )?;
        let mut replacements = Vec::new();
        for (position, value) in recursion.indices.iter().zip(values) {
            let old = &recursion.parameters[*position];
            let mut type_ = self.instantiate(&old.type_)?;
            for (id, replacement) in &replacements {
                self.tick()?;
                type_ = type_
                    .abstract_fvar(id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                type_ = self.substitute(&type_, replacement)?;
            }
            if !locals.iter().any(|local| local.user_name == old.user_name) {
                let id = FVarId(self.fresh_name()?);
                self.txn
                    .lctx
                    .add_let(id.clone(), old.user_name.clone(), type_, value.clone());
                locals.push(self.txn.lctx.find(&id).expect("branch index alias").clone());
            }
            replacements.push((old.id.clone(), value));
        }
        Ok(())
    }

    pub(super) fn recursive_major_alias(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        constructor: &Expr,
        family_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let recursion = self
            .recursion
            .as_ref()
            .expect("recursive match specification");
        let name = recursion.parameters[recursion.decreasing].user_name.clone();
        if !locals.iter().any(|local| local.user_name == name) {
            let id = FVarId(self.fresh_name()?);
            self.txn
                .lctx
                .add_let(id.clone(), name, family_type.clone(), constructor.clone());
            locals.push(self.txn.lctx.find(&id).expect("major alias").clone());
        }
        Ok(())
    }

    /// Recognize a constructor child or a fully applied function-valued child.
    /// The field and its type come from an admitted constructor's recursive
    /// slots, never from merely finding a function with a similar result type.
    /// Only transparent variable aliases are followed. Every supplied argument
    /// is returned to the caller and retained in the real hypothesis application,
    /// including proof arguments, annotations and recursive calls inside them.
    fn recursive_child_arguments<'a>(
        &mut self,
        argument: &'a Expr,
        field: &Expr,
        field_type: &Expr,
    ) -> Result<Option<(Vec<&'a Expr>, Expr)>, NatDefinitionElabError> {
        let mut head = argument;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            if self.recursive_alias_value(head)? == *field {
                break;
            }
            let ExprNode::App { f, a } = head.node() else {
                return Ok(None);
            };
            arguments.push(a);
            head = f;
        }
        arguments.reverse();
        let mut type_ = self.instantiate(field_type)?;
        for argument in &arguments {
            self.tick()?;
            let current = self.whnf(&type_)?;
            let ExprNode::ForallE { body, .. } = current.node() else {
                return Ok(None);
            };
            type_ = self.substitute(body, argument)?;
        }
        let type_ = self.whnf(&type_)?;
        if matches!(type_.node(), ExprNode::ForallE { .. }) {
            return Ok(None);
        }
        Ok(Some((arguments, type_)))
    }

    /// Transform every node, including unused values and annotations. Only the
    /// original fixed local arguments and a direct child are discarded; every
    /// other argument remains in the checked term. No beta reduction is used to
    /// hide an invalid self-call. Memoization preserves DAG sharing and depth.
    pub(super) fn lower_recursive_calls(
        &mut self,
        value: &Expr,
        hypotheses: &[(FVarId, FVarId)],
    ) -> Result<Expr, NatDefinitionElabError> {
        enum Task<'a> {
            Visit(&'a Expr),
            Node(&'a Expr),
            Call(&'a Expr, Expr, Vec<&'a Expr>),
        }
        let recursion = self
            .recursion
            .clone()
            .expect("recursive branch specification");
        let mut done: HashMap<usize, Expr> = HashMap::new();
        let mut tasks = vec![Task::Visit(value)];
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Visit(expr) => {
                    let key = expr.allocation_identity();
                    if done.contains_key(&key) {
                        continue;
                    }
                    if !expr.has_fvar() {
                        done.insert(key, expr.clone());
                        continue;
                    }
                    let mut head = expr;
                    let mut arguments = Vec::new();
                    while let ExprNode::App { f, a } = head.node() {
                        self.tick()?;
                        arguments.push(a);
                        head = f;
                    }
                    if matches!(head.node(), ExprNode::FVar { id } if id == &recursion.marker) {
                        arguments.reverse();
                        if arguments.len() <= recursion.decreasing {
                            return Err(error(RecursionError::PartialApplication));
                        }
                        for (position, (argument, parameter)) in arguments
                            .iter()
                            .zip(&recursion.parameters)
                            .take(recursion.decreasing)
                            .enumerate()
                        {
                            if !recursion.indices.contains(&position)
                                && !recursion.varying.contains(&position)
                                && !self.fixed_recursive_argument(argument, parameter)?
                            {
                                return Err(error(RecursionError::GeneralizeParameter {
                                    owner: recursion.parameters[recursion.decreasing].id.clone(),
                                    position,
                                }));
                            }
                        }
                        let mut selected = None;
                        for (field, ih) in hypotheses {
                            self.tick()?;
                            let Some(local) = self.txn.lctx.find(field).cloned() else {
                                continue;
                            };
                            if let Some((child_arguments, child_type)) = self
                                .recursive_child_arguments(
                                    arguments[recursion.decreasing],
                                    &Expr::fvar(field.clone()),
                                    &local.type_,
                                )?
                            {
                                selected =
                                    Some((Expr::fvar(ih.clone()), child_arguments, child_type));
                                break;
                            }
                        }
                        let (hypothesis, mut extra, child_type) =
                            selected.ok_or_else(|| error(RecursionError::NotDecreasing))?;
                        if !recursion.indices.is_empty() {
                            let (family, parameters) = recursion
                                .family
                                .as_ref()
                                .expect("recursive family classified");
                            let indices = self.elimination_result_indices(
                                &child_type,
                                family,
                                *parameters,
                                recursion.indices.len(),
                            )?;
                            for (position, index) in recursion.indices.iter().zip(indices) {
                                // These arguments disappear into the recursor's
                                // own indices. Require the actual child index,
                                // not conversion which could erase a bad term.
                                if *arguments[*position] != index {
                                    return Err(error(RecursionError::ChangedIndex));
                                }
                            }
                        }
                        extra.extend(
                            recursion
                                .varying
                                .iter()
                                .filter_map(|position| arguments.get(*position).copied()),
                        );
                        extra.extend(arguments.iter().skip(recursion.parameters.len()).copied());
                        tasks.push(Task::Call(expr, hypothesis, extra.clone()));
                        tasks.extend(extra.into_iter().rev().map(Task::Visit));
                    } else {
                        tasks.push(Task::Node(expr));
                        tasks.extend(children(expr).into_iter().flatten().map(Task::Visit));
                    }
                }
                Task::Call(expr, mut result, extra) => {
                    for argument in extra {
                        self.tick()?;
                        result = Expr::app(result, done[&argument.allocation_identity()].clone());
                    }
                    done.insert(expr.allocation_identity(), result);
                }
                Task::Node(expr) => {
                    let child = |e: &Expr| done[&e.allocation_identity()].clone();
                    let result = match expr.node() {
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
                        _ => expr.clone(),
                    };
                    done.insert(expr.allocation_identity(), result);
                }
            }
        }
        Ok(done
            .remove(&value.allocation_identity())
            .expect("recursive lowering finishes its root"))
    }
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
    fn fixed_parameter_eta_checks_dependent_domains_and_variable_order() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let f = FVarId(Name::from_components(["polymorphic_identity"]));
        let type_ = Expr::forall_e(
            Name::anonymous(),
            Expr::sort(Level::one()),
            Expr::forall_e(
                Name::anonymous(),
                Expr::bvar(0).unwrap(),
                Expr::bvar(1).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let parameter = LocalDecl {
            id: f.clone(),
            user_name: f.0.clone(),
            type_,
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        };
        let expanded = |domain: Expr, first: u32, second: u32| {
            Expr::lam(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::lam(
                    Name::anonymous(),
                    domain,
                    Expr::app(
                        Expr::app(Expr::fvar(f.clone()), Expr::bvar(first).unwrap()),
                        Expr::bvar(second).unwrap(),
                    ),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            )
        };
        assert!(
            context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 1, 0), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::sort(Level::zero()), 1, 0), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 0, 1), &parameter)
                .unwrap()
        );
        assert!(
            !context
                .fixed_recursive_argument(&expanded(Expr::bvar(0).unwrap(), 1, 1), &parameter)
                .unwrap()
        );
    }

    #[test]
    fn fixed_parameter_eta_refusal_does_not_reduce_discardable_annotations() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let f = FVarId(Name::from_components(["fixed"]));
        let parameter = LocalDecl {
            id: f.clone(),
            user_name: f.0.clone(),
            type_: Expr::forall_e(
                Name::anonymous(),
                Expr::sort(Level::one()),
                Expr::sort(Level::one()),
                BinderInfo::Default,
            ),
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        };
        let body = Expr::let_e(
            Name::anonymous(),
            Expr::sort(Level::zero()),
            Expr::sort(Level::one()),
            Expr::app(Expr::fvar(f), Expr::bvar(1).unwrap()),
            false,
        );
        let value = Expr::lam(
            Name::anonymous(),
            Expr::sort(Level::one()),
            body,
            BinderInfo::Default,
        );
        assert!(
            !context
                .fixed_recursive_argument(&value, &parameter)
                .unwrap()
        );
        context.txn.budget.max_heartbeats = context.txn.budget.heartbeats_consumed;
        assert!(matches!(
            context.fixed_recursive_argument(&value, &parameter),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
}
