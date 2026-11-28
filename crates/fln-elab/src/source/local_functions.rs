//! Local functions close over their lexical context as ordinary checked terms.
//! Structural `let rec` uses the declaration recursor compiler, on the same
//! heap worklist as nonrecursive lets. Closure values remain opaque until the
//! owner is complete; the source engine separately admits their lifted names.
use super::*;
use std::collections::HashSet;

pub(super) mod lifting;

/// A local recursive value is checked before its continuation, but remains
/// opaque until the enclosing declaration has finished elaborating. Captures
/// are explicit arguments to its metavariable, so closing an enclosing let or
/// lambda cannot leave hidden free variables in the deferred value.
#[derive(Clone)]
pub(super) struct Deferred {
    pub id: MVarId,
    pub value: Typed,
    pub captures: Vec<LocalDecl>,
    pub lift_name: Option<Name>,
    pub lift_context: LocalContext,
    pub partial_marker: Option<FVarId>,
}

#[derive(Clone)]
pub(super) struct Binding<'a> {
    pub name: Name,
    pub opaque: bool,
    pub recursive: bool,
    pub parameters: &'a Syntax,
    pub annotation: Option<&'a Syntax>,
    pub value: &'a Syntax,
    pub body: &'a Syntax,
    pub termination: Option<recursion::StructuralHint<'a>>,
}

#[derive(Clone)]
pub(super) struct Build<'a> {
    pub binding: Binding<'a>,
    pub expected: Option<Expr>,
    pub result_type: Option<Expr>,
    /// Written `: T` annotation preserved before opening leading lambdas/equations,
    /// so closing the local function keeps declared binder names and implicitness.
    written_result_type: Option<Expr>,
    pub value_syntax: &'a Syntax,
    pub checkpoint: Option<usize>,
    pub lift_name: Option<Name>,
    outer_parent: Option<Name>,
    parameters: Vec<LocalDecl>,
    header_parameters: usize,
    lambdas: Vec<binders::Telescope<'a>>,
    saved: LocalContext,
    outer_recursion: Option<recursion::Recursion>,
    pub marker: Option<FVarId>,
    pub partial: bool,
    generalized_parameters: HashSet<usize>,
    /// A whole-body below/brecOn candidate, with no selected source match.
    pub course_parameter: Option<usize>,
    /// A recursive local whose result type is omitted (`let rec go (i : Nat) := …`).
    pub omitted: Option<recursion::OmittedResult>,
}

/// Like tactic choices, structural candidates live on the driver's flat stack.
/// Restoring a candidate restores semantic state, never spent work. The first
/// candidate is an ordinary (possibly nonrecursive) local function; only an
/// actual surviving self-reference causes structural candidates to be tried.
pub(super) struct Checkpoint<'a> {
    context: Box<Context>,
    build: Build<'a>,
    candidates: Vec<Candidate>,
    next: usize,
    generalized_parameters: HashSet<usize>,
    pub tasks: usize,
    pub values: usize,
}

#[derive(Clone, Copy)]
enum Candidate {
    Nonrecursive,
    Primitive { column: usize, decreasing: usize },
    Course { decreasing: usize },
}

impl Candidate {
    fn decreasing(self) -> Option<usize> {
        match self {
            Self::Nonrecursive => None,
            Self::Primitive { decreasing, .. } | Self::Course { decreasing } => Some(decreasing),
        }
    }
}

fn prepared<'a>(
    context: &mut Context,
    mut syntax: &'a Syntax,
) -> Result<&'a Syntax, NatDefinitionElabError> {
    while let Some(inner) = parenthesized_inner(syntax)? {
        context.tick()?;
        syntax = inner;
    }
    Ok(syntax)
}

fn original<'a>(
    context: &mut Context,
    syntax: &'a Syntax,
) -> Result<&'a Syntax, NatDefinitionElabError> {
    let syntax = prepared(context, syntax)?;
    if let Syntax::Node { kind, args, .. } = syntax
        && kind == &parser_kind(&["Term", "localRecValue"])
    {
        return args
            .first()
            .ok_or_else(|| failure(SourceInferenceError::Scope));
    }
    Ok(syntax)
}

impl<'a> Checkpoint<'a> {
    pub fn new(
        context: &mut Context,
        mut build: Build<'a>,
        tasks: usize,
        values: usize,
    ) -> Result<Self, NatDefinitionElabError> {
        context.open_local_recursive_lambdas(&mut build)?;
        let mut candidates = vec![Candidate::Nonrecursive];
        if build.partial {
            if build.binding.termination.is_some() {
                return Err(NatDefinitionElabError::UnexpectedSyntax {
                    expected: "no termination hint on a partial local function",
                });
            }
            return Ok(Self {
                context: Box::new(context.clone()),
                build,
                candidates,
                next: 0,
                generalized_parameters: HashSet::new(),
                tasks,
                values,
            });
        }
        let body = original(context, build.value_syntax)?;
        let prepared = prepared(context, build.value_syntax)?;
        match context.recursion_columns(&build.parameters, body) {
            Ok(columns) => {
                for (column, decreasing) in columns {
                    context.tick()?;
                    if let Syntax::Node { kind, args, .. } = prepared
                        && kind == &parser_kind(&["Term", "localRecValue"])
                        && args
                            .get(column + 2)
                            .ok_or_else(|| failure(SourceInferenceError::Scope))?
                            .is_missing()
                    {
                        // Matrix preprocessing already proved this column has
                        // no structural split. It cannot rescue a failing real
                        // candidate and must not replace its termination error
                        // with the absent candidate's RootMatchRequired.
                        continue;
                    }
                    candidates.push(Candidate::Primitive { column, decreasing });
                }
            }
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                recursion::RecursionError::RootMatchRequired,
            ))) => {}
            Err(problem) => return Err(problem),
        }
        // A local body may match its decreasing argument inside an application
        // or lambda. The checked below dictionary lowers that entire body, so
        // these candidates need an actual inductive parameter, not a root match.
        for (decreasing, parameter) in build.parameters.iter().enumerate() {
            context.tick()?;
            let type_ = context.whnf(&parameter.type_)?;
            let (head, _) = context.course_spine(&type_)?;
            let ExprNode::Const { name, .. } = head.node() else {
                continue;
            };
            let single_family = matches!(
                context.txn.env.find(name),
                Some(fln_env::constants::ConstantInfo::Induct(family)) if family.all.len() == 1
            );
            if single_family && context.is_auxiliary_recursor(&Name::str(name.clone(), "brecOn"))? {
                candidates.push(Candidate::Course { decreasing });
            }
        }
        Ok(Self {
            context: Box::new(context.clone()),
            build,
            candidates,
            next: 0,
            generalized_parameters: HashSet::new(),
            tasks,
            values,
        })
    }
    pub fn begin(&mut self, index: usize) -> (Build<'a>, Option<usize>) {
        let candidate = self.candidates[self.next];
        self.next += 1;
        let mut build = self.build.clone();
        build.checkpoint = Some(index);
        build.generalized_parameters = self.generalized_parameters.clone();
        let column = match candidate {
            Candidate::Nonrecursive => None,
            Candidate::Primitive { column, .. } => Some(column),
            Candidate::Course { decreasing } => {
                build.course_parameter = Some(decreasing);
                None
            }
        };
        (build, column)
    }
    pub fn restore(&self, context: &mut Context) {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = (*self.context).clone();
        context.txn.budget.heartbeats_consumed = spent;
    }
    pub fn retry(&mut self, problem: &NatDefinitionElabError) -> bool {
        if let NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
            recursion::RecursionError::GeneralizeParameter { owner, position },
        )) = problem
        {
            if let Some(decreasing) = self
                .next
                .checked_sub(1)
                .and_then(|index| self.candidates.get(index))
                .and_then(|candidate| candidate.decreasing())
                && owner == &self.build.parameters[decreasing].id
                && *position < decreasing
                && self.generalized_parameters.insert(*position)
            {
                // Rebuild the same candidate with a strictly larger mask.
                // A request for an enclosing function must propagate to it.
                self.next -= 1;
                return true;
            }
            return false;
        }
        self.generalized_parameters.clear();
        retryable(problem) && self.next < self.candidates.len()
    }
}

pub(super) fn retryable(problem: &NatDefinitionElabError) -> bool {
    matches!(
        problem,
        NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
            recursion::RecursionError::NotDecreasing
                | recursion::RecursionError::ChangedParameter
                | recursion::RecursionError::ChangedIndex
                | recursion::RecursionError::RootMatchRequired
                | recursion::RecursionError::ExplicitParameterRequired
                | recursion::RecursionError::PartialApplication
        ))
    )
}

impl Context {
    pub(super) fn defer_local_function(
        &mut self,
        value: Typed,
        lift_name: Option<Name>,
        partial_marker: Option<FVarId>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let locals = self.txn.lctx.decls().to_vec();
        let mut reads = self.elimination_reads(&value.value)?;
        reads.extend(self.elimination_reads(&value.type_)?);
        let mut captures = Vec::new();
        for local in locals.iter().rev() {
            self.tick()?;
            if partial_marker.is_some() || reads.contains(&local.id) {
                reads.extend(self.elimination_reads(&local.type_)?);
                if let Some(value) = &local.value {
                    reads.extend(self.elimination_reads(value)?);
                }
                captures.push(local.clone());
            }
        }
        captures.reverse();
        let mut type_ = self.instantiate(&value.type_)?;
        for local in captures.iter().rev() {
            self.tick()?;
            type_ = Expr::forall_e(
                local.user_name.clone(),
                self.instantiate(&local.type_)?,
                type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                local.binder_info,
            );
        }
        let name = self.fresh_name()?;
        let id = MVarId(name.clone());
        self.txn.mvars.declare(
            id.clone(),
            name,
            type_,
            LocalContext::new(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        let mut reference = Expr::mvar(id.clone());
        for local in &captures {
            self.tick()?;
            reference = Expr::app(reference, Expr::fvar(local.id.clone()));
        }
        let type_ = value.type_.clone();
        self.deferred_local_functions.push(Deferred {
            id,
            value,
            captures,
            lift_name,
            lift_context: self.txn.lctx.clone(),
            partial_marker,
        });
        Ok(Typed {
            value: reference,
            type_,
        })
    }

    /// The pin assigns let-rec metavariables while forming the enclosing
    /// declaration's closure (`MutualClosure.mkLetRecClosures`), after its
    /// header and body constraints have already been checked. Assignment here
    /// grants no admission authority: the resulting closed declaration still
    /// passes the ordinary kernel and independent checker.
    pub(super) fn complete_local_functions(&mut self) -> Result<(), NatDefinitionElabError> {
        if self.deferred_local_functions.is_empty() {
            return Ok(());
        }
        self.resolve_instances(true)?;
        self.flush(true)?;
        let deferred = std::mem::take(&mut self.deferred_local_functions);
        for pending in deferred {
            self.tick()?;
            if pending.partial_marker.is_some() {
                // The parent and every helper close together, after all
                // delayed body constraints have settled. Inlining here would
                // erase the dependency graph or expose a recursive proof.
                self.deferred_local_functions.push(pending);
                continue;
            }
            let mut value = self.instantiate(&pending.value.value)?;
            for local in pending.captures.iter().rev() {
                self.tick()?;
                value = Expr::lam(
                    local.user_name.clone(),
                    self.instantiate(&local.type_)?,
                    value
                        .abstract_fvar(&local.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    local.binder_info,
                );
            }
            if let Some(name) = pending.lift_name {
                self.local_function_lifting.closed.push(lifting::Closed {
                    name,
                    term: pending.value,
                    context: pending.lift_context,
                });
            }
            self.txn
                .mvars
                .assign(pending.id, value, AssignmentJustification::UserGiven)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
        }
        Ok(())
    }

    /// Freeze a public signature using only closures elaborated in its public
    /// predecessor. Its proof still sees the original opaque metavariables.
    /// Universe assignments and spent work remain shared across this boundary;
    /// only the temporary disclosure of local function values is restored.
    pub(super) fn with_closed_local_function_header<T>(
        &mut self,
        freeze: impl FnOnce(&mut Context) -> Result<T, NatDefinitionElabError>,
    ) -> Result<T, NatDefinitionElabError> {
        if self.deferred_local_functions.is_empty() {
            return freeze(self);
        }
        let mvars = self.txn.mvars.clone();
        let deferred = self.deferred_local_functions.clone();
        let lifting = self.local_function_lifting.clone();
        let result = self.complete_local_functions().and_then(|()| freeze(self));
        self.txn.mvars = mvars;
        self.deferred_local_functions = deferred;
        self.local_function_lifting = lifting;
        result
    }

    pub(super) fn start_local_function<'a>(
        &mut self,
        binding: Binding<'a>,
        expected: Option<Expr>,
    ) -> Result<Build<'a>, NatDefinitionElabError> {
        let lift_name = if binding.recursive {
            self.reserve_local_function_name(&binding.name)?
        } else {
            None
        };
        let outer_parent = self.local_function_lifting.parent.clone();
        let partial = binding.recursive && self.collect_partial_locals();
        let saved = self.txn.lctx.clone();
        let parameters = self.bind_parameters(binding.parameters)?;
        let header_parameters = parameters.len();
        // A recursive local may omit its result type, as a recursive definition may: its body
        // is checked against a hole, its self reference against `?F x₁ … xₙ`.
        let omitted = if binding.recursive && binding.annotation.is_none() {
            let omitted = self.omitted_result_type(&parameters)?;
            self.omitted_results.push(omitted.clone());
            Some(omitted)
        } else {
            None
        };
        // Signatures see the enclosing scope. Nonrecursive values do too;
        // recursive values introduce their self binder after this phase.
        Ok(Build {
            value_syntax: binding.value,
            binding,
            expected,
            result_type: None,
            written_result_type: None,
            checkpoint: None,
            lift_name,
            outer_parent,
            parameters,
            header_parameters,
            lambdas: Vec::new(),
            saved,
            outer_recursion: None,
            marker: None,
            partial,
            generalized_parameters: HashSet::new(),
            course_parameter: None,
            omitted,
        })
    }

    /// A recursive local's written lambdas belong to its function telescope,
    /// just like named header parameters. Check their domains with the local
    /// self in scope, so an outer declaration with the same name cannot supply
    /// an annotation that the source's actual recursive name would invalidate.
    fn open_local_recursive_lambdas<'a>(
        &mut self,
        build: &mut Build<'a>,
    ) -> Result<(), NatDefinitionElabError> {
        let syntax = prepared(self, build.value_syntax)?;
        if self.lambda_syntax(syntax)?.is_none() {
            return Ok(());
        }
        let saved = self.txn.lctx.clone();
        let outer = self.recursion.clone();
        let enclosing = self.enclosing_recursions.len();
        let parent = self.local_function_lifting.parent.clone();
        self.start_local_function_value(build, None)?;
        let marker = build
            .marker
            .clone()
            .expect("temporary local recursive self");
        let (body, expected, mut lambdas) = self.open_recursive_lambdas(
            build.value_syntax,
            build.result_type.clone(),
            &mut build.parameters,
            Some(&marker),
        )?;
        let expected = expected.ok_or_else(|| failure(SourceInferenceError::ExpectedFunction))?;
        // A recursive call in a domain precedes the structural match, so no
        // smaller constructor field can justify it. Do not retain a temporary
        // self through the domains or turn it into an ordinary captured value.
        for parameter in &build.parameters[build.header_parameters..] {
            if self.elimination_reads(&parameter.type_)?.contains(&marker) {
                return Err(failure(SourceInferenceError::Recursion(
                    recursion::RecursionError::NotDecreasing,
                )));
            }
        }
        if self.elimination_reads(&expected)?.contains(&marker) {
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::NotDecreasing,
            )));
        }
        for lambda in &mut lambdas {
            self.forget_telescope_local(lambda, &marker)?;
        }
        self.txn.lctx = saved;
        for parameter in &build.parameters[build.header_parameters..] {
            self.tick()?;
            tactics::eliminate::add_local(&mut self.txn.lctx, parameter);
        }
        self.recursion = outer;
        self.enclosing_recursions.truncate(enclosing);
        self.local_function_lifting.parent = parent;
        build.marker = None;
        build.outer_recursion = None;
        build.written_result_type = build.result_type.clone();
        build.value_syntax = body;
        build.result_type = Some(expected);
        build.lambdas = lambdas;
        Ok(())
    }

    pub(super) fn start_local_function_value(
        &mut self,
        build: &mut Build<'_>,
        column: Option<usize>,
    ) -> Result<(), NatDefinitionElabError> {
        if !build.binding.recursive {
            return Ok(());
        }
        self.local_function_lifting.parent = build.lift_name.clone();
        // The function is not in scope in its signature. Only now can its
        // complete type and private recursive marker be introduced.
        build.outer_recursion = self.recursion.take();
        if let Some(outer) = &build.outer_recursion {
            self.enclosing_recursions.push(outer.clone());
        }
        let expected = build
            .result_type
            .as_ref()
            .expect("recursive result annotation");
        let mut body = original(self, build.value_syntax)?;
        while let Some(inner) = parenthesized_inner(body)? {
            self.tick()?;
            body = inner;
        }
        let marker = if let Some(decreasing) = build.course_parameter {
            if let Some(hint) = &build.binding.termination
                && self.structural_hint_parameter(
                    hint,
                    &build.parameters,
                    build.header_parameters,
                )? != decreasing
            {
                return Err(failure(SourceInferenceError::Recursion(
                    recursion::RecursionError::NotDecreasing,
                )));
            }
            self.prepare_recursion_parameter(
                &build.binding.name,
                &build.parameters,
                expected,
                decreasing,
            )?;
            let recursion = self.recursion.as_mut().expect("local course candidate");
            recursion.generalized_parameters = build.generalized_parameters.clone();
            // First check the original body with only its abstract self. The
            // driver's next phase installs the checked induction dictionary.
            recursion.pending = false;
            recursion.reference.clone()
        } else if let Some(column) = column {
            let columns = self.recursion_columns(&build.parameters, body)?;
            if let Some(hint) = &build.binding.termination {
                let parameter = self.structural_hint_parameter(
                    hint,
                    &build.parameters,
                    build.header_parameters,
                )?;
                if !columns
                    .iter()
                    .any(|&(candidate, position)| candidate == column && position == parameter)
                {
                    // The initial nonrecursive candidate still runs first.
                    // A surviving self reference may try only the column the
                    // hint selects, never silently succeed on another one.
                    return Err(failure(SourceInferenceError::Recursion(
                        recursion::RecursionError::NotDecreasing,
                    )));
                }
            }
            let matched: Vec<_> = columns.iter().map(|(_, position)| *position).collect();
            self.prepare_recursion(
                &build.binding.name,
                &build.parameters,
                body,
                Some(expected),
                column,
                &matched,
            )?;
            self.recursion
                .as_mut()
                .expect("local structural candidate")
                .generalized_parameters = build.generalized_parameters.clone();
            self.recursion
                .as_ref()
                .expect("local structural candidate")
                .reference
                .clone()
        } else {
            // `let rec` is also legal without a recursive occurrence. An
            // unsupported recursive occurrence keeps this marker and fails
            // the complete-term escape check below, including unused values.
            let reference = self.reference_result(expected);
            let mut type_ = self.instantiate(&reference)?;
            for parameter in build.parameters.iter().rev() {
                self.tick()?;
                type_ = Expr::forall_e(
                    self.declared_binder_name(parameter),
                    self.instantiate(&parameter.type_)?,
                    type_
                        .abstract_fvar(&parameter.id, 0)
                        .map_err(|_| failure(SourceInferenceError::Scope))?,
                    parameter.binder_info,
                );
            }
            Typed {
                value: Expr::fvar(FVarId(self.fresh_name()?)),
                type_,
            }
        };
        if let Syntax::Node { kind, args, .. } = prepared(self, build.value_syntax)?
            && kind == &parser_kind(&["Term", "localRecValue"])
        {
            let index = column.map_or(1, |column| column + 2);
            build.value_syntax = args
                .get(index)
                .ok_or_else(|| failure(SourceInferenceError::Scope))?;
            if build.value_syntax.is_missing() {
                return Err(failure(SourceInferenceError::Recursion(
                    recursion::RecursionError::RootMatchRequired,
                )));
            }
            if let Some(recursion) = &mut self.recursion {
                recursion.matrix = true;
            }
        }
        let ExprNode::FVar { id } = marker.value.node() else {
            return Err(failure(SourceInferenceError::Scope));
        };
        build.marker = Some(id.clone());
        if build.partial && build.checkpoint.is_some() {
            self.register_partial_local(
                build
                    .lift_name
                    .as_ref()
                    .ok_or_else(|| failure(SourceInferenceError::Scope))?,
                id,
            )?;
        }
        // Put the self binder BEFORE the parameters: self shadows an outer
        // local/global, but a parameter with the same source name shadows self.
        let mut context = LocalContext::new();
        for local in build.saved.decls() {
            self.tick()?;
            let mut local = local.clone();
            // A top-level recursive marker normally resolves through the
            // active Recursion record. That record is suspended while this
            // local function is checked. Retain the same identity at its same
            // lexical position, under its fully qualified source name, so the
            // enclosing recursor can still validate and lower every call.
            // Local recursive names already have the appropriate binding.
            if local.user_name.is_anonymous()
                && let Some(outer) = &build.outer_recursion
                && local.id == outer.marker
            {
                local.user_name = outer.name.clone();
            }
            tactics::eliminate::add_local(&mut context, &local);
        }
        context.add_param(
            id.clone(),
            build.binding.name.clone(),
            marker.type_,
            BinderInfo::Default,
        );
        for parameter in &build.parameters {
            self.tick()?;
            tactics::eliminate::add_local(&mut context, parameter);
        }
        self.txn.lctx = context;
        Ok(())
    }

    pub(super) fn close_local_function(
        &mut self,
        build: &Build<'_>,
        mut value: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.flush(false)?;
        value.value = self.instantiate(&value.value)?;
        value.type_ = self.instantiate(build.result_type.as_ref().unwrap_or(&value.type_))?;
        if let Some(marker) = &build.marker
            && ((!build.partial && self.elimination_reads(&value.value)?.contains(marker))
                || self.elimination_reads(&value.type_)?.contains(marker))
        {
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::NotDecreasing,
            )));
        }
        value = self.close_recursive_lambdas(&build.lambdas, value)?;
        if let Some(written) = &build.written_result_type {
            value.type_ = self.local_function_header_type(written, &value.type_)?;
        }
        // Header parameters close here rather than through finish_telescope.
        // Goals solved by the continuation must keep their local dictionaries
        // and inferred domains underneath these binders.
        value.value = self.instantiate(&value.value)?;
        value.type_ = self.instantiate(&value.type_)?;
        let parameters = &build.parameters[..build.header_parameters];
        self.capture_bound_metavars(parameters, &build.saved, &mut value)?;
        if self.capture_bound_coercions(parameters, &build.saved, &value)? {
            value.value = self.instantiate(&value.value)?;
            value.type_ = self.instantiate(&value.type_)?;
        }
        for local in parameters.iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            value.value = value
                .value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value.type_ = value
                .type_
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            value.value = Expr::lam(
                local.user_name.clone(),
                domain.clone(),
                value.value,
                local.binder_info,
            );
            value.type_ = Expr::forall_e(
                local.user_name.clone(),
                domain,
                value.type_,
                local.binder_info,
            );
        }
        self.txn.lctx = build.saved.clone();
        if build.binding.recursive {
            self.local_function_lifting.parent = build.outer_parent.clone();
            self.recursion = build.outer_recursion.clone();
            if build.outer_recursion.is_some() {
                self.enclosing_recursions.pop();
            }
        }
        // An explicit result remains in the let-bound function's full type.
        // K1 therefore checks it even when the enclosing body never calls f.
        Ok(value)
    }

    /// Closing the actual lambdas supplies a function telescope even while a
    /// header hole's universe constraints await the continuation's arguments.
    /// Keep the written prefix's names, domains and implicitness, but expose a
    /// known inferred Pi at an assignable type-hole tail. The original header
    /// equations from `finish_telescope` remain obligations; this inspection
    /// makes no assignments and cannot disclose an opaque local type.
    fn local_function_header_type(
        &mut self,
        written: &Expr,
        inferred: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let written = self.instantiate(written)?;
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut declared = written.clone();
            let mut inferred = inferred.clone();
            let mut prefix = Vec::new();
            loop {
                self.tick()?;
                let actual = self.whnf(&inferred)?;
                let ExprNode::ForallE {
                    body: actual_body, ..
                } = actual.node()
                else {
                    return Ok(written.clone());
                };
                let formal = self.whnf(&declared)?;
                if let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = formal.node()
                {
                    // Open both telescopes at the same fresh local. Reduction
                    // must never inspect their dependent bodies as loose terms.
                    let id = FVarId(self.fresh_name()?);
                    self.txn.lctx.add_param(
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    );
                    prefix.push((
                        id.clone(),
                        binder_name.clone(),
                        binder_type.clone(),
                        *binder_info,
                    ));
                    let local = Expr::fvar(id);
                    declared = self.substitute(body, &local)?;
                    inferred = self.substitute(actual_body, &local)?;
                    continue;
                }
                let mut head = &formal;
                while let ExprNode::App { f, .. } = head.node() {
                    self.tick()?;
                    head = f;
                }
                let ExprNode::MVar { id } = head.node() else {
                    return Ok(written.clone());
                };
                if !self.txn.mvars.assignment_permitted(id)
                    || self.txn.mvars.is_assigned(id)
                    || !self.txn.mvars.get_decl(id).is_some_and(|declaration| {
                        declaration.kind == MetavarKind::Natural && declaration.delayed.is_none()
                    })
                {
                    return Ok(written.clone());
                }
                let mut type_ = actual;
                for (id, name, domain, style) in prefix.into_iter().rev() {
                    self.tick()?;
                    type_ = Expr::forall_e(
                        name,
                        domain,
                        type_
                            .abstract_fvar(&id, 0)
                            .map_err(|_| failure(SourceInferenceError::Scope))?,
                        style,
                    );
                }
                return Ok(type_);
            }
        })();
        self.txn.lctx = saved;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_restore_preserves_spent_work_but_no_speculative_state() {
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let missing = Syntax::Missing;
        let binding = Binding {
            name: Name::from_components(["go"]),
            opaque: false,
            recursive: true,
            parameters: &missing,
            annotation: Some(&missing),
            value: &missing,
            body: &missing,
            termination: None,
        };
        let build = Build {
            binding,
            expected: None,
            result_type: None,
            written_result_type: None,
            value_syntax: &missing,
            checkpoint: None,
            lift_name: None,
            outer_parent: None,
            parameters: Vec::new(),
            header_parameters: 0,
            lambdas: Vec::new(),
            saved: LocalContext::new(),
            outer_recursion: None,
            marker: None,
            partial: false,
            generalized_parameters: HashSet::new(),
            course_parameter: None,
            omitted: None,
        };
        let checkpoint = Checkpoint::new(&mut context, build, 3, 7).unwrap();
        let initial_next = context.next;
        let initial_mvars = context.txn.mvars.clone();
        let hole = context.hole(Expr::sort(Level::zero())).unwrap();
        context
            .equations
            .push(SourceEquation::inference(hole.clone(), hole));
        context.attempt_depth = 12;
        let spent = context.txn.budget.heartbeats_consumed;
        assert!(spent > checkpoint.context.txn.budget.heartbeats_consumed);
        checkpoint.restore(&mut context);
        assert_eq!(context.txn.budget.heartbeats_consumed, spent);
        assert_eq!(context.next, initial_next);
        assert_eq!(context.txn.mvars, initial_mvars);
        assert_eq!(context.attempt_depth, 0);
        assert!(context.equations.is_empty());
        context.txn.budget.max_heartbeats = spent;
        assert!(matches!(
            context.tick(),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }

    #[test]
    fn prepared_local_matrices_do_not_rewrite_their_original_candidates() {
        let source = b"def result : Nat := let rec go (a b : Nat) : Nat := match a, b with | _, .zero => a | _, .succ k => go a k; go 0 3";
        let parsed = fln_parse::parse_definition(source).unwrap();
        let mut context = Context::new(&Environment::new(), Budget::DEFAULT);
        let once = context
            .lower_pattern_matrices(parsed.syntax())
            .unwrap()
            .into_owned();
        let next = context.next;
        let twice = context.lower_pattern_matrices(&once).unwrap();
        assert_eq!(*twice, once);
        assert_eq!(context.next, next);
    }
}
