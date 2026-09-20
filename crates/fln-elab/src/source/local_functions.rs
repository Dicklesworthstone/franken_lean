//! Local functions close over their lexical context as ordinary checked terms.
//! Structural `let rec` uses the declaration recursor compiler, on the same
//! heap worklist as nonrecursive lets. No generated global or axiom is used.
use super::*;

#[derive(Clone)]
pub(super) struct Binding<'a> {
    pub name: Name,
    pub opaque: bool,
    pub recursive: bool,
    pub parameters: &'a Syntax,
    pub annotation: Option<&'a Syntax>,
    pub value: &'a Syntax,
    pub body: &'a Syntax,
}

#[derive(Clone)]
pub(super) struct Build<'a> {
    pub binding: Binding<'a>,
    pub expected: Option<Expr>,
    pub result_type: Option<Expr>,
    pub value_syntax: &'a Syntax,
    pub checkpoint: Option<usize>,
    parameters: Vec<LocalDecl>,
    saved: LocalContext,
    outer_recursion: Option<recursion::Recursion>,
    marker: Option<FVarId>,
}

/// Like tactic choices, structural candidates live on the driver's flat stack.
/// Restoring a candidate restores semantic state, never spent work. The first
/// candidate is an ordinary (possibly nonrecursive) local function; only an
/// actual surviving self-reference causes structural candidates to be tried.
pub(super) struct Checkpoint<'a> {
    context: Box<Context>,
    build: Build<'a>,
    candidates: Vec<Option<usize>>,
    next: usize,
    pub tasks: usize,
    pub values: usize,
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
        build: Build<'a>,
        tasks: usize,
        values: usize,
    ) -> Result<Self, NatDefinitionElabError> {
        let mut candidates = vec![None];
        let body = original(context, build.binding.value)?;
        match context.recursion_columns(&build.parameters, body) {
            Ok(columns) => candidates.extend(columns.into_iter().map(|(column, _)| Some(column))),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::Recursion(
                recursion::RecursionError::RootMatchRequired,
            ))) => {}
            Err(problem) => return Err(problem),
        }
        Ok(Self {
            context: Box::new(context.clone()),
            build,
            candidates,
            next: 0,
            tasks,
            values,
        })
    }
    pub fn begin(&mut self, index: usize) -> (Build<'a>, Option<usize>) {
        let candidate = self.candidates[self.next];
        self.next += 1;
        let mut build = self.build.clone();
        build.checkpoint = Some(index);
        (build, candidate)
    }
    pub fn restore(&self, context: &mut Context) {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = (*self.context).clone();
        context.txn.budget.heartbeats_consumed = spent;
    }
    pub fn retry(&self) -> bool {
        self.next < self.candidates.len()
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
    pub(super) fn start_local_function<'a>(
        &mut self,
        binding: Binding<'a>,
        expected: Option<Expr>,
    ) -> Result<Build<'a>, NatDefinitionElabError> {
        if binding.recursive && binding.annotation.is_none() {
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::ResultTypeRequired,
            )));
        }
        let saved = self.txn.lctx.clone();
        let parameters = self.bind_parameters(binding.parameters)?;
        // Signatures see the enclosing scope. Nonrecursive values do too;
        // recursive values introduce their self binder after this phase.
        Ok(Build {
            value_syntax: binding.value,
            binding,
            expected,
            result_type: None,
            checkpoint: None,
            parameters,
            saved,
            outer_recursion: None,
            marker: None,
        })
    }

    pub(super) fn start_local_function_value(
        &mut self,
        build: &mut Build<'_>,
        column: Option<usize>,
    ) -> Result<(), NatDefinitionElabError> {
        if !build.binding.recursive {
            return Ok(());
        }
        // The function is not in scope in its signature. Only now can its
        // complete type and private recursive marker be introduced.
        build.outer_recursion = self.recursion.take();
        let expected = build
            .result_type
            .as_ref()
            .expect("recursive result annotation");
        let mut body = original(self, build.binding.value)?;
        while let Some(inner) = parenthesized_inner(body)? {
            self.tick()?;
            body = inner;
        }
        let marker = if let Some(column) = column {
            let columns = self.recursion_columns(&build.parameters, body)?;
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
                .as_ref()
                .expect("local structural candidate")
                .reference
                .clone()
        } else {
            // `let rec` is also legal without a recursive occurrence. An
            // unsupported recursive occurrence keeps this marker and fails
            // the complete-term escape check below, including unused values.
            let mut type_ = self.instantiate(expected)?;
            for parameter in build.parameters.iter().rev() {
                self.tick()?;
                type_ = Expr::forall_e(
                    parameter.user_name.clone(),
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
        if let Syntax::Node { kind, args, .. } = prepared(self, build.binding.value)?
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
            && (self.elimination_reads(&value.value)?.contains(marker)
                || self.elimination_reads(&value.type_)?.contains(marker))
        {
            return Err(failure(SourceInferenceError::Recursion(
                recursion::RecursionError::NotDecreasing,
            )));
        }
        for local in build.parameters.iter().rev() {
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
            self.recursion = build.outer_recursion.clone();
        }
        // An explicit result remains in the let-bound function's full type.
        // K1 therefore checks it even when the enclosing body never calls f.
        Ok(value)
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
        };
        let build = Build {
            binding,
            expected: None,
            result_type: None,
            value_syntax: &missing,
            checkpoint: None,
            parameters: Vec::new(),
            saved: LocalContext::new(),
            outer_recursion: None,
            marker: None,
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
