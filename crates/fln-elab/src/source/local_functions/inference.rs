//! A nonrecursive helper may need constraints from its uses before its value
//! can elaborate. The worklist first tries the value normally. Only a blocker
//! owned by its incomplete signature can reverse that local scheduling: the
//! continuation constrains a typed opaque placeholder, then the original value
//! is always replayed and checked before the enclosing let returns.
use super::*;

pub(in crate::source) struct Checkpoint<'a> {
    context: Box<Context>,
    build: Build<'a>,
    pub tasks: usize,
    pub values: usize,
}

pub(in crate::source) struct Replay<'a> {
    build: Build<'a>,
    header: LocalContext,
    placeholder: MVarId,
    type_: Expr,
}

pub(in crate::source) struct ReplayCheckpoint {
    context: Box<Context>,
    continuation: Typed,
    pub tasks: usize,
    pub values: usize,
}

impl ReplayCheckpoint {
    pub fn new(context: &Context, continuation: &Typed, tasks: usize, values: usize) -> Self {
        Self {
            context: Box::new(context.clone()),
            continuation: continuation.clone(),
            tasks,
            values,
        }
    }

    pub fn fail(self, context: &mut Context, problem: NatDefinitionElabError) -> Typed {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = *self.context;
        context.txn.budget.heartbeats_consumed = spent;
        // The continuation selected this synthetic value. Its later diagnostic
        // remains an error of that declaration, as for a postponed argument;
        // an enclosing tactic cannot silently replace the selected value.
        context.postponed_application_errors.push(problem);
        self.continuation
    }
}

impl<'a> Checkpoint<'a> {
    pub fn new(
        context: &mut Context,
        build: &mut Build<'a>,
        tasks: usize,
        values: usize,
    ) -> Result<Option<Self>, NatDefinitionElabError> {
        if build.binding.recursive {
            return Err(failure(SourceInferenceError::Scope));
        }
        if build.result_type.is_none() {
            let sort = context.type_expected()?;
            build.result_type = Some(context.hole(sort)?);
        }
        let mut incomplete = context
            .instantiate(build.result_type.as_ref().expect("local result"))?
            .has_expr_mvar();
        for parameter in &build.parameters {
            context.tick()?;
            incomplete |= context.instantiate(&parameter.type_)?.has_expr_mvar();
        }
        Ok(incomplete.then(|| Self {
            context: Box::new(context.clone()),
            build: build.clone(),
            tasks,
            values,
        }))
    }

    /// A failed projection or expected-type notation is suspension only when
    /// its unavailable type descends from this helper's own signature holes.
    /// Unknown constants, type errors, internal failures and exhausted work
    /// never select this path.
    pub fn owns(
        &self,
        context: &mut Context,
        blocker: &MVarId,
    ) -> Result<bool, NatDefinitionElabError> {
        for root in self
            .build
            .parameters
            .iter()
            .map(|parameter| &parameter.type_)
            .chain(self.build.result_type.iter())
        {
            context.tick()?;
            let current = context.instantiate(root)?;
            if context.txn.mvars.collect_mvars(&current).contains(blocker) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn restore(&self, context: &mut Context) {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = (*self.context).clone();
        context.txn.budget.heartbeats_consumed = spent;
    }

    pub fn suspend(
        self,
        context: &mut Context,
    ) -> Result<(Replay<'a>, Typed), NatDefinitionElabError> {
        let mut build = self.build;
        build.checkpoint = None;
        let header = context.txn.lctx.clone();
        for index in 0..build.parameters.len() {
            context.tick()?;
            let domain = context.instantiate(&build.parameters[index].type_)?;
            let sort = context
                .known_type(&domain)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let mut domain = Typed {
                value: domain,
                type_: sort,
            };
            context.capture_bound_metavars(&build.parameters, &build.saved, &mut domain)?;
            build.parameters[index].type_ = domain.value;
        }
        let result = build.result_type.clone().expect("local result");
        let sort = context
            .known_type(&result)?
            .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
        let mut signature = Typed {
            value: result,
            type_: sort,
        };
        // Close inference holes before abstracting the written parameters.
        // Otherwise a later assignment could introduce a removed local under
        // the already closed function telescope.
        context.capture_bound_metavars(&build.parameters, &build.saved, &mut signature)?;
        let type_ = context.forall_captured(&build.parameters, signature.value)?;
        context.txn.lctx = build.saved.clone();
        let name = context.fresh_name()?;
        let placeholder = MVarId(name.clone());
        context.txn.mvars.declare(
            placeholder.clone(),
            name,
            type_.clone(),
            context.txn.lctx.clone(),
            MetavarKind::SyntheticOpaque,
            0,
            None,
        );
        let value = Typed {
            value: Expr::mvar(placeholder.clone()),
            type_: type_.clone(),
        };
        Ok((
            Replay {
                build,
                header,
                placeholder,
                type_,
            },
            value,
        ))
    }
}

impl<'a> Replay<'a> {
    pub fn binding(&self) -> &Binding<'a> {
        &self.build.binding
    }

    pub fn expected(&self) -> Option<Expr> {
        self.build.expected.clone()
    }

    pub fn begin(&self, context: &mut Context) -> (&'a Syntax, Option<Expr>) {
        // Its own name was absent from this scope when the helper was written.
        // The continuation's local is never visible while replaying its value.
        context.txn.lctx = self.header.clone();
        (self.build.binding.value, self.build.result_type.clone())
    }

    pub fn finish(
        self,
        context: &mut Context,
        value: Typed,
        mut continuation: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        let value = context.close_local_function(&self.build, value)?;
        context.constrain_type(&value.type_, &self.type_)?;
        context
            .txn
            .assign_mvar(
                self.placeholder,
                value.value,
                AssignmentJustification::SyntheticHole,
            )
            .map_err(|error| {
                failure(SourceInferenceError::Unification(Box::new(
                    UnificationError::Metavariable(error),
                )))
            })?;
        context.flush(false)?;
        continuation.value = context.instantiate(&continuation.value)?;
        continuation.type_ = context.instantiate(&continuation.type_)?;
        Ok(continuation)
    }
}
