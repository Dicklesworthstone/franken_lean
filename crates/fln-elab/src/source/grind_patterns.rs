//! Global explicit triggers, elaborated in the admitted theorem's telescope.
//! The pinned command is Lean/Elab/Tactic/Grind/Main.lean:elabGrindPattern.
//! Unsupported normalization and constraint forms refuse before publication.
use super::*;
use crate::grind_patterns::{self as registry, GrindPattern, GrindPatternError};
use fln_env::constants::ConstantInfo;

pub struct Request<'a> {
    declaration: &'a Syntax,
    patterns: Vec<&'a Syntax>,
}

pub fn registry_error(error: GrindPatternError) -> NatDefinitionElabError {
    match error {
        GrindPatternError::Limit => failure(SourceInferenceError::ResourceLimit),
        error => failure(SourceInferenceError::GrindPattern(error)),
    }
}

fn unsupported(feature: &'static str) -> NatDefinitionElabError {
    registry_error(GrindPatternError::Unsupported(feature))
}

pub fn command(syntax: &Syntax) -> Result<Request<'_>, NatDefinitionElabError> {
    let [
        kind,
        keyword,
        attribute,
        declaration,
        arrow,
        patterns,
        constraints,
    ] = expect_node(
        syntax,
        &parser_kind(&["Command", "grindPattern"]),
        7,
        "a grind_pattern command",
    )?
    else {
        return Err(unsupported("malformed command"));
    };
    let [kind] = expect_node(
        kind,
        &parser_kind(&["Term", "attrKind"]),
        1,
        "grind_pattern scope",
    )?
    else {
        return Err(unsupported("malformed command scope"));
    };
    if !expect_null_args(kind, "global grind_pattern")?.is_empty() {
        return Err(unsupported("local or scoped registration"));
    }
    expect_atom(keyword, "grind_pattern", "grind_pattern keyword")?;
    match expect_null_args(attribute, "grind registry selection")? {
        [] => {}
        [
            open,
            Syntax::Ident {
                val, preresolved, ..
            },
            close,
        ] if *val == Name::from_components(["grind"]) && preresolved.is_empty() => {
            expect_atom(open, "[", "grind registry opener")?;
            expect_atom(close, "]", "grind registry closer")?;
        }
        _ => return Err(unsupported("a custom grind registry")),
    }
    if !matches!(declaration, Syntax::Ident { preresolved, .. } if preresolved.is_empty()) {
        return Err(unsupported("a non-global or pre-resolved theorem name"));
    }
    if !matches!(arrow, Syntax::Atom { val, .. } if val == "=>" || val == "⇒") {
        return Err(unsupported("a malformed pattern arrow"));
    }
    if !expect_null_args(constraints, "grind pattern constraints")?.is_empty() {
        return Err(unsupported("where constraints"));
    }
    let parts = expect_null_args(patterns, "grind multipattern")?;
    if parts.is_empty() || parts.len() % 2 == 0 {
        return Err(unsupported("an empty or malformed multipattern"));
    }
    if parts.len() > registry::MAX_PATTERNS * 2 - 1 {
        return Err(failure(SourceInferenceError::ResourceLimit));
    }
    let mut patterns = Vec::new();
    for (index, pattern) in parts.iter().enumerate() {
        if index % 2 == 0 {
            patterns.push(pattern);
        } else {
            expect_atom(pattern, ",", "grind pattern separator")?;
        }
    }
    Ok(Request {
        declaration,
        patterns,
    })
}

fn proposition(context: &mut Context, expression: &Expr) -> Result<bool, NatDefinitionElabError> {
    let Some(type_) = context.known_type(expression)? else {
        return Err(unsupported("an unknown theorem or parameter type"));
    };
    let type_ = context.whnf(&type_)?;
    Ok(matches!(type_.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero()))
}

/// Compile without changing the supplied environment or lexical scope. All
/// terms are checked before normalization can erase an ill-typed subexpression.
pub fn compile(
    env: &Environment,
    scope: &SourceScope,
    kernel: Budget,
    request: &Request<'_>,
) -> Result<GrindPattern, NatDefinitionElabError> {
    let Syntax::Ident { val, .. } = request.declaration else {
        return Err(unsupported("a theorem name"));
    };
    let declaration = scope::executable::resolve(env, scope, val)?
        .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
    let info = env.find(&declaration).ok_or_else(|| {
        registry_error(GrindPatternError::UnknownDeclaration(declaration.clone()))
    })?;
    if !registry::safe_proof_candidate(info) {
        return Err(unsupported("an unsafe or non-proof declaration kind"));
    }
    let level_parameters = info.constant_val().level_params.clone();
    let mut cursor = info.constant_val().type_.clone();
    let mut context = Context::scoped(env, kernel, scope)?;
    context.infer_level_params = false;
    context.level_params = scope.universes.clone();
    for parameter in scope.variables.levels() {
        if !context.level_params.contains(parameter) {
            context.level_params.push(parameter.clone());
        }
    }
    if !proposition(&mut context, &cursor)? {
        return Err(unsupported("a declaration whose type is not a proposition"));
    }
    let mut locals = Vec::new();
    let mut data_params = 0u32;
    let mut proof_suffix = false;
    // Match forallTelescope, not forallTelescopeReducing: binder names come from
    // the declaration's actual telescope, not an unfolded result-type alias.
    while let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = cursor.node()
    {
        context.tick()?;
        if locals.len() >= registry::MAX_PARAMETERS as usize {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let proof = proposition(&mut context, binder_type)?;
        if proof {
            proof_suffix = true;
            if body.has_loose_bvars() {
                return Err(unsupported("a dependent proof parameter"));
            }
        } else if proof_suffix {
            return Err(unsupported("a data parameter following a proof parameter"));
        } else {
            data_params += 1;
        }
        let id = FVarId(context.fresh_name()?);
        context.txn.lctx.add_param(
            id.clone(),
            binder_name.clone(),
            binder_type.clone(),
            *binder_info,
        );
        let opened = context.substitute(body, &Expr::fvar(id.clone()))?;
        locals.push(id);
        cursor = opened;
    }
    if matches!(context.whnf(&cursor)?.node(), ExprNode::ForallE { .. }) {
        return Err(unsupported("a telescope exposed by a result-type alias"));
    }
    let num_params =
        u32::try_from(locals.len()).map_err(|_| failure(SourceInferenceError::ResourceLimit))?;
    let mut checking_levels = level_parameters;
    for parameter in &context.level_params {
        if !checking_levels.contains(parameter) {
            checking_levels.push(parameter.clone());
        }
    }
    let mut patterns = Vec::new();
    for syntax in &request.patterns {
        // Pattern elaboration must not create auxiliary proof declarations
        // that this metadata-only transaction could publish without admission.
        let mut pending = vec![*syntax];
        while let Some(syntax) = pending.pop() {
            context.tick()?;
            if let Syntax::Node { kind, args, .. } = syntax {
                if *kind == parser_kind(&["Term", "byTactic"]) {
                    return Err(unsupported("a tactic proof inside a pattern"));
                }
                pending.extend(args);
            }
        }
        let term = context.term(syntax, None)?;
        let term = context.finish(term)?;
        context.check_grind_pattern_term(&term, &checking_levels)?;
        let mut expression = context.prepare_grind_pattern(&term.value)?;
        for (index, id) in locals.iter().enumerate() {
            context.tick()?;
            expression = expression
                .abstract_fvar(id, num_params - index as u32 - 1)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
        }
        patterns.push(expression);
    }
    let row = GrindPattern {
        declaration,
        num_params,
        data_params,
        patterns,
    };
    registry::validate(env, &row).map_err(registry_error)?;
    Ok(row)
}

impl Context {
    /// Fold only a physical projection named by checked structure metadata and
    /// whose admitted definition has the generated projection body. Shared with
    /// E-matching normalization so triggers and observed ground terms agree.
    pub(in crate::source) fn grind_fold_projection(
        &mut self,
        structure: &Name,
        index: u64,
        receiver: &Expr,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        let structures = crate::records::imported::ImportedStructures::read(&self.txn.env)
            .map_err(|error| failure(SourceInferenceError::Record(error)))?;
        let Some(field) = structures.get(structure).and_then(|entry| {
            usize::try_from(index)
                .ok()
                .and_then(|index| entry.fields.get(index))
        }) else {
            return Ok(None);
        };
        let name = field.projection.clone();
        let Some(ConstantInfo::Defn(definition)) = self.txn.env.find(&name).cloned() else {
            return Ok(None);
        };
        let env = self.txn.env.clone();
        let Some(descriptor) =
            crate::records::projection::generated_projection(&env, &definition, || self.tick())?
        else {
            return Ok(None);
        };
        if descriptor.structure != *structure || descriptor.index != index {
            return Ok(None);
        }
        let Some(type_) = self.known_type(receiver)? else {
            return Ok(None);
        };
        let type_ = self.whnf(&type_)?;
        let mut head = &type_;
        let mut parameters = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            parameters.push(a.clone());
            head = f;
        }
        parameters.reverse();
        let ExprNode::Const {
            name: family,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if family != structure
            || parameters.len() != descriptor.parameters
            || levels.len() != definition.base.level_params.len()
        {
            return Ok(None);
        }
        let mut result = Expr::const_(name, levels.clone());
        for parameter in parameters {
            self.tick()?;
            result = Expr::app(result, parameter);
        }
        Ok(Some(Expr::app(result, receiver.clone())))
    }

    fn prepare_grind_pattern(&mut self, root: &Expr) -> Result<Expr, NatDefinitionElabError> {
        enum Task {
            Visit(Expr, usize),
            Apply,
            Projection(Name, u64),
        }
        let mut tasks = vec![Task::Visit(root.clone(), 0)];
        let mut values = Vec::new();
        let mut visited = 0usize;
        while let Some(task) = tasks.pop() {
            self.tick()?;
            visited += 1;
            if visited > 65_536 {
                return Err(failure(SourceInferenceError::ResourceLimit));
            }
            match task {
                Task::Visit(term, depth) => {
                    if depth >= 128 {
                        return Err(failure(SourceInferenceError::ResourceLimit));
                    }
                    let term = self.whnf_with_transparency(
                        &term,
                        UnificationTransparency::Abbreviations,
                        true,
                    )?;
                    match term.node() {
                        ExprNode::MData { expr, .. } => {
                            tasks.push(Task::Visit(expr.clone(), depth))
                        }
                        ExprNode::App { f, a } => {
                            tasks.push(Task::Apply);
                            tasks.push(Task::Visit(a.clone(), depth + 1));
                            tasks.push(Task::Visit(f.clone(), depth + 1));
                        }
                        ExprNode::Proj {
                            struct_name,
                            idx,
                            expr,
                        } => {
                            tasks.push(Task::Projection(struct_name.clone(), *idx));
                            tasks.push(Task::Visit(expr.clone(), depth + 1));
                        }
                        ExprNode::Const { .. }
                        | ExprNode::FVar { .. }
                        | ExprNode::Sort { .. }
                        | ExprNode::Lit { .. } => values.push(term),
                        _ => return Err(unsupported("a binder, hole or higher-order subpattern")),
                    }
                }
                Task::Apply => {
                    let argument = values
                        .pop()
                        .ok_or_else(|| unsupported("a malformed application"))?;
                    let function = values
                        .pop()
                        .ok_or_else(|| unsupported("a malformed application"))?;
                    let Some(type_) = self.known_type(&argument)? else {
                        return Err(unsupported("a pattern argument with unknown type"));
                    };
                    if proposition(self, &type_)? {
                        // The pin drops proof arguments before checking coverage.
                        // Counting their variables here would accept invalid
                        // patterns; the bounded matcher has no dontCare gadget.
                        return Err(unsupported(
                            "a proof argument requiring wildcard preprocessing",
                        ));
                    }
                    self.check_grind_support_argument(&function, &argument, &type_)?;
                    values.push(Expr::app(function, argument));
                }
                Task::Projection(structure, index) => {
                    let receiver = values
                        .pop()
                        .ok_or_else(|| unsupported("a malformed projection"))?;
                    let projection = self
                        .grind_fold_projection(&structure, index, &receiver)?
                        .ok_or_else(|| unsupported("an unregistered physical projection"))?;
                    // Folding exposes implicit structure parameters and the
                    // receiver; they obey the same support rules as source apps.
                    let mut application = &projection;
                    while let ExprNode::App { f, a } = application.node() {
                        self.tick()?;
                        let Some(type_) = self.known_type(a)? else {
                            return Err(unsupported("a projection argument with unknown type"));
                        };
                        if proposition(self, &type_)? {
                            return Err(unsupported(
                                "a proof argument requiring wildcard preprocessing",
                            ));
                        }
                        self.check_grind_support_argument(f, a, &type_)?;
                        application = f;
                    }
                    values.push(projection);
                }
            }
        }
        let result = values
            .pop()
            .ok_or_else(|| unsupported("an empty pattern"))?;
        if !values.is_empty() {
            return Err(unsupported("malformed pattern normalization"));
        }
        Ok(result)
    }

    /// The pin erases nontrivial supporting arguments before coverage checks.
    /// Without its wildcard gadgets, accepting variables that occur only there
    /// would invent a usable trigger. Bare variables and ground support remain
    /// exact; compound type, instance and out-parameter support explicitly refuse.
    fn check_grind_support_argument(
        &mut self,
        function: &Expr,
        argument: &Expr,
        argument_type: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if !argument.has_fvar() || matches!(argument.node(), ExprNode::FVar { .. }) {
            return Ok(());
        }
        let argument_type = self.whnf(argument_type)?;
        // Propositions are relevant arguments in the pin, before the instance
        // or type-former classification. Proof-valued arguments refuse earlier.
        if matches!(argument_type.node(), ExprNode::Sort { level } if level.normalize_fixpoint().is_zero())
        {
            return Ok(());
        }
        // This bounded subset also refuses compound function-valued support;
        // exposing an arbitrary codomain would require the pin's full classifier.
        let type_former = matches!(
            argument_type.node(),
            ExprNode::Sort { .. } | ExprNode::ForallE { .. }
        );
        let mut head = &argument_type;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        let class = match head.node() {
            ExprNode::Const { name, .. } => self.instance_registry()?.is_class(name),
            _ => false,
        };
        let Some(function_type) = self.known_type(function)? else {
            return Err(unsupported("a pattern function with unknown type"));
        };
        let function_type = self.whnf(&function_type)?;
        let ExprNode::ForallE {
            binder_info,
            binder_type,
            ..
        } = function_type.node()
        else {
            return Err(unsupported("a pattern function without a parameter"));
        };
        let mut domain_head = binder_type;
        loop {
            self.tick()?;
            match domain_head.node() {
                ExprNode::App { f, .. } => domain_head = f,
                ExprNode::MData { expr, .. } => domain_head = expr,
                _ => break,
            }
        }
        let out_parameter = matches!(domain_head.node(), ExprNode::Const { name, .. }
            if *name == Name::from_components(["outParam"])
                || *name == Name::from_components(["semiOutParam"]));
        if type_former || class || *binder_info == BinderInfo::InstImplicit || out_parameter {
            return Err(unsupported(
                "a compound support argument requiring wildcard preprocessing",
            ));
        }
        Ok(())
    }

    fn check_grind_pattern_term(
        &mut self,
        term: &Typed,
        level_params: &[Name],
    ) -> Result<(), NatDefinitionElabError> {
        let mut value = term.value.clone();
        let mut expected = term.type_.clone();
        for local in self.txn.lctx.clone().decls().iter().rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            value = value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            expected = expected
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            if let Some(local_value) = &local.value {
                let local_value = self.instantiate(local_value)?;
                value = Expr::let_e(
                    local.user_name.clone(),
                    domain.clone(),
                    local_value.clone(),
                    value,
                    false,
                );
                expected = Expr::let_e(
                    local.user_name.clone(),
                    domain,
                    local_value,
                    expected,
                    false,
                );
            } else {
                value = Expr::lam(
                    local.user_name.clone(),
                    domain.clone(),
                    value,
                    local.binder_info,
                );
                expected =
                    Expr::forall_e(local.user_name.clone(), domain, expected, local.binder_info);
            }
        }
        let reducibility = crate::reducibility::table(&self.txn.env).map_err(|error| {
            failure(SourceInferenceError::Unification(Box::new(
                UnificationError::Reducibility(error),
            )))
        })?;
        let remaining = if self.txn.budget.max_heartbeats == 0 {
            u64::MAX
        } else {
            self.txn
                .budget
                .max_heartbeats
                .saturating_sub(self.txn.budget.heartbeats_consumed)
        };
        let outcome = fln_kernel::check_type_with_unfolding(
            &self.txn.env,
            level_params,
            &value,
            &expected,
            self.kernel
                .narrowed(self.kernel.steps.min(remaining), self.kernel.depth),
            fln_kernel::DefEqUnfolding {
                opaque_definitions: reducibility.opaque_definitions(),
                unfold_theorems: false,
            },
        );
        let consumed = match &outcome {
            Outcome::Complete(Verdict::Accepted { consumption })
            | Outcome::Complete(Verdict::Rejected { consumption, .. }) => consumption.steps_used,
            Outcome::Inconclusive(problem) => match &problem.cause {
                fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
                    if matches!(usage.reason, fln_core::diag::ResourceReason::ExecutionSteps) =>
                {
                    usage.observed
                }
                _ => 0,
            },
            _ => 0,
        };
        self.txn.budget.heartbeats_consumed =
            self.txn.budget.heartbeats_consumed.saturating_add(consumed);
        match outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => Ok(()),
            outcome => Err(failure(SourceInferenceError::TypeObligation(Box::new(
                outcome,
            )))),
        }
    }
}
