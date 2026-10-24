//! Named application arguments share the ordinary bidirectional term worklist.
//! Parameters are consumed in telescope order, not in the order labels occur.
//! Missing explicit parameters are inferred when a later named type needs them;
//! otherwise they become fresh, capture-free eta binders. No source is rewritten.
use super::*;
use std::collections::{HashSet, VecDeque};

pub(super) mod postponed;

struct Named<'a> {
    name: Name,
    value: ApplicationValue<'a>,
}

pub(super) enum ApplicationValue<'a> {
    Syntax(&'a Syntax),
    Elaborated(Typed),
}

pub(super) struct NamedApplication<'a> {
    function: Typed,
    initial: bool,
    positional: VecDeque<ApplicationValue<'a>>,
    named: Vec<Named<'a>>,
    explicit: bool,
    ellipsis: bool,
    expected: Option<Expr>,
    result_expected: Option<Expr>,
    saved: LocalContext,
    eta: Vec<(Name, FVarId, Expr)>,
}

impl NamedApplication<'_> {
    pub(super) fn function_type(&self) -> &Expr {
        &self.function.type_
    }

    pub(super) fn initial(&self) -> bool {
        self.initial
    }

    pub(super) fn start(&mut self) {
        self.initial = false;
    }

    pub(super) fn has_arguments(&self) -> bool {
        self.ellipsis || !self.positional.is_empty() || !self.named.is_empty()
    }
}

pub(super) struct Argument<'a> {
    pub(super) value: ApplicationValue<'a>,
    pub(super) domain: Expr,
    pub(super) codomain: Expr,
    pub(super) infer_exception_action: bool,
}

/// Select the telescope-aware application path. Besides named arguments,
/// ellipsis needs that path even when no explicit arguments remain to visit.
pub(super) fn has_named(arguments: &[Syntax]) -> bool {
    let kind = parser_kind(&["Term", "namedArgument"]);
    arguments
        .iter()
        .any(|argument| argument.kind() == Some(&kind) || is_ellipsis(argument))
}

pub(super) fn is_ellipsis(argument: &Syntax) -> bool {
    argument.kind() == Some(&parser_kind(&["Term", "ellipsis"]))
}

/// Ellipsis consumes the remaining telescope; it is not a term argument.
/// Validate its exact node and terminal position even for macro-built syntax.
pub(super) fn split_ellipsis(
    arguments: &[Syntax],
) -> Result<(&[Syntax], bool), NatDefinitionElabError> {
    let Some((last, prefix)) = arguments.split_last() else {
        return Ok((arguments, false));
    };
    if prefix.iter().any(is_ellipsis) {
        return Err(failure(SourceInferenceError::ExpectedFunction));
    }
    if !is_ellipsis(last) {
        return Ok((arguments, false));
    }
    let parts = expect_node(
        last,
        &parser_kind(&["Term", "ellipsis"]),
        1,
        "application ellipsis",
    )?;
    expect_atom(&parts[0], "..", "application ellipsis")?;
    Ok((prefix, true))
}

impl Context {
    pub(super) fn start_named_application<'a>(
        &mut self,
        function: Typed,
        arguments: &'a [Syntax],
        expected: Option<Expr>,
        explicit: bool,
    ) -> Result<NamedApplication<'a>, NatDefinitionElabError> {
        let mut positional = VecDeque::new();
        let (arguments, ellipsis) = split_ellipsis(arguments)?;
        let mut named = Vec::new();
        let mut names = HashSet::new();
        let kind = parser_kind(&["Term", "namedArgument"]);
        for argument in arguments {
            self.tick()?;
            if argument.kind() != Some(&kind) {
                positional.push_back(ApplicationValue::Syntax(argument));
                continue;
            }
            let parts = expect_node(argument, &kind, 5, "named argument")?;
            expect_atom(&parts[0], "(", "named argument opener")?;
            expect_atom(&parts[2], ":=", "named argument assignment")?;
            expect_atom(&parts[4], ")", "named argument closer")?;
            let Syntax::Ident { val: name, .. } = &parts[1] else {
                return Err(failure(SourceInferenceError::Scope));
            };
            if name.is_anonymous() {
                return Err(failure(SourceInferenceError::Scope));
            }
            if !names.insert(name.clone()) {
                return Err(failure(SourceInferenceError::DuplicateNamedArgument(
                    name.clone(),
                )));
            }
            let value =
                match self.do_for_monad_argument(&function, name, &parts[3], expected.as_ref())? {
                    Some(value) => ApplicationValue::Elaborated(value),
                    None => ApplicationValue::Syntax(&parts[3]),
                };
            named.push(Named {
                name: name.clone(),
                value,
            });
        }
        Ok(NamedApplication {
            function,
            initial: true,
            positional,
            named,
            explicit,
            ellipsis,
            result_expected: expected.clone(),
            expected,
            saved: self.txn.lctx.clone(),
            eta: Vec::new(),
        })
    }

    pub(super) fn next_named_argument<'a>(
        &mut self,
        state: &mut NamedApplication<'a>,
    ) -> Result<Option<Argument<'a>>, NatDefinitionElabError> {
        loop {
            let has_arguments = !state.positional.is_empty() || !state.named.is_empty();
            if !has_arguments {
                if state.ellipsis {
                    // Saturate only the actual known Pi telescope. An unknown
                    // result is not evidence for inventing another function.
                    let type_ = self.whnf(&state.function.type_)?;
                    if !matches!(type_.node(), ExprNode::ForallE { .. }) {
                        break;
                    }
                    state.function.type_ = type_;
                } else if state.explicit || !self.has_optional_parameter(&state.function.type_)? {
                    break;
                }
            }
            self.tick()?;
            state.function = match self.coerce_function(state.function.clone()) {
                Err(NatDefinitionElabError::Inference(SourceInferenceError::ExpectedFunction))
                    if !state.named.is_empty() =>
                {
                    return Err(failure(SourceInferenceError::InvalidNamedArgument(
                        state.named[0].name.clone(),
                    )));
                }
                result => result?,
            };
            if let Some(expected) = &state.result_expected {
                self.do_exception_result_hint(&state.function, expected)?;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = state.function.type_.node()
            else {
                return Err(failure(match state.named.first() {
                    Some(argument) => {
                        SourceInferenceError::InvalidNamedArgument(argument.name.clone())
                    }
                    None => SourceInferenceError::ExpectedFunction,
                }));
            };
            let name = binder_name.clone();
            let domain = binder_type.clone();
            let argument_domain = self.projection_domain(domain.clone())?;
            let codomain = body.clone();
            let style = *binder_info;
            if !has_arguments && !state.explicit && style == BinderInfo::StrictImplicit {
                break;
            }
            let mut selected = None;
            for (index, argument) in state.named.iter().enumerate() {
                self.tick()?;
                if argument.name == name {
                    selected = Some(index);
                    break;
                }
            }
            let value = if let Some(index) = selected {
                Some(state.named.remove(index).value)
            } else if !state.explicit && style != BinderInfo::Default {
                let argument = if style == BinderInfo::InstImplicit {
                    self.instance_hole(argument_domain)?
                } else {
                    self.hole(argument_domain)?
                };
                self.append_named_value(state, &codomain, argument)?;
                continue;
            } else {
                state.positional.pop_front()
            };
            if let Some(value) = value {
                if state.positional.is_empty()
                    && state.named.is_empty()
                    && !state.ellipsis
                    && !codomain.has_loose_bvar(0)
                    && let Some(expected) = &state.result_expected
                {
                    self.do_operation_result_hint(&state.function, &codomain, expected)?;
                    self.constrain_result_hint(&codomain, expected)?;
                }
                return Ok(Some(Argument {
                    value,
                    infer_exception_action: self
                        .do_exception_infer_action(&state.function, &argument_domain)?,
                    domain: argument_domain,
                    codomain,
                }));
            }
            // There is a later named parameter, but no positional argument for
            // this explicit parameter. A dependent named type must determine it,
            // rather than being checked under an arbitrary eta-bound variable.
            let argument = if !state.explicit
                && let Some(value) = optional::default_value(&domain)
            {
                value.clone()
            } else if state.ellipsis
                || self.named_argument_depends_on_current(&state.function.type_, &state.named)?
            {
                self.hole(argument_domain)?
            } else {
                let id = FVarId(self.fresh_name()?);
                let hidden = self.fresh_name()?;
                self.txn.lctx.add_param(
                    id.clone(),
                    hidden,
                    argument_domain.clone(),
                    BinderInfo::Default,
                );
                if let Some(expected) = state.result_expected.take() {
                    let expected = self.whnf(&expected)?;
                    if let ExprNode::ForallE {
                        binder_type, body, ..
                    } = expected.node()
                    {
                        self.constrain_type(&argument_domain, binder_type)?;
                        state.result_expected =
                            Some(self.substitute(body, &Expr::fvar(id.clone()))?);
                    }
                }
                state.eta.push((name, id.clone(), argument_domain));
                Expr::fvar(id)
            };
            self.append_named_value(state, &codomain, argument)?;
        }
        Ok(None)
    }

    fn append_named_value(
        &mut self,
        state: &mut NamedApplication<'_>,
        codomain: &Expr,
        argument: Expr,
    ) -> Result<(), NatDefinitionElabError> {
        state.function.type_ = self.substitute(codomain, &argument)?;
        state.function.value = Expr::app(state.function.value.clone(), argument);
        Ok(())
    }

    pub(super) fn add_named_argument(
        &mut self,
        state: &mut NamedApplication<'_>,
        codomain: &Expr,
        argument: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.append_named_value(state, codomain, argument.value)
    }

    pub(super) fn finish_named_application(
        &mut self,
        state: NamedApplication<'_>,
    ) -> Result<Typed, NatDefinitionElabError> {
        let result = (|| {
            let mut term = if state.explicit {
                self.finish_explicit_term(state.function, state.result_expected.as_ref())?
            } else {
                self.finish_application_implicits(state.function, state.result_expected.as_ref())?
            };
            term.value = self.instantiate(&term.value)?;
            term.type_ = self.instantiate(&term.type_)?;
            for (name, id, domain) in state.eta.into_iter().rev() {
                self.tick()?;
                let domain = self.instantiate(&domain)?;
                let value = term
                    .value
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                let type_ = term
                    .type_
                    .abstract_fvar(&id, 0)
                    .map_err(|_| failure(SourceInferenceError::Scope))?;
                term = Typed {
                    value: Expr::lam(name.clone(), domain.clone(), value, BinderInfo::Default),
                    type_: Expr::forall_e(name, domain, type_, BinderInfo::Default),
                };
            }
            self.txn.lctx = state.saved.clone();
            self.finish_explicit_term(term, state.expected.as_ref())
        })();
        self.txn.lctx = state.saved;
        result
    }

    /// The pinned `Lean.Elab.App.addLValArg` selects the first parameter
    /// whose type has the receiver's head. Selection never searches for a
    /// later parameter merely because unification with the first would fail.
    /// A positional insertion is preferred; otherwise the binder name must
    /// be usable as a named argument. All ordinary argument checking is still
    /// performed by the same application worklist.
    pub(super) fn start_field_application<'a>(
        &mut self,
        function: Typed,
        receiver: Typed,
        base: &Name,
        arguments: &'a [Syntax],
        expected: Option<Expr>,
        explicit: bool,
    ) -> Result<NamedApplication<'a>, NatDefinitionElabError> {
        let mut state = self.start_named_application(function, arguments, expected, explicit)?;
        let mut trial = self.clone();
        let selected = trial.field_argument_position(&state, base);
        self.txn.budget.heartbeats_consumed = trial.txn.budget.heartbeats_consumed;
        match selected? {
            Some(Ok(index)) => state
                .positional
                .insert(index, ApplicationValue::Elaborated(receiver)),
            Some(Err(name)) => state.named.push(Named {
                name,
                value: ApplicationValue::Elaborated(receiver),
            }),
            None => {
                let mut function = &state.function.value;
                while let ExprNode::App { f, .. } | ExprNode::MData { expr: f, .. } =
                    function.node()
                {
                    self.tick()?;
                    function = f;
                }
                return Err(failure(SourceInferenceError::InvalidFieldReceiver(
                    Box::new(super::FieldReceiverRefusal {
                        function: function.clone(),
                        base: base.clone(),
                        receiver: receiver.value,
                        locals: state.saved.clone(),
                    }),
                )));
            }
        }
        Ok(state)
    }

    fn field_argument_position(
        &mut self,
        state: &NamedApplication<'_>,
        base: &Name,
    ) -> Result<Option<Result<usize, Name>>, NatDefinitionElabError> {
        let mut cursor = state.function.type_.clone();
        let mut positional = 0;
        let mut remaining: HashSet<_> = state.named.iter().map(|arg| arg.name.clone()).collect();
        let mut unusable = remaining.clone();
        loop {
            self.tick()?;
            cursor = self.whnf(&cursor)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = cursor.node()
            else {
                return Ok(None);
            };
            let supplied = remaining.remove(binder_name);
            if !supplied && self.field_parameter_matches(binder_type, base)? {
                if positional <= state.positional.len()
                    && (state.explicit || *binder_info == BinderInfo::Default)
                {
                    return Ok(Some(Ok(positional)));
                }
                if binder_name.is_anonymous() || unusable.contains(binder_name) {
                    return Err(failure(SourceInferenceError::UnusableFieldParameter(
                        base.clone(),
                    )));
                }
                return Ok(Some(Err(binder_name.clone())));
            }
            if !supplied && (state.explicit || *binder_info == BinderInfo::Default) {
                positional += 1;
            }
            unusable.insert(binder_name.clone());
            let argument = self.hole(binder_type.clone())?;
            cursor = self.substitute(body, &argument)?;
        }
    }

    fn field_parameter_matches(
        &mut self,
        type_: &Expr,
        base: &Name,
    ) -> Result<bool, NatDefinitionElabError> {
        let matches = |type_: &Expr| {
            if base == &Name::from_components(["Function"]) {
                return matches!(type_.node(), ExprNode::ForallE { .. });
            }
            let mut head = type_;
            while let ExprNode::App { f, .. } | ExprNode::MData { expr: f, .. } = head.node() {
                head = f;
            }
            matches!(head.node(), ExprNode::Const { name, .. } if name == base)
        };
        let type_ = self.instantiate(type_)?;
        if matches(&type_) {
            return Ok(true);
        }
        let reduced =
            self.whnf_with_transparency(&type_, UnificationTransparency::Abbreviations, true)?;
        Ok(matches(&reduced))
    }

    /// Traverse a temporary, opened telescope so reduction never sees loose
    /// de Bruijn variables. Dependence is transitive through intervening types.
    /// Fresh local names cannot become source-visible, and every exit restores
    /// the caller context. The query performs no speculative assignments.
    fn named_argument_depends_on_current(
        &mut self,
        type_: &Expr,
        arguments: &[Named<'_>],
    ) -> Result<bool, NatDefinitionElabError> {
        let saved = self.txn.lctx.clone();
        let result = (|| {
            let mut pending: HashSet<_> = arguments.iter().map(|arg| arg.name.clone()).collect();
            let mut dependent = HashSet::new();
            let mut cursor = type_.clone();
            let mut first = true;
            loop {
                self.tick()?;
                let reduced = self.whnf(&cursor)?;
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    ..
                } = reduced.node()
                else {
                    return Ok(false);
                };
                // The pin's `findNamedArgDependsOn?` ignores annotation
                // payloads: a default mentioning this parameter is not a
                // dependency of the later named argument's actual type.
                let domain = self.projection_domain(binder_type.clone())?;
                let depends = first || self.mentions_named_dependencies(&domain, &dependent)?;
                if !first && pending.remove(binder_name) && depends {
                    return Ok(true);
                }
                if !first && pending.is_empty() {
                    return Ok(false);
                }
                let id = FVarId(self.fresh_name()?);
                let hidden = self.fresh_name()?;
                self.txn.lctx.add_param(
                    id.clone(),
                    hidden,
                    binder_type.clone(),
                    BinderInfo::Default,
                );
                if depends {
                    dependent.insert(id.clone());
                }
                cursor = self.substitute(body, &Expr::fvar(id))?;
                first = false;
            }
        })();
        self.txn.lctx = saved;
        result
    }

    fn mentions_named_dependencies(
        &mut self,
        expression: &Expr,
        variables: &HashSet<FVarId>,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut seen = HashSet::new();
        let mut pending = vec![expression];
        while let Some(expr) = pending.pop() {
            if !seen.insert(std::ptr::from_ref(expr.node())) {
                continue;
            }
            self.tick()?;
            match expr.node() {
                ExprNode::FVar { id } if variables.contains(id) => return Ok(true),
                ExprNode::App { f, a } => {
                    pending.push(f);
                    pending.push(a);
                }
                ExprNode::ForallE {
                    binder_type, body, ..
                }
                | ExprNode::Lam {
                    binder_type, body, ..
                } => {
                    pending.push(binder_type);
                    pending.push(body);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    pending.push(type_);
                    pending.push(value);
                    pending.push(body);
                }
                ExprNode::Proj { expr, .. } | ExprNode::MData { expr, .. } => pending.push(expr),
                _ => {}
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
mod ellipsis_tests {
    use super::*;
    use fln_syntax::source::SourceInfo;

    fn marker(parts: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", "ellipsis"]), parts)
    }
    fn dots() -> Syntax {
        marker(vec![Syntax::atom(SourceInfo::None, "..")])
    }
    fn function() -> Typed {
        let mut type_ = nat_const();
        for _ in 0..32 {
            type_ = Expr::forall_e(Name::anonymous(), nat_const(), type_, BinderInfo::Default);
        }
        Typed {
            value: Expr::const_(Name::from_components(["telescopeFixture"]), vec![]),
            type_,
        }
    }
    #[test]
    fn macro_built_ellipsis_must_be_terminal_and_have_its_exact_shape() {
        let ordinary = Syntax::atom(SourceInfo::None, "argument");
        let args = [ordinary.clone(), dots()];
        let (prefix, ellipsis) = split_ellipsis(&args).unwrap();
        assert!(ellipsis);
        assert_eq!(prefix, std::slice::from_ref(&ordinary));
        assert!(has_named(&args));
        for malformed in [
            vec![dots(), ordinary.clone()],
            vec![dots(), dots()],
            vec![marker(vec![])],
            vec![marker(vec![ordinary.clone()])],
            vec![marker(vec![Syntax::atom(SourceInfo::None, ".."), ordinary])],
        ] {
            assert!(split_ellipsis(&malformed).is_err());
        }
        assert_eq!(split_ellipsis(&[]).unwrap(), (&[][..], false));
    }
    #[test]
    fn saturation_creates_ordinary_holes_and_never_eta_binds_the_missing_arguments() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let mut cx = Context::new(&env, Budget::DEFAULT);
        let args = [dots()];
        let mut state = cx
            .start_named_application(function(), &args, None, false)
            .unwrap();
        assert!(cx.next_named_argument(&mut state).unwrap().is_none());
        assert!(state.eta.is_empty());
        assert_eq!(state.function.type_, nat_const());
        assert!(state.function.value.has_expr_mvar());
        assert!(!state.function.value.has_fvar());
        let mut value = &state.function.value;
        let mut count = 0;
        while let ExprNode::App { f, a } = value.node() {
            assert!(matches!(a.node(), ExprNode::MVar { .. }));
            count += 1;
            value = f;
        }
        assert_eq!(count, 32);
    }
    #[test]
    fn generated_argument_saturation_obeys_the_callers_work_limit() {
        let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
        let mut cx = Context::new(&env, Budget::DEFAULT);
        let args = [dots()];
        let mut state = cx
            .start_named_application(function(), &args, None, false)
            .unwrap();
        cx.txn.budget.max_heartbeats = cx.txn.budget.heartbeats_consumed + 2;
        assert!(matches!(
            cx.next_named_argument(&mut state),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(state.eta.is_empty());
        let mut clean = Context::new(&env, Budget::DEFAULT);
        let mut retry = clean
            .start_named_application(function(), &args, None, false)
            .unwrap();
        assert!(clean.next_named_argument(&mut retry).unwrap().is_none());
        assert_eq!(retry.function.type_, nat_const());
    }
}
