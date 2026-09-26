//! Named application arguments share the ordinary bidirectional term worklist.
//! Parameters are consumed in telescope order, not in the order labels occur.
//! Missing explicit parameters are inferred when a later named type needs them;
//! otherwise they become fresh, capture-free eta binders. No source is rewritten.
use super::*;
use std::collections::{HashSet, VecDeque};

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
    positional: VecDeque<ApplicationValue<'a>>,
    named: Vec<Named<'a>>,
    explicit: bool,
    expected: Option<Expr>,
    result_expected: Option<Expr>,
    saved: LocalContext,
    eta: Vec<(Name, FVarId, Expr)>,
}

pub(super) struct Argument<'a> {
    pub(super) value: ApplicationValue<'a>,
    pub(super) domain: Expr,
    pub(super) codomain: Expr,
}

pub(super) fn has_named(arguments: &[Syntax]) -> bool {
    let kind = parser_kind(&["Term", "namedArgument"]);
    arguments
        .iter()
        .any(|argument| argument.kind() == Some(&kind))
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
            named.push(Named {
                name: name.clone(),
                value: ApplicationValue::Syntax(&parts[3]),
            });
        }
        Ok(NamedApplication {
            function,
            positional,
            named,
            explicit,
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
        while !state.positional.is_empty() || !state.named.is_empty() {
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
            let codomain = body.clone();
            let style = *binder_info;
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
                    self.instance_hole(domain)?
                } else {
                    self.hole(domain)?
                };
                self.append_named_value(state, &codomain, argument)?;
                continue;
            } else {
                state.positional.pop_front()
            };
            if let Some(value) = value {
                if state.positional.is_empty()
                    && state.named.is_empty()
                    && !codomain.has_loose_bvar(0)
                    && let Some(expected) = &state.result_expected
                {
                    self.constrain_result_hint(&codomain, expected)?;
                }
                return Ok(Some(Argument {
                    value,
                    domain,
                    codomain,
                }));
            }
            // There is a later named parameter, but no positional argument for
            // this explicit parameter. A dependent named type must determine it,
            // rather than being checked under an arbitrary eta-bound variable.
            let argument = if self
                .named_argument_depends_on_current(&state.function.type_, &state.named)?
            {
                self.hole(domain)?
            } else {
                let id = FVarId(self.fresh_name()?);
                let hidden = self.fresh_name()?;
                self.txn
                    .lctx
                    .add_param(id.clone(), hidden, domain.clone(), BinderInfo::Default);
                if let Some(expected) = state.result_expected.take() {
                    let expected = self.whnf(&expected)?;
                    if let ExprNode::ForallE {
                        binder_type, body, ..
                    } = expected.node()
                    {
                        self.constrain_type(&domain, binder_type)?;
                        state.result_expected =
                            Some(self.substitute(body, &Expr::fvar(id.clone()))?);
                    }
                }
                state.eta.push((name, id.clone(), domain));
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
                self.finish_term(state.function, state.result_expected.as_ref())?
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
            Ok(index) => state
                .positional
                .insert(index, ApplicationValue::Elaborated(receiver)),
            Err(name) => state.named.push(Named {
                name,
                value: ApplicationValue::Elaborated(receiver),
            }),
        }
        Ok(state)
    }

    fn field_argument_position(
        &mut self,
        state: &NamedApplication<'_>,
        base: &Name,
    ) -> Result<Result<usize, Name>, NatDefinitionElabError> {
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
                return Err(failure(SourceInferenceError::InvalidFieldReceiver(
                    base.clone(),
                )));
            };
            let supplied = remaining.remove(binder_name);
            if !supplied && self.field_parameter_matches(binder_type, base)? {
                if positional <= state.positional.len()
                    && (state.explicit || *binder_info == BinderInfo::Default)
                {
                    return Ok(Ok(positional));
                }
                if binder_name.is_anonymous() || unusable.contains(binder_name) {
                    return Err(failure(SourceInferenceError::InvalidFieldReceiver(
                        base.clone(),
                    )));
                }
                return Ok(Err(binder_name.clone()));
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
                let depends = first || self.mentions_named_dependencies(binder_type, &dependent)?;
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
