//! Dependent lambda/Pi binders elaborated left-to-right on the term worklist.
//! Every written domain remains in the final term. Expected types constrain
//! inference, but never replace annotations or grant declaration admission.
use super::*;
use fln_syntax::source::SourceInfo;

pub(super) struct Binder<'a> {
    names: Vec<Name>,
    annotation: Option<&'a Syntax>,
    style: BinderInfo,
}

pub(super) struct Telescope<'a> {
    binders: Vec<Binder<'a>>,
    cursor: usize,
    locals: Vec<LocalDecl>,
    levels: Vec<Level>,
    saved: LocalContext,
    expected: Option<Expr>,
    expected_body: Option<Expr>,
    lambda: bool,
    pub(super) body: &'a Syntax,
}

fn invalid() -> NatDefinitionElabError {
    failure(SourceInferenceError::Scope)
}

fn binder_name(syntax: &Syntax) -> Result<Name, NatDefinitionElabError> {
    match syntax {
        Syntax::Ident { val, .. } if !val.is_anonymous() && val.parent().is_anonymous() => {
            Ok(val.clone())
        }
        Syntax::Node { kind, args, .. } if kind == &parser_kind(&["Term", "hole"]) => {
            let [hole] = args.as_slice() else {
                return Err(invalid());
            };
            expect_atom(hole, "_", "anonymous binder")?;
            Ok(Name::anonymous())
        }
        _ => Err(invalid()),
    }
}

fn simple(syntax: &Syntax) -> bool {
    matches!(syntax, Syntax::Ident { .. }) || syntax.kind() == Some(&parser_kind(&["Term", "hole"]))
}

fn names(syntax: &[Syntax]) -> Result<Vec<Name>, NatDefinitionElabError> {
    if syntax.is_empty() {
        return Err(invalid());
    }
    syntax.iter().map(binder_name).collect()
}

impl Context {
    fn term_binder<'a>(
        &mut self,
        syntax: &'a Syntax,
        lambda: bool,
    ) -> Result<Binder<'a>, NatDefinitionElabError> {
        self.tick()?;
        if simple(syntax) {
            return Ok(Binder {
                names: vec![binder_name(syntax)?],
                annotation: None,
                style: BinderInfo::Default,
            });
        }
        let Syntax::Node { kind, args, .. } = syntax else {
            return Err(invalid());
        };
        if lambda
            && (kind == &parser_kind(&["Term", "typeAscription"])
                || kind == &parser_kind(&["Term", "paren"]))
        {
            let typed = kind == &parser_kind(&["Term", "typeAscription"]);
            let parts = expect_node(
                syntax,
                kind,
                if typed { 5 } else { 3 },
                "lambda binder group",
            )?;
            // Validate the same hygienic parentheses as ordinary source terms.
            let _ = parenthesized_inner(&Syntax::node(
                parser_kind(&["Term", "paren"]),
                vec![
                    parts[0].clone(),
                    parts[1].clone(),
                    parts[parts.len() - 1].clone(),
                ],
            ))?;
            let mut ids = Vec::new();
            if parts[1].kind() == Some(&parser_kind(&["Term", "app"])) {
                let app = expect_node(
                    &parts[1],
                    &parser_kind(&["Term", "app"]),
                    2,
                    "lambda binder names",
                )?;
                ids.push(binder_name(&app[0])?);
                ids.extend(names(expect_null_args(&app[1], "lambda binder names")?)?);
            } else {
                ids.push(binder_name(&parts[1])?);
            }
            let annotation = if typed {
                expect_atom(&parts[2], ":", "lambda binder type")?;
                let [domain] = expect_null_args(&parts[3], "lambda binder annotation")? else {
                    return Err(invalid());
                };
                Some(domain)
            } else {
                // An untyped parenthesized global name is a pattern upstream,
                // not a binder. Do not silently turn a constructor into a local.
                for id in &ids {
                    if !id.is_anonymous() && self.resolve_source_name(id)?.is_some() {
                        return Err(invalid());
                    }
                }
                None
            };
            return Ok(Binder {
                names: ids,
                annotation,
                style: BinderInfo::Default,
            });
        }
        if kind == &parser_kind(&["Term", "instBinder"]) {
            let [open, name, domain, close] = args.as_slice() else {
                return Err(invalid());
            };
            expect_atom(open, "[", "instance binder opener")?;
            expect_atom(close, "]", "instance binder closer")?;
            let name = match expect_null_args(name, "instance binder name")? {
                [] => Name::anonymous(),
                [name, colon] => {
                    expect_atom(colon, ":", "instance binder colon")?;
                    binder_name(name)?
                }
                _ => return Err(invalid()),
            };
            return Ok(Binder {
                names: vec![name],
                annotation: Some(domain),
                style: BinderInfo::InstImplicit,
            });
        }
        let (style, open, close, arity) = if kind == &parser_kind(&["Term", "implicitBinder"]) {
            (BinderInfo::Implicit, "{", "}", 4)
        } else if kind == &parser_kind(&["Term", "strictImplicitBinder"]) {
            (BinderInfo::StrictImplicit, "⦃", "⦄", 4)
        } else if kind == &parser_kind(&["Term", "explicitBinder"]) {
            (BinderInfo::Default, "(", ")", 5)
        } else {
            return Err(invalid());
        };
        let parts = expect_node(syntax, kind, arity, "term binder")?;
        expect_atom(&parts[0], open, "term binder opener")?;
        expect_atom(&parts[arity - 1], close, "term binder closer")?;
        if arity == 5 {
            expect_empty_null(&parts[3], "unsupported binder default")?;
        }
        let ids = names(expect_null_args(&parts[1], "term binder names")?)?;
        let annotation = match expect_null_args(&parts[2], "term binder type")? {
            [] => None,
            [colon, domain] => {
                expect_atom(colon, ":", "term binder colon")?;
                Some(domain)
            }
            _ => return Err(invalid()),
        };
        Ok(Binder {
            names: ids,
            annotation,
            style,
        })
    }

    pub(super) fn start_telescope<'a>(
        &mut self,
        syntax: &'a Syntax,
        expected: Option<Expr>,
        lambda: bool,
    ) -> Result<Telescope<'a>, NatDefinitionElabError> {
        let dependent = syntax.kind() == Some(&parser_kind(&["Term", "depArrow"]));
        let (raw, annotation, body) = if dependent {
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "depArrow"]),
                3,
                "dependent arrow",
            )?;
            if !matches!(&parts[1], Syntax::Atom { val, .. } if val == "->" || val == "→") {
                return Err(invalid());
            }
            (std::slice::from_ref(&parts[0]), None, &parts[2])
        } else if lambda {
            let parts = expect_node(syntax, &parser_kind(&["Term", "fun"]), 2, "lambda")?;
            if !matches!(&parts[0], Syntax::Atom { val, .. } if val == "fun" || val == "λ") {
                return Err(invalid());
            }
            let parts = expect_node(
                &parts[1],
                &parser_kind(&["Term", "basicFun"]),
                4,
                "lambda body",
            )?;
            if !matches!(&parts[2], Syntax::Atom { val, .. } if val == "=>" || val == "↦") {
                return Err(invalid());
            }
            (
                expect_null_args(&parts[0], "lambda binders")?,
                optional_type_syntax(&parts[1])?,
                &parts[3],
            )
        } else {
            let parts = expect_node(
                syntax,
                &parser_kind(&["Term", "forall"]),
                5,
                "universal quantifier",
            )?;
            if !matches!(&parts[0], Syntax::Atom { val, .. } if val == "forall" || val == "∀") {
                return Err(invalid());
            }
            expect_atom(&parts[3], ",", "quantifier separator")?;
            (
                expect_null_args(&parts[1], "quantifier binders")?,
                optional_type_syntax(&parts[2])?,
                &parts[4],
            )
        };
        if raw.is_empty() {
            return Err(invalid());
        }
        let shared = annotation;
        let mut binders = Vec::new();
        // A trailing ascription annotates each bare binder, not the body, and
        // cannot be combined with bracketed binders (the Reference macro rule).
        if let Some(annotation) = shared {
            if !raw.iter().all(simple) {
                return Err(invalid());
            }
            binders.push(Binder {
                names: names(raw)?,
                annotation: Some(annotation),
                style: BinderInfo::Default,
            });
        } else {
            for binder in raw {
                binders.push(self.term_binder(binder, lambda)?);
            }
        }
        // A grouped annotation is elaborated separately for each name, in the
        // context extended by the preceding names, just like separate binders.
        // Reusing one elaborated domain would incorrectly ignore shadowing.
        let mut individual = Vec::new();
        for binder in binders {
            for name in binder.names {
                self.tick()?;
                individual.push(Binder {
                    names: vec![name],
                    annotation: binder.annotation,
                    style: binder.style,
                });
            }
        }
        let mut state = Telescope {
            binders: individual,
            cursor: 0,
            locals: Vec::new(),
            levels: Vec::new(),
            saved: self.txn.lctx.clone(),
            expected_body: if lambda { expected.clone() } else { None },
            expected,
            lambda,
            body,
        };
        self.open_implicit_lambda_prefix(&mut state)?;
        Ok(state)
    }

    /// Expected implicit lambdas precede a written ordinary lambda. Explicit
    /// `{}`/`[]` binders suppress this feature; a leading strict implicit alone
    /// does not trigger it. Once triggered, preserve every non-explicit binder.
    /// Synthetic locals cannot capture source names (the Reference uses fresh
    /// macro scopes here); their domains still enter both checked telescopes.
    fn open_implicit_lambda_prefix(
        &mut self,
        state: &mut Telescope<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        if !state.lambda
            || state.binders.iter().any(|binder| {
                matches!(
                    binder.style,
                    BinderInfo::Implicit | BinderInfo::InstImplicit
                )
            })
        {
            return Ok(());
        }
        let Some(expected) = &state.expected_body else {
            return Ok(());
        };
        let mut expected = self.whnf(expected)?;
        if !matches!(
            expected.node(),
            ExprNode::ForallE {
                binder_info: BinderInfo::Implicit | BinderInfo::InstImplicit,
                ..
            }
        ) {
            return Ok(());
        }
        loop {
            self.tick()?;
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = expected.node()
            else {
                break;
            };
            if *binder_info == BinderInfo::Default {
                break;
            }
            let type_ = self.known_type(binder_type)?.ok_or_else(invalid)?;
            let level = self.sort_level(&Typed {
                value: binder_type.clone(),
                type_,
            })?;
            if *binder_info == BinderInfo::InstImplicit {
                self.validate_instance_binder(binder_type)?;
            }
            let id = FVarId(self.fresh_name()?);
            let name = self.fresh_name()?;
            self.txn
                .lctx
                .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            state.locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("inserted implicit binder")
                    .clone(),
            );
            state.levels.push(level);
            let body = self.substitute(body, &Expr::fvar(id))?;
            expected = self.whnf(&body)?;
        }
        state.expected_body = Some(expected);
        Ok(())
    }

    /// Returns the next annotation to elaborate, or None once all binders are
    /// open. Unannotated domains use an expected Pi domain or a typed hole.
    pub(super) fn next_telescope_domain<'a>(
        &mut self,
        state: &mut Telescope<'a>,
    ) -> Result<Option<&'a Syntax>, NatDefinitionElabError> {
        while state.cursor < state.binders.len() {
            if let Some(annotation) = state.binders[state.cursor].annotation {
                return Ok(Some(annotation));
            }
            self.open_telescope_group(state, None)?;
        }
        Ok(None)
    }

    pub(super) fn open_telescope_group(
        &mut self,
        state: &mut Telescope<'_>,
        domain: Option<Typed>,
    ) -> Result<(), NatDefinitionElabError> {
        let group = &state.binders[state.cursor];
        let annotated = domain
            .map(|term| {
                let level = self.sort_level(&term)?;
                Ok((term.value, level))
            })
            .transpose()?;
        for name in &group.names {
            self.tick()?;
            let expected = state
                .expected_body
                .as_ref()
                .map(|ty| self.whnf(ty))
                .transpose()?;
            let (hint, codomain) = match expected.as_ref().map(Expr::node) {
                Some(ExprNode::ForallE {
                    binder_type, body, ..
                }) => (Some(binder_type.clone()), Some(body.clone())),
                _ => (None, None),
            };
            let (domain, level) = if let Some((domain, level)) = &annotated {
                if let Some(hint) = &hint {
                    self.constrain_type(domain, hint)?;
                }
                (domain.clone(), level.clone())
            } else {
                let level = self.level()?;
                let domain = if let Some(hint) = hint {
                    hint
                } else {
                    self.hole(Expr::sort(level.clone()))?
                };
                // Its actual sort may be determined by later binders/body.
                let ty = self.known_type(&domain)?.ok_or_else(invalid)?;
                self.constrain_type(&ty, &Expr::sort(level.clone()))?;
                (domain, level)
            };
            if group.style == BinderInfo::InstImplicit {
                self.validate_instance_binder(&domain)?;
            }
            let id = FVarId(self.fresh_name()?);
            let name = if name.is_anonymous() {
                self.fresh_name()?
            } else {
                name.clone()
            };
            self.txn
                .lctx
                .add_param(id.clone(), name, domain, group.style);
            state.locals.push(
                self.txn
                    .lctx
                    .find(&id)
                    .expect("new telescope binder")
                    .clone(),
            );
            state.levels.push(level);
            state.expected_body = codomain
                .map(|body| self.substitute(&body, &Expr::fvar(id)))
                .transpose()?;
        }
        state.cursor += 1;
        Ok(())
    }

    pub(super) fn telescope_body_expected(
        &mut self,
        state: &Telescope<'_>,
    ) -> Result<Option<Expr>, NatDefinitionElabError> {
        if state.lambda {
            Ok(state.expected_body.clone())
        } else {
            Ok(Some(self.type_expected()?))
        }
    }

    pub(super) fn finish_telescope(
        &mut self,
        state: Telescope<'_>,
        mut body: Typed,
    ) -> Result<Typed, NatDefinitionElabError> {
        body.value = self.instantiate(&body.value)?;
        body.type_ = self.instantiate(&body.type_)?;
        let mut universe = if state.lambda {
            None
        } else {
            Some(self.sort_level(&body)?)
        };
        for (local, level) in state.locals.iter().zip(&state.levels).rev() {
            self.tick()?;
            let domain = self.instantiate(&local.type_)?;
            body.value = body
                .value
                .abstract_fvar(&local.id, 0)
                .map_err(|_| invalid())?;
            if state.lambda {
                body.type_ = body
                    .type_
                    .abstract_fvar(&local.id, 0)
                    .map_err(|_| invalid())?;
                body.value = Expr::lam(
                    local.user_name.clone(),
                    domain.clone(),
                    body.value,
                    local.binder_info,
                );
                body.type_ = Expr::forall_e(
                    local.user_name.clone(),
                    domain,
                    body.type_,
                    local.binder_info,
                );
            } else {
                body.value = Expr::forall_e(
                    local.user_name.clone(),
                    domain,
                    body.value,
                    local.binder_info,
                );
                universe = Some(
                    Level::imax(level.clone(), universe.take().expect("Pi body universe"))
                        .map_err(|_| invalid())?,
                );
            }
        }
        if let Some(level) = universe {
            body.type_ = Expr::sort(level);
        }
        self.txn.lctx = state.saved;
        self.finish_term(body, state.expected.as_ref())
    }
}

/// The pin's `∃` notation (`«term∃_,_»`, `Init/NotationExtra.lean`): a macro over
/// `explicitBinders` whose expansion, `expandExplicitBinders ``Exists`, is one
/// `Exists fun x : T => …` per bound name, innermost last.
fn exists_kind() -> Name {
    Name::str(Name::anonymous(), "term∃_,_")
}

/// Whether a node is an `∃` the expansion pass must rewrite.
pub(super) fn is_exists(syntax: &Syntax) -> bool {
    syntax.kind() == Some(&exists_kind())
}

/// A node's parts, taken out of it (`Syntax` drops iteratively, so it cannot be
/// destructured by move). Anything else is handed back unchanged.
fn node_parts(mut syntax: Syntax) -> Result<(Name, Vec<Syntax>), Syntax> {
    if let Syntax::Node { kind, args, .. } = &mut syntax {
        return Ok((kind.clone(), std::mem::take(args)));
    }
    Err(syntax)
}

fn take_null(syntax: Syntax) -> Result<Vec<Syntax>, NatDefinitionElabError> {
    match node_parts(syntax) {
        Ok((kind, args)) if kind == Name::from_components(["null"]) => Ok(args),
        _ => Err(invalid()),
    }
}

/// `(colon, domain)` of an optional `: T`, or nothing.
fn take_domain(syntax: Syntax) -> Result<Option<Syntax>, NatDefinitionElabError> {
    let mut parts = take_null(syntax)?;
    match parts.len() {
        0 => Ok(None),
        2 => {
            expect_atom(&parts[0], ":", "existential binder colon")?;
            Ok(parts.pop())
        }
        _ => Err(invalid()),
    }
}

impl Context {
    /// Rewrite one rebuilt `∃ binders, body` node into the pin's expansion. Every
    /// other node is returned unchanged. Only explicit binders exist in this
    /// notation, as at the pin: `∃ {x}, p` and `∃ [C], p` are refused, and so is a
    /// pattern position (`∃` is a term, never a pattern).
    pub(super) fn expand_exists_node(
        &mut self,
        syntax: Syntax,
        pattern: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        if syntax.kind() != Some(&exists_kind()) {
            return Ok(syntax);
        }
        if pattern {
            return Err(invalid());
        }
        let Ok((_, parts)) = node_parts(syntax) else {
            return Err(invalid());
        };
        let Ok([keyword, binders, separator, body]) = <[Syntax; 4]>::try_from(parts) else {
            return Err(invalid());
        };
        expect_atom(&keyword, "∃", "existential keyword")?;
        expect_atom(&separator, ",", "existential separator")?;
        let lean = |name: &str| Name::from_components(["Lean", name]);
        let binder_ident = |syntax: Syntax| -> Result<Syntax, NatDefinitionElabError> {
            match node_parts(syntax) {
                Ok((kind, args)) if kind == lean("binderIdent") => {
                    let Ok([name]) = <[Syntax; 1]>::try_from(args) else {
                        return Err(invalid());
                    };
                    if !simple(&name) {
                        return Err(invalid());
                    }
                    Ok(name)
                }
                _ => Err(invalid()),
            }
        };
        let inner = match node_parts(binders) {
            Ok((kind, args)) if kind == lean("explicitBinders") => {
                let Ok([inner]) = <[Syntax; 1]>::try_from(args) else {
                    return Err(invalid());
                };
                inner
            }
            _ => return Err(invalid()),
        };
        let mut bound: Vec<(Syntax, Option<Syntax>)> = Vec::new();
        match node_parts(inner) {
            // `unbracketedExplicitBinders`: names with one optional shared type.
            Ok((kind, args)) if kind == lean("unbracketedExplicitBinders") => {
                let Ok([names, domain]) = <[Syntax; 2]>::try_from(args) else {
                    return Err(invalid());
                };
                let domain = take_domain(domain)?;
                for name in take_null(names)? {
                    self.tick()?;
                    bound.push((binder_ident(name)?, domain.clone()));
                }
            }
            // One `bracketedExplicitBinders` per `(names : type)` group.
            Ok((kind, groups)) if kind == Name::from_components(["null"]) => {
                for group in groups {
                    self.tick()?;
                    let Ok((kind, parts)) = node_parts(group) else {
                        return Err(invalid());
                    };
                    if kind != lean("bracketedExplicitBinders") {
                        return Err(invalid());
                    }
                    let Ok([open, names, colon, domain, close]) = <[Syntax; 5]>::try_from(parts)
                    else {
                        return Err(invalid());
                    };
                    expect_atom(&open, "(", "existential binder opener")?;
                    expect_atom(&colon, ":", "existential binder colon")?;
                    expect_atom(&close, ")", "existential binder closer")?;
                    for name in take_null(names)? {
                        bound.push((binder_ident(name)?, Some(domain.clone())));
                    }
                }
            }
            _ => return Err(invalid()),
        }
        if bound.is_empty() {
            return Err(invalid());
        }
        let mut result = body;
        for (name, domain) in bound.into_iter().rev() {
            self.tick()?;
            let annotation = match domain {
                Some(domain) => Syntax::node(
                    Name::from_components(["null"]),
                    vec![Syntax::node(
                        parser_kind(&["Term", "typeSpec"]),
                        vec![Syntax::atom(SourceInfo::None, ":"), domain],
                    )],
                ),
                None => Syntax::node(Name::from_components(["null"]), Vec::new()),
            };
            let lambda = Syntax::node(
                parser_kind(&["Term", "fun"]),
                vec![
                    Syntax::atom(SourceInfo::None, "fun"),
                    Syntax::node(
                        parser_kind(&["Term", "basicFun"]),
                        vec![
                            Syntax::node(Name::from_components(["null"]), vec![name]),
                            annotation,
                            Syntax::atom(SourceInfo::None, "=>"),
                            result,
                        ],
                    ),
                ],
            );
            result = Syntax::node(
                parser_kind(&["Term", "app"]),
                vec![
                    Syntax::Ident {
                        info: SourceInfo::None,
                        raw_val: fln_syntax::source::ByteSpan::default(),
                        val: Name::from_components(["Exists"]),
                        preresolved: Vec::new(),
                    },
                    Syntax::node(Name::from_components(["null"]), vec![lambda]),
                ],
            );
        }
        Ok(result)
    }
}
