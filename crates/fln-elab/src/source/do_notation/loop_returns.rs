//! Nonlocal returns through ordinary ForIn accumulators and checked joins.
//!
//! Each returning loop carries Option R: none means fall through, some value
//! means return from the enclosing do. ForInStep still distinguishes the loop's
//! own break/continue. A nested loop forwards some unchanged and stops its
//! parent; no exception primitive, transformer instance or new axiom is needed.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn root(parts: &[&str]) -> Syntax {
    ident(Name::from_components(
        std::iter::once("_root_").chain(parts.iter().copied()),
    ))
}
fn app(function: Syntax, args: Vec<Syntax>) -> Syntax {
    term("app", vec![function, null(args)])
}
fn step(stop: bool, value: Syntax) -> Syntax {
    app(
        root(&["ForInStep", if stop { "done" } else { "yield" }]),
        vec![value],
    )
}
fn resume(name: Syntax) -> Syntax {
    app(name, vec![root(&["Bool", "false"])])
}
fn skip() -> Syntax {
    call(false, vec![root(&["PUnit", "unit"])])
}
fn option_parameter(return_type: &Syntax) -> Syntax {
    term(
        "namedArgument",
        vec![
            atom("("),
            ident(Name::from_components(["α"])),
            atom(":="),
            return_type.clone(),
            atom(")"),
        ],
    )
}
fn packet(tag: Syntax, state: &[Syntax]) -> Syntax {
    if state.is_empty() {
        tag
    } else {
        let mut fields = Vec::with_capacity(state.len() + 1);
        fields.push(tag);
        fields.extend_from_slice(state);
        mutation::state_tuple(&fields)
    }
}

#[derive(Clone)]
pub(super) struct LoopScope {
    pub(super) targets: control::LoopTargets,
    accumulator: Syntax,
}

pub(super) struct LoopBuild {
    header: for_loop::LoopHeader,
    accumulator: Syntax,
    parameter: Syntax,
    state: Vec<Syntax>,
    normal_tag: Option<Syntax>,
    initial: Syntax,
    join: Syntax,
    suffix: Syntax,
    parent: Option<control::LoopTargets>,
}

impl Context {
    /// Examine statement positions only. Real nested do expressions and action
    /// values own their own return scope and must never trigger propagation.
    pub(super) fn loop_has_return(
        &mut self,
        syntax: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![syntax];
        while let Some(syntax) = work.pop() {
            self.tick()?;
            let Syntax::Node { kind, args, .. } = syntax else {
                continue;
            };
            if nested::sequence(syntax).is_some() {
                // A value-bearing nested element also needs the enclosing
                // continuation worklist. Keep this loop until that worklist
                // owns its normal completion, break/continue and return paths.
                return Ok(true);
            }
            if kind == &parser_kind(&["Term", "doReturn"])
                || kind == &parser_kind(&["Term", "nativeDoReturningFor"])
            {
                // Descendant loops were already inspected by the inside-out
                // walk. Their marker avoids quadratic rescanning at depth.
                return Ok(true);
            }
            if kind == &parser_kind(&["Term", "doFor"]) {
                let parts = expect_node(syntax, kind, 4, "return-carrying loop")?;
                work.push(&parts[3]);
            } else if kind == &parser_kind(&["Term", "nativeDoTry"]) {
                let parts = expect_node(syntax, kind, 2, "retained exception region")?;
                expect_atom(&parts[1], "returning", "retained exception control")?;
                work.push(&parts[0]);
            } else if kind == &parser_kind(&["Term", "doTry"]) {
                let parts = expect_node(syntax, kind, 4, "return-carrying exception region")?;
                // Only the protected action and handlers share this return.
                // Cleanup has its own scope and cannot escape into the loop.
                work.push(&parts[1]);
                work.push(&parts[2]);
            } else if kind == &parser_kind(&["Term", "doCatch"]) {
                let parts = expect_node(syntax, kind, 5, "return-carrying handler")?;
                work.push(&parts[4]);
            } else if kind == &parser_kind(&["Term", "doCatchMatch"]) {
                let parts = expect_node(syntax, kind, 2, "return-carrying pattern handler")?;
                work.push(&parts[1]);
            } else if kind == &parser_kind(&["Term", "doIf"]) {
                let parts = expect_node(syntax, kind, 6, "return-carrying branch")?;
                work.push(&parts[3]);
                work.push(&parts[5]);
            } else if kind == &parser_kind(&["Term", "doMatch"]) {
                let parts = expect_node(syntax, kind, 7, "return-carrying match")?;
                work.push(&parts[6]);
            } else if kind == &parser_kind(&["Term", "matchAlt"]) {
                let parts = expect_node(syntax, kind, 4, "return-carrying arm")?;
                work.push(&parts[3]);
            } else if kind == &parser_kind(&["Term", "doSeqItem"]) {
                let parts = expect_node(syntax, kind, 2, "loop statement")?;
                work.push(&parts[0]);
            } else if kind == &parser_kind(&["Term", "doSeqIndent"])
                || kind == &parser_kind(&["Term", "doSeqBracketed"])
                || kind == &parser_kind(&["Term", "matchAlts"])
                || kind == &Name::from_components(["null"])
            {
                work.extend(args);
            }
        }
        Ok(false)
    }

    /// The existing named-argument path checks this type like any written
    /// Option constructor parameter. Its source is the enclosing join's ORIGINAL
    /// result, before Id/State alias reduction; no monad injectivity is assumed.
    pub(super) fn do_loop_result_argument(
        &mut self,
        function: &Typed,
        name: &Name,
        syntax: &Syntax,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.tick()?;
        let stateful =
            syntax.kind() == Some(&parser_kind(&["Term", "nativeDoStateLoopResultType"]));
        let parts = expect_node(
            syntax,
            &parser_kind(&[
                "Term",
                if stateful {
                    "nativeDoStateLoopResultType"
                } else {
                    "nativeDoLoopResultType"
                },
            ]),
            1,
            "loop result type",
        )?;
        let Syntax::Ident { val: join, .. } = &parts[0] else {
            return Err(invalid());
        };
        if !join.parent().is_anonymous()
            || !matches!(join.leaf_view(), fln_core::name::LeafView::Num(_))
            || name != &Name::from_components(["α"])
            || !matches!(function.value.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["Option", "none"])
                    || name == &Name::from_components(["Option", "some"]))
        {
            return Err(invalid());
        }
        let local = self.txn.lctx.find_by_user_name(join).ok_or_else(invalid)?;
        let type_ = self.instantiate(&local.type_.clone())?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Err(invalid());
        };
        let mut result = if stateful {
            // nativeDoBindJoin checks its body against the ORIGINAL enclosing
            // result and gives the state continuation a nondependent domain.
            // Remove no dependency and invent no term of the state type.
            if body.has_loose_bvars() {
                return Err(invalid());
            }
            body.clone()
        } else {
            let bool_type = self.constant(&Name::from_components(["Bool"]))?.value;
            self.constrain_type(binder_type, &bool_type)?;
            let no = self
                .constant(&Name::from_components(["Bool", "false"]))?
                .value;
            self.substitute(body, &no)?
        };
        loop {
            self.tick()?;
            match result.node() {
                ExprNode::MData { expr, .. } => result = expr.clone(),
                ExprNode::LetE { value, body, .. } => result = self.substitute(body, value)?,
                ExprNode::App { a, .. } => {
                    let value = a.clone();
                    let type_ = self.known_type(&value)?.ok_or_else(invalid)?;
                    return Ok(Typed { value, type_ });
                }
                _ => return Err(invalid()),
            }
        }
    }

    pub(super) fn prepare_returning_loop(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        parent: Option<&LoopScope>,
    ) -> Result<(LoopBuild, Syntax, LoopScope, Syntax), NatDefinitionElabError> {
        self.tick()?;
        let (syntax, state) =
            if syntax.kind() == Some(&parser_kind(&["Term", "nativeDoReturningMutFor"])) {
                let mut parts = node(syntax, "nativeDoReturningMutFor", 5)?;
                let state = children(parts.pop().expect("mutable returning loop state"))?;
                if state.is_empty()
                    || state.iter().any(|name| {
                        !matches!(name, Syntax::Ident { val, .. }
                    if !val.is_anonymous() && val.parent().is_anonymous())
                    })
                {
                    return Err(invalid());
                }
                (term("doFor", parts), state)
            } else {
                (syntax, Vec::new())
            };
        let (header, sequence) = self.split_for_loop(syntax)?;
        let join = self.do_control_name()?;
        let accumulator = self.do_control_name()?;
        let parameter = if state.is_empty() {
            accumulator.clone()
        } else {
            self.do_control_name()?
        };
        let return_type = match parent {
            Some(parent) => parent.targets.return_type.clone().ok_or_else(invalid)?,
            None => term(
                if state.is_empty() {
                    "nativeDoLoopResultType"
                } else {
                    "nativeDoStateLoopResultType"
                },
                vec![join.clone()],
            ),
        };
        let none = app(
            root(&["Option", "none"]),
            vec![option_parameter(&return_type)],
        );
        let initial = if state.is_empty() {
            parent.map_or_else(|| none.clone(), |parent| parent.accumulator.clone())
        } else {
            packet(none.clone(), &state)
        };
        let normal = call(
            false,
            vec![step(false, packet(accumulator.clone(), &state))],
        );
        let mut targets = control::LoopTargets::new(&normal)?;
        targets.return_type = Some(return_type);
        targets.return_state = state.clone();
        let scope = LoopScope {
            targets,
            accumulator: accumulator.clone(),
        };
        Ok((
            LoopBuild {
                header,
                accumulator,
                parameter,
                normal_tag: (!state.is_empty()).then_some(none),
                state,
                initial,
                join,
                suffix: suffix.unwrap_or_else(skip),
                parent: parent.map(|parent| parent.targets.clone()),
            },
            sequence,
            scope,
            normal,
        ))
    }

    pub(super) fn expand_loop_return(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.expand_loop_return_with_signal(syntax, false, None)
    }

    pub(super) fn expand_loop_return_with_signal(
        &mut self,
        syntax: Syntax,
        signal: bool,
        return_type: Option<&Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.expand_loop_return_with_state(syntax, signal, return_type, &[])
    }

    pub(super) fn expand_scoped_loop_return(
        &mut self,
        syntax: Syntax,
        signal: bool,
        targets: &control::LoopTargets,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let return_type = targets.return_type.as_ref().ok_or_else(invalid)?;
        self.expand_loop_return_with_state(syntax, signal, Some(return_type), &targets.return_state)
    }

    fn expand_loop_return_with_state(
        &mut self,
        syntax: Syntax,
        signal: bool,
        return_type: Option<&Syntax>,
        state: &[Syntax],
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let mut parts = node(syntax, "doReturn", 2)?;
        let mut values = children(parts.pop().expect("return payload"))?;
        expect_atom(&parts[0], "return", "return keyword")?;
        if values.len() != 1 {
            return Err(invalid());
        }
        // Construct the payload at the return site, not in a delayed thunk.
        // Its expected R comes from the checked Option R accumulator.
        if let Some(return_type) = return_type {
            // An all-return protected action need not mention the accumulator.
            // Use the already-checked outer join to choose Option's parameter,
            // before the handler's signal match needs its inductive head.
            values.insert(0, option_parameter(return_type));
        }
        let result = step(true, packet(app(root(&["Option", "some"]), values), state));
        // The outer done skips the branch/exception suffix; the inner done
        // stops ForIn with the value. Both tags survive handlers and cleanup.
        Ok(call(
            false,
            vec![if signal { step(true, result) } else { result }],
        ))
    }

    pub(super) fn finish_returning_loop(
        &mut self,
        build: LoopBuild,
        body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let body = if let Some(none) = build.normal_tag {
            // ForIn may supply any prior packet. Each actual normal exit uses
            // a fresh none, together with the values at that exit site.
            let body = self.rebind_loop_state(
                &build.state,
                &build.parameter,
                1,
                build.state.len() + 1,
                body,
            )?;
            self.bind_loop_local(build.accumulator, none, body)?
        } else {
            body
        };
        let action = self.finish_for_loop(build.header, build.parameter, build.initial, body)?;
        let exit = self.do_control_name()?;
        let returned = self.do_control_name()?;
        let propagate = if let Some(parent) = &build.parent {
            let return_type = parent.return_type.as_ref().ok_or_else(invalid)?;
            let tag = app(
                root(&["Option", "some"]),
                vec![option_parameter(return_type), returned.clone()],
            );
            call(false, vec![step(true, packet(tag, &parent.return_state))])
        } else {
            call(false, vec![returned.clone()])
        };
        let result_tag = if build.state.is_empty() {
            exit.clone()
        } else {
            mutation::component(&exit, 0, build.state.len() + 1)
        };
        let resume = if build.state.is_empty() {
            resume(build.join.clone())
        } else {
            app(
                build.join.clone(),
                vec![mutation::state_tuple(&build.state)],
            )
        };
        let alternative = |pattern, body| {
            term(
                "matchAlt",
                vec![atom("|"), null(vec![null(vec![pattern])]), atom("=>"), body],
            )
        };
        let dispatch = term(
            "match",
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![term("matchDiscr", vec![null(vec![]), result_tag])]),
                atom("with"),
                term(
                    "matchAlts",
                    vec![null(vec![
                        alternative(app(root(&["Option", "none"]), vec![]), resume),
                        alternative(app(root(&["Option", "some"]), vec![returned]), propagate),
                    ])],
                ),
            ],
        );
        let dispatch = self.lower_do_pattern_match(dispatch)?;
        // Rebind before both dispatch arms: a nested return must forward the
        // child's final values into its parent's packet, including shared state.
        let dispatch =
            self.rebind_loop_state(&build.state, &exit, 1, build.state.len() + 1, dispatch)?;
        let action = call(true, vec![action, lambda(exit, null(vec![]), dispatch)?]);
        // Check the suffix outside callback/pattern binders. Mutable values
        // arrive as its parameter, never as a thunk's stale captured values.
        if build.state.is_empty() {
            Ok(term("nativeDoJoin", vec![build.join, build.suffix, action]))
        } else {
            let parameter = self.do_control_name()?;
            let suffix = self.rebind_loop_state(
                &build.state,
                &parameter,
                0,
                build.state.len(),
                build.suffix,
            )?;
            let annotation = self.loop_state_annotation(&build.state)?;
            let continuation = lambda(parameter, annotation, suffix)?;
            Ok(term(
                "nativeDoBindJoin",
                vec![build.join, continuation, action],
            ))
        }
    }

    /// Fix the continuation's state domain from the variables already in
    /// scope, before nested callback projections create inference constraints.
    /// Reassignment preserves these checked types, including their free-local
    /// identities; no body or monadic action is evaluated to recover them.
    fn loop_state_annotation(
        &mut self,
        state: &[Syntax],
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut names = state.iter().rev();
        let last = names.next().ok_or_else(invalid)?;
        self.tick()?;
        let mut type_ = term("nativeDoTypeOf", vec![last.clone()]);
        for name in names {
            self.tick()?;
            type_ = app(
                root(&["Prod"]),
                vec![term("nativeDoTypeOf", vec![name.clone()]), type_],
            );
        }
        Ok(null(vec![term("typeSpec", vec![atom(":"), type_])]))
    }

    fn bind_loop_local(
        &mut self,
        name: Syntax,
        value: Syntax,
        body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        Ok(term(
            "let",
            vec![
                atom("let"),
                term("letConfig", vec![null(vec![])]),
                term(
                    "letDecl",
                    vec![term(
                        "letIdDecl",
                        vec![
                            term("letId", vec![name]),
                            null(vec![]),
                            null(vec![]),
                            atom(":="),
                            value,
                        ],
                    )],
                ),
                atom(";"),
                body,
            ],
        ))
    }

    fn rebind_loop_state(
        &mut self,
        state: &[Syntax],
        parameter: &Syntax,
        first: usize,
        count: usize,
        mut body: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        for (index, name) in state.iter().enumerate().rev() {
            self.tick()?;
            body = self.bind_loop_local(
                name.clone(),
                mutation::component(parameter, first + index, count),
                body,
            )?;
        }
        Ok(body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn named(name: &str) -> Syntax {
        ident(Name::from_components([name]))
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn sequence(elements: Vec<Syntax>) -> Syntax {
        term(
            "doSeqIndent",
            vec![null(
                elements
                    .into_iter()
                    .map(|element| term("doSeqItem", vec![element, null(vec![])]))
                    .collect(),
            )],
        )
    }
    fn returning(value: &str) -> Syntax {
        term("doReturn", vec![atom("return"), null(vec![named(value)])])
    }
    fn loop_(body: Syntax) -> Syntax {
        term(
            "doFor",
            vec![
                atom("for"),
                null(vec![term(
                    "doForDecl",
                    vec![null(vec![]), named("x"), atom("in"), named("collection")],
                )]),
                atom("do"),
                body,
            ],
        )
    }
    fn count(syntax: &Syntax, name: &str) -> usize {
        let name = Name::from_components([name]);
        let mut pending = vec![syntax];
        let mut n = 0;
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == &name => n += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        n
    }
    fn expanded(body: Syntax) -> Syntax {
        context()
            .lower_pattern_matrices(&term("do", vec![atom("do"), body]))
            .unwrap()
            .into_owned()
    }
    #[test]
    fn returns_store_the_original_value_once_in_a_checked_some_payload() {
        let result = context().expand_loop_return(returning("value")).unwrap();
        assert_eq!(count(&result, "value"), 1);
        let pure = expect_node(
            &result,
            &parser_kind(&["Term", "nativeDoPure"]),
            1,
            "return",
        )
        .unwrap();
        let outer = expect_node(&pure[0], &parser_kind(&["Term", "app"]), 2, "done").unwrap();
        assert_eq!(outer[0], root(&["ForInStep", "done"]));
        let [payload] = expect_null_args(&outer[1], "payload").unwrap() else {
            panic!("one value")
        };
        let inner = expect_node(payload, &parser_kind(&["Term", "app"]), 2, "some").unwrap();
        assert_eq!(inner[0], root(&["Option", "some"]));
    }

    #[test]
    fn exception_return_signals_wrap_the_loop_stop_without_delaying_its_payload() {
        let hint = term("nativeDoLoopResultType", vec![named("checkedJoin")]);
        let result = context()
            .expand_loop_return_with_signal(returning("payload"), true, Some(&hint))
            .unwrap();
        assert_eq!(count(&result, "payload"), 1);
        assert_eq!(count(&result, "checkedJoin"), 1);
        let pure = expect_node(
            &result,
            &parser_kind(&["Term", "nativeDoPure"]),
            1,
            "signal",
        )
        .unwrap();
        let signal =
            expect_node(&pure[0], &parser_kind(&["Term", "app"]), 2, "outer done").unwrap();
        assert_eq!(signal[0], root(&["ForInStep", "done"]));
        let [loop_stop] = expect_null_args(&signal[1], "loop stop").unwrap() else {
            panic!("one stop")
        };
        let stop = expect_node(loop_stop, &parser_kind(&["Term", "app"]), 2, "inner done").unwrap();
        assert_eq!(stop[0], root(&["ForInStep", "done"]));
    }

    #[test]
    fn return_discovery_crosses_handlers_but_not_cleanup_or_action_values() {
        let retained = |body, catches, cleanup| {
            term(
                "nativeDoTry",
                vec![
                    term(
                        "doTry",
                        vec![atom("try"), body, null(catches), null(cleanup)],
                    ),
                    atom("returning"),
                ],
            )
        };
        let ordinary = || sequence(vec![term("doExpr", vec![named("action")])]);
        let handler = term(
            "doCatch",
            vec![
                atom("catch"),
                named("e"),
                null(vec![]),
                atom("=>"),
                sequence(vec![returning("payload")]),
            ],
        );
        assert!(
            context()
                .loop_has_return(&retained(ordinary(), vec![handler], vec![]))
                .unwrap()
        );
        let cleanup = term(
            "doFinally",
            vec![atom("finally"), sequence(vec![returning("ownReturn")])],
        );
        let independent = sequence(vec![term(
            "doExpr",
            vec![term(
                "do",
                vec![atom("do"), sequence(vec![returning("ownReturn")])],
            )],
        )]);
        assert!(
            !context()
                .loop_has_return(&retained(independent, vec![], vec![cleanup]))
                .unwrap()
        );
    }
    #[test]
    fn nested_loops_keep_each_collection_value_and_source_suffix_once() {
        let inner = loop_(sequence(vec![returning("payload")]));
        let outer = loop_(sequence(vec![
            inner,
            term("doExpr", vec![named("innerSuffix")]),
        ]));
        let result = expanded(sequence(vec![outer, returning("outerSuffix")]));
        for name in ["payload", "innerSuffix", "outerSuffix"] {
            assert_eq!(count(&result, name), 1);
        }
        assert_eq!(count(&result, "collection"), 2);
        assert_eq!(result.kind(), Some(&parser_kind(&["Term", "nativeDoJoin"])));
    }
    #[test]
    fn distinct_do_expressions_are_not_scanned_as_nonlocal_return_sites() {
        let separate = term(
            "doExpr",
            vec![term(
                "do",
                vec![atom("do"), sequence(vec![returning("inner")])],
            )],
        );
        assert!(
            !context()
                .loop_has_return(&loop_(sequence(vec![separate])))
                .unwrap()
        );
        let sequence = sequence(vec![returning("outer")]);
        assert!(context().loop_has_return(&loop_(sequence)).unwrap());
    }
    #[test]
    fn malformed_return_payloads_and_result_type_handoffs_fail_closed() {
        for bad in [
            term("doReturn", vec![]),
            term("doReturn", vec![atom("yield"), null(vec![named("x")])]),
            term("doReturn", vec![atom("return"), null(vec![])]),
            term(
                "doReturn",
                vec![atom("return"), null(vec![named("x"), named("y")])],
            ),
        ] {
            assert!(context().expand_loop_return(bad).is_err());
        }
        let function = Typed {
            value: Expr::const_(Name::from_components(["Option", "none"]), vec![]),
            type_: Expr::sort(Level::one()),
        };
        for payload in [
            named("spellable"),
            ident(Name::num(Name::anonymous(), 999)),
            Syntax::Missing,
        ] {
            let syntax = term("nativeDoLoopResultType", vec![payload]);
            assert!(
                context()
                    .do_for_monad_argument(&function, &Name::from_components(["α"]), &syntax, None)
                    .is_err()
            );
        }
        assert!(
            context()
                .do_for_monad_argument(
                    &function,
                    &Name::from_components(["m"]),
                    &term("nativeDoLoopResultType", vec![]),
                    None
                )
                .is_err()
        );
    }
    #[test]
    fn deeply_nested_returning_loops_use_the_heap_without_quadratic_scan_work() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut body = returning("payload");
                for _ in 0..600 {
                    body = loop_(sequence(vec![body]));
                }
                let result = expanded(sequence(vec![body, returning("suffix")]));
                assert_eq!(count(&result, "collection"), 600);
                assert_eq!(count(&result, "payload"), 1);
                assert_eq!(count(&result, "suffix"), 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn request_exhaustion_is_typed_and_fresh_requests_recover() {
        let body = term(
            "do",
            vec![
                atom("do"),
                sequence(vec![
                    loop_(sequence(vec![returning("payload")])),
                    returning("suffix"),
                ]),
            ],
        );
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            stopped.lower_pattern_matrices(&body),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().lower_pattern_matrices(&body).is_ok());
    }
}
