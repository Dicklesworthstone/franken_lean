//! Checked exception combinators. Handlers are real lambdas; the instance's
//! admitted implementation decides which action runs. No host exception or
//! privileged execution path is introduced by this syntax expansion.
use super::*;

fn apply(name: &[&str], mut arguments: Vec<Syntax>) -> Syntax {
    // Use the ordinary named-argument path so the expected action parameters
    // are available before checking the protected action or pattern handler.
    // The monad is still inferred and checked at the admitted operation's type.
    arguments.insert(
        0,
        Syntax::node(
            parser_kind(&["Term", "namedArgument"]),
            vec![
                atom("("),
                ident(Name::from_components(["m"])),
                atom(":="),
                Syntax::node(parser_kind(&["Term", "hole"]), vec![atom("_")]),
                atom(")"),
            ],
        ),
    );
    Syntax::node(
        parser_kind(&["Term", "app"]),
        vec![
            ident(Name::from_components(
                std::iter::once("_root_").chain(name.iter().copied()),
            )),
            null(arguments),
        ],
    )
}
impl Context {
    /// Choose an exception combinator's still-unknown monad/result parameters
    /// before its protected action, not just before its last argument. Nested
    /// handlers and finalizers need that expected monad while resolving the
    /// exception dictionary that gives a pattern handler its discriminant type.
    /// This is ordinary typed parameter inference, never monad injectivity.
    pub(in crate::source) fn do_exception_result_hint(
        &mut self,
        function: &Typed,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        let mut head = &function.value;
        let mut supplied = 0_usize;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            supplied = supplied.checked_add(1).ok_or_else(invalid)?;
            head = f;
        }
        let ExprNode::Const { name, .. } = head.node() else {
            return Ok(());
        };
        if name != &Name::from_components(["MonadExcept", "tryCatch"])
            && name != &Name::from_components(["tryCatchThe"])
            && name != &Name::from_components(["tryFinally"])
        {
            return Ok(());
        }
        let Some(info) = self.txn.env.find(name) else {
            return Ok(());
        };
        let mut declaration_type = info.constant_val().type_.clone();
        let mut arity = 0_usize;
        while let ExprNode::ForallE { body, .. } = declaration_type.node() {
            self.tick()?;
            arity = arity.checked_add(1).ok_or_else(invalid)?;
            declaration_type = body.clone();
        }
        let Some(remaining) = arity.checked_sub(supplied).filter(|n| *n != 0) else {
            // Later arguments of a function-valued result do not belong to
            // the operation's own telescope and must not change its choices.
            return Ok(());
        };
        let mut result = function.type_.clone();
        for _ in 0..remaining {
            self.tick()?;
            let ExprNode::ForallE { body, .. } = result.node() else {
                return Ok(());
            };
            result = body.clone();
        }
        if result.has_loose_bvars() {
            return Ok(());
        }
        let result = self.instantiate(&result)?;
        let expected = self.instantiate(expected)?;
        let (
            ExprNode::App {
                f: monad,
                a: element,
            },
            ExprNode::App {
                f: target_monad,
                a: target_element,
            },
        ) = (result.node(), expected.node())
        else {
            return Ok(());
        };
        if matches!(monad.node(), ExprNode::MVar { .. }) {
            self.constrain_type(monad, target_monad)?;
        } else if monad != target_monad {
            return Ok(());
        }
        if matches!(element.node(), ExprNode::MVar { .. }) {
            self.constrain_type(element, target_element)?;
        }
        Ok(())
    }

    /// The pin lowers `catch | ...` to a fresh named handler whose body is a
    /// do-match. Keep the original alternatives: coverage, dot constructors,
    /// branch bindings and every branch's typing belong to the shared matcher.
    /// A private numeric name cannot capture a source identifier in a pattern.
    fn expand_catch_pattern(&mut self, syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let mut parts = node(syntax, "doCatchMatch", 2)?;
        expect_atom(&parts[0], "catch", "pattern handler keyword")?;
        let alternatives = parts.pop().expect("handler alternatives");
        expect_node(
            &alternatives,
            &parser_kind(&["Term", "matchAlts"]),
            1,
            "pattern handler alternatives",
        )?;
        let name = self.do_control_name()?;
        let term = |kind: &str, args| Syntax::node(parser_kind(&["Term", kind]), args);
        let body = term(
            "doMatch",
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![]),
                null(vec![term("matchDiscr", vec![null(vec![]), name.clone()])]),
                atom("with"),
                alternatives,
            ],
        );
        Ok(term(
            "doCatch",
            vec![
                parts.pop().expect("catch keyword"),
                name,
                null(vec![]),
                atom("=>"),
                term(
                    "doSeqIndent",
                    vec![null(vec![term("doSeqItem", vec![body, null(vec![])])])],
                ),
            ],
        ))
    }

    fn exception_control(&mut self, syntax: &Syntax) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![syntax];
        while let Some(s) = work.pop() {
            self.tick()?;
            if control::is_jump(s) || s.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                return Ok(true);
            }
            if s.kind() == Some(&parser_kind(&["Term", "nativeDoTry"])) {
                let parts = expect_node(
                    s,
                    &parser_kind(&["Term", "nativeDoTry"]),
                    2,
                    "exception action",
                )?;
                if matches!(&parts[1],Syntax::Atom {val,..} if val=="returning") {
                    return Ok(true);
                }
                continue;
            }
            if let Syntax::Node { args, .. } = s {
                work.extend(args);
            }
        }
        Ok(false)
    }

    pub(super) fn expand_do_try(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "doTry", 4)?;
        expect_atom(&parts[0], "try", "exception keyword")?;
        let finally = parts.pop().expect("optional finalizer");
        let mut finally = children(finally)?;
        let catches = children(parts.pop().expect("handlers"))?;
        if finally.len() > 1 || catches.is_empty() && finally.is_empty() {
            return Err(invalid());
        }
        let body = parts.pop().expect("protected sequence");
        let mut returning = self.exception_control(&body)?;
        let mut action = self.expand_do_sequence(body, None)?;
        for handler in catches {
            let handler = if handler.kind() == Some(&parser_kind(&["Term", "doCatchMatch"])) {
                self.expand_catch_pattern(handler)?
            } else {
                handler
            };
            let mut parts = node(handler, "doCatch", 5)?;
            expect_atom(&parts[0], "catch", "handler keyword")?;
            if !matches!(&parts[3],Syntax::Atom{val,..} if val=="=>" || val=="↦") {
                return Err(invalid());
            }
            let body = parts.pop().expect("handler sequence");
            returning |= self.exception_control(&body)?;
            let body = self.expand_do_sequence(body, None)?;
            let annotation = children(parts.remove(2))?;
            let name = parts.remove(1);
            let handler = lambda(name, null(vec![]), body)?;
            action = match annotation.as_slice() {
                [] => apply(&["MonadExcept", "tryCatch"], vec![action, handler]),
                [colon, type_] => {
                    expect_atom(colon, ":", "handler type")?;
                    apply(&["tryCatchThe"], vec![type_.clone(), action, handler])
                }
                _ => return Err(invalid()),
            };
        }
        if let Some(finalizer) = finally.pop() {
            let mut parts = node(finalizer, "doFinally", 2)?;
            expect_atom(&parts[0], "finally", "finalizer keyword")?;
            let body = parts.pop().expect("finalizer sequence");
            // As in the pin's doTryToCode, cleanup cannot escape its region.
            // Use tryFinally, not bind: cleanup also runs when the action or
            // a catch handler fails, and the admitted instance owns precedence.
            if self.exception_control(&body)? {
                return Err(invalid());
            }
            let cleanup = self.expand_do_sequence(body, None)?;
            action = apply(&["tryFinally"], vec![action, cleanup]);
        }
        Ok(if returning {
            Syntax::node(
                parser_kind(&["Term", "nativeDoTry"]),
                vec![action, atom("returning")],
            )
        } else {
            // Normal completion must remain a doExpr: the enclosing nested-do
            // worklist attaches its value continuation to that category.
            Syntax::node(parser_kind(&["Term", "doExpr"]), vec![action])
        })
    }

    pub(super) fn prepend_do_try(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        scope: SequenceScope<'_>,
        terminal: bool,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "nativeDoTry", 2)?;
        let flag = parts.pop().expect("exception control flag");
        let returning = match &flag {
            Syntax::Atom { val, .. } if val == "returning" => true,
            Syntax::Atom { val, .. } if val == "action" => false,
            _ => return Err(invalid()),
        };
        // Until tagged exits are threaded through the combinator, refuse a
        // nonlocal exit rather than treating return/break as ordinary fallthrough.
        if returning && (!terminal || suffix.is_some() || !scope.allow_return) {
            return Err(invalid());
        }
        self.prepend_do_element(
            Syntax::node(parser_kind(&["Term", "doExpr"]), parts),
            suffix,
            scope,
            terminal,
        )
    }
}

#[cfg(test)]
mod pattern_tests {
    use super::*;

    fn term(name: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", name]), args)
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn alternatives() -> Syntax {
        term(
            "matchAlts",
            vec![null(vec![term(
                "matchAlt",
                vec![
                    atom("|"),
                    null(vec![null(vec![ident(Name::from_components(["payload"]))])]),
                    atom("=>"),
                    term(
                        "doSeqIndent",
                        vec![null(vec![term(
                            "doSeqItem",
                            vec![
                                term(
                                    "doReturn",
                                    vec![
                                        atom("return"),
                                        null(vec![ident(Name::from_components(["payload"]))]),
                                    ],
                                ),
                                null(vec![]),
                            ],
                        )])],
                    ),
                ],
            )])],
        )
    }
    #[test]
    fn fresh_handler_keeps_original_alternatives_and_only_one_discriminant() {
        let mut context = context();
        let rows = alternatives();
        let result = context
            .expand_catch_pattern(term("doCatchMatch", vec![atom("catch"), rows.clone()]))
            .unwrap();
        let parts = node(result, "doCatch", 5).unwrap();
        let Syntax::Ident { val, .. } = &parts[1] else {
            panic!("fresh handler")
        };
        assert!(val.parent().is_anonymous());
        assert!(matches!(val.leaf_view(), fln_core::name::LeafView::Num(_)));
        let statements = sequence_items(parts[4].clone()).unwrap();
        assert_eq!(statements.len(), 1);
        let matching = node(
            sequence_element(statements[0].clone()).unwrap(),
            "doMatch",
            7,
        )
        .unwrap();
        let discriminants = children(matching[4].clone()).unwrap();
        assert_eq!(discriminants.len(), 1);
        let discriminant = node(discriminants[0].clone(), "matchDiscr", 2).unwrap();
        assert_eq!(discriminant[1], parts[1]);
        assert_eq!(matching[6], rows);
        assert!(context.exception_control(&parts[4]).unwrap());
    }

    #[test]
    fn malformed_pattern_handler_nodes_are_not_silently_rewritten() {
        for input in [
            Syntax::Missing,
            term("doCatchMatch", vec![atom("catch")]),
            term("doCatchMatch", vec![atom("finally"), alternatives()]),
            term("doCatchMatch", vec![atom("catch"), Syntax::Missing]),
            term(
                "doCatchMatch",
                vec![atom("catch"), alternatives(), atom("unchecked")],
            ),
        ] {
            assert!(context().expand_catch_pattern(input).is_err());
        }
    }

    #[test]
    fn expansion_exhaustion_is_typed_and_a_fresh_attempt_recovers() {
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        stopped.txn.budget.heartbeats_consumed = 1;
        let input = term("doCatchMatch", vec![atom("catch"), alternatives()]);
        assert!(matches!(
            stopped.expand_catch_pattern(input.clone()),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().expand_catch_pattern(input).is_ok());
    }
}
