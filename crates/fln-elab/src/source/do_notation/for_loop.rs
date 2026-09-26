//! Immutable single-collection iteration through the ordinary ForIn dictionary.
//!
//! The pattern-planning walk calls this inside out: nested doFor elements have
//! already become doExpr elements, while a genuine nested do has its own return
//! scope. No recursive expansion, collection-specific primitive or runtime loop
//! is introduced. Instance search and final declaration admission remain unchanged.
use super::*;

fn root(components: &[&str]) -> Syntax {
    ident(Name::from_components(
        std::iter::once("_root_").chain(components.iter().copied()),
    ))
}
fn application(function: Syntax, arguments: Vec<Syntax>) -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "app"]),
        vec![function, null(arguments)],
    )
}

// A private named-argument marker reaches the ordinary application worklist.
// It carries no guessed source expression and cannot be spelled by the parser.
fn monad_argument() -> Syntax {
    Syntax::node(
        parser_kind(&["Term", "namedArgument"]),
        vec![
            atom("("),
            ident(Name::from_components(["m"])),
            atom(":="),
            Syntax::node(parser_kind(&["Term", "nativeDoForMonad"]), vec![]),
            atom(")"),
        ],
    )
}

impl Context {
    /// Preserve the expected monad before alias reduction (notably Id/State)
    /// can erase its application head. Return a typed named argument so the
    /// ordinary application worklist checks and supplies it; this does not infer
    /// injectivity of a higher-kinded metavariable application.
    pub(in crate::source) fn do_for_monad_argument(
        &mut self,
        function: &Typed,
        name: &Name,
        syntax: &Syntax,
        expected: Option<&Expr>,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let marker = parser_kind(&["Term", "nativeDoForMonad"]);
        if syntax.kind() != Some(&marker) {
            return Ok(None);
        }
        expect_node(syntax, &marker, 0, "internal loop monad hint")?;
        if name != &Name::from_components(["m"])
            || !matches!(function.value.node(), ExprNode::Const { name, .. }
                if name == &Name::from_components(["ForIn", "forIn"]))
        {
            return Err(invalid());
        }
        let type_ = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            ..
        } = type_.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        if binder_name != name {
            return Err(invalid());
        }
        let monad = match expected {
            Some(type_) => self.do_monad(type_)?,
            None => None,
        };
        let (value, type_) = match monad {
            Some(monad) => {
                let actual = self
                    .known_type(&monad)?
                    .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
                (monad, actual)
            }
            None => (self.hole(binder_type.clone())?, binder_type.clone()),
        };
        Ok(Some(Typed { value, type_ }))
    }

    pub(super) fn expand_for_loop(
        &mut self,
        syntax: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let mut parts = node(syntax, "doFor", 4)?;
        let sequence = parts.pop().expect("validated loop sequence");
        expect_atom(&parts[0], "for", "loop keyword")?;
        expect_atom(&parts[2], "do", "loop body keyword")?;
        let mut declarations = children(parts.remove(1))?;
        if declarations.len() != 1 {
            return Err(invalid());
        }
        let mut declaration = node(
            declarations.pop().expect("single loop declaration"),
            "doForDecl",
            4,
        )?;
        expect_empty_null(&declaration[0], "loop without membership witness")?;
        expect_atom(&declaration[2], "in", "loop membership keyword")?;
        if !matches!(&declaration[1], Syntax::Ident { val, .. }
            if !val.is_anonymous() && val.parent().is_anonymous())
        {
            return Err(invalid());
        }
        let collection = declaration.pop().expect("validated collection");
        let name = declaration.remove(1);
        let serial = self.next;
        let _ = self.fresh_name()?;
        let accumulator = ident(Name::num(Name::anonymous(), serial));
        let yield_step = application(root(&["ForInStep", "yield"]), vec![accumulator.clone()]);
        // Supplying a continuation rejects any return in this sequence. A loop
        // does not establish the independent return scope that `do` establishes.
        let body = self.expand_do_sequence(sequence, Some(call(false, vec![yield_step])))?;
        let callback = lambda(
            name,
            null(vec![]),
            lambda(accumulator, null(vec![]), body)?,
        )?;
        let action = application(
            root(&["ForIn", "forIn"]),
            vec![monad_argument(), collection, root(&["PUnit", "unit"]), callback],
        );
        // Retain a doElem, not a bare term: the enclosing sequence determines
        // whether to return this action or bind it to the remaining statements.
        Ok(Syntax::node(parser_kind(&["Term", "doExpr"]), vec![action]))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", kind]), args)
    }
    fn named(s: &str) -> Syntax {
        ident(Name::from_components([s]))
    }
    fn sequence(elements: Vec<Syntax>, bracketed: bool) -> Syntax {
        let items = null(
            elements
                .into_iter()
                .map(|element| term("doSeqItem", vec![element, null(vec![])]))
                .collect(),
        );
        if bracketed {
            term("doSeqBracketed", vec![atom("{"), items, atom("}")])
        } else {
            term("doSeqIndent", vec![items])
        }
    }
    fn loop_element(body: Syntax) -> Syntax {
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
    fn count_name(syntax: &Syntax, name: &Name) -> usize {
        let mut count = 0;
        let mut pending = vec![syntax];
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == name => count += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        count
    }
    fn expanded(sequence: Syntax) -> Result<Syntax, NatDefinitionElabError> {
        let syntax = term("do", vec![atom("do"), sequence]);
        Ok(context().lower_pattern_matrices(&syntax)?.into_owned())
    }

    #[test]
    fn monad_hint_is_restricted_to_the_canonical_operation_and_parameter() {
        let mut context = context();
        let marker = term("nativeDoForMonad", vec![]);
        for (function_name, argument_name) in [
            (Name::from_components(["unrelated"]), Name::from_components(["m"])),
            (Name::from_components(["ForIn", "forIn"]), Name::from_components(["wrong"])),
        ] {
            let function = Typed {
                value: Expr::const_(function_name, vec![]),
                type_: Expr::sort(Level::one()),
            };
            assert!(context
                .do_for_monad_argument(&function, &argument_name, &marker, None)
                .is_err());
        }
    }

    #[test]
    fn ordinary_named_arguments_keep_their_original_inference_path() {
        let mut context = context();
        let function = Typed {
            value: Expr::const_(Name::from_components(["ForIn", "forIn"]), vec![]),
            type_: Expr::sort(Level::one()),
        };
        assert!(context
            .do_for_monad_argument(
                &function,
                &Name::from_components(["m"]),
                &term("hole", vec![atom("_")]),
                None,
            )
            .unwrap()
            .is_none());
        assert_eq!(context.next, 0);
    }

    #[test]
    fn loop_keeps_collection_once_and_body_inside_a_hygienic_callback() {
        for bracketed in [false, true] {
            let body = sequence(vec![term("doExpr", vec![named("action")])], bracketed);
            let actual = context().expand_for_loop(loop_element(body)).unwrap();
            let accumulator = ident(Name::num(Name::anonymous(), 0));
            let ignored = ident(Name::num(Name::anonymous(), 1));
            let yielded = call(
                false,
                vec![application(
                    root(&["ForInStep", "yield"]),
                    vec![accumulator.clone()],
                )],
            );
            let body = call(
                true,
                vec![
                    named("action"),
                    lambda(ignored, unit_annotation(), yielded).unwrap(),
                ],
            );
            let expected = term(
                "doExpr",
                vec![application(
                    root(&["ForIn", "forIn"]),
                    vec![
                        monad_argument(),
                        named("collection"),
                        root(&["PUnit", "unit"]),
                        lambda(
                            named("x"),
                            null(vec![]),
                            lambda(accumulator, null(vec![]), body).unwrap(),
                        )
                        .unwrap(),
                    ],
                )],
            );
            assert_eq!(actual, expected);
            for name in ["collection", "action"] {
                assert_eq!(count_name(&actual, &Name::from_components([name])), 1);
            }
        }
    }

    #[test]
    fn nested_loops_and_outer_continuations_use_the_existing_heap_walk() {
        let inner = loop_element(sequence(
            vec![term("doExpr", vec![named("action")])],
            false,
        ));
        let outer = loop_element(sequence(vec![inner], true));
        let result = expanded(sequence(
            vec![
                outer,
                term("doReturn", vec![atom("return"), null(vec![named("x")])]),
            ],
            false,
        ))
        .unwrap();
        let Syntax::Node { kind, args, .. } = &result else {
            panic!("a nonterminal loop must bind its result");
        };
        assert_eq!(kind, &parser_kind(&["Term", "nativeDoBind"]));
        assert_eq!(
            count_name(&args[0], &Name::from_components(["_root_", "ForIn", "forIn"])),
            2
        );
        // The continuation contains neither iteration nor a loop's x binder.
        // Its reference resolves in the outer source context, never the callback.
        assert_eq!(count_name(&args[1], &Name::from_components(["x"])), 1);
        assert_eq!(count_name(&args[1], &Name::from_components(["collection"])), 0);
        assert_eq!(count_name(&result, &Name::num(Name::anonymous(), 0)), 2);
        assert_eq!(count_name(&result, &Name::num(Name::anonymous(), 2)), 2);
    }

    #[test]
    fn loop_returns_are_nonlocal_but_nested_do_returns_have_their_own_scope() {
        let returning = term(
            "doReturn",
            vec![atom("return"), null(vec![named("value")])],
        );
        let direct = loop_element(sequence(vec![returning.clone()], false));
        assert!(expanded(sequence(vec![direct.clone()], false)).is_err());
        let nested_loop = loop_element(sequence(vec![direct], true));
        assert!(expanded(sequence(vec![nested_loop], true)).is_err());
        let nested_do = term("do", vec![atom("do"), sequence(vec![returning], true)]);
        let valid = loop_element(sequence(vec![term("doExpr", vec![nested_do])], false));
        assert!(expanded(sequence(vec![valid], false)).is_ok());
    }

    #[test]
    fn malformed_loops_and_pattern_loops_fail_closed() {
        let good = loop_element(sequence(
            vec![term("doExpr", vec![named("action")])],
            false,
        ));
        assert!(context().expand_do_node(good.clone(), true).is_err());
        for slot in 0..4 {
            let mut bad = good.clone();
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            args[slot] = Syntax::Missing;
            assert!(context().expand_for_loop(bad).is_err());
        }
        // Collection typing belongs to elaboration, not syntax expansion.
        for slot in 0..3 {
            let mut bad = good.clone();
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            let Syntax::Node { args, .. } = &mut args[1] else {
                unreachable!()
            };
            let Syntax::Node { args, .. } = &mut args[0] else {
                unreachable!()
            };
            args[slot] = named("not_the_required_syntax");
            if slot == 1 {
                args[slot] = atom("_");
            }
            assert!(context().expand_for_loop(bad).is_err());
        }
        let empty = loop_element(sequence(vec![], false));
        assert!(context().expand_for_loop(empty).is_err());
    }

    #[test]
    fn loop_expansion_obeys_the_request_budget_and_a_fresh_request_recovers() {
        let input = term(
            "do",
            vec![
                atom("do"),
                sequence(
                    vec![loop_element(sequence(
                        vec![term("doExpr", vec![named("action")])],
                        false,
                    ))],
                    false,
                ),
            ],
        );
        let mut exhausted = context();
        exhausted.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            exhausted.lower_pattern_matrices(&input),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().lower_pattern_matrices(&input).is_ok());
    }
}
