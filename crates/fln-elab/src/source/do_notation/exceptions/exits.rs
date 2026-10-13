//! Transport nonlocal returns as checked Option values across exception regions.
//!
//! None resumes the outside suffix; Some carries a value evaluated at its
//! original return site. The handler chain and finalizer see only the protected
//! action. The dispatcher, and therefore every outside effect, runs afterwards.
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
fn packet(join: &Syntax, value: Option<Syntax>) -> Syntax {
    let mut args = vec![term(
        "namedArgument",
        vec![
            atom("("),
            ident(Name::from_components(["α"])),
            atom(":="),
            term("nativeDoLoopResultType", vec![join.clone()]),
            atom(")"),
        ],
    )];
    let some = value.is_some();
    args.extend(value);
    app(root(&["Option", if some { "some" } else { "none" }]), args)
}

/// Traverse only statement scopes. A let initializer, lambda, parenthesized do
/// expression, condition, or return payload owns its own control flow. Bare
/// nested do elements and loop bodies share the enclosing return.
fn statement_child(kind: &Name, index: usize) -> bool {
    if kind == &Name::from_components(["null"]) {
        return true;
    }
    let is = |name| kind == &parser_kind(&["Term", name]);
    (is("doSeqIndent") || is("doSeqBracketed") || is("matchAlts"))
        || (is("doSeqItem") && index == 0)
        || ((is("doNested") || is("doCatchMatch")) && index == 1)
        || (is("doIf") && (index == 3 || index == 5))
        || (is("doMatch") && index == 6)
        || (is("matchAlt") && index == 3)
        || (is("doLetElse") && index >= 7)
        || (is("doLetArrow") && index == 3)
        || (is("doIdDecl") && index == 3)
        || (is("doPatDecl") && index >= 3)
        || (is("nativeDoTry") && index == 0)
        || (is("doTry") && (index == 1 || index == 2))
        || (is("doCatch") && index == 4)
        || (is("doFor") && index == 3)
        || (is("nativeDoReturningFor") && index == 0)
}

impl Context {
    fn packetize_exception_returns(
        &mut self,
        syntax: Syntax,
        join: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Work {
            Visit(Syntax, usize),
            Keep(Syntax),
            Build(fln_syntax::source::SourceInfo, Name, usize),
        }
        let mut work = vec![Work::Visit(syntax, 0)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Work::Keep(syntax) => values.push(syntax),
                Work::Build(info, kind, count) => {
                    let start = values.len().checked_sub(count).ok_or_else(invalid)?;
                    let args = values.split_off(start);
                    let syntax = Syntax::Node { info, kind, args };
                    values.push(
                        if syntax.kind() == Some(&parser_kind(&["Term", "nativeDoTry"])) {
                            let mut parts = node(syntax, "nativeDoTry", 2)?;
                            expect_atom(&parts[1], "returning", "retained exception control")?;
                            // Descendant regions have already been transformed by
                            // this heap walk. All of them share this packet type;
                            // entering one cannot recursively packetize its source.
                            let action = self.expand_do_try_action(parts.remove(0), Some(join))?;
                            self.forward_exception_packet(action, join)?
                        } else {
                            syntax
                        },
                    );
                }
                Work::Visit(mut syntax, loop_depth) => {
                    if syntax.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                        let mut parts = node(syntax, "doReturn", 2)?;
                        let mut payload = children(parts.pop().expect("return payload"))?;
                        expect_atom(&parts[0], "return", "return keyword")?;
                        if payload.len() != 1 {
                            return Err(invalid());
                        }
                        values.push(term(
                            "doReturn",
                            vec![parts.remove(0), null(vec![packet(join, payload.pop())])],
                        ));
                        continue;
                    }
                    if control::is_jump(&syntax) && loop_depth == 0 {
                        // Loop exits need the loop owner's signal, not an
                        // arbitrary return packet. Keep this boundary explicit.
                        return Err(invalid());
                    }
                    let Syntax::Node { info, kind, args } = &mut syntax else {
                        values.push(syntax);
                        continue;
                    };
                    let info = *info;
                    let kind = kind.clone();
                    let args = std::mem::take(args);
                    let depth = if kind == parser_kind(&["Term", "doFor"]) {
                        loop_depth.checked_add(1).ok_or_else(invalid)?
                    } else {
                        loop_depth
                    };
                    work.push(Work::Build(info, kind.clone(), args.len()));
                    for (index, arg) in args.into_iter().enumerate().rev() {
                        self.tick()?;
                        work.push(if statement_child(&kind, index) {
                            Work::Visit(arg, depth)
                        } else {
                            Work::Keep(arg)
                        });
                    }
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid());
        }
        values.pop().ok_or_else(invalid)
    }

    pub(super) fn expand_exception_sequence(
        &mut self,
        sequence: Syntax,
        join: Option<&Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        match join {
            None => self.expand_do_sequence(sequence, None),
            Some(join) => self.expand_returning_sequence_at(
                sequence,
                Some(call(false, vec![packet(join, None)])),
            ),
        }
    }

    /// Forward an inner packet without executing the outer continuation in
    /// that inner handler's dynamic extent. This is an ordinary monadic match.
    fn forward_exception_packet(
        &mut self,
        action: Syntax,
        join: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let value = self.do_control_name()?;
        let branch = |pattern, element| {
            term(
                "matchAlt",
                vec![
                    atom("|"),
                    null(vec![null(vec![pattern])]),
                    atom("=>"),
                    term(
                        "doSeqIndent",
                        vec![null(vec![term("doSeqItem", vec![element, null(vec![])])])],
                    ),
                ],
            )
        };
        Ok(term(
            "doMatch",
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![]),
                null(vec![term(
                    "matchDiscr",
                    vec![
                        null(vec![]),
                        term(
                            "nestedAction",
                            vec![atom("←"), term("doExpr", vec![action])],
                        ),
                    ],
                )]),
                atom("with"),
                term(
                    "matchAlts",
                    vec![null(vec![
                        branch(
                            app(root(&["Option", "none"]), vec![]),
                            term("doExpr", vec![call(false, vec![root(&["PUnit", "unit"])])]),
                        ),
                        branch(
                            app(root(&["Option", "some"]), vec![value.clone()]),
                            term(
                                "doReturn",
                                vec![atom("return"), null(vec![packet(join, Some(value))])],
                            ),
                        ),
                    ])],
                ),
            ],
        ))
    }

    pub(super) fn expand_returning_try(
        &mut self,
        region: Syntax,
        suffix: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let join = self.do_control_name()?;
        let region = self.packetize_exception_returns(region, &join)?;
        let action = self.expand_do_try_action(region, Some(&join))?;
        let outcome = self.do_control_name()?;
        let returned = self.do_control_name()?;
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
                null(vec![term(
                    "matchDiscr",
                    vec![null(vec![]), outcome.clone()],
                )]),
                atom("with"),
                term(
                    "matchAlts",
                    vec![null(vec![
                        alternative(
                            app(root(&["Option", "none"]), vec![]),
                            app(join.clone(), vec![root(&["Bool", "false"])]),
                        ),
                        alternative(
                            app(root(&["Option", "some"]), vec![returned.clone()]),
                            call(false, vec![returned]),
                        ),
                    ])],
                ),
            ],
        );
        let dispatch = self.lower_do_pattern_match(dispatch)?;
        let body = call(true, vec![action, lambda(outcome, null(vec![]), dispatch)?]);
        Ok(term("nativeDoJoin", vec![join, suffix, body]))
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
    fn sequence(element: Syntax) -> Syntax {
        term(
            "doSeqIndent",
            vec![null(vec![term("doSeqItem", vec![element, null(vec![])])])],
        )
    }
    fn returning(value: Syntax) -> Syntax {
        term("doReturn", vec![atom("return"), null(vec![value])])
    }
    fn region(body: Syntax) -> Syntax {
        term(
            "doTry",
            vec![
                atom("try"),
                sequence(body),
                null(vec![term(
                    "doCatch",
                    vec![
                        atom("catch"),
                        ident(Name::from_components(["e"])),
                        null(vec![]),
                        atom("=>"),
                        sequence(term(
                            "doExpr",
                            vec![call(false, vec![root(&["PUnit", "unit"])])],
                        )),
                    ],
                )]),
                null(vec![]),
            ],
        )
    }
    fn count(syntax: &Syntax, label: &str) -> usize {
        let mut work = vec![syntax];
        let mut count = 0;
        while let Some(syntax) = work.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                count += usize::from(kind == &parser_kind(&["Term", label]));
                work.extend(args);
            }
        }
        count
    }
    #[test]
    fn return_payloads_are_retained_once_and_independent_terms_are_not_rewritten() {
        let join = ident(Name::num(Name::anonymous(), 900));
        let payload = term("do", vec![atom("do"), sequence(returning(atom("42")))]);
        let syntax = sequence(returning(payload.clone()));
        let transformed = context()
            .packetize_exception_returns(syntax, &join)
            .unwrap();
        assert_eq!(count(&transformed, "nativeDoLoopResultType"), 1);
        assert_eq!(count(&transformed, "doReturn"), 2);
        let independent = sequence(term("doExpr", vec![payload]));
        assert_eq!(
            context()
                .packetize_exception_returns(independent.clone(), &join)
                .unwrap(),
            independent
        );
    }
    #[test]
    fn nested_packet_regions_are_lowered_on_heap_frames() {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let mut context = context();
                let join = context.do_control_name().unwrap();
                let mut syntax = returning(atom("42"));
                for _ in 0..80 {
                    syntax = term("nativeDoTry", vec![region(syntax), atom("returning")]);
                }
                let transformed = context
                    .packetize_exception_returns(sequence(syntax), &join)
                    .unwrap();
                assert_eq!(count(&transformed, "nativeDoTry"), 0);
                assert_eq!(count(&transformed, "nestedAction"), 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn terminal_regions_share_the_sequence_worklist_instead_of_the_host_stack() {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let mut syntax = returning(atom("42"));
                for _ in 0..160 {
                    syntax = term("nativeDoTry", vec![region(syntax), atom("returning")]);
                }
                let transformed = context()
                    .expand_returning_sequence(sequence(syntax))
                    .unwrap();
                assert_eq!(count(&transformed, "nativeDoTry"), 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn malformed_payloads_loop_escapes_and_work_exhaustion_do_not_succeed() {
        let join = ident(Name::num(Name::anonymous(), 900));
        for syntax in [
            term("doReturn", vec![atom("return"), null(vec![])]),
            term(
                "doReturn",
                vec![atom("return"), null(vec![atom("1"), atom("2")])],
            ),
            term("doBreak", vec![atom("break")]),
            term("doContinue", vec![atom("continue")]),
        ] {
            assert!(
                context()
                    .packetize_exception_returns(sequence(syntax), &join)
                    .is_err()
            );
        }
        let input = sequence(returning(atom("42")));
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            stopped.packetize_exception_returns(input.clone(), &join),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().packetize_exception_returns(input, &join).is_ok());
    }
}
