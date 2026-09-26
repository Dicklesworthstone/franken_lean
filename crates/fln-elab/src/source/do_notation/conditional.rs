//! Scope-preserving do conditionals over the ordinary checked term machinery.
//!
//! A loop branch returns one of three signals using ForInStep twice: outer
//! done forwards a break/continue step, outer yield resumes the remaining body.
//! The suffix occurs once, outside all source branch binders. No branch action
//! is executed by the frontend and no control instruction gains kernel authority.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn root(label: &str) -> Syntax {
    ident(Name::from_components(["_root_", "ForInStep", label]))
}
fn one_element(sequence: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut items = sequence_items(sequence)?;
    if items.len() != 1 {
        return Err(invalid());
    }
    let mut item = node(
        items.pop().expect("single conditional branch"),
        "doSeqItem",
        2,
    )?;
    let separators = children(item.pop().expect("optional branch separator"))?;
    match separators.as_slice() {
        [] => {}
        [separator] => {
            expect_atom(separator, ";", "branch separator")?;
        }
        _ => return Err(invalid()),
    }
    item.pop().ok_or_else(invalid)
}

/// Validate the complete bounded doIf shape before moving its branches into
/// the heap worklist. An unsupported else-if list is never silently discarded.
fn split(syntax: Syntax) -> Result<(Vec<Syntax>, Syntax, Syntax), NatDefinitionElabError> {
    let mut parts = node(syntax, "doIf", 6)?;
    let mut otherwise = children(parts.pop().expect("else clause"))?;
    if otherwise.len() != 2 {
        return Err(invalid());
    }
    let no = one_element(otherwise.pop().expect("else sequence"))?;
    let else_token = otherwise.pop().expect("else keyword");
    expect_atom(&else_token, "else", "else keyword")?;
    expect_empty_null(
        &parts.pop().expect("else-if clauses"),
        "nested conditionals, not else-if clauses",
    )?;
    let yes = one_element(parts.pop().expect("then sequence"))?;
    let then_token = parts.pop().expect("then keyword");
    expect_atom(&then_token, "then", "then keyword")?;
    let mut condition = node(parts.pop().expect("do condition"), "doIfProp", 2)?;
    let predicate = condition.pop().expect("condition predicate");
    let binding = condition.pop().expect("optional condition binder");
    match expect_null_args(&binding, "condition binder")? {
        [] => {}
        [binder, colon] => {
            expect_atom(colon, ":", "condition binder colon")?;
            if !matches!(binder, Syntax::Ident { val, .. } if !val.is_anonymous() && val.parent().is_anonymous())
                && !matches!(binder, Syntax::Atom { val, .. } if val == "_")
            {
                return Err(invalid());
            }
        }
        _ => return Err(invalid()),
    }
    let if_token = parts.pop().expect("if keyword");
    expect_atom(&if_token, "if", "if keyword")?;
    Ok((
        vec![if_token, binding, predicate, then_token, else_token],
        yes,
        no,
    ))
}

impl Context {
    fn do_control_name(&mut self) -> Result<Syntax, NatDefinitionElabError> {
        let serial = self.next;
        self.fresh_name()?;
        Ok(ident(Name::num(Name::anonymous(), serial)))
    }

    pub(super) fn expand_do_conditional(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        targets: Option<&control::LoopTargets>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task {
            Visit(Syntax),
            Finish(Vec<Syntax>),
        }
        let mut tasks = vec![Task::Visit(syntax)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Finish(mut header) => {
                    let no = values.pop().ok_or_else(invalid)?;
                    let yes = values.pop().ok_or_else(invalid)?;
                    header.insert(4, yes);
                    header.push(no);
                    values.push(term("ifThenElse", header));
                }
                Task::Visit(syntax) => {
                    if syntax.kind() == Some(&parser_kind(&["Term", "doIf"])) {
                        let (header, yes, no) = split(syntax)?;
                        tasks.push(Task::Finish(header));
                        tasks.push(Task::Visit(no));
                        tasks.push(Task::Visit(yes));
                    } else if control::is_jump(&syntax) {
                        let stop = control::jump_kind(syntax)?;
                        values.push(targets.ok_or_else(invalid)?.signal(Some(stop)));
                    } else {
                        let mut parts = node(syntax, "doExpr", 1)?;
                        let action = parts.pop().expect("conditional branch action");
                        values.push(if let Some(targets) = targets {
                            let ignored = self.do_control_name()?;
                            call(
                                true,
                                vec![
                                    action,
                                    lambda(ignored, unit_annotation(), targets.signal(None))?,
                                ],
                            )
                        } else {
                            action
                        });
                    }
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid());
        }
        let conditional = values.pop().expect("one conditional result");
        let Some(suffix) = suffix else {
            // Terminal ordinary do conditionals retain their inferred result.
            // A loop always supplies its normal exit, even for a final if.
            return if targets.is_none() {
                Ok(conditional)
            } else {
                Err(invalid())
            };
        };
        let signal = self.do_control_name()?;
        if targets.is_none() {
            return Ok(call(
                true,
                vec![conditional, lambda(signal, unit_annotation(), suffix)?],
            ));
        }
        let step = self.do_control_name()?;
        let ignored = self.do_control_name()?;
        let alternative = |label: &str, binder: Syntax, body: Syntax| {
            term(
                "matchAlt",
                vec![
                    atom("|"),
                    null(vec![null(vec![term(
                        "app",
                        vec![root(label), null(vec![binder])],
                    )])]),
                    atom("=>"),
                    body,
                ],
            )
        };
        let dispatcher = term(
            "match",
            vec![
                atom("match"),
                null(vec![]),
                null(vec![]),
                null(vec![term("matchDiscr", vec![null(vec![]), signal.clone()])]),
                atom("with"),
                term(
                    "matchAlts",
                    vec![null(vec![
                        alternative("done", step.clone(), call(false, vec![step])),
                        alternative("yield", ignored, suffix),
                    ])],
                ),
            ],
        );
        Ok(call(
            true,
            vec![conditional, lambda(signal, null(vec![]), dispatcher)?],
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn named(s: &str) -> Syntax {
        ident(Name::from_components([s]))
    }
    fn action(s: &str) -> Syntax {
        term("doExpr", vec![named(s)])
    }
    fn sequence(element: Syntax) -> Syntax {
        term(
            "doSeqIndent",
            vec![null(vec![term("doSeqItem", vec![element, null(vec![])])])],
        )
    }
    fn condition(yes: Syntax, no: Syntax) -> Syntax {
        term(
            "doIf",
            vec![
                atom("if"),
                term("doIfProp", vec![null(vec![]), named("test")]),
                atom("then"),
                sequence(yes),
                null(vec![]),
                null(vec![atom("else"), sequence(no)]),
            ],
        )
    }
    fn jump(stop: bool) -> Syntax {
        term(
            if stop { "doBreak" } else { "doContinue" },
            vec![atom(if stop { "break" } else { "continue" })],
        )
    }
    fn normal() -> Syntax {
        call(
            false,
            vec![term(
                "app",
                vec![
                    root("yield"),
                    null(vec![ident(Name::num(Name::anonymous(), 9999))]),
                ],
            )],
        )
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn count(syntax: &Syntax, name: &Name) -> usize {
        let mut pending = vec![syntax];
        let mut found = 0;
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == name => found += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        found
    }
    #[test]
    fn nested_conditions_keep_one_suffix_and_each_original_action_once() {
        let input = condition(
            condition(jump(true), action("left")),
            condition(jump(false), action("right")),
        );
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let result = context()
            .expand_do_conditional(input, Some(named("suffix")), Some(&targets))
            .unwrap();
        for name in ["suffix", "left", "right"] {
            assert_eq!(count(&result, &Name::from_components([name])), 1);
        }
        assert_eq!(count(&result, &Name::from_components(["test"])), 3);
        assert!(
            count(
                &result,
                &Name::from_components(["_root_", "ForInStep", "done"])
            ) >= 3
        );
        assert!(
            count(
                &result,
                &Name::from_components(["_root_", "ForInStep", "yield"])
            ) >= 3
        );
    }
    #[test]
    fn ordinary_terminal_conditionals_keep_their_result_without_loop_signals() {
        let result = context()
            .expand_do_conditional(condition(action("yes"), action("no")), None, None)
            .unwrap();
        assert_eq!(result.kind(), Some(&parser_kind(&["Term", "ifThenElse"])));
        assert_eq!(
            count(
                &result,
                &Name::from_components(["_root_", "ForInStep", "done"])
            ),
            0
        );
        for stop in [false, true] {
            assert!(
                context()
                    .expand_do_conditional(condition(jump(stop), action("unused")), None, None)
                    .is_err()
            );
        }
    }
    #[test]
    fn malformed_conditionals_never_discard_metadata_or_unchecked_branches() {
        for slot in 0..6 {
            let mut input = condition(action("yes"), action("no"));
            let Syntax::Node { args, .. } = &mut input else {
                unreachable!()
            };
            args[slot] = Syntax::Missing;
            assert!(context().expand_do_conditional(input, None, None).is_err());
        }
        let input = condition(
            term("doReturn", vec![atom("return"), null(vec![named("value")])]),
            action("no"),
        );
        assert!(context().expand_do_conditional(input, None, None).is_err());
    }
    #[test]
    fn named_branch_binder_does_not_enclose_the_shared_suffix() {
        let mut input = condition(action("yes"), action("no"));
        let Syntax::Node { args, .. } = &mut input else {
            unreachable!()
        };
        args[1] = term(
            "doIfProp",
            vec![null(vec![named("h"), atom(":")]), named("test")],
        );
        let result = context()
            .expand_do_conditional(input, Some(named("h")), None)
            .unwrap();
        let args = expect_node(
            &result,
            &parser_kind(&["Term", "nativeDoBind"]),
            2,
            "shared suffix",
        )
        .unwrap();
        assert_eq!(count(&args[0], &Name::from_components(["h"])), 1);
        assert_eq!(count(&args[1], &Name::from_components(["h"])), 1);
    }
    #[test]
    fn deep_conditions_use_a_bounded_heap_walk_and_fresh_requests_recover() {
        let mut input = action("leaf");
        for _ in 0..1024 {
            input = condition(input, action("other"));
        }
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 10;
        assert!(matches!(
            stopped.expand_do_conditional(input.clone(), Some(named("suffix")), Some(&targets)),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        let result = context()
            .expand_do_conditional(input, Some(named("suffix")), Some(&targets))
            .unwrap();
        assert_eq!(count(&result, &Name::from_components(["suffix"])), 1);
        assert_eq!(count(&result, &Name::from_components(["test"])), 1024);
    }
}
