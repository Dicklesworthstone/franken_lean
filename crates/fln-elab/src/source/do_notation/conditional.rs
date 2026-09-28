//! Branch sequences and their joins on one budgeted heap worklist.
//!
//! Loop branches distinguish fall-through from break/continue using the same
//! checked ForInStep signal at every nesting depth. A join retains each source
//! suffix once, outside the branch's local variables and proposition binders.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn root(label: &str) -> Syntax {
    ident(Name::from_components(["_root_", "ForInStep", label]))
}
fn skip() -> Syntax {
    call(false, vec![ident(Name::from_components(["_root_", "PUnit", "unit"]))])
}

pub(super) enum Header {
    Proposition(Vec<Syntax>),
    Pattern {
        operands: Box<(Syntax, Syntax)>,
        monadic: bool,
    },
}

impl Context {
    pub(super) fn finish_do_condition(
        &mut self,
        header: Header,
        yes: Syntax,
        no: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        match header {
            Header::Proposition(mut header) => {
                header.insert(4, yes);
                header.push(no);
                Ok(term("ifThenElse", header))
            }
            Header::Pattern { operands, monadic } => {
                let (pattern, value) = *operands;
                self.expand_do_pattern_condition(pattern, value, monadic, yes, no)
            }
        }
    }
}

pub(super) struct Branches {
    pub(super) header: Header,
    pub(super) yes: Syntax,
    pub(super) no: Option<Syntax>,
}

/// Validate every structural slot. An absent else means skip; an explicit
/// empty or malformed sequence is not an absent else. Else-if list support
/// remains separate, so no unrecognized clause can be silently dropped.
pub(super) fn split(syntax: Syntax) -> Result<Branches, NatDefinitionElabError> {
    let mut parts = node(syntax, "doIf", 6)?;
    let mut otherwise = children(parts.pop().expect("else clause"))?;
    let (else_token, no) = match otherwise.len() {
        0 => (atom("else"), None),
        2 => {
            let sequence = otherwise.pop().expect("else sequence");
            let keyword = otherwise.pop().expect("else keyword");
            expect_atom(&keyword, "else", "else keyword")?;
            (keyword, Some(sequence))
        }
        _ => return Err(invalid()),
    };
    expect_empty_null(
        &parts.pop().expect("else-if clauses"),
        "nested conditionals, not else-if clauses",
    )?;
    let yes = parts.pop().expect("then sequence");
    let then_token = parts.pop().expect("then keyword");
    expect_atom(&then_token, "then", "then keyword")?;
    let condition = parts.pop().expect("do condition");
    let if_token = parts.pop().expect("if keyword");
    expect_atom(&if_token, "if", "if keyword")?;
    let header = if condition.kind() == Some(&parser_kind(&["Term", "doIfLet"])) {
        let (pattern, value, monadic) = if_let::parts(condition)?;
        Header::Pattern {
            operands: Box::new((pattern, value)),
            monadic,
        }
    } else {
        let mut condition = node(condition, "doIfProp", 2)?;
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
        Header::Proposition(vec![if_token, binding, predicate, then_token, else_token])
    };
    Ok(Branches { header, yes, no })
}

struct Block<'a> {
    statements: Vec<Syntax>,
    result: Option<Syntax>,
    scope: SequenceScope<'a>,
    terminal: bool,
}
impl<'a> Block<'a> {
    fn new(sequence: Syntax, scope: SequenceScope<'a>) -> Result<Self, NatDefinitionElabError> {
        let statements = sequence_items(sequence)?;
        if statements.is_empty() {
            return Err(invalid());
        }
        Ok(Self {
            statements,
            result: scope.targets.map(|targets| targets.signal(None)),
            scope,
            terminal: true,
        })
    }
}

impl Context {
    pub(super) fn expand_do_conditional(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        targets: Option<&control::LoopTargets>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task<'a> {
            Conditional(Syntax, Option<Syntax>, SequenceScope<'a>),
            Finish(Header, Option<Syntax>, SequenceScope<'a>),
            Block(Block<'a>),
            Resume(Block<'a>),
            Value(Syntax),
        }
        if targets.is_some() && suffix.is_none() {
            return Err(invalid());
        }
        let scope = SequenceScope {
            targets,
            signal: false,
            require_unit: targets.is_some(),
            allow_return: targets.is_none() && suffix.is_none(),
        };
        let mut tasks = vec![Task::Conditional(syntax, suffix, scope)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.tick()?;
            match task {
                Task::Value(value) => values.push(value),
                Task::Conditional(syntax, suffix, scope) => {
                    let branches = split(syntax)?;
                    let branch_scope = SequenceScope {
                        targets: scope.targets,
                        signal: scope.targets.is_some(),
                        require_unit: scope.require_unit || suffix.is_some(),
                        allow_return: scope.allow_return && suffix.is_none(),
                    };
                    let yes = Block::new(branches.yes, branch_scope)?;
                    let no = match branches.no {
                        Some(no) => Task::Block(Block::new(no, branch_scope)?),
                        None => Task::Value(match scope.targets {
                            Some(targets) => targets.signal(None),
                            None => skip(),
                        }),
                    };
                    tasks.push(Task::Finish(branches.header, suffix, scope));
                    tasks.push(no);
                    tasks.push(Task::Block(yes));
                }
                Task::Block(mut block) => {
                    let Some(statement) = block.statements.pop() else {
                        values.push(block.result.ok_or_else(invalid)?);
                        continue;
                    };
                    let terminal = block.terminal;
                    block.terminal = false;
                    let element = sequence_element(statement)?;
                    if element.kind() == Some(&parser_kind(&["Term", "doIf"])) {
                        // A terminal nested conditional already returns the
                        // same signal as its enclosing branch. Do not append
                        // an administrative bind that just forwards that signal.
                        let suffix = if terminal && block.scope.signal {
                            None
                        } else {
                            block.result.take()
                        };
                        let scope = block.scope;
                        tasks.push(Task::Resume(block));
                        tasks.push(Task::Conditional(element, suffix, scope));
                    } else {
                        block.result = Some(self.prepend_do_element(
                            element,
                            block.result,
                            block.scope,
                            terminal,
                        )?);
                        tasks.push(Task::Block(block));
                    }
                }
                Task::Resume(mut block) => {
                    block.result = Some(values.pop().ok_or_else(invalid)?);
                    tasks.push(Task::Block(block));
                }
                Task::Finish(header, suffix, scope) => {
                    let no = values.pop().ok_or_else(invalid)?;
                    let yes = values.pop().ok_or_else(invalid)?;
                    let conditional = self.finish_do_condition(header, yes, no)?;
                    values.push(self.join_do_conditional(conditional, suffix, scope)?);
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid());
        }
        values.pop().ok_or_else(invalid)
    }

    fn join_do_conditional(
        &mut self,
        conditional: Syntax,
        suffix: Option<Syntax>,
        scope: SequenceScope<'_>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        let Some(suffix) = suffix else {
            return Ok(conditional);
        };
        let signal = self.do_control_name()?;
        if scope.targets.is_none() {
            return Ok(call(
                true,
                vec![conditional, lambda(signal, unit_annotation(), suffix)?],
            ));
        }
        let step = self.do_control_name()?;
        let ignored = self.do_control_name()?;
        // A nested join must forward the WHOLE signal. Unwrapping here would
        // turn a continue into fall-through and run the enclosing suffix.
        let exit = if scope.signal {
            call(false, vec![signal.clone()])
        } else {
            call(false, vec![step.clone()])
        };
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
                        alternative("done", step, exit),
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
        assert!(
            context()
                .expand_do_conditional(input, Some(named("outer_suffix")), None)
                .is_err()
        );
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

    fn block(elements: Vec<Syntax>, bracketed: bool) -> Syntax {
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

    fn branch_blocks(yes: Syntax, no: Option<Syntax>) -> Syntax {
        term(
            "doIf",
            vec![
                atom("if"),
                term("doIfProp", vec![null(vec![]), named("test")]),
                atom("then"),
                yes,
                null(vec![]),
                no.map_or_else(|| null(vec![]), |no| null(vec![atom("else"), no])),
            ],
        )
    }

    fn binding(name: &str, value: &str, monadic: bool) -> Syntax {
        let config = term("letConfig", vec![null(vec![])]);
        if monadic {
            term(
                "doLetArrow",
                vec![
                    atom("let"),
                    null(vec![]),
                    config,
                    term(
                        "doIdDecl",
                        vec![named(name), null(vec![]), atom("←"), action(value)],
                    ),
                ],
            )
        } else {
            term(
                "doLet",
                vec![
                    atom("let"),
                    null(vec![]),
                    config,
                    term(
                        "letDecl",
                        vec![term(
                            "letIdDecl",
                            vec![
                                term("letId", vec![named(name)]),
                                null(vec![]),
                                null(vec![]),
                                atom(":="),
                                named(value),
                            ],
                        )],
                    ),
                ],
            )
        }
    }

    #[test]
    fn branch_blocks_retain_pure_lets_binds_actions_and_the_shared_suffix_once() {
        for bracketed in [false, true] {
            let input = branch_blocks(
                block(
                    vec![
                        binding("local", "initializer", false),
                        binding("bound", "read_action", true),
                        action("first"),
                        action("second"),
                    ],
                    bracketed,
                ),
                Some(block(vec![action("other")], bracketed)),
            );
            let targets = control::LoopTargets::new(&normal()).unwrap();
            let output = context()
                .expand_do_conditional(input, Some(named("shared_suffix")), Some(&targets))
                .unwrap();
            for name in ["initializer", "read_action", "first", "second", "other", "shared_suffix"] {
                assert_eq!(count(&output, &Name::from_components([name])), 1, "{name}");
            }
            let parts = expect_node(
                &output,
                &parser_kind(&["Term", "nativeDoBind"]),
                2,
                "outer join",
            )
            .unwrap();
            assert_eq!(count(&parts[1], &Name::from_components(["local"])), 0);
            assert_eq!(count(&parts[1], &Name::from_components(["bound"])), 0);
            assert_eq!(count(&parts[1], &Name::from_components(["shared_suffix"])), 1);
        }
    }

    #[test]
    fn absent_else_is_skip_but_explicit_empty_sequences_are_refused() {
        let output = context()
            .expand_do_conditional(branch_blocks(block(vec![action("yes")], false), None), None, None)
            .unwrap();
        let parts = expect_node(&output, &parser_kind(&["Term", "ifThenElse"]), 7, "conditional").unwrap();
        assert_eq!(parts[6], skip());
        for bracketed in [false, true] {
            for input in [
                branch_blocks(block(vec![], bracketed), None),
                branch_blocks(block(vec![action("yes")], bracketed), Some(block(vec![], bracketed))),
            ] {
                assert!(context().expand_do_conditional(input, None, None).is_err());
            }
        }
    }

    #[test]
    fn absent_else_in_a_loop_has_a_normal_signal_not_a_loop_exit() {
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let output = context()
            .expand_do_conditional(
                branch_blocks(block(vec![jump(true)], false), None),
                Some(named("suffix")),
                Some(&targets),
            )
            .unwrap();
        let join = expect_node(&output, &parser_kind(&["Term", "nativeDoBind"]), 2, "join").unwrap();
        let condition = expect_node(&join[0], &parser_kind(&["Term", "ifThenElse"]), 7, "conditional").unwrap();
        assert_eq!(condition[4], targets.signal(Some(true)));
        assert_eq!(condition[6], targets.signal(None));
        assert_eq!(count(&output, &Name::from_components(["suffix"])), 1);
    }

    #[test]
    fn nested_nonterminal_conditional_forwards_the_whole_control_signal() {
        let input = branch_blocks(
            block(vec![condition(jump(true), jump(false)), action("inner_suffix")], false),
            Some(block(vec![action("other")], false)),
        );
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let output = context()
            .expand_do_conditional(input, Some(named("outer_suffix")), Some(&targets))
            .unwrap();
        let mut pending = vec![&output];
        let mut forwarded = 0;
        let mut unwrapped = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                pending.extend(args);
                if kind != &parser_kind(&["Term", "nativeDoBind"]) {
                    continue;
                }
                let lambda = expect_node(&args[1], &parser_kind(&["Term", "fun"]), 2, "join lambda").unwrap();
                let basic = expect_node(&lambda[1], &parser_kind(&["Term", "basicFun"]), 4, "join body").unwrap();
                if basic[3].kind() != Some(&parser_kind(&["Term", "match"])) {
                    continue;
                }
                let [signal] = expect_null_args(&basic[0], "signal binder").unwrap() else {
                    panic!("one generated join binder");
                };
                let dispatch = expect_node(&basic[3], &parser_kind(&["Term", "match"]), 6, "dispatcher").unwrap();
                let alternatives = expect_node(&dispatch[5], &parser_kind(&["Term", "matchAlts"]), 1, "alternatives").unwrap();
                let alternatives = expect_null_args(&alternatives[0], "alternatives").unwrap();
                let done = expect_node(&alternatives[0], &parser_kind(&["Term", "matchAlt"]), 4, "done branch").unwrap();
                let pure = expect_node(&done[3], &parser_kind(&["Term", "nativeDoPure"]), 1, "forwarded value").unwrap();
                if &pure[0] == signal {
                    forwarded += 1;
                } else {
                    unwrapped += 1;
                }
            }
        }
        assert_eq!((forwarded, unwrapped), (1, 1));
        for name in ["inner_suffix", "outer_suffix", "other"] {
            assert_eq!(count(&output, &Name::from_components([name])), 1);
        }
    }

    #[test]
    fn branch_returns_need_the_outer_return_scope_and_no_pending_source_suffix() {
        let returning = || term("doReturn", vec![atom("return"), null(vec![named("value")])]);
        let input = || branch_blocks(
            block(vec![binding("local", "initializer", false), returning()], false),
            Some(block(vec![action("other")], false)),
        );
        assert!(context().expand_do_conditional(input(), None, None).is_ok());
        assert!(context().expand_do_conditional(input(), Some(named("outer_suffix")), None).is_err());
        let targets = control::LoopTargets::new(&normal()).unwrap();
        assert!(context().expand_do_conditional(input(), Some(normal()), Some(&targets)).is_err());
        let nested = condition(input(), action("other"));
        assert!(context().expand_do_conditional(nested, Some(named("outer_suffix")), None).is_err());
    }

    #[test]
    fn unconditional_exits_never_drop_a_source_suffix_inside_a_branch() {
        let targets = control::LoopTargets::new(&normal()).unwrap();
        for stop in [false, true] {
            let input = branch_blocks(
                block(vec![jump(stop), action("unreachable")], false),
                Some(block(vec![action("other")], false)),
            );
            assert!(context().expand_do_conditional(input, Some(normal()), Some(&targets)).is_err());
        }
        let malformed = term("doSeqIndent", vec![null(vec![term(
            "doSeqItem", vec![action("yes"), null(vec![named("hidden")])],
        )])]);
        assert!(context().expand_do_conditional(branch_blocks(malformed, None), None, None).is_err());
    }

    #[test]
    fn nested_block_size_is_linear_and_budget_exhaustion_is_recoverable() {
        let mut body = action("leaf");
        for _ in 0..512 {
            body = branch_blocks(
                block(vec![body, action("suffix")], false),
                Some(block(vec![action("other")], false)),
            );
        }
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 10;
        assert!(matches!(
            stopped.expand_do_conditional(body.clone(), Some(normal()), Some(&targets)),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
        ));
        let output = context().expand_do_conditional(body, Some(normal()), Some(&targets)).unwrap();
        assert_eq!(count(&output, &Name::from_components(["test"])), 512);
        assert_eq!(count(&output, &Name::from_components(["suffix"])), 512);
        assert_eq!(count(&output, &Name::from_components(["other"])), 512);
        assert_eq!(count(&output, &Name::from_components(["leaf"])), 1);
        let mut pending = vec![&output];
        let mut size = 0;
        while let Some(syntax) = pending.pop() {
            size += 1;
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        assert!(size < 512 * 150, "unexpected continuation multiplication: {size}");
    }
}
