//! Ordinary-do early returns with checked, lazy, lexically scoped join points.
//!
//! A join stores the remaining source once as a lambda. Each fall-through
//! branch calls it; a returning branch does not. The term worklist checks the
//! suffix in its original context and expected result type, even if no branch
//! will call it. No exception primitive, effect transformer or new axiom is used.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn resume(name: &Syntax) -> Syntax {
    term(
        "app",
        vec![
            name.clone(),
            null(vec![ident(Name::from_components([
                "_root_", "Bool", "false",
            ]))]),
        ],
    )
}
fn skip() -> Syntax {
    call(
        false,
        vec![ident(Name::from_components(["_root_", "PUnit", "unit"]))],
    )
}

pub(in crate::source) fn join_parts(
    args: &[Syntax],
) -> Result<(Name, &Syntax, &Syntax), NatDefinitionElabError> {
    let [Syntax::Ident { val, .. }, suffix, body] = args else {
        return Err(invalid());
    };
    if !val.parent().is_anonymous() || !matches!(val.leaf_view(), fln_core::name::LeafView::Num(_))
    {
        return Err(invalid());
    }
    Ok((val.clone(), suffix, body))
}

struct Block {
    statements: Vec<Syntax>,
    result: Option<Syntax>,
    require_unit: bool,
    terminal: bool,
}
impl Block {
    fn new(
        sequence: Syntax,
        result: Option<Syntax>,
        require_unit: bool,
    ) -> Result<Self, NatDefinitionElabError> {
        let statements = sequence_items(sequence)?;
        if statements.is_empty() {
            return Err(invalid());
        }
        Ok(Self {
            statements,
            result,
            require_unit,
            terminal: true,
        })
    }
}

impl Context {
    /// Inspect only do-element positions. A nested do expression, lambda,
    /// collection callback or let value owns its own scope and is not scanned.
    pub(super) fn has_branch_return(
        &mut self,
        sequence: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![(sequence, false)];
        while let Some((syntax, branch)) = work.pop() {
            self.tick()?;
            let Syntax::Node { kind, args, .. } = syntax else {
                continue;
            };
            if kind == &parser_kind(&["Term", "doReturn"]) && branch {
                return Ok(true);
            }
            if kind == &parser_kind(&["Term", "doIf"]) {
                let parts = expect_node(syntax, kind, 6, "returning conditional")?;
                work.push((&parts[3], true));
                let otherwise = expect_null_args(&parts[5], "optional else")?;
                if let [_, sequence] = otherwise {
                    work.push((sequence, true));
                }
            } else if kind == &parser_kind(&["Term", "doSeqIndent"])
                || kind == &parser_kind(&["Term", "doSeqBracketed"])
                || kind == &Name::from_components(["null"])
            {
                work.extend(args.iter().map(|arg| (arg, branch)));
            } else if kind == &parser_kind(&["Term", "doSeqItem"])
                && let Some(element) = args.first()
            {
                work.push((element, branch));
            }
        }
        Ok(false)
    }

    /// Build one ordinary lambda over the already checked suffix. Bool is a
    /// seed type and the ignored argument carries no information. It avoids
    /// imposing ForInStep, Sum, or even PUnit on a pure early-return program.
    pub(in crate::source) fn do_join_thunk(
        &mut self,
        value: Typed,
        result_type: &Expr,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.constrain_type(&value.type_, result_type)?;
        let domain = self.constant(&Name::from_components(["Bool"]))?;
        self.sort_level(&domain)?;
        let name = self.fresh_name()?;
        Ok(Typed {
            value: Expr::lam(
                name.clone(),
                domain.value.clone(),
                value.value.lift_loose(0, 1).map_err(|_| invalid())?,
                BinderInfo::Default,
            ),
            type_: Expr::forall_e(
                name,
                domain.value,
                result_type.lift_loose(0, 1).map_err(|_| invalid())?,
                BinderInfo::Default,
            ),
        })
    }

    pub(super) fn expand_returning_sequence(
        &mut self,
        sequence: Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task {
            Block(Block),
            Resume(Block),
            Conditional(Syntax, Option<Syntax>, bool),
            Finish(conditional::Header, Option<(Syntax, Syntax)>),
            Value(Syntax),
        }
        let mut work = vec![Task::Block(Block::new(sequence, None, false)?)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            match task {
                Task::Value(value) => values.push(value),
                Task::Block(mut block) => {
                    let Some(statement) = block.statements.pop() else {
                        values.push(block.result.ok_or_else(invalid)?);
                        continue;
                    };
                    let terminal = block.terminal;
                    block.terminal = false;
                    let element = sequence_element(statement)?;
                    if element.kind() == Some(&parser_kind(&["Term", "doIf"])) {
                        let suffix = block.result.take();
                        let require_unit = block.require_unit;
                        work.push(Task::Resume(block));
                        work.push(Task::Conditional(element, suffix, require_unit));
                    } else {
                        if element.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                            // Only an administrative join can be skipped. Source
                            // after an unconditional return still refuses rather
                            // than disappearing before ordinary checking.
                            if !terminal {
                                return Err(invalid());
                            }
                            block.result = None;
                        }
                        let scope = SequenceScope {
                            targets: None,
                            signal: false,
                            require_unit: block.require_unit,
                            allow_return: true,
                        };
                        block.result = Some(self.prepend_do_element(
                            element,
                            block.result,
                            scope,
                            terminal,
                        )?);
                        work.push(Task::Block(block));
                    }
                }
                Task::Resume(mut block) => {
                    block.result = Some(values.pop().ok_or_else(invalid)?);
                    work.push(Task::Block(block));
                }
                Task::Conditional(syntax, suffix, require_unit) => {
                    let branches = conditional::split(syntax)?;
                    let require_unit = require_unit || suffix.is_some();
                    let join = suffix
                        .map(|suffix| Ok((self.do_control_name()?, suffix)))
                        .transpose()?;
                    // Only the constant-size call is copied, never source code.
                    let next = join.as_ref().map(|(name, _)| resume(name));
                    let yes = Block::new(branches.yes, next.clone(), require_unit)?;
                    let no = match branches.no {
                        Some(no) => Task::Block(Block::new(no, next, require_unit)?),
                        None => Task::Value(next.unwrap_or_else(skip)),
                    };
                    work.push(Task::Finish(branches.header, join));
                    work.push(no);
                    work.push(Task::Block(yes));
                }
                Task::Finish(header, join) => {
                    let no = values.pop().ok_or_else(invalid)?;
                    let yes = values.pop().ok_or_else(invalid)?;
                    let body = self.finish_do_condition(header, yes, no)?;
                    values.push(match join {
                        Some((name, suffix)) => term("nativeDoJoin", vec![name, suffix, body]),
                        None => body,
                    });
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid());
        }
        values.pop().ok_or_else(invalid)
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
    fn returning(s: &str) -> Syntax {
        term("doReturn", vec![atom("return"), null(vec![named(s)])])
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
    fn condition(yes: Syntax, no: Option<Syntax>) -> Syntax {
        term(
            "doIf",
            vec![
                atom("if"),
                term("doIfProp", vec![null(vec![]), named("predicate")]),
                atom("then"),
                yes,
                null(vec![]),
                no.map_or_else(|| null(vec![]), |no| null(vec![atom("else"), no])),
            ],
        )
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn count(syntax: &Syntax, name: &str) -> usize {
        let name = Name::from_components([name]);
        let mut count = 0;
        let mut pending = vec![syntax];
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == &name => count += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        count
    }
    #[test]
    fn later_source_is_retained_once_outside_every_branch_binder() {
        let input = sequence(vec![
            condition(sequence(vec![action("prefix"), returning("early")]), None),
            action("suffix"),
        ]);
        let result = context().expand_do_sequence(input, None).unwrap();
        let parts =
            expect_node(&result, &parser_kind(&["Term", "nativeDoJoin"]), 3, "join").unwrap();
        assert_eq!(count(&parts[1], "suffix"), 1);
        assert_eq!(count(&parts[2], "suffix"), 0);
        for name in ["suffix", "prefix", "early", "predicate"] {
            assert_eq!(count(&result, name), 1);
        }
    }
    #[test]
    fn deep_returning_branches_use_one_heap_walk_and_linear_output() {
        let mut nested = condition(sequence(vec![returning("early")]), None);
        for _ in 0..1024 {
            nested = condition(sequence(vec![nested, action("branch_suffix")]), None);
        }
        let result = context()
            .expand_do_sequence(sequence(vec![nested, action("outer_suffix")]), None)
            .unwrap();
        assert_eq!(count(&result, "branch_suffix"), 1024);
        assert_eq!(count(&result, "outer_suffix"), 1);
        assert_eq!(count(&result, "early"), 1);
        let mut pending = vec![&result];
        let mut nodes = 0;
        while let Some(syntax) = pending.pop() {
            nodes += 1;
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        assert!(nodes < 1025 * 64, "nonlinear output: {nodes}");
    }
    #[test]
    fn returns_in_term_scopes_are_not_captured_and_loop_returns_still_refuse() {
        let nested_do = term("do", vec![atom("do"), sequence(vec![returning("inner")])]);
        let input = sequence(vec![term("doExpr", vec![nested_do])]);
        assert!(!context().has_branch_return(&input).unwrap());
        let input = sequence(vec![condition(sequence(vec![returning("outer")]), None)]);
        let exit = call(
            false,
            vec![term(
                "app",
                vec![
                    ident(Name::from_components(["_root_", "ForInStep", "yield"])),
                    null(vec![ident(Name::num(Name::anonymous(), 99))]),
                ],
            )],
        );
        assert!(context().expand_do_sequence(input, Some(exit)).is_err());
    }
    #[test]
    fn forged_joins_bad_returns_and_unreachable_source_are_rejected() {
        for args in [
            vec![],
            vec![named("spellable"), named("suffix"), named("body")],
            vec![
                ident(Name::num(Name::from_components(["qualified"]), 0)),
                named("suffix"),
                named("body"),
            ],
        ] {
            assert!(join_parts(&args).is_err());
        }
        for body in [
            sequence(vec![]),
            sequence(vec![returning("early"), action("unchecked")]),
            sequence(vec![term("doReturn", vec![atom("return"), null(vec![])])]),
        ] {
            let input = sequence(vec![condition(body, None), action("suffix")]);
            assert!(context().expand_do_sequence(input, None).is_err());
        }
    }
    #[test]
    fn exhausted_expansion_publishes_no_partial_tree_and_fresh_context_recovers() {
        let input = sequence(vec![
            condition(sequence(vec![returning("early")]), None),
            action("suffix"),
        ]);
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            stopped.expand_do_sequence(input.clone(), None),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().expand_do_sequence(input, None).is_ok());
    }
}
