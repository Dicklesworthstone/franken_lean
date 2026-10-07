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
    loop_scope: Option<loop_returns::LoopScope>,
    completion: Option<Syntax>,
    nested: bool,
}
impl Block {
    fn new(
        sequence: Syntax,
        result: Option<Syntax>,
        require_unit: bool,
        loop_scope: Option<loop_returns::LoopScope>,
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
            loop_scope,
            completion: None,
            nested: false,
        })
    }
}

impl Context {
    /// Inspect only do-element positions. A nested do expression, lambda,
    /// or let value owns its own scope and is not scanned. Retained returning
    /// loops explicitly request this shared worklist.
    /// General matches also need joins to preserve the expected monad through
    /// the equation-refining match checker, even without explicit returns.
    pub(super) fn needs_scoped_join(
        &mut self,
        sequence: &Syntax,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut work = vec![(sequence, false)];
        while let Some((syntax, branch)) = work.pop() {
            self.tick()?;
            let Syntax::Node { kind, args, .. } = syntax else {
                continue;
            };
            if nested::sequence(syntax).is_some() || kind == &parser_kind(&["Term", "nativeDoTry"])
            {
                return Ok(true);
            }
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
            } else if kind == &parser_kind(&["Term", "nativeDoReturningFor"]) {
                // Only return-carrying loops survive the inside-out walk.
                return Ok(true);
            } else if kind == &parser_kind(&["Term", "doMatch"]) || fallback::is_binding(syntax) {
                // Unlike a Boolean if, a constructor match may refine the
                // discriminant's type and introduce equality evidence. Share
                // its suffix through a checked join so every arm receives the
                // enclosing expected monad before refinement, rather than
                // inferring a standalone monadic action without that context.
                return Ok(true);
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
        self.expand_returning_sequence_at(sequence, None)
    }

    /// An exception region has a normal-completion packet, not a source
    /// statement after its last return. Keep that distinction on the worklist:
    /// returns bypass this continuation, while ordinary actions must finish at
    /// Unit before it is produced.
    pub(super) fn expand_returning_sequence_at(
        &mut self,
        sequence: Syntax,
        normal: Option<Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        enum Task {
            Block(Block),
            Resume(Block),
            FinishException(exceptions::ExceptionRegion, usize),
            Conditional(
                Syntax,
                Option<Syntax>,
                bool,
                Option<loop_returns::LoopScope>,
                Option<Syntax>,
                bool,
            ),
            FinishNested(Option<(Syntax, Syntax)>),
            FinishLoop(Box<loop_returns::LoopBuild>),
            Finish(conditional::Header, usize, Option<(Syntax, Syntax)>, bool),
            Value(Syntax),
        }
        let require_unit = normal.is_some();
        let mut work = vec![Task::Block(Block::new(
            sequence,
            normal,
            require_unit,
            None,
        )?)];
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
                    if element.kind() == Some(&parser_kind(&["Term", "nativeDoTry"]))
                        && block.result.is_none()
                        && block.loop_scope.is_none()
                    {
                        // A value-bearing nested completion needs a separate
                        // normal payload as well as the return packet. Never
                        // discard that continuation or invoke it inside try.
                        if !terminal || block.completion.is_some() {
                            return Err(invalid());
                        }
                        let mut parts = node(element, "nativeDoTry", 2)?;
                        expect_atom(&parts[1], "returning", "retained exception control")?;
                        let (region, sequences) = self.split_exception_region(parts.remove(0))?;
                        work.push(Task::Resume(block));
                        work.push(Task::FinishException(region, values.len()));
                        for sequence in sequences.into_iter().rev() {
                            self.tick()?;
                            work.push(Task::Block(Block::new(sequence, None, false, None)?));
                        }
                        continue;
                    }
                    if nested::sequence(&element).is_some() {
                        let scope = SequenceScope {
                            targets: block.loop_scope.as_ref().map(|scope| &scope.targets),
                            signal: false,
                            require_unit: block.require_unit,
                            allow_return: true,
                        };
                        let nested = self.prepare_nested_do(
                            element,
                            block.result.take(),
                            block.completion.clone(),
                            scope,
                        )?;
                        let mut inner =
                            Block::new(nested.sequence, None, false, block.loop_scope.clone())?;
                        inner.completion = nested.completion;
                        inner.nested = true;
                        work.push(Task::Resume(block));
                        work.push(Task::FinishNested(nested.join));
                        work.push(Task::Block(inner));
                    } else if element.kind()
                        == Some(&parser_kind(&["Term", "nativeDoReturningFor"]))
                    {
                        if block.result.is_none()
                            && let Some(completion) = &block.completion
                        {
                            block.result = Some(nested::complete(skip(), completion.clone()));
                        }
                        let mut element = node(element, "nativeDoReturningFor", 1)?;
                        let (build, sequence, scope, normal) = self.prepare_returning_loop(
                            element.pop().expect("retained loop"),
                            block.result.take(),
                            block.loop_scope.as_ref(),
                        )?;
                        work.push(Task::Resume(block));
                        work.push(Task::FinishLoop(Box::new(build)));
                        work.push(Task::Block(Block::new(
                            sequence,
                            Some(normal),
                            true,
                            Some(scope),
                        )?));
                    } else if conditional::is_compound(&element) {
                        let suffix = block.result.take();
                        let require_unit = block.require_unit;
                        let loop_scope = block.loop_scope.clone();
                        let completion =
                            suffix.is_none().then(|| block.completion.clone()).flatten();
                        let nested = block.nested;
                        work.push(Task::Resume(block));
                        work.push(Task::Conditional(
                            element,
                            suffix,
                            require_unit,
                            loop_scope,
                            completion,
                            nested,
                        ));
                    } else {
                        if element.kind() == Some(&parser_kind(&["Term", "doReturn"])) {
                            // Only an administrative join can be skipped. Source
                            // after an unconditional return still refuses rather
                            // than disappearing before ordinary checking.
                            if !terminal {
                                return Err(invalid());
                            }
                            if block.loop_scope.is_some() {
                                block.result = Some(self.expand_loop_return(element)?);
                                work.push(Task::Block(block));
                                continue;
                            }
                            block.result = None;
                        }
                        let scope = SequenceScope {
                            targets: block.loop_scope.as_ref().map(|scope| &scope.targets),
                            signal: false,
                            require_unit: block.require_unit,
                            allow_return: true,
                        };
                        let completes = terminal
                            && block.result.is_none()
                            && element.kind() == Some(&parser_kind(&["Term", "doExpr"]));
                        let value =
                            self.prepend_do_element(element, block.result, scope, terminal)?;
                        block.result = Some(if completes {
                            match &block.completion {
                                Some(completion) => nested::complete(value, completion.clone()),
                                None => value,
                            }
                        } else {
                            value
                        });
                        work.push(Task::Block(block));
                    }
                }
                Task::Resume(mut block) => {
                    block.result = Some(values.pop().ok_or_else(invalid)?);
                    work.push(Task::Block(block));
                }
                Task::FinishNested(join) => {
                    let body = values.pop().ok_or_else(invalid)?;
                    values.push(match join {
                        Some((name, continuation)) if self.do_syntax_uses(&body, &name)? => {
                            term("nativeDoBindJoin", vec![name, continuation, body])
                        }
                        Some((_, continuation)) => match nested::bind_join_domain(&continuation)? {
                            // The binder belongs to the reachable declaration,
                            // even when the continuation body is dead. Check its
                            // explicit type without imposing it on early returns.
                            Some(annotation) => {
                                term("nativeDoNestedAnnotation", vec![annotation.clone(), body])
                            }
                            None => body,
                        },
                        _ => body,
                    });
                }
                Task::FinishException(region, start) => {
                    let bodies = values.split_off(start);
                    values.push(self.finish_exception_region(region, bodies)?);
                }
                Task::FinishLoop(build) => {
                    let body = values.pop().ok_or_else(invalid)?;
                    values.push(self.finish_returning_loop(*build, body)?);
                }
                Task::Conditional(syntax, suffix, require_unit, loop_scope, completion, nested) => {
                    let branches = conditional::split(self, syntax)?;
                    let require_unit = require_unit || suffix.is_some();
                    let join = suffix
                        .map(|suffix| Ok((self.do_control_name()?, suffix)))
                        .transpose()?;
                    // Only the constant-size call is copied, never source code.
                    let next = join.as_ref().map(|(name, _)| resume(name));
                    work.push(Task::Finish(branches.header, values.len(), join, nested));
                    for arm in branches.arms.into_iter().rev() {
                        self.tick()?;
                        work.push(match arm {
                            Some(sequence) => {
                                let mut block = Block::new(
                                    sequence,
                                    next.clone(),
                                    require_unit,
                                    loop_scope.clone(),
                                )?;
                                block.completion = completion.clone();
                                block.nested = nested;
                                Task::Block(block)
                            }
                            None => {
                                Task::Value(next.clone().unwrap_or_else(|| match &completion {
                                    Some(completion) => {
                                        nested::complete(skip(), completion.clone())
                                    }
                                    None => skip(),
                                }))
                            }
                        });
                    }
                }
                Task::Finish(header, start, join, nested) => {
                    let bodies = values.split_off(start);
                    let body = self.finish_do_condition(header, bodies)?;
                    values.push(match join {
                        Some((name, suffix)) if !nested || self.do_syntax_uses(&body, &name)? => {
                            term("nativeDoJoin", vec![name, suffix, body])
                        }
                        Some(_) => body,
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
        assert!(!context().needs_scoped_join(&input).unwrap());
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
