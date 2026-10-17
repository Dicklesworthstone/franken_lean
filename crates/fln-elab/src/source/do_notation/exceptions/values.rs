//! Carry a value continuation through cleanup without executing it in the
//! protected dynamic scope. Normal values and returns become ordinary checked
//! Sum values. The action and return payload are evaluated before cleanup; only
//! the continuation is delayed. No new instance or trust primitive is needed.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn root(parts: &[&str]) -> Syntax {
    ident(Name::from_components(
        std::iter::once("_root_").chain(parts.iter().copied()),
    ))
}
fn apply(function: Syntax, argument: Syntax) -> Syntax {
    term("app", vec![function, null(vec![argument])])
}
fn continuation_type(join: &Syntax, slot: &str) -> Syntax {
    term("nativeDoContinuationType", vec![join.clone(), atom(slot)])
}
fn packet(join: &Syntax, normal: bool, value: Syntax) -> Syntax {
    let parameter = |name, slot| {
        term(
            "namedArgument",
            vec![
                atom("("),
                ident(Name::from_components([name])),
                atom(":="),
                continuation_type(join, slot),
                atom(")"),
            ],
        )
    };
    term(
        "app",
        vec![
            root(&["Sum", if normal { "inl" } else { "inr" }]),
            null(vec![
                parameter("α", "domain"),
                parameter("β", "carrier"),
                value,
            ]),
        ],
    )
}

pub(in crate::source::do_notation) struct ValueRegion {
    region: ExceptionRegion,
    pub(in crate::source::do_notation) normal: Syntax,
    pub(in crate::source::do_notation) resume: Syntax,
    pub(in crate::source::do_notation) cleanup: bool,
    outside: Option<(Syntax, Syntax)>,
}

impl Context {
    /// Read the checked join's original telescope before monad alias reduction.
    /// This is only an explicit Sum type argument: the ordinary application
    /// checker still checks the declaration, parameter domain and result type.
    pub(in crate::source) fn do_exception_type_argument(
        &mut self,
        function: &Typed,
        parameter: &Name,
        syntax: &Syntax,
    ) -> Result<Typed, NatDefinitionElabError> {
        self.tick()?;
        let parts = expect_node(
            syntax,
            &parser_kind(&["Term", "nativeDoContinuationType"]),
            2,
            "exception result type",
        )?;
        let [
            Syntax::Ident { val: name, .. },
            Syntax::Atom { val: slot, .. },
        ] = parts
        else {
            return Err(invalid());
        };
        let mut head = &function.value;
        while let ExprNode::App { f, .. } = head.node() {
            self.tick()?;
            head = f;
        }
        if !matches!(head.node(), ExprNode::Const { name, .. }
            if name == &Name::from_components(["Sum", "inl"]) || name == &Name::from_components(["Sum", "inr"]))
            || !name.parent().is_anonymous()
            || !matches!(name.leaf_view(), fln_core::name::LeafView::Num(_))
        {
            return Err(invalid());
        }
        let local = self.txn.lctx.find_by_user_name(name).ok_or_else(invalid)?;
        let type_ = self.instantiate(&local.type_.clone())?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = type_.node()
        else {
            return Err(invalid());
        };
        if body.has_loose_bvars() {
            return Err(invalid());
        }
        let value = match slot.as_str() {
            "domain" if parameter == &Name::from_components(["α"]) => binder_type.clone(),
            "carrier" if parameter == &Name::from_components(["β"]) => {
                let ExprNode::App { a, .. } = body.node() else {
                    return Err(invalid());
                };
                a.clone()
            }
            _ => return Err(invalid()),
        };
        let type_ = self.known_type(&value)?.ok_or_else(invalid)?;
        Ok(Typed { value, type_ })
    }

    pub(in crate::source::do_notation) fn prepare_value_exception(
        &mut self,
        syntax: Syntax,
        suffix: Option<Syntax>,
        completion: Option<Syntax>,
    ) -> Result<(ValueRegion, Vec<Syntax>), NatDefinitionElabError> {
        self.tick()?;
        let mut parts = node(syntax, "nativeDoTry", 2)?;
        expect_atom(&parts[1], "returning", "retained exception control")?;
        let (region, sequences) = self.split_exception_region(parts.remove(0))?;
        let (resume, outside) = match suffix {
            Some(suffix) => {
                let resume = self.do_control_name()?;
                let ignored = self.do_control_name()?;
                let continuation = lambda(ignored, unit_annotation(), suffix)?;
                (resume.clone(), Some((resume, continuation)))
            }
            None => (completion.ok_or_else(invalid)?, None),
        };
        Ok((
            ValueRegion {
                cleanup: region.finally,
                region,
                normal: self.do_control_name()?,
                resume,
                outside,
            },
            sequences,
        ))
    }

    /// Construct the return packet at the original return site, so the payload
    /// is evaluated before cleanup, not deferred to the outside continuation.
    pub(in crate::source::do_notation) fn exception_return_packet(
        &mut self,
        value: Syntax,
        resume: &Syntax,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        Ok(packet(resume, false, value))
    }

    pub(in crate::source::do_notation) fn finish_value_exception(
        &mut self,
        build: ValueRegion,
        bodies: Vec<Syntax>,
    ) -> Result<Syntax, NatDefinitionElabError> {
        self.tick()?;
        let action = self.finish_exception_region(build.region, bodies)?;
        let value = self.do_control_name()?;
        let normal = lambda(
            value.clone(),
            null(vec![]),
            call(false, vec![packet(&build.resume, true, value)]),
        )?;
        let action = term("nativeDoBindJoin", vec![build.normal, normal, action]);
        let outcome = self.do_control_name()?;
        let value = self.do_control_name()?;
        let returned = self.do_control_name()?;
        let alternative = |tag, binder, body| {
            term(
                "matchAlt",
                vec![
                    atom("|"),
                    null(vec![null(vec![apply(root(&["Sum", tag]), binder)])]),
                    atom("=>"),
                    body,
                ],
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
                        alternative("inl", value.clone(), apply(build.resume.clone(), value)),
                        alternative("inr", returned.clone(), call(false, vec![returned])),
                    ])],
                ),
            ],
        );
        let dispatch = self.lower_do_pattern_match(dispatch)?;
        let dispatch = lambda(outcome, null(vec![]), dispatch)?;
        let body = call(true, vec![action, dispatch]);
        Ok(match build.outside {
            Some((name, continuation)) => term("nativeDoBindJoin", vec![name, continuation, body]),
            None => body,
        })
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
    fn named(name: &str) -> Syntax {
        ident(Name::from_components([name]))
    }
    fn constructor() -> Typed {
        Typed {
            value: Expr::const_(Name::from_components(["Sum", "inr"]), vec![]),
            type_: Expr::sort(Level::one()),
        }
    }
    fn local(context: &mut Context, result: Expr) -> Syntax {
        let name = Name::num(Name::anonymous(), 900);
        context.txn.lctx.add_param(
            FVarId(Name::from_components(["join-id"])),
            name.clone(),
            Expr::forall_e(
                Name::anonymous(),
                Expr::sort(Level::zero()),
                result,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        ident(name)
    }
    fn result() -> Expr {
        Expr::app(
            Expr::const_(Name::from_components(["M"]), vec![]),
            Expr::sort(Level::one()),
        )
    }
    #[test]
    fn packet_parameters_come_from_the_original_checked_join_telescope() {
        let mut ctx = context();
        let name = local(&mut ctx, result());
        for (parameter, slot, expected) in [
            ("α", "domain", Expr::sort(Level::zero())),
            ("β", "carrier", Expr::sort(Level::one())),
        ] {
            let value = ctx
                .do_exception_type_argument(
                    &constructor(),
                    &Name::from_components([parameter]),
                    &continuation_type(&name, slot),
                )
                .unwrap();
            assert_eq!(value.value, expected);
        }
        let mut stopped = context();
        let name = local(&mut stopped, result());
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            stopped.do_exception_type_argument(
                &constructor(),
                &Name::from_components(["β"]),
                &continuation_type(&name, "carrier")
            ),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
    }
    #[test]
    fn forged_packet_type_hints_and_dependent_results_are_refused() {
        let mut ctx = context();
        let name = local(&mut ctx, result());
        for marker in [
            term("nativeDoContinuationType", vec![]),
            continuation_type(&named("spellable"), "carrier"),
            continuation_type(
                &ident(Name::num(Name::from_components(["qualified"]), 1)),
                "carrier",
            ),
            continuation_type(&ident(Name::num(Name::anonymous(), 901)), "carrier"),
            continuation_type(&name, "unknown"),
            continuation_type(&name, "domain"),
            term(
                "nativeDoContinuationType",
                vec![name.clone(), atom("carrier"), named("hidden")],
            ),
        ] {
            assert!(
                ctx.do_exception_type_argument(
                    &constructor(),
                    &Name::from_components(["β"]),
                    &marker
                )
                .is_err()
            );
        }
        let foreign = Typed {
            value: Expr::const_(Name::from_components(["Other", "inr"]), vec![]),
            ..constructor()
        };
        assert!(
            ctx.do_exception_type_argument(
                &foreign,
                &Name::from_components(["β"]),
                &continuation_type(&name, "carrier")
            )
            .is_err()
        );
        for body in [Expr::bvar(0).unwrap(), Expr::sort(Level::one())] {
            let mut ctx = context();
            let name = local(&mut ctx, body);
            assert!(
                ctx.do_exception_type_argument(
                    &constructor(),
                    &Name::from_components(["β"]),
                    &continuation_type(&name, "carrier")
                )
                .is_err()
            );
        }
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
    fn action(label: &str) -> Syntax {
        term("doExpr", vec![named(label)])
    }
    fn binding(body: Syntax) -> Syntax {
        let region = term(
            "nativeDoTry",
            vec![
                term(
                    "doTry",
                    vec![
                        atom("try"),
                        body,
                        null(vec![]),
                        null(vec![term(
                            "doFinally",
                            vec![atom("finally"), sequence(vec![action("cleanup")])],
                        )]),
                    ],
                ),
                atom("returning"),
            ],
        );
        term(
            "doLetArrow",
            vec![
                atom("let"),
                null(vec![]),
                term("letConfig", vec![null(vec![])]),
                term(
                    "doIdDecl",
                    vec![
                        named("value"),
                        null(vec![]),
                        atom("←"),
                        term("doNested", vec![atom("do"), sequence(vec![region])]),
                    ],
                ),
            ],
        )
    }
    fn count(syntax: &Syntax, label: &str) -> usize {
        let mut work = vec![syntax];
        let wanted = Name::from_components([label]);
        let mut total = 0;
        while let Some(syntax) = work.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == &wanted => total += 1,
                Syntax::Node { args, .. } => work.extend(args),
                _ => {}
            }
        }
        total
    }
    #[test]
    fn value_exception_nesting_is_heap_driven_and_preserves_each_source_once() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let mut body = sequence(vec![term(
                    "doReturn",
                    vec![atom("return"), null(vec![named("payload")])],
                )]);
                for _ in 0..128 {
                    body = sequence(vec![binding(body), action("normal")]);
                }
                let input = sequence(vec![binding(body), action("outside")]);
                let mut stopped = context();
                stopped.txn.budget.max_heartbeats = 10;
                assert!(matches!(
                    stopped.expand_returning_sequence(input.clone()),
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ResourceLimit
                    ))
                ));
                let output = context().expand_returning_sequence(input).unwrap();
                assert_eq!(count(&output, "payload"), 1);
                assert_eq!(count(&output, "cleanup"), 129);
                assert_eq!(count(&output, "outside"), 1);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
