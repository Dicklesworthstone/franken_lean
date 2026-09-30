//! `unless` is a conditional branch in the surrounding do/loop scope.
//! Swap the branches, not the predicate's type: Bool and Decidable Prop both
//! keep the existing conditional checker. The shared branch-sequence worklist
//! handles local bindings, nested blocks, exits, and a single continuation.
use super::*;

pub(super) fn expand(syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut parts = node(syntax, "doUnless", 4)?;
    let body = parts.pop().expect("unless body");
    expect_atom(&parts[0], "unless", "unless keyword")?;
    expect_atom(&parts[2], "do", "unless body keyword")?;
    let condition = parts.remove(1);
    let skip = call(
        false,
        vec![ident(Name::from_components(["_root_", "PUnit", "unit"]))],
    );
    let yes = Syntax::node(
        parser_kind(&["Term", "doSeqIndent"]),
        vec![null(vec![Syntax::node(
            parser_kind(&["Term", "doSeqItem"]),
            vec![
                Syntax::node(parser_kind(&["Term", "doExpr"]), vec![skip]),
                null(vec![]),
            ],
        )])],
    );
    Ok(Syntax::node(
        parser_kind(&["Term", "doIf"]),
        vec![
            atom("if"),
            Syntax::node(
                parser_kind(&["Term", "doIfProp"]),
                vec![null(vec![]), condition],
            ),
            atom("then"),
            yes,
            null(vec![]),
            null(vec![atom("else"), body]),
        ],
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", kind]), args)
    }
    fn named(s: &str) -> Syntax {
        ident(Name::from_components([s]))
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
    fn input(body: Syntax) -> Syntax {
        term(
            "doUnless",
            vec![atom("unless"), named("condition"), atom("do"), body],
        )
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
        )
    }
    fn normal() -> Syntax {
        call(
            false,
            vec![term(
                "app",
                vec![
                    ident(Name::from_components(["_root_", "ForInStep", "yield"])),
                    null(vec![ident(Name::num(Name::anonymous(), 99))]),
                ],
            )],
        )
    }
    fn count(syntax: &Syntax, name: &Name) -> usize {
        let mut pending = vec![syntax];
        let mut n = 0;
        while let Some(syntax) = pending.pop() {
            match syntax {
                Syntax::Ident { val, .. } if val == name => n += 1,
                Syntax::Node { args, .. } => pending.extend(args),
                _ => {}
            }
        }
        n
    }
    #[test]
    fn branches_swap_without_changing_or_copying_the_predicate() {
        let body = sequence(vec![term("doExpr", vec![named("action")])]);
        let lowered = expand(input(body.clone())).unwrap();
        let args = expect_node(
            &lowered,
            &parser_kind(&["Term", "doIf"]),
            6,
            "unless conditional",
        )
        .unwrap();
        let otherwise = expect_null_args(&args[5], "else").unwrap();
        assert_eq!(otherwise[1], body);
        assert_eq!(count(&lowered, &Name::from_components(["condition"])), 1);
        assert_eq!(count(&lowered, &Name::from_components(["action"])), 1);
    }
    #[test]
    fn multiple_actions_share_one_suffix_and_forward_loop_exits() {
        let body = sequence(vec![
            term("doExpr", vec![named("first")]),
            term("doExpr", vec![named("second")]),
            term("doContinue", vec![atom("continue")]),
        ]);
        let targets = control::LoopTargets::new(&normal()).unwrap();
        let result = context()
            .expand_do_conditional(
                expand(input(body)).unwrap(),
                Some(named("suffix")),
                Some(&targets),
            )
            .unwrap();
        for name in ["condition", "first", "second", "suffix"] {
            assert_eq!(count(&result, &Name::from_components([name])), 1);
        }
    }
    #[test]
    fn malformed_empty_or_out_of_scope_controls_fail_closed() {
        let good = input(sequence(vec![term("doExpr", vec![named("action")])]));
        for slot in [0, 2] {
            let mut bad = good.clone();
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            args[slot] = Syntax::Missing;
            assert!(expand(bad).is_err());
        }
        for body in [
            sequence(vec![]),
            sequence(vec![term("doBreak", vec![atom("break")])]),
        ] {
            assert!(
                context()
                    .expand_do_conditional(expand(input(body)).unwrap(), None, None)
                    .is_err()
            );
        }
        assert!(context().expand_do_node(good, true).is_err());
    }
    #[test]
    fn expansion_remains_request_budgeted() {
        let input = input(sequence(vec![term("doExpr", vec![named("action")])]));
        // ElabBudget uses zero for unlimited, not for an exhausted budget.
        let mut unlimited = context();
        unlimited.txn.budget.max_heartbeats = 0;
        assert!(unlimited.expand_do_node(input.clone(), false).is_ok());
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(stopped.expand_do_node(input.clone(), false).is_ok());
        assert_eq!(stopped.txn.budget.heartbeats_consumed, 1);
        assert!(matches!(
            stopped.expand_do_node(input.clone(), false),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert!(context().expand_do_node(input, false).is_ok());
    }
}
