//! The pin's `expandDoRepeatUntil`: `repeat (do body); if condition then break`.
//! Keep the explicit nested *element*: it hides body-local bindings from the
//! post-condition without introducing a new return or loop-control scope.
use super::*;

pub(super) fn expand(syntax: Syntax) -> Result<Syntax, NatDefinitionElabError> {
    let mut parts = node(syntax, "doRepeatUntil", 4)?;
    let condition = parts.pop().expect("post-condition");
    expect_atom(&parts[2], "until", "post-condition keyword")?;
    expect_atom(&parts[0], "repeat", "loop keyword")?;
    let body = parts.remove(1);
    let nested = Syntax::node(parser_kind(&["Term", "doNested"]), vec![atom("do"), body]);
    let stop = Syntax::node(
        parser_kind(&["Term", "doIf"]),
        vec![
            atom("if"),
            Syntax::node(
                parser_kind(&["Term", "doIfProp"]),
                vec![null(vec![]), condition],
            ),
            atom("then"),
            sequence(Syntax::node(
                parser_kind(&["Term", "doBreak"]),
                vec![atom("break")],
            )),
            null(vec![]),
            null(vec![]),
        ],
    );
    let body = Syntax::node(
        parser_kind(&["Term", "doSeqIndent"]),
        vec![null(
            [nested, stop]
                .into_iter()
                .map(|element| {
                    Syntax::node(
                        parser_kind(&["Term", "doSeqItem"]),
                        vec![element, null(vec![])],
                    )
                })
                .collect(),
        )],
    );
    Ok(loop_over(body))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn term(label: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", label]), args)
    }
    fn named(label: &str) -> Syntax {
        ident(Name::from_components([label]))
    }
    fn input(body: Syntax, condition: Syntax) -> Syntax {
        term(
            "doRepeatUntil",
            vec![atom("repeat"), body, atom("until"), condition],
        )
    }
    fn context() -> Context {
        Context::new(
            &Environment::new(),
            Budget::for_stack_bytes(2 * 1024 * 1024),
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
    fn body_precedes_the_condition_without_leaking_its_lexical_scope() {
        let body = sequence(term("doExpr", vec![named("action")]));
        let predicate = term("nestedAction", vec![atom("←"), named("condition")]);
        let lowered = expand(input(body.clone(), predicate.clone())).unwrap();
        let loop_args = expect_node(&lowered, &parser_kind(&["Term", "doFor"]), 4, "loop").unwrap();
        let seq = expect_node(
            &loop_args[3],
            &parser_kind(&["Term", "doSeqIndent"]),
            1,
            "sequence",
        )
        .unwrap();
        let items = expect_null_args(&seq[0], "items").unwrap();
        assert_eq!(items.len(), 2);
        let first =
            expect_node(&items[0], &parser_kind(&["Term", "doSeqItem"]), 2, "first").unwrap();
        assert_eq!(first[0], term("doNested", vec![atom("do"), body]));
        let second =
            expect_node(&items[1], &parser_kind(&["Term", "doSeqItem"]), 2, "second").unwrap();
        let conditional =
            expect_node(&second[0], &parser_kind(&["Term", "doIf"]), 6, "condition").unwrap();
        assert_eq!(
            conditional[1],
            term("doIfProp", vec![null(vec![]), predicate])
        );
        assert_eq!(count(&conditional[3], "doBreak"), 1);
        assert!(
            expect_null_args(&conditional[5], "absent else")
                .unwrap()
                .is_empty()
        );
        assert_eq!(count(&lowered, "nestedAction"), 1);
        assert_eq!(count(&lowered, "do"), 0);
    }
    #[test]
    fn exits_remain_inside_the_original_loop_control_scope() {
        for (label, keyword) in [("doContinue", "continue"), ("doBreak", "break")] {
            let body = sequence(term(label, vec![atom(keyword)]));
            let lowered = expand(input(body.clone(), named("condition"))).unwrap();
            assert_eq!(
                count(&lowered, label),
                if label == "doBreak" { 2 } else { 1 }
            );
            assert_eq!(count(&lowered, "doNested"), 1);
            assert_eq!(count(&lowered, "do"), 0);
        }
    }
    #[test]
    fn nested_loops_expand_inner_first_without_leaving_surface_loop_nodes() {
        let mut tree = input(
            sequence(term("doExpr", vec![named("action")])),
            named("inner"),
        );
        for _ in 0..1000 {
            tree = input(sequence(tree), named("outer"));
        }
        let lowered = context().expand_while_loops(&tree).unwrap();
        assert_eq!(count(&lowered, "doFor"), 1001);
        assert_eq!(count(&lowered, "doRepeatUntil"), 0);
        assert_eq!(count(&lowered, "doNested"), 1001);
    }
    #[test]
    fn malformed_delimiters_and_arity_fail_closed() {
        let good = input(
            sequence(term("doExpr", vec![named("action")])),
            named("condition"),
        );
        for slot in [0, 2] {
            let mut bad = good.clone();
            let Syntax::Node { args, .. } = &mut bad else {
                unreachable!()
            };
            args[slot] = atom("wrong");
            assert!(expand(bad).is_err());
        }
        assert!(expand(term("doRepeatUntil", vec![])).is_err());
        assert!(expand(term("doRepeat", vec![atom("repeat"), named("body")])).is_err());
    }
    #[test]
    fn traversal_is_budgeted_and_a_refusal_does_not_mutate_input() {
        let syntax = input(
            sequence(term("doExpr", vec![named("action")])),
            named("condition"),
        );
        let saved = syntax.clone();
        let mut limited = context();
        limited.txn.budget.max_heartbeats = 1;
        assert!(matches!(
            limited.expand_while_loops(&syntax),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::ResourceLimit
            ))
        ));
        assert_eq!(syntax, saved);
        assert!(context().expand_while_loops(&syntax).is_ok());
    }
}
