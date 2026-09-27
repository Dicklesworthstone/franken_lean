//! Dependent callbacks are syntax only: all proof domains come from ForIn'.
use super::*;

fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::node(parser_kind(&["Term", kind]), args)
}
fn named(name: &str) -> Syntax {
    ident(Name::from_components([name]))
}
fn context() -> Context {
    Context::new(&Environment::new(), Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn loop_(witness: Syntax, name: Syntax, body: Syntax) -> Syntax {
    term("doFor", vec![
        atom("for"),
        null(vec![term("doForDecl", vec![witness, name, atom("in"), named("collection")])]),
        atom("do"),
        term("doSeqIndent", vec![null(vec![term("doSeqItem", vec![body, null(vec![])])])]),
    ])
}
fn witness() -> Syntax {
    null(vec![named("h"), atom(":")])
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
fn binder_and_body(syntax: &Syntax) -> (&Syntax, &Syntax) {
    let parts = expect_node(syntax, &parser_kind(&["Term", "fun"]), 2, "callback").unwrap();
    let parts = expect_node(&parts[1], &parser_kind(&["Term", "basicFun"]), 4, "callback binder").unwrap();
    let [name] = expect_null_args(&parts[0], "single callback binder").unwrap() else {
        panic!("single binder")
    };
    (name, &parts[3])
}

#[test]
fn callback_opens_element_then_proof_then_accumulator_without_copying_collection() {
    let input = loop_(witness(), named("x"), term("doContinue", vec![atom("continue")]));
    let output = context().expand_for_loop(input).unwrap();
    let parts = expect_node(&output, &parser_kind(&["Term", "doExpr"]), 1, "loop action").unwrap();
    let parts = expect_node(&parts[0], &parser_kind(&["Term", "app"]), 2, "operation").unwrap();
    assert_eq!(parts[0], root(&["ForIn'", "forIn'"]));
    let arguments = expect_null_args(&parts[1], "arguments").unwrap();
    assert_eq!(arguments.len(), 4);
    let (element, body) = binder_and_body(&arguments[3]);
    let (proof, body) = binder_and_body(body);
    let (accumulator, _) = binder_and_body(body);
    assert_eq!(element, &named("x"));
    assert_eq!(proof, &named("h"));
    assert!(matches!(accumulator, Syntax::Ident { val, .. }
        if val == &Name::num(Name::anonymous(), 0)));
    assert_eq!(count(&output, &Name::from_components(["collection"])), 1);
    // No Membership application, equality proof or guessed dictionary is
    // synthesized. These are supplied only by the ordinary typed operation.
    assert_eq!(count(&output, &Name::from_components(["Membership"])), 0);
}

#[test]
fn wildcard_is_a_fresh_binder_not_an_unresolved_type_or_term_hole() {
    for membership in [false, true] {
        let input = loop_(
            if membership { witness() } else { null(vec![]) },
            term("hole", vec![atom("_")]),
            term("doBreak", vec![atom("break")]),
        );
        let output = context().expand_for_loop(input).unwrap();
        assert_eq!(count(&output, &Name::num(Name::anonymous(), 0)), 1);
        assert_eq!(count(&output, &Name::num(Name::anonymous(), 1)), 2);
        let mut pending = vec![&output];
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                assert_ne!(kind, &parser_kind(&["Term", "hole"]));
                pending.extend(args);
            }
        }
    }
}

#[test]
fn dependent_monad_hint_retains_the_same_checked_operation_guards() {
    let mut context = context();
    let marker = term("nativeDoForMonad", vec![]);
    let function = Typed {
        value: Expr::const_(Name::from_components(["ForIn'", "forIn'"]), vec![]),
        type_: Expr::forall_e(Name::from_components(["m"]), Expr::sort(Level::one()),
            Expr::sort(Level::one()), BinderInfo::Implicit),
    };
    let argument = context.do_for_monad_argument(&function, &Name::from_components(["m"]), &marker, None).unwrap().unwrap();
    assert!(matches!(argument.value.node(), ExprNode::MVar { .. }));
    assert_eq!(argument.type_, Expr::sort(Level::one()));
    assert!(context.do_for_monad_argument(&function, &Name::from_components(["wrong"]), &marker, None).is_err());
    let wrong = Typed { value: Expr::const_(Name::from_components(["Shadow", "ForIn'", "forIn'"]), vec![]), ..function };
    assert!(context.do_for_monad_argument(&wrong, &Name::from_components(["m"]), &marker, None).is_err());
}

#[test]
fn malformed_witnesses_and_wildcards_are_rejected_before_callback_construction() {
    for witness in [
        null(vec![named("h")]), null(vec![named("h"), atom("=")]),
        null(vec![atom("_"), atom(":")]), null(vec![root(&["h"]), atom(":")]),
        null(vec![named("h"), atom(":"), named("extra")]),
    ] {
        let input = loop_(witness, named("x"), term("doBreak", vec![atom("break")]));
        assert!(context().expand_for_loop(input).is_err());
    }
    for name in [term("hole", vec![]), term("hole", vec![named("x")]), atom("_")] {
        let input = loop_(witness(), name, term("doContinue", vec![atom("continue")]));
        assert!(context().expand_for_loop(input).is_err());
    }
}
