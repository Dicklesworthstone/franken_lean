//! Bare method identifiers share the application's expected-result inference.
use super::*;
use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal, ReducibilityHints};

fn name(spelling: &str) -> Name {
    Name::from_components(spelling.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn constructor_type() -> Expr {
    Expr::forall_e(
        name("A"),
        Expr::sort(Level::one()),
        Expr::sort(Level::one()),
        BinderInfo::Default,
    )
}

fn fixture() -> Environment {
    let environment = crate::seed::bootstrap_nat_environment(budget()).unwrap();
    // A named family whose ordinary reduction hides the constructor head.
    // The method below is an explicit type fixture; each source consumer is
    // still elaborated and checked by the normal declaration admission door.
    let environment = environment
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("ReaderLike"),
                level_params: vec![],
                type_: constructor_type(),
            },
            value: Expr::lam(
                name("A"),
                Expr::sort(Level::one()),
                Expr::forall_e(
                    name("state"),
                    nat_const(),
                    Expr::bvar(1).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name("ReaderLike")],
        }))
        .unwrap();
    let environment = environment
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("Nat.asReader"),
                level_params: vec![],
                type_: Expr::forall_e(
                    name("m"),
                    constructor_type(),
                    Expr::forall_e(
                        name("receiver"),
                        nat_const(),
                        Expr::app(Expr::bvar(1).unwrap(), nat_const()),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Implicit,
                ),
            },
            is_unsafe: false,
        }))
        .unwrap();
    environment
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("Nat.identity"),
                level_params: vec![],
                type_: Expr::forall_e(
                    name("receiver"),
                    nat_const(),
                    nat_const(),
                    BinderInfo::Default,
                ),
            },
            value: Expr::lam(
                name("receiver"),
                nat_const(),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name("Nat.identity")],
        }))
        .unwrap()
}

fn accepted(environment: &Environment, source: &str) {
    let checked = crate::check_definition_source(source.as_bytes(), environment, budget())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(matches!(
        checked.outcome,
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let Declaration::Defn(definition) = checked.declaration else {
        panic!("the source produces a definition");
    };
    assert!(!definition.value.has_expr_mvar());
    assert!(!definition.value.has_level_mvar());
}

#[test]
fn bare_method_identifiers_receive_the_expected_type_constructor() {
    let environment = fixture();
    for value in [
        "receiver.asReader",
        "(receiver).asReader",
        "Nat.asReader receiver",
    ] {
        accepted(
            &environment,
            &format!("def inferred (receiver : Nat) : ReaderLike Nat := {value}"),
        );
    }
}

#[test]
fn only_the_last_field_path_component_receives_the_result_expectation() {
    let environment = fixture();
    for value in ["receiver.identity.asReader", "(receiver.identity).asReader"] {
        accepted(
            &environment,
            &format!("def inferred (receiver : Nat) : ReaderLike Nat := {value}"),
        );
    }
}

#[test]
fn an_unhinted_method_cannot_publish_its_unresolved_constructor() {
    assert!(
        crate::check_definition_source(
            b"def unresolved (receiver : Nat) := receiver.asReader",
            &fixture(),
            budget(),
        )
        .is_err()
    );
}
