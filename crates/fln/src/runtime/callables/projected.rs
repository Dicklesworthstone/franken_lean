//! Annotation discovery is not evaluation or permission to publish a lambda.
use super::*;

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
structure Callback where
  run : Nat -> Nat
def boxed : Callback := { run := fun n => n + 3 }
def ordinary (c : Callback) : Nat -> Nat := fun n => n
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn c(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}
fn projection() -> Expr {
    Expr::app(c("Callback.run"), c("boxed"))
}

#[test]
fn both_projection_forms_reveal_literal_callbacks_without_registering_them() {
    let engine = engine();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    for value in [projection(), Expr::proj(name("Callback"), 0, c("boxed"))] {
        let identity = value.allocation_identity();
        assert!(prep.has_literal_callable_tail(&value).unwrap());
        assert_eq!(value.allocation_identity(), identity);
        assert!(
            prep.lambdas.is_empty(),
            "discovery is not closure registration"
        );
    }
}

#[test]
fn strict_prefixes_are_not_evaluated_during_discovery() {
    let engine = engine();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    // The initializer is intentionally not executable: the probe may inspect
    // only the result path. Real execution must still process this initializer.
    let value = Expr::let_e(
        name("strict"),
        c("Nat"),
        c("notExecutable"),
        Expr::mdata(KVMap::new(), projection()),
        false,
    );
    assert!(prep.has_literal_callable_tail(&value).unwrap());
    assert!(matches!(value.node(), ExprNode::LetE { .. }));
    assert!(prep.lambdas.is_empty());
}

#[test]
fn unrelated_functions_bad_projections_and_callback_applications_are_not_evaluated() {
    let engine = engine();
    for value in [
        Expr::app(c("ordinary"), c("boxed")),
        Expr::proj(name("Other"), 0, c("boxed")),
        Expr::proj(name("Callback"), 1, c("boxed")),
        Expr::proj(name("Callback"), 0, Expr::bvar(0).unwrap()),
        c("Callback.run"),
        Expr::app(projection(), nat::literal(2)),
        Expr::app(
            Expr::const_(name("Callback.run"), vec![fln_core::level::Level::one()]),
            c("boxed"),
        ),
    ] {
        let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
        assert!(
            !prep.has_literal_callable_tail(&value).unwrap(),
            "{value:?}"
        );
        assert!(prep.lambdas.is_empty());
    }
}

#[test]
fn discovery_exhaustion_stays_a_resource_stop_and_does_not_poison_retries() {
    let engine = engine();
    let limits = IngressLimits {
        max_nodes: 1,
        ..IngressLimits::default()
    };
    assert!(matches!(
        Preparation::new(&engine.environment, limits).has_literal_callable_tail(&projection()),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
    assert!(
        Preparation::new(&engine.environment, IngressLimits::default())
            .has_literal_callable_tail(&projection())
            .unwrap()
    );
}
