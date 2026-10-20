//! Execution selectors must not turn a generated field into a metadata bypass.
use super::*;
use std::sync::OnceLock;

fn engine() -> &'static Engine {
    static ENGINE: OnceLock<Engine> = OnceLock::new();
    ENGINE.get_or_init(|| {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
structure Projection (n : Nat) where
  value : Nat
def replacement (n : Nat) (r : Projection n) : Nat := n + r.value
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine
    })
}
fn head() -> Expr {
    Expr::const_(name("Projection.value"), vec![])
}
fn args() -> [Expr; 2] {
    [
        nat::literal(5),
        Expr::app(
            Expr::app(Expr::const_(name("Projection.mk"), vec![]), nat::literal(5)),
            nat::literal(42),
        ),
    ]
}
#[test]
fn partial_projection_keeps_one_receiver_and_full_projection_is_idempotent() {
    let environment = engine().environment();
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    let arguments = args();
    let partial = preparation
        .inline_generated_projection(&head(), &arguments[..1])
        .unwrap()
        .unwrap();
    assert!(matches!(partial.node(), ExprNode::Lam { body, .. }
        if matches!(body.node(), ExprNode::Proj { expr, .. } if matches!(expr.node(), ExprNode::BVar { idx: 0 }))));
    let complete = preparation
        .inline_generated_projection(&head(), &arguments)
        .unwrap()
        .unwrap();
    assert_eq!(
        complete,
        Expr::proj(name("Projection"), 0, arguments[1].clone())
    );
    assert!(
        preparation
            .inline_generated_projection(&complete, &[])
            .unwrap()
            .is_none()
    );
}
#[test]
fn initialized_and_overridden_projections_never_inline_their_logical_body() {
    let environment = engine().environment();
    let initialized = BTreeSet::from([name("Projection.value")]);
    let mut preparation = Preparation::new(environment, IngressLimits::default())
        .with_runtime_initializers(&initialized);
    assert_eq!(
        preparation
            .inline_generated_projection(&head(), &args())
            .unwrap(),
        None
    );
    let overridden = fln_elab::implemented_by::register(
        environment,
        &name("Projection.value"),
        &name("replacement"),
    )
    .unwrap();
    let mut preparation = Preparation::new(&overridden, IngressLimits::default());
    assert_eq!(
        preparation
            .inline_generated_projection(&head(), &args())
            .unwrap(),
        None
    );
}
#[test]
fn unsupported_extern_and_corrupt_metadata_cannot_fall_back_to_projection_erasure() {
    let environment = engine().environment();
    let foreign = fln_elab::externs::register(
        environment,
        &name("Projection.value"),
        vec![fln_elab::externs::ExternEntry::Opaque],
    )
    .unwrap();
    let mut preparation = Preparation::new(&foreign, IngressLimits::default());
    assert!(matches!(
        preparation.inline_generated_projection(&head(), &args()),
        Err(IngressError::UnsupportedNode { .. })
    ));
    let overridden = fln_elab::implemented_by::register(
        environment,
        &name("Projection.value"),
        &name("replacement"),
    )
    .unwrap();
    let corrupt = overridden
        .push_extension_entry(
            &fln_elab::implemented_by::journal_name(),
            b"broken".to_vec(),
        )
        .unwrap();
    let mut preparation = Preparation::new(&corrupt, IngressLimits::default());
    assert!(matches!(
        preparation.inline_generated_projection(&head(), &args()),
        Err(IngressError::UnsupportedNode { .. })
    ));
}
#[test]
fn every_metered_prefix_stops_without_a_result_and_fresh_retry_is_identical() {
    let environment = engine().environment();
    let root = environment.logical_root(&KVMap::new());
    let mut full = Preparation::new(environment, IngressLimits::default());
    let expected = full.inline_generated_projection(&head(), &args()).unwrap();
    let required = full.visited;
    assert!(expected.is_some() && required > 1);
    for max_nodes in 0..required {
        let mut limited = Preparation::new(
            environment,
            IngressLimits {
                max_nodes,
                ..IngressLimits::default()
            },
        );
        assert!(
            matches!(
                limited.inline_generated_projection(&head(), &args()),
                Err(IngressError::ResourceLimit { .. })
            ),
            "limit {max_nodes}"
        );
    }
    let mut retry = Preparation::new(environment, IngressLimits::default());
    assert_eq!(
        retry.inline_generated_projection(&head(), &args()).unwrap(),
        expected
    );
    assert_eq!(retry.visited, required);
    assert_eq!(environment.logical_root(&KVMap::new()), root);
}
