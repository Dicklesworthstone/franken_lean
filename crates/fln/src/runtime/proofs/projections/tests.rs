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
class Weight (n : Nat) where
  weight : Nat
instance fiveWeight : Weight 5 := { weight := 42 }
structure ProjectionWitness (n : Nat) where
  property : n = n
  value : Nat
abbrev ProjectionAlias (n : Nat) : Type := ProjectionWitness n
structure ProjectionPredicate (p : Nat -> Prop) where
  value : Nat
  property : p value
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
/// A class projection takes its structure instance-implicitly and stays an application:
/// inlined, `pure ()` and `(1.5 : Float)` left `inst.1` for an ingress that lowers class
/// methods only through the application.
#[test]
fn a_class_projection_is_not_inlined() {
    let environment = engine().environment();
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    let head = Expr::const_(name("Weight.weight"), vec![]);
    let arguments = [nat::literal(5), Expr::const_(name("fiveWeight"), vec![])];
    assert_eq!(
        preparation
            .inline_generated_projection(&head, &arguments)
            .unwrap(),
        None
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

fn large_parameter() -> Expr {
    (0..2048).fold(nat::literal(0), |n, _| {
        Expr::app(Expr::const_(name("Nat.succ"), vec![]), n)
    })
}

#[test]
fn field_type_preserves_value_parameters_through_family_head_reductions() {
    let environment = engine().environment();
    let parameter = large_parameter();
    let nat = Expr::const_(name("Nat"), vec![]);
    let family = name("ProjectionWitness");
    let receiver = Expr::bvar(0).unwrap();
    let applied = |n| Expr::app(Expr::const_(family.clone(), vec![]), n);
    let expected = [nat.clone(), parameter.clone(), parameter.clone()]
        .into_iter()
        .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app);
    let sources = [
        applied(parameter.clone()),
        Expr::mdata(KVMap::new(), applied(parameter.clone())),
        Expr::app(
            Expr::const_(name("ProjectionAlias"), vec![]),
            parameter.clone(),
        ),
        Expr::app(
            Expr::lam(
                Name::anonymous(),
                nat.clone(),
                applied(receiver.clone()),
                BinderInfo::Default,
            ),
            parameter.clone(),
        ),
        Expr::let_e(
            Name::anonymous(),
            nat.clone(),
            parameter,
            applied(receiver.clone()),
            false,
        ),
    ];
    for source in sources {
        let mut preparation = Preparation::new(
            environment,
            IngressLimits {
                max_nodes: 512,
                ..IngressLimits::default()
            },
        );
        assert_eq!(
            preparation
                .original_projection_type(&source, &family, 0, &receiver)
                .unwrap(),
            Some(expected.clone())
        );
        assert_eq!(
            preparation
                .original_projection_type(&source, &family, 1, &receiver)
                .unwrap(),
            Some(nat.clone())
        );
    }
}

#[test]
fn field_type_preserves_subtype_predicates_without_normalizing_their_values() {
    let environment = engine().environment();
    let nat = Expr::const_(name("Nat"), vec![]);
    let receiver = Expr::bvar(0).unwrap();
    let equality = [nat.clone(), receiver.clone(), large_parameter()]
        .into_iter()
        .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app);
    let predicate = Expr::lam(
        Name::anonymous(),
        nat.clone(),
        equality,
        BinderInfo::Default,
    );
    let family = name("ProjectionPredicate");
    let source = Expr::app(Expr::const_(family.clone(), vec![]), predicate.clone());
    let expected = Expr::app(predicate, Expr::proj(family.clone(), 0, receiver.clone()));
    let mut preparation = Preparation::new(
        environment,
        IngressLimits {
            max_nodes: 512,
            ..IngressLimits::default()
        },
    );
    assert_eq!(
        preparation
            .original_projection_type(&source, &family, 0, &receiver)
            .unwrap(),
        Some(nat)
    );
    assert_eq!(
        preparation
            .original_projection_type(&source, &family, 1, &receiver)
            .unwrap(),
        Some(expected)
    );
    assert_eq!(
        preparation.original_projection_type(&source, &family, 2, &receiver),
        Err(unsupported(
            "projection field outside constructor telescope"
        ))
    );
}

#[test]
fn field_layout_erases_value_parameters_before_normalizing_the_receiver() {
    let environment = engine().environment();
    let nat = Expr::const_(name("Nat"), vec![]);
    let family = name("ProjectionWitness");
    let applied = |n| Expr::app(Expr::const_(family.clone(), vec![]), n);
    for source in [
        applied(nat::literal(0)),
        applied(large_parameter()),
        Expr::app(
            Expr::const_(name("ProjectionAlias"), vec![]),
            large_parameter(),
        ),
    ] {
        let mut preparation = Preparation::new(
            environment,
            IngressLimits {
                max_nodes: 4096,
                ..IngressLimits::default()
            },
        );
        let (shape, field) = preparation
            .projection_slot(&source, &family, 1)
            .unwrap()
            .unwrap();
        assert_eq!(field, nat);
        assert_eq!(
            shape.constructors[0].fields,
            vec![erased_type(), nat.clone()]
        );
        let (_, again) = preparation
            .projection_slot(&source, &shape.name, 1)
            .unwrap()
            .unwrap();
        assert_eq!(again, nat);
        assert!(matches!(
            preparation.projection_slot(&source, &name("Projection"), 1),
            Err(IngressError::UnsupportedNode {
                kind: "projection receiver family mismatch"
            })
        ));
        assert!(matches!(
            preparation.projection_slot(&source, &family, 2),
            Err(IngressError::UnsupportedNode {
                kind: "projection field outside constructor telescope"
            })
        ));
    }
}
