use super::*;

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

#[test]
fn proof_classification_is_bound_to_original_local_types() {
    let engine = engine();
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    let same_variable = Expr::bvar(0).unwrap();
    for (local_type, proof) in [
        (Expr::sort(Level::zero()), true),
        (Expr::sort(Level::one()), false),
        (Expr::const_(name("Nat"), vec![]), false),
        (Expr::sort(Level::zero()), true),
    ] {
        assert_eq!(
            prep.proposition_type(&same_variable, &[local_type])
                .unwrap(),
            proof,
        );
    }
    assert!(!prep.proposition_type(&same_variable, &[]).unwrap());
    let before = engine.logical_root(&KVMap::new());
    assert!(prep.lambdas.is_empty());
    assert!(prep.constructors.is_empty());
    assert_eq!(before, engine.logical_root(&KVMap::new()));
}

#[test]
fn type_functions_erase_only_proof_dependencies_in_original_context() {
    let engine = engine();
    let before = engine.logical_root(&KVMap::new());
    let bool_type = erased_type();
    let motive = Expr::lam(
        name("b"),
        bool_type.clone(),
        Expr::forall_e(
            name("h"),
            Expr::bvar(1).unwrap(),
            bool_type.clone(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let erased = Expr::lam(
        name("b"),
        bool_type.clone(),
        Expr::forall_e(
            name("h"),
            bool_type.clone(),
            bool_type.clone(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    for (local_sort, expected) in [
        (Level::zero(), &erased),
        (Level::one(), &motive),
        (Level::zero(), &erased),
    ] {
        assert_eq!(
            &prep
                .erase_type_argument(&motive, &[Expr::sort(local_sort)])
                .unwrap(),
            expected,
        );
    }
    assert!(!erased.has_loose_bvars());
    assert!(motive.has_loose_bvars());

    // A captured return type also remains an actual specialization dependency.
    let captured_type = Expr::lam(
        name("b"),
        bool_type,
        Expr::bvar(1).unwrap(),
        BinderInfo::Default,
    );
    assert_eq!(
        prep.erase_type_argument(&captured_type, &[Expr::sort(Level::one())])
            .unwrap(),
        captured_type,
    );
    assert!(prep.lambdas.is_empty());
    assert!(prep.constructors.is_empty());
    assert_eq!(before, engine.logical_root(&KVMap::new()));
}

#[test]
fn proposition_arguments_and_captured_predicates_keep_their_identity() {
    let engine = engine();
    let nat = Expr::const_(name("Nat"), vec![]);
    let equality = Expr::app(
        Expr::app(
            Expr::app(Expr::const_(name("Eq"), vec![Level::one()]), nat.clone()),
            Expr::bvar(0).unwrap(),
        ),
        Expr::bvar(1).unwrap(),
    );
    let predicate = Expr::lam(
        name("n"),
        nat.clone(),
        equality.clone(),
        BinderInfo::Default,
    );
    let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
    assert!(
        prep.proposition_type(&equality, &[nat.clone(), nat.clone()])
            .unwrap()
    );
    assert_eq!(
        prep.erase_type_argument(&predicate, std::slice::from_ref(&nat))
            .unwrap(),
        predicate,
    );
    assert_eq!(predicate.loose_bvar_range(), 1);

    // The same captured equality is erasable when it is only a proof domain
    // inside a Type-valued motive, rather than the predicate's logical result.
    let motive = Expr::lam(
        name("n"),
        nat.clone(),
        Expr::forall_e(name("h"), equality, nat.clone(), BinderInfo::Default),
        BinderInfo::Default,
    );
    let expected = Expr::lam(
        name("n"),
        nat.clone(),
        Expr::forall_e(name("h"), erased_type(), nat, BinderInfo::Default),
        BinderInfo::Default,
    );
    assert_eq!(
        prep.erase_type_argument(&motive, &[Expr::const_(name("Nat"), vec![])])
            .unwrap(),
        expected,
    );
    assert!(!expected.has_loose_bvars());

    let proposition = Expr::bvar(0).unwrap();
    assert_eq!(
        prep.erase_type_argument(&proposition, &[Expr::sort(Level::zero())])
            .unwrap(),
        proposition,
    );
    assert!(prep.lambdas.is_empty());
}

#[test]
fn deep_proof_classification_and_stops_use_heap_continuations() {
    let engine = engine();
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let nat = Expr::const_(name("Nat"), vec![]);
            let mut type_ = nat.clone();
            for _ in 0..300 {
                type_ = Expr::forall_e(Name::anonymous(), nat.clone(), type_, BinderInfo::Default);
            }
            let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
            assert_eq!(prep.erase_runtime_type(&type_).unwrap(), type_);
            let limits = IngressLimits {
                max_context_depth: 20,
                ..IngressLimits::default()
            };
            assert!(matches!(
                Preparation::new(&engine.environment, limits).erase_runtime_type(&type_),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::ContextDepth,
                    ..
                })
            ));
            let limits = IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            };
            assert!(matches!(
                Preparation::new(&engine.environment, limits).erase_runtime_type(&type_),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    ..
                })
            ));

            let mut motive = nat.clone();
            for _ in 0..300 {
                motive = Expr::lam(Name::anonymous(), nat.clone(), motive, BinderInfo::Default);
            }
            let mut prep = Preparation::new(&engine.environment, IngressLimits::default());
            assert_eq!(prep.erase_type_argument(&motive, &[]).unwrap(), motive);
            for (limits, expected) in [
                (
                    IngressLimits {
                        max_context_depth: 20,
                        ..IngressLimits::default()
                    },
                    IngressResource::ContextDepth,
                ),
                (
                    IngressLimits {
                        max_nodes: 1,
                        ..IngressLimits::default()
                    },
                    IngressResource::Nodes,
                ),
            ] {
                let Err(IngressError::ResourceLimit { resource, .. }) =
                    Preparation::new(&engine.environment, limits).erase_type_argument(&motive, &[])
                else {
                    panic!("type-function erasure must propagate its resource stop")
                };
                assert_eq!(resource, expected);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn proof_representation_never_assumes_a_familiar_scalar_name_is_authoritative() {
    let environment = Environment::new();
    let source = Expr::const_(name("unavailableProof"), vec![]);
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    assert!(!prep.proof_erasure_available());
    assert_eq!(prep.erase_proofs(&source, None).unwrap(), source);
    let motive = Expr::lam(
        name("n"),
        Expr::const_(name("Nat"), vec![]),
        Expr::forall_e(name("h"), source, erased_type(), BinderInfo::Default),
        BinderInfo::Default,
    );
    assert_eq!(prep.erase_type_argument(&motive, &[]).unwrap(), motive);
    assert!(prep.constructors.is_empty());
}
