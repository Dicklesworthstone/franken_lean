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
    assert!(prep.constructors.is_empty());
}
