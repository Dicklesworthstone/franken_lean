//! Constructor parameters are static inputs to post-admission preparation.
//! These tests use source-admitted families, not constructor-name allowlists.
use super::*;

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
noncomputable def hiddenParameter : Nat := 5
inductive ErasureCarrier (n : Nat) where
  | mk (value : Nat)
inductive TwoErasureParameters (n m : Nat) where
  | mk (value : Nat)
inductive ProofCarrier (n : Nat) where
  | mk (proof : n = n) (value : Nat)
namespace OrdinaryFactory
def mk (n value : Nat) : Nat := value
end OrdinaryFactory
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}

fn call(text: &str, arguments: Vec<Expr>) -> Expr {
    arguments.into_iter().fold(constant(text), Expr::app)
}

fn noncomputable_refusal(environment: &Environment, input: &Expr) {
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    assert!(matches!(
        preparation.erase_proofs(input, None),
        Err(IngressError::UnsupportedNode {
            kind: "noncomputable runtime dependency"
        })
    ));
}

#[test]
fn checked_data_parameter_prefix_survives_saturated_and_partial_applications() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let secret = constant("hiddenParameter");
    for (constructor, parameters) in [
        ("ErasureCarrier.mk", 1),
        ("TwoErasureParameters.mk", 2),
    ] {
        let Some(ConstantInfo::Ctor(info)) = engine.environment.find(&name(constructor)) else {
            panic!("source did not admit the constructor");
        };
        assert_eq!(info.num_params, parameters);
        // Stop both inside the static prefix and at a partially applied runtime
        // telescope, not only at a fully saturated constructor expression.
        for supplied in 1..=parameters as usize {
            let partial = call(constructor, vec![secret.clone(); supplied]);
            let mut preparation =
                Preparation::new(&engine.environment, IngressLimits::default());
            assert_eq!(preparation.erase_proofs(&partial, None).unwrap(), partial);
        }
        let mut arguments = vec![secret.clone(); parameters as usize];
        arguments.push(nat::literal(42));
        let saturated = call(constructor, arguments);
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert_eq!(preparation.erase_proofs(&saturated, None).unwrap(), saturated);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn captured_data_parameters_remain_exact_under_the_original_telescope() {
    let engine = engine();
    let parameter = call(
        "Nat.add",
        vec![Expr::bvar(0).unwrap(), constant("hiddenParameter")],
    );
    let input = Expr::lam(
        name("n"),
        constant("Nat"),
        call("ErasureCarrier.mk", vec![parameter, nat::literal(42)]),
        BinderInfo::Default,
    );
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.erase_proofs(&input, None).unwrap(), input);
}

#[test]
fn shared_parameter_and_runtime_field_never_share_a_false_executable_cache_entry() {
    let engine = engine();
    let secret = constant("hiddenParameter");
    for field in [
        secret.clone(),
        call("Nat.add", vec![secret.clone(), nat::literal(1)]),
    ] {
        noncomputable_refusal(
            &engine.environment,
            &call("ErasureCarrier.mk", vec![secret.clone(), field]),
        );
    }
    // An ordinary function, even one named mk, has no constructor parameter
    // prefix. Its unused Nat argument is still an executable source argument.
    noncomputable_refusal(
        &engine.environment,
        &call("OrdinaryFactory.mk", vec![secret, nat::literal(42)]),
    );
    noncomputable_refusal(
        &engine.environment,
        &call(
            "ErasureCarrier.mk",
            vec![nat::literal(5), constant("hiddenParameter")],
        ),
    );
}

#[test]
fn dependent_proof_fields_still_erase_after_static_parameter_substitution() {
    let engine = engine();
    let secret = constant("hiddenParameter");
    let proof = [constant("Nat"), secret.clone()]
        .into_iter()
        .fold(Expr::const_(name("Eq.refl"), vec![Level::one()]), Expr::app);
    let input = call(
        "ProofCarrier.mk",
        vec![secret.clone(), proof, nat::literal(42)],
    );
    let expected = call(
        "ProofCarrier.mk",
        vec![secret, erased_value(), nat::literal(42)],
    );
    assert_ne!(input, expected);
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.erase_proofs(&input, None).unwrap(), expected);
}

#[test]
fn static_parameters_do_not_exempt_the_constructor_head_or_corrupt_metadata() {
    let engine = engine();
    let input = call(
        "ErasureCarrier.mk",
        vec![constant("hiddenParameter"), nat::literal(42)],
    );
    // Deliberately altered metadata is an analysis-only negative control; it
    // supplies no checked declaration and is never submitted for execution.
    let unavailable =
        fln_elab::noncomputable::register(&engine.environment, &name("ErasureCarrier.mk"))
            .unwrap();
    noncomputable_refusal(&unavailable, &input);
    let corrupt = engine
        .environment
        .push_extension_entry(&fln_elab::noncomputable::journal_name(), b"broken".to_vec())
        .unwrap();
    let mut preparation = Preparation::new(&corrupt, IngressLimits::default());
    assert!(matches!(
        preparation.erase_proofs(&input, None),
        Err(IngressError::UnsupportedNode {
            kind: "malformed native noncomputable journal"
        })
    ));
    assert!(preparation.noncomputable.is_none());
}

#[test]
fn parameter_retention_is_metered_and_incomplete_work_cannot_escape() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let input = call(
        "TwoErasureParameters.mk",
        vec![
            constant("hiddenParameter"),
            constant("hiddenParameter"),
            nat::literal(42),
        ],
    );
    let mut complete = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(complete.erase_proofs(&input, None).unwrap(), input);
    let required = complete.visited;
    assert!(required > 1);
    for allowed in [0, required / 2, required - 1] {
        let mut limited = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes: allowed,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            limited.erase_proofs(&input, None),
            Err(IngressError::ResourceLimit { .. })
        ));
    }
    let mut retry = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(retry.erase_proofs(&input, None).unwrap(), input);
    assert_eq!(retry.visited, required);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
