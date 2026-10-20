//! Recursor parameter erasure uses admitted metadata, not recursor spellings.
//! Parameters select a datatype; minors, value indices and majors execute.
use super::*;

fn engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
noncomputable def hiddenRecursorParameter : Nat := 5
inductive ParamMatch (n : Nat) where
  | mk (value : Nat)
inductive TwoParamMatch (n m : Nat) where
  | mk (value : Nat)
inductive IndexedMatch : Nat -> Type where
  | mk (n value : Nat) : IndexedMatch (Nat.succ n)
namespace OrdinaryRecursor
def rec (n value : Nat) : Nat := value
end OrdinaryRecursor
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

fn application(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn constructor(family: &str, parameters: &[Expr], field: Expr) -> Expr {
    application(
        constant(&format!("{family}.mk")),
        parameters.iter().cloned().chain(std::iter::once(field)),
    )
}

fn arguments(family: &str, parameters: &[Expr], minor: Expr, major: Expr) -> Vec<Expr> {
    let carrier = application(constant(family), parameters.iter().cloned());
    parameters
        .iter()
        .cloned()
        .chain([lambda(carrier, constant("Nat")), minor, major])
        .collect()
}

fn recursor(family: &str) -> Expr {
    Expr::const_(name(&format!("{family}.rec")), vec![Level::one()])
}

fn identity() -> Expr {
    lambda(constant("Nat"), Expr::bvar(0).unwrap())
}

fn refuses(environment: &Environment, input: &Expr) {
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    assert!(matches!(
        preparation.erase_proofs(input, Some(constant("Nat"))),
        Err(IngressError::UnsupportedNode {
            kind: "noncomputable runtime dependency"
        })
    ));
}

#[test]
fn recursor_parameter_prefix_is_static_at_partial_and_saturated_uses() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    for (family, count) in [("ParamMatch", 1usize), ("TwoParamMatch", 2)] {
        let Some(ConstantInfo::Rec(info)) =
            engine.environment.find(&name(&format!("{family}.rec")))
        else {
            panic!("source did not admit a recursor");
        };
        assert_eq!(info.num_params as usize, count);
        let parameters = vec![constant("hiddenRecursorParameter"); count];
        let args = arguments(
            family,
            &parameters,
            identity(),
            constructor(family, &parameters, nat::literal(42)),
        );
        for supplied in 1..=args.len() {
            let input = application(recursor(family), args[..supplied].iter().cloned());
            let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
            assert_eq!(preparation.erase_proofs(&input, None).unwrap(), input);
        }
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn captured_parameters_stay_static_and_the_motive_uses_the_erased_layout_key() {
    let engine = engine();
    let parameter = application(
        constant("Nat.add"),
        [Expr::bvar(0).unwrap(), constant("hiddenRecursorParameter")],
    );
    let parameters = [parameter];
    let major = constructor("ParamMatch", &parameters, nat::literal(42));
    let input = lambda(
        constant("Nat"),
        application(
            recursor("ParamMatch"),
            arguments("ParamMatch", &parameters, identity(), major.clone()),
        ),
    );
    // The parameter and the major's parameter are kept verbatim and never
    // executed. The motive is a runtime type that captures a local, so
    // erase_type_argument keys its value parameter by the erased layout
    // parameter, which serves every value (runtime/indexed.rs). The source
    // program for this shape reaches the VM in
    // tests/source_noncomputable_parameters.rs.
    let erased_motive = lambda(
        application(
            constant("ParamMatch"),
            [constant("_fln_runtime_erased_parameter")],
        ),
        constant("Nat"),
    );
    let expected = lambda(
        constant("Nat"),
        application(
            recursor("ParamMatch"),
            parameters
                .iter()
                .cloned()
                .chain([erased_motive, identity(), major]),
        ),
    );
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.erase_proofs(&input, None).unwrap(), expected);
}

#[test]
fn shared_parameter_syntax_does_not_exempt_minors_or_constructor_fields() {
    let engine = engine();
    let secret = constant("hiddenRecursorParameter");
    for (minor, field) in [
        (lambda(constant("Nat"), secret.clone()), nat::literal(42)),
        (identity(), secret.clone()),
    ] {
        let parameters = [secret.clone()];
        let input = application(
            recursor("ParamMatch"),
            arguments(
                "ParamMatch",
                &parameters,
                minor,
                constructor("ParamMatch", &parameters, field),
            ),
        );
        refuses(&engine.environment, &input);
    }
    refuses(
        &engine.environment,
        &application(constant("OrdinaryRecursor.rec"), [secret, nat::literal(42)]),
    );
}

#[test]
fn value_indices_are_not_mistaken_for_datatype_parameters() {
    let engine = engine();
    let Some(ConstantInfo::Rec(info)) = engine.environment.find(&name("IndexedMatch.rec")) else {
        panic!("source did not admit the indexed recursor");
    };
    assert_eq!(info.num_params, 0);
    assert_eq!(info.num_indices, 1);
    let motive = lambda(
        constant("Nat"),
        lambda(
            Expr::app(constant("IndexedMatch"), Expr::bvar(0).unwrap()),
            constant("Nat"),
        ),
    );
    let minor = lambda(constant("Nat"), identity());
    let major = application(
        constant("IndexedMatch.mk"),
        [nat::literal(4), nat::literal(42)],
    );
    // hiddenRecursorParameter reduces logically to 5 = Nat.succ 4, so the
    // major has the required source type. Its separate scalar index remains
    // executable. The index is `Nat.succ n`, not a bare constructor variable:
    // the pin promotes a uniform `IndexedMatch n` index to a parameter
    // (numParams=1, numIndices=0), which would test nothing here.
    let input = application(
        recursor("IndexedMatch"),
        [motive, minor, constant("hiddenRecursorParameter"), major],
    );
    refuses(&engine.environment, &input);
}

#[test]
fn recursor_authority_and_malformed_metadata_are_checked_before_erased_arguments() {
    let engine = engine();
    let parameters = [constant("hiddenRecursorParameter")];
    let input = application(
        recursor("ParamMatch"),
        arguments(
            "ParamMatch",
            &parameters,
            identity(),
            constructor("ParamMatch", &parameters, nat::literal(42)),
        ),
    );
    // Analysis-only negative controls do not grant any execution authority.
    let unavailable =
        fln_elab::noncomputable::register(&engine.environment, &name("ParamMatch.rec")).unwrap();
    refuses(&unavailable, &input);
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
fn recursor_erasure_is_bounded_and_a_fresh_retry_has_no_partial_result() {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let parameters = vec![constant("hiddenRecursorParameter"); 2];
    let input = application(
        recursor("TwoParamMatch"),
        arguments(
            "TwoParamMatch",
            &parameters,
            identity(),
            constructor("TwoParamMatch", &parameters, nat::literal(42)),
        ),
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
