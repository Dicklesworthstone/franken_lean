use super::*;

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
    .unwrap()
    .into_complete()
    .unwrap()
}

fn metadata_engine() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    engine()
        .check_source_files(
            &[br#"
def preservePredicate (P : Prop) (n : Nat) : Nat := n
def preservePredicateFamily (P : Nat -> Prop) (n : Nat) : Nat := n
def preserveTypeFamily (A : Nat -> Type) (n : Nat) : Nat := n
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn captured_proposition_indices_remain_metadata_with_bounded_erasure() {
    let engine = metadata_engine();
    let original_root = engine.logical_root(&KVMap::new());
    let nat = Expr::const_(name("Nat"), vec![]);
    let add = Expr::const_(name("Nat.add"), vec![]);
    let indexed_value = |variable| {
        let mut value = Expr::bvar(variable).unwrap();
        for _ in 0..14 {
            value = Expr::app(Expr::app(add.clone(), value.clone()), value);
        }
        value
    };
    let equality = |value: Expr| {
        [nat.clone(), value.clone(), value]
            .into_iter()
            .fold(Expr::const_(name("Eq"), vec![Level::one()]), Expr::app)
    };
    let proposition = equality(indexed_value(0));
    let predicate = Expr::lam(
        name("x"),
        nat.clone(),
        equality(indexed_value(1)),
        BinderInfo::Default,
    );
    let runtime_argument = Expr::app(
        Expr::app(add.clone(), Expr::bvar(0).unwrap()),
        nat::literal(1),
    );
    let limits = IngressLimits {
        max_nodes: 1024,
        ..IngressLimits::default()
    };
    for (callee, metadata) in [
        ("preservePredicate", proposition.clone()),
        ("preservePredicateFamily", predicate),
    ] {
        let source = Expr::lam(
            name("n"),
            nat.clone(),
            Expr::app(
                Expr::app(Expr::const_(name(callee), vec![]), metadata),
                runtime_argument.clone(),
            ),
            BinderInfo::Default,
        );
        let mut preparation = Preparation::new(&engine.environment, limits);
        assert_eq!(preparation.erase_proofs(&source, None).unwrap(), source);
        // The executable Nat.add operand remains in place; only the inspected
        // parameter type makes the large captured predicate static metadata.
        let mut stopped = Preparation::new(
            &engine.environment,
            IngressLimits {
                max_nodes: 1,
                ..limits
            },
        );
        assert!(matches!(
            stopped.erase_proofs(&source, None),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 1,
                observed: 2,
            })
        ));
    }
    // The old hidden-carrier traversal really exceeds this budget. The same
    // large syntax also remains bounded work when it is an executable operand.
    let mut hidden = Preparation::new(&engine.environment, limits);
    assert!(matches!(
        hidden.erase_type_argument(&proposition, std::slice::from_ref(&nat)),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 1024,
            observed: 1025,
        })
    ));
    let executable = Expr::lam(
        name("n"),
        nat,
        Expr::app(
            Expr::app(Expr::const_(name("preservePredicate"), vec![]), proposition),
            indexed_value(0),
        ),
        BinderInfo::Default,
    );
    let mut runtime = Preparation::new(&engine.environment, limits);
    assert!(matches!(
        runtime.erase_proofs(&executable, None),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 1024,
            observed: 1025,
        })
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), original_root);
}

#[test]
fn type_valued_arguments_still_erase_captured_proof_dependencies() {
    let engine = metadata_engine();
    let nat = Expr::const_(name("Nat"), vec![]);
    let family = |proof_domain| {
        Expr::lam(
            name("n"),
            nat.clone(),
            Expr::forall_e(
                name("proof"),
                proof_domain,
                nat.clone(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    let source = |argument| {
        Expr::lam(
            name("P"),
            Expr::sort(Level::zero()),
            Expr::app(
                Expr::app(Expr::const_(name("preserveTypeFamily"), vec![]), argument),
                nat::literal(42),
            ),
            BinderInfo::Default,
        )
    };
    let input = source(family(Expr::bvar(1).unwrap()));
    let expected = source(family(erased_type()));
    assert_ne!(input, expected);
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(preparation.erase_proofs(&input, None).unwrap(), expected);
}

#[test]
fn closed_erasure_reuses_exact_syntax_with_identical_shared_and_unshared_bounds() {
    fn fresh_tree(depth: usize) -> Expr {
        if depth == 0 {
            nat::literal(1)
        } else {
            Expr::app(
                Expr::app(Expr::const_(name("Nat.add"), vec![]), fresh_tree(depth - 1)),
                fresh_tree(depth - 1),
            )
        }
    }
    let engine = engine();
    let mut shared = nat::literal(1);
    for _ in 0..12 {
        shared = Expr::app(
            Expr::app(Expr::const_(name("Nat.add"), vec![]), shared.clone()),
            shared,
        );
    }
    let unshared = fresh_tree(12);
    assert_eq!(shared, unshared);
    // More than eight thousand original runtime nodes remain in the result.
    // Only repeated closed analysis fits this smaller preparation budget.
    let limits = IngressLimits {
        max_nodes: 4096,
        ..IngressLimits::default()
    };
    let mut left = Preparation::new(&engine.environment, limits);
    let mut right = Preparation::new(&engine.environment, limits);
    assert_eq!(left.erase_proofs(&shared, None).unwrap(), shared);
    assert_eq!(right.erase_proofs(&unshared, None).unwrap(), unshared);
    assert_eq!(left.visited, right.visited);
    let required = left.visited;
    assert!(required < limits.max_nodes);
    for budget in [0, required - 1] {
        for source in [&shared, &unshared] {
            let mut stopped = Preparation::new(
                &engine.environment,
                IngressLimits {
                    max_nodes: budget,
                    ..limits
                },
            );
            assert!(matches!(
                stopped.erase_proofs(source, None),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes,
                    limit,
                    observed,
                }) if limit == budget && observed == budget + 1
            ));
        }
    }
    let mut retry = Preparation::new(&engine.environment, limits);
    assert_eq!(retry.erase_proofs(&shared, None).unwrap(), shared);
    assert_eq!(retry.visited, required);
}

#[test]
fn closed_erasure_memo_never_reuses_an_open_variable_in_another_scope() {
    let engine = engine();
    let nat = Expr::const_(name("Nat"), vec![]);
    let variable = Expr::bvar(0).unwrap();
    let identity = Expr::app(
        Expr::lam(
            name("n"),
            nat.clone(),
            variable.clone(),
            BinderInfo::Default,
        ),
        nat::literal(1),
    );
    let eliminate = |proof| {
        Expr::app(
            Expr::app(
                Expr::const_(name("False.elim"), vec![Level::one()]),
                nat.clone(),
            ),
            proof,
        )
    };
    for reverse in [false, true] {
        let body = |proof| {
            let args = if reverse {
                [eliminate(proof), identity.clone()]
            } else {
                [identity.clone(), eliminate(proof)]
            };
            args.into_iter()
                .fold(Expr::const_(name("Nat.add"), vec![]), Expr::app)
        };
        let input = Expr::lam(
            name("h"),
            Expr::const_(name("False"), vec![]),
            body(variable.clone()),
            BinderInfo::Default,
        );
        let expected = Expr::lam(
            name("h"),
            erased_type(),
            body(erased_value()),
            BinderInfo::Default,
        );
        let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
        assert_eq!(preparation.erase_proofs(&input, None).unwrap(), expected);
    }
}

#[test]
fn closed_erasure_memo_preserves_strict_nonreturning_runtime_calls() {
    use fln_env::constants::{ConstantVal, ReducibilityHints};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let nat = Expr::const_(name("Nat"), vec![]);
    let logical_name = name("spin");
    let executable_name = Name::str(logical_name.clone(), "_unsafe_rec");
    let lambda = |body| Expr::lam(name("n"), nat.clone(), body, BinderInfo::Default);
    let logical = DefinitionVal {
        base: ConstantVal {
            name: logical_name.clone(),
            level_params: vec![],
            type_: Expr::forall_e(name("n"), nat.clone(), nat.clone(), BinderInfo::Default),
        },
        value: lambda(nat::literal(0)),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![logical_name.clone()],
    };
    let mut executable = logical.clone();
    executable.base.name = executable_name.clone();
    executable.value = lambda(Expr::app(
        Expr::const_(executable_name.clone(), vec![]),
        Expr::bvar(0).unwrap(),
    ));
    executable.safety = DefinitionSafety::Partial;
    executable.all = vec![executable_name.clone()];
    let mut engine = engine();
    for declaration in [
        Declaration::Defn(logical),
        Declaration::Mutual(vec![executable]),
    ] {
        engine = engine
            .admit_declaration(declaration, &KVMap::new(), limits.admission())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    let repeated_call = |callee| {
        let call = Expr::app(Expr::const_(callee, vec![]), nat::literal(0));
        Expr::app(
            Expr::app(Expr::const_(name("Nat.add"), vec![]), call.clone()),
            call,
        )
    };
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    assert_eq!(
        preparation
            .erase_proofs(&repeated_call(logical_name), None)
            .unwrap(),
        repeated_call(executable_name),
    );
    let root = engine.logical_root(&KVMap::new());
    let mut bounded = limits;
    bounded.vm.max_steps = 200;
    let outcome = engine
        .execute_source_definitions(
            &[b"#eval let ignored : Nat := Nat.add (spin 0) (spin 0); 42"],
            &KVMap::new(),
            bounded,
        )
        .unwrap();
    let Outcome::Inconclusive(stopped) = outcome else {
        panic!("strict repeated calls must execute before the unused binding is discarded")
    };
    assert!(matches!(
        stopped.cause,
        fln_core::outcome::InconclusiveCause::ResourceExhausted { usage }
            if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                && usage.allowed == 200 && usage.observed == 201
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
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
