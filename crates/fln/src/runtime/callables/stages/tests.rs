use super::*;

fn signature(parameters: Vec<ValueType>, result: ValueType) -> ClosureSignature {
    ClosureSignature {
        parameter_ownership: borrowed_runtime_parameters(parameters.len()).unwrap(),
        parameters,
        result,
        result_ownership: result_ownership(result),
    }
}

#[test]
fn result_grouping_preserves_parameter_types_ownership_and_terminal_representations() {
    let environment = Environment::new();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    let suffix = prep
        .stage_interface(signature(vec![ValueType::String], ValueType::Nat))
        .unwrap();
    let staged = prep
        .stage_interface(signature(vec![ValueType::Nat], suffix))
        .unwrap();
    let flat = prep
        .stage_interface(signature(
            vec![ValueType::Nat, ValueType::String],
            ValueType::Nat,
        ))
        .unwrap();
    assert!(prep.same_stage_telescope(staged, flat).unwrap());
    let wrong = prep
        .stage_interface(signature(
            vec![ValueType::String, ValueType::Nat],
            ValueType::Nat,
        ))
        .unwrap();
    assert!(!prep.same_stage_telescope(staged, wrong).unwrap());
    let wrong_result = prep
        .stage_interface(signature(
            vec![ValueType::Nat, ValueType::String],
            ValueType::String,
        ))
        .unwrap();
    assert!(!prep.same_stage_telescope(staged, wrong_result).unwrap());
    // A callback parameter is not a result stage: do not regroup its interface.
    let staged_arg = prep
        .stage_interface(signature(vec![staged], ValueType::Nat))
        .unwrap();
    let flat_arg = prep
        .stage_interface(signature(vec![flat], ValueType::Nat))
        .unwrap();
    assert!(!prep.same_stage_telescope(staged_arg, flat_arg).unwrap());
    let mut owned = signature(vec![ValueType::Nat, ValueType::String], ValueType::Nat);
    owned.parameter_ownership[1] = fln_comp::flbc::ArgumentOwnership::Owned;
    let owned = prep.stage_interface(owned).unwrap();
    assert!(!prep.same_stage_telescope(flat, owned).unwrap());
}

#[test]
fn known_aliases_and_partial_applications_keep_exact_stages_without_guessing_captures() {
    let environment = Environment::new();
    let mut prep = Preparation::new(&environment, IngressLimits::default());
    let suffix = prep
        .stage_interface(signature(vec![ValueType::String], ValueType::Nat))
        .unwrap();
    let staged = prep
        .stage_interface(signature(vec![ValueType::Nat, ValueType::Nat], suffix))
        .unwrap();
    let partial = prep.stage_apply(staged, 1).unwrap().unwrap();
    assert_eq!(prep.stage_apply(partial, 1).unwrap(), Some(suffix));
    assert_eq!(prep.stage_apply(staged, 3).unwrap(), Some(ValueType::Nat));
    assert_eq!(prep.stage_apply(staged, 4).unwrap(), None);
    let b = |i| Expr::bvar(i).unwrap();
    let nat = Expr::const_(name("Nat"), vec![]);
    let expr = Expr::let_e(
        name("alias"),
        nat.clone(),
        b(0),
        Expr::let_e(name("scalar"), nat, nat::literal(7), b(1), false),
        false,
    );
    assert_eq!(prep.staged_result(&expr, &[staged]).unwrap(), Some(staged));
    assert_eq!(prep.staged_result(&b(1), &[staged]).unwrap(), None);
    assert_eq!(
        prep.staged_result(&b(fln_core::expr::MAX_LOOSE_BVAR_RANGE - 1), &[])
            .unwrap(),
        None
    );
    let mut bounded = Preparation::new(
        &environment,
        IngressLimits {
            max_nodes: 1,
            ..IngressLimits::default()
        },
    );
    assert!(matches!(
        bounded.staged_result(&expr, &[staged]),
        Err(IngressError::ResourceLimit { .. })
    ));
    let mut tables = Preparation::new(
        &environment,
        IngressLimits {
            fir: fln_comp::fir::ValidationLimits {
                max_closure_types: 0,
                ..IngressLimits::default().fir
            },
            ..IngressLimits::default()
        },
    );
    assert!(
        tables
            .stage_interface(signature(vec![ValueType::Nat], ValueType::Nat))
            .is_err()
    );
}

#[test]
fn result_discovery_uses_a_bounded_heap_stack_and_rejects_cyclic_interfaces() {
    let mut body = Expr::bvar(2000).unwrap();
    let nat = Expr::const_(name("Nat"), vec![]);
    for _ in 0..2000 {
        body = Expr::let_e(Name::anonymous(), nat.clone(), nat::literal(0), body, false);
    }
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let environment = Environment::new();
            let mut prep = Preparation::new(
                &environment,
                IngressLimits {
                    max_context_depth: 4096,
                    ..IngressLimits::default()
                },
            );
            let value = prep
                .stage_interface(signature(vec![ValueType::Nat], ValueType::Nat))
                .unwrap();
            assert_eq!(prep.staged_result(&body, &[value]).unwrap(), Some(value));
            let mut bounded = Preparation::new(
                &environment,
                IngressLimits {
                    max_context_depth: 20,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                bounded.staged_result(&body, &[value]),
                Err(IngressError::ResourceLimit { .. })
            ));
            // Malformed metadata is an internal negative control, not an admitted proof.
            let cycle = ValueType::Closure(ClosureTypeId::new(0));
            prep.interfaces[0].result = cycle;
            prep.interfaces[0].result_ownership = result_ownership(cycle);
            assert!(prep.same_stage_telescope(cycle, cycle).is_err());
        })
        .unwrap()
        .join()
        .unwrap();
}
