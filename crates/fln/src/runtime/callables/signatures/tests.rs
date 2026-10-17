use super::*;
use fln_comp::fir::EffectClass;
use fln_comp::flbc::ResultOwnership;

fn signature(parameters: Vec<ValueType>, result: ValueType) -> ClosureSignature {
    ClosureSignature {
        parameter_ownership: vec![ArgumentOwnership::Borrowed; parameters.len()],
        parameters,
        result,
        result_ownership: result_ownership(result),
    }
}

#[test]
fn unowned_multiplicity_changes_neither_owned_rows_nor_full_signature_identity() {
    let base = signature(vec![ValueType::Nat], ValueType::Nat);
    let mut owned_argument = base.clone();
    owned_argument.parameter_ownership[0] = ArgumentOwnership::Owned;
    let mut unique_argument = base.clone();
    unique_argument.parameter_ownership[0] = ArgumentOwnership::Unique;
    let mut erased_result = base.clone();
    erased_result.result_ownership = CallableResultOwnership::Erased;
    let closure = |id| {
        signature(
            vec![ValueType::Closure(ClosureTypeId::new(id))],
            ValueType::Nat,
        )
    };
    let expected = vec![
        (Some(7), base.clone()),
        (None, base.clone()),
        (None, owned_argument.clone()),
        (None, unique_argument),
        (None, erased_result.clone()),
        (None, signature(vec![ValueType::Bool], ValueType::Nat)),
        (None, signature(vec![ValueType::Nat], ValueType::Bool)),
        (None, closure(1)),
        (None, closure(2)),
        (Some(8), base.clone()),
    ];
    let mut rows = expected.clone();
    rows.insert(2, (None, base.clone()));
    rows.push((None, erased_result));
    rows.push((None, owned_argument));
    rows.push((None, base));
    let mut visited = 0;
    deduplicate_unowned(&mut rows, IngressLimits::default(), &mut visited).unwrap();
    assert_eq!(rows, expected);
    assert!(visited > rows.len());
}

fn prepared(
    environment: &Environment,
    order: [usize; 4],
    duplicate_lambdas: usize,
    limits: IngressLimits,
) -> (Preparation<'_>, IntrinsicBinding) {
    let mut preparation = Preparation::new(environment, limits);
    let source_id = |logical| {
        ValueType::Closure(ClosureTypeId::new(
            order.iter().position(|&item| item == logical).unwrap() as u32,
        ))
    };
    for logical in order {
        let (parameters, result) = match logical {
            0 => (vec![ValueType::Nat, ValueType::Nat], ValueType::Nat),
            1 => (vec![ValueType::String], ValueType::String),
            2 => (vec![source_id(0), ValueType::Nat], ValueType::Nat),
            3 => (vec![ValueType::Bool], source_id(2)),
            _ => unreachable!(),
        };
        assert_eq!(
            preparation
                .register_function_type(
                    Expr::const_(Name::num(name("signature"), logical as u64), vec![]),
                    parameters,
                    result,
                )
                .unwrap(),
            source_id(logical)
        );
    }
    // Distinct source lambdas can share the complete ABI and both partial
    // application suffixes. Their expression identities are retained.
    for index in 0..duplicate_lambdas {
        let nat = Expr::const_(name("Nat"), vec![]);
        preparation.lambdas.push(LambdaBinding {
            lambda: Expr::lam(
                Name::num(name("left"), index as u64),
                nat.clone(),
                Expr::lam(
                    name("right"),
                    nat,
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            parameters: vec![ValueType::Nat, ValueType::Nat],
            parameter_ownership: vec![ArgumentOwnership::Borrowed; 2],
            result: ValueType::Nat,
            result_ownership: CallableResultOwnership::OwnedOrScalar,
            recursion: LambdaRecursion::NonRecursive,
        });
    }
    let binding = IntrinsicBinding {
        name: name("signatureProbe"),
        universe_arity: 0,
        row: "test:signatureProbe".to_owned(),
        arguments: (0..4).map(source_id).collect(),
        argument_ownership: vec![ArgumentOwnership::Borrowed; 4],
        result: source_id(3),
        result_ownership: ResultOwnership::Owned,
        effect: EffectClass::Pure,
    };
    (preparation, binding)
}

#[test]
fn nested_closure_ranks_remain_canonical_with_many_suffixes_and_reversed_discovery() {
    let environment = Environment::new();
    let limits = IngressLimits {
        max_nodes: 4_000,
        ..IngressLimits::default()
    };
    let mut reference = None;
    for order in [[0, 1, 2, 3], [3, 2, 1, 0], [1, 3, 0, 2]] {
        let (mut preparation, binding) = prepared(&environment, order, 96, limits);
        let original_lambdas = preparation.lambdas.clone();
        let mut bindings = [binding];
        let interfaces = preparation
            .finalize_callables(&mut [], &mut bindings)
            .unwrap();
        // Canonical rows are Bool -> callback, Nat -> Nat, Nat -> Nat -> Nat,
        // String -> String, and the callback-consuming two-argument interface.
        let expected: Vec<_> = [2, 3, 4, 0]
            .into_iter()
            .map(|id| ValueType::Closure(ClosureTypeId::new(id)))
            .collect();
        assert_eq!(bindings[0].arguments, expected);
        assert_eq!(
            bindings[0].result,
            ValueType::Closure(ClosureTypeId::new(0))
        );
        let mut logical_interfaces: Vec<_> = order.into_iter().zip(interfaces).collect();
        logical_interfaces.sort_by_key(|(logical, _)| *logical);
        if let Some((expected_binding, expected_interfaces)) = &reference {
            assert_eq!(&bindings[0], expected_binding);
            assert_eq!(&logical_interfaces, expected_interfaces);
        } else {
            reference = Some((bindings[0].clone(), logical_interfaces));
        }
        assert_eq!(preparation.lambdas, original_lambdas);
        assert!(preparation.visited < limits.max_nodes);
    }
}

#[test]
fn duplicate_suffixes_still_obey_the_original_raw_table_limit() {
    let environment = Environment::new();
    let mut limits = IngressLimits::default();
    limits.fir.max_closure_types = 16;
    let (mut preparation, binding) = prepared(&environment, [0, 1, 2, 3], 24, limits);
    let interfaces = preparation.interfaces.clone();
    let lambdas = preparation.lambdas.clone();
    let mut bindings = [binding.clone()];
    assert!(matches!(
        preparation.finalize_callables(&mut [], &mut bindings),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 16,
            observed: 17,
        })
    ));
    assert_eq!(preparation.interfaces, interfaces);
    assert_eq!(preparation.lambdas, lambdas);
    assert_eq!(bindings, [binding]);
    preparation.limits = IngressLimits::default();
    preparation.visited = 0;
    let actual = preparation
        .finalize_callables(&mut [], &mut bindings)
        .unwrap();
    let (mut fresh, fresh_binding) =
        prepared(&environment, [0, 1, 2, 3], 24, IngressLimits::default());
    let mut fresh_bindings = [fresh_binding];
    assert_eq!(
        actual,
        fresh
            .finalize_callables(&mut [], &mut fresh_bindings)
            .unwrap()
    );
    assert_eq!(bindings, fresh_bindings);
}

#[test]
fn exhausted_deduplication_leaves_rows_intact_and_can_retry() {
    let base = signature(vec![ValueType::String, ValueType::Nat], ValueType::String);
    let original = vec![
        (None, base.clone()),
        (None, base.clone()),
        (Some(0), base.clone()),
        (None, base),
    ];
    let mut expected = original.clone();
    let mut complete_work = 0;
    deduplicate_unowned(&mut expected, IngressLimits::default(), &mut complete_work).unwrap();
    let mut rows = original.clone();
    let mut visited = 0;
    let limits = IngressLimits {
        max_nodes: complete_work - 1,
        ..IngressLimits::default()
    };
    assert!(matches!(
        deduplicate_unowned(&mut rows, limits, &mut visited),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        }) if limit == complete_work - 1 && observed == complete_work
    ));
    assert_eq!(rows, original);
    visited = 0;
    deduplicate_unowned(&mut rows, IngressLimits::default(), &mut visited).unwrap();
    assert_eq!(rows, expected);
    assert_eq!(visited, complete_work);
}

#[test]
fn every_parameter_and_ownership_field_is_bounded_before_hashing() {
    for wide_ownership in [false, true] {
        let mut value = signature(vec![ValueType::Nat], ValueType::Nat);
        if wide_ownership {
            value.parameter_ownership = vec![ArgumentOwnership::Borrowed; 128];
        } else {
            value.parameters = vec![ValueType::Nat; 128];
        }
        let original = vec![(None, value)];
        let mut rows = original.clone();
        let mut visited = 0;
        assert!(matches!(
            deduplicate_unowned(
                &mut rows,
                IngressLimits {
                    max_nodes: 32,
                    ..IngressLimits::default()
                },
                &mut visited,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 32,
                observed: 33,
            })
        ));
        assert_eq!(rows, original);
    }
}
