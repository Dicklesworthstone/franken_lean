use super::*;

fn closure(id: u32) -> ValueType {
    ValueType::Closure(ClosureTypeId::new(id))
}

fn signature(parameters: Vec<ValueType>, result: ValueType) -> ClosureSignature {
    ClosureSignature {
        parameter_ownership: vec![ArgumentOwnership::Borrowed; parameters.len()],
        parameters,
        result,
        result_ownership: result_ownership(result),
    }
}

fn reference_order(rows: &[(Option<usize>, ClosureSignature)]) -> Vec<usize> {
    let mut order: Vec<_> = (0..rows.len()).collect();
    order.sort_by(|&left, &right| signature_order(&rows[left].1, &rows[right].1));
    order
}

fn mixed_rows() -> Vec<(Option<usize>, ClosureSignature)> {
    let values = [
        ValueType::Unit,
        ValueType::Bool,
        ValueType::Nat,
        ValueType::String,
        ValueType::Float,
        ValueType::Float32,
        ValueType::UInt32,
        ValueType::UInt64,
        ValueType::Constructor,
        ValueType::Array,
        ValueType::Ref,
        ValueType::Thunk,
        ValueType::Task,
        closure(0),
        closure(1),
        closure(u32::MAX),
        ValueType::Abi,
    ];
    let ownerships = [
        ArgumentOwnership::Borrowed,
        ArgumentOwnership::Owned,
        ArgumentOwnership::Unique,
        ArgumentOwnership::Scalar,
    ];
    let results = [
        CallableResultOwnership::Owned,
        CallableResultOwnership::Scalar,
        CallableResultOwnership::OwnedOrScalar,
        CallableResultOwnership::Erased,
    ];
    let mut rows = Vec::new();
    for (index, &value) in values.iter().enumerate() {
        for variant in 0..4 {
            let mut entry = signature(vec![value; variant + 1], values[(index + 7) % values.len()]);
            entry.parameter_ownership[variant] = ownerships[variant];
            entry.result_ownership = results[variant];
            rows.push((Some(rows.len()), entry.clone()));
            rows.push((None, entry));
        }
    }
    // Equal parameter vectors must still compare ownership and then both
    // result fields in exactly the FIR's established order.
    for ownership in ownerships {
        for result in results {
            let mut entry = signature(vec![ValueType::Nat, closure(3)], ValueType::String);
            entry.parameter_ownership[0] = ownership;
            entry.result_ownership = result;
            rows.push((None, entry));
        }
    }
    rows
}

#[test]
fn every_signature_component_and_original_equal_class_order_match_the_stable_reference() {
    let rows = mixed_rows();
    let original = rows.clone();
    let expected = reference_order(&rows);
    let forward: Vec<_> = (0..rows.len()).collect();
    let mut rotated = forward.clone();
    rotated.rotate_left(37);
    let mut interleaved: Vec<_> = (0..rows.len()).step_by(2).collect();
    interleaved.extend((1..rows.len()).step_by(2).rev());
    for mut order in [
        forward.clone(),
        forward.into_iter().rev().collect(),
        rotated,
        interleaved,
        expected.clone(),
    ] {
        stable_order(&rows, &mut order, IngressLimits::default(), &mut 0).unwrap();
        assert_eq!(order, expected);
        assert_eq!(
            rows, original,
            "source rows and owner identities stay unchanged"
        );
    }
}

#[test]
fn remapping_can_merge_previous_classes_without_reordering_equal_source_owners() {
    let mut rows = vec![
        (Some(0), signature(vec![closure(3)], ValueType::Nat)),
        (None, signature(vec![closure(0)], ValueType::Nat)),
        (Some(1), signature(vec![closure(2)], ValueType::Nat)),
        (Some(2), signature(vec![closure(1)], ValueType::Nat)),
    ];
    let mut order: Vec<_> = (0..rows.len()).collect();
    stable_order(&rows, &mut order, IngressLimits::default(), &mut 0).unwrap();
    assert_eq!(order, [1, 3, 2, 0]);
    for (_, value) in &mut rows {
        value.parameters[0] = closure(7);
    }
    stable_order(&rows, &mut order, IngressLimits::default(), &mut 0).unwrap();
    assert_eq!(order, [0, 1, 2, 3]);
    assert_eq!(order, reference_order(&rows));
}

#[test]
fn sorted_and_nearly_sorted_large_signatures_use_their_actual_bounded_work() {
    let mut rows: Vec<_> = (0..512)
        .map(|index| {
            let mut parameters = vec![ValueType::Nat; 8];
            parameters.push(closure(index));
            (Some(index as usize), signature(parameters, ValueType::Nat))
        })
        .collect();
    let mut order: Vec<_> = (0..rows.len()).collect();
    let original = order.clone();
    let mut visited = 0;
    let limits = IngressLimits {
        max_nodes: 6_000,
        ..IngressLimits::default()
    };
    stable_order(&rows, &mut order, limits, &mut visited).unwrap();
    assert_eq!(order, original);
    assert!(visited > 4_500 && visited < 6_000);
    // The former whole-table envelope alone was 51,200 nodes for these
    // signatures, even when the previous refinement had already sorted them.
    let legacy_envelope =
        rows.len() * (rows[0].1.parameters.len() + 1) * (rows.len().ilog2() as usize + 1);
    assert!(legacy_envelope > limits.max_nodes * 8);

    // A newly equal nested signature crosses only one old run boundary. The
    // complete ordering, including the original row tie, must still be found.
    rows[270].1.parameters[8] = closure(0);
    let mut visited = 0;
    stable_order(
        &rows,
        &mut order,
        IngressLimits {
            max_nodes: 15_000,
            ..IngressLimits::default()
        },
        &mut visited,
    )
    .unwrap();
    assert_eq!(order, reference_order(&rows));
    assert!(visited < 15_000);
}

#[test]
fn comparison_and_move_exhaustion_stop_before_publication_and_retry_exactly() {
    let rows = mixed_rows();
    let expected = reference_order(&rows);
    let mut initial: Vec<_> = (0..rows.len()).step_by(2).rev().collect();
    initial.extend((1..rows.len()).step_by(2));
    let mut successful = initial.clone();
    let mut total = 0;
    stable_order(&rows, &mut successful, IngressLimits::default(), &mut total).unwrap();
    assert_eq!(successful, expected);
    assert!(total > rows.len() * 2);

    for allowed in [0, 1, 17, total / 2, total - 1] {
        let mut order = initial.clone();
        let mut visited = 0;
        assert_eq!(
            stable_order(
                &rows,
                &mut order,
                IngressLimits {
                    max_nodes: allowed,
                    ..IngressLimits::default()
                },
                &mut visited,
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: allowed,
                observed: allowed + 1,
            })
        );
        assert_eq!(visited, allowed);
        let mut retained_rows = order.clone();
        retained_rows.sort_unstable();
        assert_eq!(retained_rows, (0..rows.len()).collect::<Vec<_>>());
        visited = 0;
        stable_order(&rows, &mut order, IngressLimits::default(), &mut visited).unwrap();
        assert_eq!(order, expected);
    }
}

fn legacy_ranks(interfaces: &[ClosureSignature]) -> Result<Vec<u32>, IngressError> {
    let limits = IngressLimits::default();
    let mut rows = Vec::new();
    for (index, value) in interfaces.iter().enumerate() {
        add_suffixes(&mut rows, value, Some(index), limits, &mut 0)?;
    }
    let mut ranks: Vec<_> = (0..interfaces.len() as u32).collect();
    for _ in 0..=interfaces.len() {
        let mut ordered = rows
            .iter()
            .map(|(owner, value)| Ok((*owner, remap_signature(value, &ranks)?)))
            .collect::<Result<Vec<_>, IngressError>>()?;
        ordered.sort_by(|(_, left), (_, right)| signature_order(left, right));
        let mut next = vec![0; ranks.len()];
        let mut rank = 0;
        for (index, (owner, value)) in ordered.iter().enumerate() {
            if index > 0 && value != &ordered[index - 1].1 {
                rank += 1;
            }
            if let Some(owner) = owner {
                next[*owner] = rank;
            }
        }
        if next == ranks {
            return Ok(ranks);
        }
        ranks = next;
    }
    Err(unsupported("cyclic callback signature ranks"))
}

#[test]
fn complete_nested_refinement_and_owner_ids_match_the_legacy_fixed_point() {
    let environment = Environment::new();
    let forward: Vec<_> = (0..24).collect();
    let reverse: Vec<_> = forward.iter().rev().copied().collect();
    let mut rotated = forward.clone();
    rotated.rotate_left(9);
    for discovery in [forward, reverse, rotated] {
        let source_id = |logical: usize| {
            closure(
                discovery
                    .iter()
                    .position(|&entry| entry == logical)
                    .unwrap() as u32,
            )
        };
        let interfaces: Vec<_> = discovery
            .iter()
            .map(|&logical| match logical {
                0 => signature(vec![ValueType::Nat], ValueType::Nat),
                1 => signature(vec![ValueType::String], ValueType::String),
                _ => {
                    let mut value = signature(
                        vec![ValueType::Bool, source_id((logical - 1) / 2)],
                        source_id(logical - 1),
                    );
                    if logical % 3 == 0 {
                        value.parameter_ownership[1] = ArgumentOwnership::Owned;
                    }
                    value
                }
            })
            .collect();
        let ranks = legacy_ranks(&interfaces).unwrap();
        let expected: Vec<_> = interfaces
            .iter()
            .map(|value| remap_signature(value, &ranks).unwrap())
            .collect();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        preparation.interfaces = interfaces;
        let actual = preparation.finalize_callables(&mut [], &mut []).unwrap();
        assert_eq!(actual, expected);
    }
}

#[test]
fn table_limits_unknown_nested_ids_and_nonsettling_cycles_keep_their_refusals() {
    let rows = mixed_rows();
    let mut order: Vec<_> = (0..rows.len()).collect();
    let original = order.clone();
    let mut limits = IngressLimits::default();
    limits.fir.max_closure_types = rows.len() - 1;
    assert_eq!(
        stable_order(&rows, &mut order, limits, &mut 0),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: rows.len() - 1,
            observed: rows.len(),
        })
    );
    assert_eq!(order, original);

    let environment = Environment::new();
    for interfaces in [
        vec![signature(vec![closure(99)], ValueType::Nat)],
        vec![
            signature(vec![closure(1)], ValueType::Nat),
            signature(vec![closure(0)], ValueType::Nat),
        ],
    ] {
        let expected = legacy_ranks(&interfaces).unwrap_err();
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        preparation.interfaces = interfaces;
        assert_eq!(
            preparation.finalize_callables(&mut [], &mut []),
            Err(expected)
        );
    }
}
