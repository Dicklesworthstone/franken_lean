use super::*;
use fln_core::{expr::Expr, level::Level};
use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints, TheoremVal};
fn name(s: &str) -> Name {
    Name::from_components([s])
}

// Codec fixtures only; declaration admission is exercised by engine tests.
fn environment() -> Environment {
    let mut env = Environment::new();
    for n in [name("origin"), name("data")] {
        env = env
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n.clone(),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n],
            }))
            .unwrap();
    }
    for n in [
        name("first"),
        name("second"),
        Name::str(Name::num(name("private"), 7), "proof"),
        Name::from_components(["private", "7", "proof"]),
    ] {
        env = env
            .add_decl(ConstantInfo::Thm(TheoremVal {
                base: ConstantVal {
                    name: n.clone(),
                    level_params: vec![],
                    type_: Expr::sort(Level::zero()),
                },
                value: Expr::sort(Level::zero()),
                all: vec![n],
            }))
            .unwrap();
    }
    env
}
fn proof(s: &str, priority: u32) -> ImportedSimpRule {
    ImportedSimpRule::Proof {
        origin: name("origin"),
        proof: name(s),
        priority,
    }
}
#[test]
fn legacy_and_structural_rows_keep_exact_bytes_beside_auxiliary_proofs() {
    let textual = Name::from_components(["private", "7", "proof"]);
    let numeric = Name::str(Name::num(name("private"), 7), "proof");
    let old = append(
        &environment(),
        source_payload(&textual, Some((500, false))).unwrap(),
    )
    .unwrap();
    let old = append(&old, source_payload(&numeric, Some((700, false))).unwrap()).unwrap();
    let before: Vec<_> = old
        .extension(&descriptor().name)
        .unwrap()
        .entries()
        .map(|r| r.payload.clone())
        .collect();
    assert!(before[0].starts_with(MAGIC));
    assert!(before[1].starts_with(STRUCTURAL_MAGIC));
    let both = register_imported_proof(&old, &name("origin"), &numeric, 1000).unwrap();
    assert_eq!(read(&both).unwrap()[0].proof, Some(numeric));
    let after: Vec<_> = both
        .extension(&descriptor().name)
        .unwrap()
        .entries()
        .map(|r| r.payload.clone())
        .collect();
    assert_eq!(&after[..2], &before);
    assert!(after[2].starts_with(PROOF_MAGIC));
    assert_eq!(
        read(&update(&both, &name("origin"), None).unwrap()).unwrap(),
        read(&old).unwrap()
    );
}
#[test]
fn multiple_proofs_share_erasure_but_not_evidence_identity() {
    let both = import_rules(
        &environment(),
        &[proof("first", 900), proof("second", 1000)],
    )
    .unwrap();
    let rows = read(&both).unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].proof, Some(name("second")));
    assert!(
        rows.iter()
            .all(|r| r.declaration == name("origin") && !r.reverse)
    );
    let changed = read(&update(&both, &name("origin"), Some((1000, false))).unwrap()).unwrap();
    assert_eq!(changed.len(), 1);
    assert_eq!(changed[0].proof, None);
    assert!(
        read(&update(&both, &name("origin"), None).unwrap())
            .unwrap()
            .is_empty()
    );
    assert_eq!(read(&both).unwrap(), rows);
}

#[test]
fn equation_origins_and_unfolding_coexist_with_independent_erasure() {
    let env = environment();
    let first = ImportedSimpRule::Proof {
        origin: name("first"),
        proof: name("first"),
        priority: 900,
    };
    let second = ImportedSimpRule::Proof {
        origin: name("second"),
        proof: name("second"),
        priority: 900,
    };
    let association = ImportedSimpRule::UnfoldTheorems {
        declaration: name("origin"),
        theorems: vec![name("first"), name("second")],
    };
    let unfolding = ImportedSimpRule::Unfold {
        declaration: name("origin"),
    };
    let operations = [first.clone(), second, association, unfolding];
    let registered = import_rules(&env, &operations).unwrap();
    let rows = read(&registered).unwrap();
    assert_eq!(rows.len(), 3);
    assert_eq!(rows[0].declaration, name("origin"));
    assert_eq!(rows[0].proof, None);
    assert_eq!(rows[1].declaration, name("second"));
    assert_eq!(rows[2].declaration, name("first"));

    let one_erased = update(&registered, &name("first"), None).unwrap();
    let remaining = read(&one_erased).unwrap();
    assert_eq!(remaining.len(), 2);
    assert!(
        remaining
            .iter()
            .any(|row| row.declaration == name("origin"))
    );
    assert!(
        remaining
            .iter()
            .any(|row| row.declaration == name("second"))
    );
    let all_erased = update(&one_erased, &name("origin"), None).unwrap();
    assert!(read(&all_erased).unwrap().is_empty());

    // The pin retains the association after erasure. Even with no active
    // unfolding, erasing the parent again must erase a re-added equation.
    let readded = import_rules(&all_erased, &[first]).unwrap();
    assert_eq!(read(&readded).unwrap().len(), 1);
    assert!(
        read(&update(&readded, &name("origin"), None).unwrap())
            .unwrap()
            .is_empty()
    );
    let repeated = import_rules(&registered, &operations).unwrap();
    assert_eq!(read(&repeated).unwrap().len(), 3);
    assert_eq!(
        repeated.extension(&descriptor().name).unwrap().len(),
        operations.len() * 2
    );
    assert_eq!(read(&registered).unwrap(), rows);
}

#[test]
fn association_alone_preserves_theorems_and_erases_without_an_unfold_entry() {
    let selected =
        register_imported_proof(&environment(), &name("first"), &name("first"), 700).unwrap();
    let associated =
        register_unfold_theorems(&selected, &name("origin"), &[name("first")]).unwrap();
    assert_eq!(read(&selected).unwrap(), read(&associated).unwrap());
    assert!(
        read(&update(&associated, &name("origin"), None).unwrap())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn malformed_or_unavailable_equation_associations_fail_without_a_prefix() {
    let env = environment().register_extension(descriptor()).unwrap();
    let payload = unfold_theorems_payload(&name("origin"), &[name("first")]).unwrap();
    for end in 0..payload.len() {
        let broken = env
            .push_extension_entry(&descriptor().name, payload[..end].to_vec())
            .unwrap();
        assert!(read(&broken).is_err(), "association prefix {end}");
    }
    let mut trailing = payload.clone();
    trailing.push(0);
    let mut bad_operation = payload;
    bad_operation[UNFOLD_THEOREMS_MAGIC.len()] = 2;
    for malformed in [trailing, bad_operation] {
        let broken = env
            .push_extension_entry(&descriptor().name, malformed)
            .unwrap();
        assert_eq!(read(&broken), Err(SimpSetError::Malformed));
    }
    for theorem in [name("missing"), name("data")] {
        assert!(
            import_rules(
                &env,
                &[
                    proof("first", 900),
                    ImportedSimpRule::UnfoldTheorems {
                        declaration: name("origin"),
                        theorems: vec![theorem],
                    },
                ],
            )
            .is_err()
        );
    }
    assert!(read(&env).unwrap().is_empty());
    assert_eq!(
        unfold_theorems_payload(&Name::anonymous(), &[]),
        Err(SimpSetError::Malformed)
    );
    assert_eq!(
        unfold_theorems_payload(&name("origin"), &vec![name("first"); MAX_BYTES]),
        Err(SimpSetError::Limit)
    );
}
#[test]
fn redundant_import_events_survive_a_different_replay_context() {
    let env = environment();
    let first = import_rules(&env, &[proof("first", 1000)]).unwrap();
    let duplicate = import_rules(&first, &[proof("first", 1000)]).unwrap();
    let events: Vec<_> = duplicate
        .extension(&descriptor().name)
        .unwrap()
        .entries()
        .map(|r| r.payload.clone())
        .collect();
    assert_eq!(events.len(), 2);
    let erased = update(&first, &name("origin"), None).unwrap();
    let replayed = erased
        .push_extension_entry(&descriptor().name, events[1].to_vec())
        .unwrap();
    assert_eq!(read(&replayed).unwrap().len(), 1);
    let withdrawal = import_rules(
        &env,
        &[ImportedSimpRule::Erase {
            declaration: name("origin"),
        }],
    )
    .unwrap();
    let row = withdrawal
        .extension(&descriptor().name)
        .unwrap()
        .entries()
        .next()
        .unwrap()
        .payload
        .clone();
    assert!(
        read(
            &first
                .push_extension_entry(&descriptor().name, row.to_vec())
                .unwrap()
        )
        .unwrap()
        .is_empty()
    );
}
#[test]
fn truncated_corrupt_and_twice_reversed_proofs_are_not_defaults() {
    let env = environment().register_extension(descriptor()).unwrap();
    let payload = proof_payload(&name("origin"), &name("first"), 1000).unwrap();
    for end in 0..payload.len() {
        let broken = env
            .push_extension_entry(&descriptor().name, payload[..end].to_vec())
            .unwrap();
        assert!(read(&broken).is_err(), "prefix {end}");
    }
    for index in [PROOF_MAGIC.len(), payload.len() - 1] {
        let mut broken = payload.clone();
        broken[index] = 1;
        assert_eq!(
            read(
                &env.push_extension_entry(&descriptor().name, broken)
                    .unwrap()
            ),
            Err(SimpSetError::Malformed)
        );
    }
    let mut trailing = payload;
    trailing.push(0);
    assert_eq!(
        read(
            &env.push_extension_entry(&descriptor().name, trailing)
                .unwrap()
        ),
        Err(SimpSetError::Malformed)
    );
}
#[test]
fn missing_or_data_valued_proofs_fail_atomically() {
    let env = environment();
    for (origin, proof_name) in [
        ("missing", "first"),
        ("origin", "missing"),
        ("origin", "data"),
    ] {
        assert!(
            import_rules(
                &env,
                &[
                    proof("first", 1000),
                    ImportedSimpRule::Proof {
                        origin: name(origin),
                        proof: name(proof_name),
                        priority: 1000
                    }
                ]
            )
            .is_err()
        );
        assert!(read(&env).unwrap().is_empty());
    }
    assert_eq!(
        proof_payload(&Name::anonymous(), &name("first"), 1),
        Err(SimpSetError::Malformed)
    );
    let huge = Name::str(name("private"), "x".repeat(MAX_BYTES));
    assert_eq!(
        proof_payload(&huge, &name("first"), 1),
        Err(SimpSetError::Limit)
    );
}
#[test]
fn imported_population_is_not_limited_by_one_proofs_traversal_fuel() {
    let env = environment();
    let population = 4_097;
    let full = import_rules(&env, &vec![proof("first", 1); population]).unwrap();
    let rows = read(&full).unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].order, population - 1);
    let next = import_rules(&full, &[proof("second", 2)]).unwrap();
    let next_rows = read(&next).unwrap();
    assert_eq!(next_rows.len(), 2);
    assert_eq!(next_rows[0].proof, Some(name("second")));
    assert_eq!(next_rows[0].order, population);
    let journal = next.extension(&descriptor().name).unwrap();
    assert_eq!(
        journal.payload_bytes(),
        journal
            .entries()
            .map(|row| row.payload.len() as u128)
            .sum::<u128>()
    );
    assert_eq!(read(&full).unwrap(), rows);
    assert!(env.extension(&descriptor().name).is_none());
}

#[test]
fn journal_bytes_and_entry_handles_share_a_checked_aggregate_bound() {
    let remaining = MAX_JOURNAL_BYTES - ENTRY_ACCOUNTING_BYTES;
    assert_eq!(check_journal_capacity(1, remaining), Ok(()));
    assert_eq!(
        check_journal_capacity(1, remaining + 1),
        Err(SimpSetError::Limit)
    );
    assert_eq!(
        check_journal_capacity(2, remaining),
        Err(SimpSetError::Limit)
    );
    assert_eq!(
        check_journal_capacity(1, u128::MAX),
        Err(SimpSetError::Limit)
    );
}

#[test]
fn imported_population_does_not_increase_proof_shape_fuel() {
    use fln_core::expr::BinderInfo;
    let mut ty = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
                Expr::sort(Level::zero()),
            ),
            Expr::sort(Level::zero()),
        ),
        Expr::sort(Level::zero()),
    );
    for _ in 0..4_096 {
        ty = Expr::forall_e(
            name("x"),
            Expr::sort(Level::zero()),
            ty,
            BinderInfo::Default,
        );
    }
    let long = name("long");
    let env = environment()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: long.clone(),
                level_params: vec![],
                type_: ty,
            },
            value: Expr::sort(Level::zero()),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![long.clone()],
        }))
        .unwrap();
    assert_eq!(validate_proof(&env, &long), Err(SimpSetError::Limit));
    assert!(env.extension(&descriptor().name).is_none());
}
