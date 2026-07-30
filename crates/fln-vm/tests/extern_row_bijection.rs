//! `extern_row_bijection` — the registry mechanics and the row/implementation
//! bijection accounting, over the REAL generated table (bead `franken_lean-pw6t`).
//!
//! The bijection law has two directions and both are asserted, never inferred
//! from one: every table row without an implementation is named in
//! `rows_without_impls` (the families' work queue), and every registered
//! implementation resolves to a real table row (`impls_without_rows` is empty
//! by construction — registration refuses unknown rows — and the assertion
//! exists so a future hole is loud). Fixture registrations move the accounting
//! by exactly their count, and removing them moves it back exactly.

#![forbid(unsafe_code)]

use fln_vm::dispatch::{DispatchRefusal, IntrinsicImpl, IntrinsicRegistry, ResolveVerdict};
use fln_vm::extern_table_generated::{EXTERN_ROW_COUNT, EXTERN_ROWS};

/// Fixture implementations over rows that really exist in the table.
fn fixture_impls() -> [IntrinsicImpl; 4] {
    [
        IntrinsicImpl {
            row: "extern:Nat.add",
            name: "fixture-nat-add",
        },
        IntrinsicImpl {
            row: "extern:String.append",
            name: "fixture-string-append",
        },
        IntrinsicImpl {
            row: "extern:Array.size",
            name: "fixture-array-size",
        },
        IntrinsicImpl {
            row: "extern:IO.getStdin",
            name: "fixture-io-get-stdin",
        },
    ]
}

#[test]
fn the_fixture_rows_exist_in_the_real_table() {
    // The whole battery rests on fixture rows; a census edit that removes one
    // must fail here, loudly, rather than silently vacating every cell below.
    for implementation in fixture_impls() {
        assert!(
            EXTERN_ROWS.iter().any(|row| row.id == implementation.row),
            "fixture row {} is absent from the generated table",
            implementation.row
        );
    }
    assert_eq!(
        EXTERN_ROWS.len(),
        EXTERN_ROW_COUNT,
        "the generated table's length and its declared count must agree"
    );
}

#[test]
fn an_empty_registry_accounts_every_row_and_no_impls() {
    let registry = IntrinsicRegistry::new();
    let report = registry.bijection();
    assert_eq!(
        report.rows_without_impls.len(),
        EXTERN_ROW_COUNT,
        "an empty registry owes every row an implementation"
    );
    assert!(
        report.impls_without_rows.is_empty(),
        "nothing is registered, so nothing can dangle"
    );
    assert_eq!(registry.registered_count(), 0);
}

#[test]
fn registrations_move_the_accounting_exactly_in_both_directions() {
    let mut registry = IntrinsicRegistry::new();
    let fixtures = fixture_impls();
    for (index, implementation) in fixtures.iter().enumerate() {
        registry
            .register(*implementation)
            .expect("fixture registration must succeed");
        let report = registry.bijection();
        assert_eq!(
            report.rows_without_impls.len(),
            EXTERN_ROW_COUNT - (index + 1),
            "each registration retires exactly one row from the queue"
        );
        assert!(
            !report
                .rows_without_impls
                .contains(&implementation.row.to_string()),
            "a registered row must leave the work queue"
        );
        assert!(report.impls_without_rows.is_empty());
    }
    assert_eq!(registry.registered_count(), fixtures.len());

    for (index, implementation) in fixtures.iter().enumerate() {
        let removed = registry
            .unregister(implementation.row)
            .expect("unregistering a held slot must succeed");
        assert_eq!(removed.name, implementation.name);
        let report = registry.bijection();
        assert_eq!(
            report.rows_without_impls.len(),
            EXTERN_ROW_COUNT - fixtures.len() + (index + 1),
            "each unregister returns exactly one row to the queue"
        );
        assert!(
            report
                .rows_without_impls
                .contains(&implementation.row.to_string()),
            "an unregistered row must rejoin the work queue"
        );
    }
    assert_eq!(registry.registered_count(), 0);
}

#[test]
fn duplicate_registration_is_refused_with_both_names() {
    let mut registry = IntrinsicRegistry::new();
    let first = fixture_impls()[0];
    registry.register(first).expect("first registration");
    let attempted = IntrinsicImpl {
        row: first.row,
        name: "fixture-nat-add-shadow",
    };
    let refusal = registry
        .register(attempted)
        .expect_err("a second registration on one slot must refuse");
    assert_eq!(
        refusal,
        DispatchRefusal::Duplicate {
            row: first.row.to_string(),
            existing: first.name.to_string(),
            attempted: attempted.name.to_string(),
        },
        "the refusal must name the row, the holder, and the attempt"
    );
    // The holder is undisturbed: duplicate refusal is a refusal, not a swap.
    assert_eq!(
        registry.resolve(first.row),
        Ok(ResolveVerdict::Resolved(&first)),
    );
}

#[test]
fn unknown_rows_are_refused_at_every_surface() {
    let mut registry = IntrinsicRegistry::new();
    for bad in [
        "",
        "extern:",
        "extern:No.Such.Row",
        "Nat.add",
        "extern:nat.add",
    ] {
        let refusal = registry
            .register(IntrinsicImpl {
                row: bad,
                name: "fixture-bad",
            })
            .expect_err("an unknown row id must be refused at registration");
        assert_eq!(
            refusal,
            DispatchRefusal::UnknownRow {
                row: bad.to_string()
            }
        );
        assert_eq!(
            registry.resolve(bad),
            Err(DispatchRefusal::UnknownRow {
                row: bad.to_string()
            }),
            "resolve must refuse the same id the same way"
        );
        assert_eq!(
            registry.unregister(bad),
            Err(DispatchRefusal::UnknownRow {
                row: bad.to_string()
            }),
            "unregister must refuse the same id the same way"
        );
    }
    assert_eq!(registry.registered_count(), 0);
}

#[test]
fn resolve_distinguishes_absent_from_unimplemented() {
    let mut registry = IntrinsicRegistry::new();
    let fixture = fixture_impls()[0];
    assert_eq!(
        registry.resolve(fixture.row),
        Ok(ResolveVerdict::NotImplemented),
        "a real row with no implementation is NotImplemented, the families' to fill"
    );
    registry.register(fixture).expect("register fixture");
    assert_eq!(
        registry.resolve(fixture.row),
        Ok(ResolveVerdict::Resolved(&fixture)),
    );
}

#[test]
fn unregistering_an_empty_slot_is_a_typed_refusal_not_a_noop() {
    let mut registry = IntrinsicRegistry::new();
    let fixture = fixture_impls()[0];
    assert_eq!(
        registry.unregister(fixture.row),
        Err(DispatchRefusal::NotRegistered {
            row: fixture.row.to_string()
        }),
        "a balance bug in the caller must surface as a typed refusal"
    );
    registry.register(fixture).expect("register");
    registry.unregister(fixture.row).expect("unregister");
    assert_eq!(
        registry.unregister(fixture.row),
        Err(DispatchRefusal::NotRegistered {
            row: fixture.row.to_string()
        }),
        "a double-unregister must refuse, not report success"
    );
}

#[test]
fn replacement_is_an_auditable_unregister_register_pair() {
    let mut registry = IntrinsicRegistry::new();
    let fixture = fixture_impls()[0];
    let shadow = IntrinsicImpl {
        row: fixture.row,
        name: "fixture-nat-add-v2",
    };
    registry.register(fixture).expect("register");
    registry
        .register(shadow)
        .expect_err("the occupied slot refuses a silent swap");
    let removed = registry.unregister(fixture.row).expect("explicit removal");
    assert_eq!(removed.name, fixture.name);
    registry
        .register(shadow)
        .expect("the vacated slot accepts the replacement");
    assert_eq!(
        registry.resolve(fixture.row),
        Ok(ResolveVerdict::Resolved(&shadow)),
        "the replacement, and only the replacement, holds the slot"
    );
}
