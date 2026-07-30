//! The type-model suite for the W5 dispatch foundation (bead
//! `franken_lean-pw6t`): the refusal algebra as *types*, not messages. Every
//! assertion names the exact expected variant and fields — an `is_err()`
//! anywhere a variant can be matched would be a vaguer contract than the one
//! `dispatch.rs` ships.
//!
//! Coverage:
//! 1. `DispatchRefusal` variant totality: exact fields, non-empty `Display`,
//!    `std::error::Error` implemented.
//! 2. The full registration state machine with the exact refusal at every
//!    illegal transition.
//! 3. Unknown-row resolve refusals for malformed ids.
//! 4. Closed-enum totality: every variant of `ExternKind`, `EffectClass`,
//!    `SafetyClass`, `PartitionClass`, `ModeSupport`, and `Ownership`
//!    round-trips `as_str` -> `parse`; unknown spellings are refused.
//! 5. Bijection accounting moves exactly with registrations.

#![forbid(unsafe_code)]

use fln_vm::dispatch::{
    BijectionReport, DispatchRefusal, IntrinsicImpl, IntrinsicRegistry, ResolveVerdict,
};
use fln_vm::extern_row::{
    EffectClass, ExternKind, ModeSupport, Ownership, PartitionClass, SafetyClass,
};
use fln_vm::extern_table_generated::{EXTERN_ROW_COUNT, EXTERN_ROWS};

/// A row id that exists in the generated table (verified below and at the top
/// of every fixture use — a guessed row would be a refusal, never a slot).
const ROW_NAT_ADD: &str = "extern:Nat.add";
const ROW_STRING_APPEND: &str = "extern:String.append";

fn nat_add_impl() -> IntrinsicImpl {
    IntrinsicImpl {
        row: ROW_NAT_ADD,
        name: "nat_add_intrinsic",
    }
}

fn string_append_impl() -> IntrinsicImpl {
    IntrinsicImpl {
        row: ROW_STRING_APPEND,
        name: "string_append_intrinsic",
    }
}

#[test]
fn fixture_rows_really_exist_in_the_generated_table() {
    let ids: Vec<&str> = EXTERN_ROWS.iter().map(|row| row.id).collect();
    assert_eq!(ids.len(), EXTERN_ROW_COUNT);
    assert!(
        ids.contains(&ROW_NAT_ADD),
        "fixture row {ROW_NAT_ADD} must exist in EXTERN_ROWS"
    );
    assert!(
        ids.contains(&ROW_STRING_APPEND),
        "fixture row {ROW_STRING_APPEND} must exist in EXTERN_ROWS"
    );
}

#[test]
fn refusal_variants_carry_their_exact_fields() {
    let unknown = DispatchRefusal::UnknownRow {
        row: "extern:No.Such.Row".to_string(),
    };
    match &unknown {
        DispatchRefusal::UnknownRow { row } => assert_eq!(row, "extern:No.Such.Row"),
        other => panic!("expected UnknownRow, got {other:?}"),
    }

    let duplicate = DispatchRefusal::Duplicate {
        row: ROW_NAT_ADD.to_string(),
        existing: "nat_add_intrinsic".to_string(),
        attempted: "nat_add_intrinsic_v2".to_string(),
    };
    match &duplicate {
        DispatchRefusal::Duplicate {
            row,
            existing,
            attempted,
        } => {
            assert_eq!(row, ROW_NAT_ADD);
            assert_eq!(existing, "nat_add_intrinsic");
            assert_eq!(attempted, "nat_add_intrinsic_v2");
        }
        other => panic!("expected Duplicate, got {other:?}"),
    }

    let not_registered = DispatchRefusal::NotRegistered {
        row: ROW_STRING_APPEND.to_string(),
    };
    match &not_registered {
        DispatchRefusal::NotRegistered { row } => assert_eq!(row, ROW_STRING_APPEND),
        other => panic!("expected NotRegistered, got {other:?}"),
    }
}

#[test]
fn refusal_display_is_non_empty_and_names_the_row() {
    let cases: Vec<(DispatchRefusal, &str)> = vec![
        (
            DispatchRefusal::UnknownRow {
                row: "extern:No.Such.Row".to_string(),
            },
            "extern:No.Such.Row",
        ),
        (
            DispatchRefusal::Duplicate {
                row: ROW_NAT_ADD.to_string(),
                existing: "nat_add_intrinsic".to_string(),
                attempted: "nat_add_intrinsic_v2".to_string(),
            },
            ROW_NAT_ADD,
        ),
        (
            DispatchRefusal::NotRegistered {
                row: ROW_STRING_APPEND.to_string(),
            },
            ROW_STRING_APPEND,
        ),
    ];
    for (refusal, row) in &cases {
        let rendered = refusal.to_string();
        assert!(
            !rendered.is_empty(),
            "Display must not be empty: {refusal:?}"
        );
        assert!(
            rendered.contains(row),
            "Display of {refusal:?} must name the row {row:?}, got {rendered:?}"
        );
    }
    // The Duplicate report also names both contestants, per its doc contract.
    let duplicate = DispatchRefusal::Duplicate {
        row: ROW_NAT_ADD.to_string(),
        existing: "nat_add_intrinsic".to_string(),
        attempted: "nat_add_intrinsic_v2".to_string(),
    };
    let rendered = duplicate.to_string();
    assert!(rendered.contains("nat_add_intrinsic"));
    assert!(rendered.contains("nat_add_intrinsic_v2"));
}

#[test]
fn refusal_implements_std_error() {
    let refusals = [
        DispatchRefusal::UnknownRow {
            row: "extern:No.Such.Row".to_string(),
        },
        DispatchRefusal::Duplicate {
            row: ROW_NAT_ADD.to_string(),
            existing: "nat_add_intrinsic".to_string(),
            attempted: "nat_add_intrinsic_v2".to_string(),
        },
        DispatchRefusal::NotRegistered {
            row: ROW_STRING_APPEND.to_string(),
        },
    ];
    for refusal in &refusals {
        let as_error: &dyn std::error::Error = refusal;
        assert!(!as_error.to_string().is_empty());
        assert!(
            as_error.source().is_none(),
            "leaf refusal has no source: {refusal:?}"
        );
    }
}

#[test]
fn registration_state_machine_refuses_every_illegal_transition() {
    let mut registry = IntrinsicRegistry::new();
    assert_eq!(registry.registered_count(), 0);

    // Fresh table: the fixture row resolves as an honest absence.
    let verdict = registry.resolve(ROW_NAT_ADD);
    assert!(
        matches!(verdict, Ok(ResolveVerdict::NotImplemented)),
        "unregistered in-table row must be NotImplemented, got {verdict:?}"
    );

    // Register occupies the slot; resolve hands back the exact impl.
    registry
        .register(nat_add_impl())
        .expect("first registration of an in-table row must succeed");
    assert_eq!(registry.registered_count(), 1);
    match registry.resolve(ROW_NAT_ADD) {
        Ok(ResolveVerdict::Resolved(implementation)) => {
            assert_eq!(
                *implementation,
                IntrinsicImpl {
                    row: ROW_NAT_ADD,
                    name: "nat_add_intrinsic",
                }
            );
        }
        other => panic!("registered row must resolve Resolved, got {other:?}"),
    }

    // Duplicate registration is refused with both names spelled out.
    let attempted = IntrinsicImpl {
        row: ROW_NAT_ADD,
        name: "nat_add_intrinsic_v2",
    };
    let refusal = registry.register(attempted);
    assert_eq!(
        refusal,
        Err(DispatchRefusal::Duplicate {
            row: ROW_NAT_ADD.to_string(),
            existing: "nat_add_intrinsic".to_string(),
            attempted: "nat_add_intrinsic_v2".to_string(),
        })
    );
    // A refused duplicate never displaces the slot holder.
    assert_eq!(registry.registered_count(), 1);
    match registry.resolve(ROW_NAT_ADD) {
        Ok(ResolveVerdict::Resolved(implementation)) => {
            assert_eq!(implementation.name, "nat_add_intrinsic");
        }
        other => panic!("slot holder must survive a refused duplicate, got {other:?}"),
    }

    // Unregister frees the slot and returns the impl that held it.
    let removed = registry.unregister(ROW_NAT_ADD);
    assert_eq!(removed, Ok(nat_add_impl()));
    assert_eq!(registry.registered_count(), 0);
    let verdict = registry.resolve(ROW_NAT_ADD);
    assert!(
        matches!(verdict, Ok(ResolveVerdict::NotImplemented)),
        "freed slot must be NotImplemented, got {verdict:?}"
    );

    // Unregistering an empty in-table slot is a typed NotRegistered refusal.
    let refusal = registry.unregister(ROW_NAT_ADD);
    assert_eq!(
        refusal,
        Err(DispatchRefusal::NotRegistered {
            row: ROW_NAT_ADD.to_string(),
        })
    );

    // Re-registration after unregister is legal and audible as a pair.
    registry
        .register(nat_add_impl())
        .expect("re-registration after unregister must succeed");
    assert_eq!(registry.registered_count(), 1);
    let removed = registry.unregister(ROW_NAT_ADD);
    assert_eq!(removed, Ok(nat_add_impl()));
    assert_eq!(registry.registered_count(), 0);
}

#[test]
fn unregister_of_an_unknown_row_is_an_unknown_row_refusal() {
    let mut registry = IntrinsicRegistry::new();
    let refusal = registry.unregister("extern:No.Such.Row");
    assert_eq!(
        refusal,
        Err(DispatchRefusal::UnknownRow {
            row: "extern:No.Such.Row".to_string(),
        })
    );
    // Unknown-row refusal wins over the empty-slot question: the id is not
    // even in the table, so NotRegistered never applies.
    let mut registry = IntrinsicRegistry::new();
    registry
        .register(nat_add_impl())
        .expect("fixture registration must succeed");
    let refusal = registry.unregister("Nat.add");
    assert_eq!(
        refusal,
        Err(DispatchRefusal::UnknownRow {
            row: "Nat.add".to_string(),
        })
    );
}

#[test]
fn resolve_refuses_malformed_ids_as_unknown_row() {
    let registry = IntrinsicRegistry::new();
    let malformed = ["", "extern:", "extern:No.Such.Row", "Nat.add"];
    for id in malformed {
        let verdict = registry.resolve(id);
        assert_eq!(
            verdict,
            Err(DispatchRefusal::UnknownRow {
                row: id.to_string()
            }),
            "resolve({id:?}) must be Err(UnknownRow) naming the id exactly"
        );
    }
}

#[test]
fn register_refuses_an_unknown_row_before_any_slot_question() {
    let mut registry = IntrinsicRegistry::new();
    let refusal = registry.register(IntrinsicImpl {
        row: "extern:No.Such.Row",
        name: "ghost_impl",
    });
    assert_eq!(
        refusal,
        Err(DispatchRefusal::UnknownRow {
            row: "extern:No.Such.Row".to_string(),
        })
    );
    assert_eq!(registry.registered_count(), 0);
}

#[test]
fn extern_kind_round_trips_and_refuses_unknown() {
    let variants = [
        ExternKind::Defn,
        ExternKind::Opaque,
        ExternKind::Ctor,
        ExternKind::Axiom,
    ];
    for variant in variants {
        let parsed = ExternKind::parse(variant.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", variant.as_str()));
        assert_eq!(parsed, variant);
    }
    // as_str values are distinct — no two variants share a spelling.
    let spellings: Vec<&str> = variants.iter().map(|variant| variant.as_str()).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }
    for unknown in ["", "def", "Defn", "DEFN", "opaque ", "constructor"] {
        assert!(
            ExternKind::parse(unknown).is_err(),
            "ExternKind::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn effect_class_round_trips_and_refuses_unknown() {
    let variants = [
        EffectClass::Pure,
        EffectClass::ToolchainMonad,
        EffectClass::Io,
        EffectClass::MonadTransformer,
        EffectClass::Task,
        EffectClass::State,
        EffectClass::Effect,
    ];
    for variant in variants {
        let parsed = EffectClass::parse(variant.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", variant.as_str()));
        assert_eq!(parsed, variant);
    }
    let spellings: Vec<&str> = variants.iter().map(|variant| variant.as_str()).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }
    for unknown in ["", "purely", "Pure", "IO", "monad", " side-effect "] {
        assert!(
            EffectClass::parse(unknown).is_err(),
            "EffectClass::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn safety_class_round_trips_and_refuses_unknown() {
    let variants = [SafetyClass::Safe, SafetyClass::Partial, SafetyClass::Unsafe];
    for variant in variants {
        let parsed = SafetyClass::parse(variant.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", variant.as_str()));
        assert_eq!(parsed, variant);
    }
    let spellings: Vec<&str> = variants.iter().map(|variant| variant.as_str()).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }
    for unknown in ["", "Safe", "safer", "UNSAFE", "trusted"] {
        assert!(
            SafetyClass::parse(unknown).is_err(),
            "SafetyClass::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn partition_class_round_trips_and_refuses_unknown() {
    let variants = [
        PartitionClass::ToolchainApi,
        PartitionClass::LibraryCode,
        PartitionClass::UserFacingData,
    ];
    for variant in variants {
        let parsed = PartitionClass::parse(variant.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", variant.as_str()));
        assert_eq!(parsed, variant);
    }
    let spellings: Vec<&str> = variants.iter().map(|variant| variant.as_str()).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }
    for unknown in ["", "toolchain", "ToolchainApi", "library", "user-data"] {
        assert!(
            PartitionClass::parse(unknown).is_err(),
            "PartitionClass::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn mode_support_round_trips_and_refuses_unknown() {
    let variants = [ModeSupport::All, ModeSupport::Frontier];
    for variant in variants {
        let parsed = ModeSupport::parse(variant.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", variant.as_str()));
        assert_eq!(parsed, variant);
    }
    let spellings: Vec<&str> = variants.iter().map(|variant| variant.as_str()).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }
    for unknown in ["", "All", "ALL", "sovereign", " frontier"] {
        assert!(
            ModeSupport::parse(unknown).is_err(),
            "ModeSupport::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn ownership_accepts_every_rule_form_and_passes_abi_signatures_through() {
    let rules = [
        Ownership::DefaultRuleOwnedResult,
        Ownership::DefaultRuleBorrowedResult,
        Ownership::ScalarRule,
        Ownership::LlvmCApi,
    ];
    for rule in &rules {
        let parsed = Ownership::parse(&rule.as_str())
            .unwrap_or_else(|error| panic!("parse({:?}) must succeed: {error}", rule.as_str()));
        assert_eq!(&parsed, rule);
    }
    // Rule spellings are distinct from each other.
    let spellings: Vec<String> = rules.iter().map(Ownership::as_str).collect();
    for (index, spelling) in spellings.iter().enumerate() {
        assert!(!spellings[..index].contains(spelling));
    }

    // abi(...) is a passthrough: the signature inside the parens is carried
    // verbatim, and as_str re-frames it exactly.
    let signature = "borrowed,borrowed,owned";
    let parsed = Ownership::parse("abi(borrowed,borrowed,owned)")
        .expect("a non-empty abi() signature must parse");
    assert_eq!(parsed, Ownership::AbiSignature(signature.to_string()));
    assert_eq!(parsed.as_str(), "abi(borrowed,borrowed,owned)");
    // An abi signature round-trips through as_str -> parse.
    let round_tripped = Ownership::parse(&parsed.as_str()).expect("abi as_str must re-parse");
    assert_eq!(round_tripped, parsed);
    // Signatures with interior parens-adjacent content are carried as-is.
    let exotic = Ownership::parse("abi(x:y,z)").expect("non-empty abi payload must parse");
    assert_eq!(exotic, Ownership::AbiSignature("x:y,z".to_string()));
}

#[test]
fn ownership_refuses_empty_abi_and_unknown_forms() {
    let empty = Ownership::parse("abi()");
    assert!(
        empty.is_err(),
        "empty abi() ownership signature must be refused"
    );
    for unknown in [
        "",
        "abi",
        "abi(",
        "abi",
        "rule()",
        "rule(borrowed-args)",
        "rule(owned-args,owned-result)",
        "borrowed-args,owned-result",
        "ABI(owned)",
    ] {
        assert!(
            Ownership::parse(unknown).is_err(),
            "Ownership::parse({unknown:?}) must be refused"
        );
    }
}

#[test]
fn bijection_accounting_moves_exactly_with_registrations() {
    let mut registry = IntrinsicRegistry::new();

    // Empty registry: every row is the families' work queue; no orphan impls.
    let report = registry.bijection();
    assert_eq!(report.rows_without_impls.len(), EXTERN_ROW_COUNT);
    assert!(report.impls_without_rows.is_empty());
    assert!(report.rows_without_impls.contains(&ROW_NAT_ADD.to_string()));
    assert!(
        report
            .rows_without_impls
            .contains(&ROW_STRING_APPEND.to_string())
    );

    // One registration removes exactly that row from the queue.
    registry
        .register(nat_add_impl())
        .expect("fixture registration must succeed");
    let report = registry.bijection();
    assert_eq!(report.rows_without_impls.len(), EXTERN_ROW_COUNT - 1);
    assert!(!report.rows_without_impls.contains(&ROW_NAT_ADD.to_string()));
    assert!(
        report
            .rows_without_impls
            .contains(&ROW_STRING_APPEND.to_string())
    );
    assert!(report.impls_without_rows.is_empty());

    // A second registration removes exactly one more.
    registry
        .register(string_append_impl())
        .expect("fixture registration must succeed");
    let report = registry.bijection();
    assert_eq!(report.rows_without_impls.len(), EXTERN_ROW_COUNT - 2);
    assert!(!report.rows_without_impls.contains(&ROW_NAT_ADD.to_string()));
    assert!(
        !report
            .rows_without_impls
            .contains(&ROW_STRING_APPEND.to_string())
    );
    assert!(report.impls_without_rows.is_empty());

    // Unregistering returns exactly that row to the queue.
    registry
        .unregister(ROW_NAT_ADD)
        .expect("unregister of a registered row must succeed");
    let report = registry.bijection();
    assert_eq!(report.rows_without_impls.len(), EXTERN_ROW_COUNT - 1);
    assert!(report.rows_without_impls.contains(&ROW_NAT_ADD.to_string()));
    assert!(
        !report
            .rows_without_impls
            .contains(&ROW_STRING_APPEND.to_string())
    );
    assert!(report.impls_without_rows.is_empty());

    // impls_without_rows is structurally empty by construction (registration
    // refuses unknown rows); the default report agrees.
    assert_eq!(
        BijectionReport::default(),
        BijectionReport {
            rows_without_impls: Vec::new(),
            impls_without_rows: Vec::new(),
        }
    );
}
