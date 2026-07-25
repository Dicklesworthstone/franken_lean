//! Closed supported/refused contract tests for Verdict bitblasting.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use fln_verdict::{
    BITBLAST_MANIFEST, BITBLAST_MANIFEST_ID, BITBLAST_MANIFEST_ROWS, BITBLAST_MANIFEST_VERSION,
    BitblastConstruct, BitblastInconclusive, BitblastInputKind, BitblastLimits, BitblastOutcome,
    BitblastRefusal, BitblastResource, BitblastSupport, BitblastSymbol, BoolBinaryOp, BoolExpr,
    BvComparison, BvExpr, CANONICAL_BITBLAST_POLICY, CANONICAL_BITBLAST_POLICY_ID, UnsupportedBvOp,
    bitblast, bitblast_with_cancel,
};

fn symbol(raw: u32) -> BitblastSymbol {
    BitblastSymbol::new(raw).expect("test symbols are nonzero")
}

fn zero(width: u32) -> BvExpr {
    BvExpr::constant(vec![false; width as usize])
}

#[test]
fn manifest_v1_is_complete_unique_and_byte_semantics_are_explicit() {
    assert_eq!(BITBLAST_MANIFEST.id, BITBLAST_MANIFEST_ID);
    assert_eq!(BITBLAST_MANIFEST.version, BITBLAST_MANIFEST_VERSION);
    assert_eq!(BITBLAST_MANIFEST.version, 1);
    assert_eq!(BITBLAST_MANIFEST.policy_id, CANONICAL_BITBLAST_POLICY_ID);
    assert_eq!(
        BITBLAST_MANIFEST.width_semantics,
        "all widths from zero through the explicit operation budget; operands requiring equality must have exactly equal widths"
    );
    assert_eq!(
        BITBLAST_MANIFEST.bit_order,
        "bit index zero and serialized input position zero are least significant"
    );
    assert_eq!(
        BITBLAST_MANIFEST.overflow_semantics,
        "negation, addition, subtraction, and multiplication are modulo 2^width; width zero has the unique empty value"
    );
    assert_eq!(
        BITBLAST_MANIFEST.signed_semantics,
        "signed comparisons use width-indexed two's-complement interpretation; unsigned comparisons use natural binary interpretation"
    );
    assert_eq!(
        BITBLAST_MANIFEST.shift_semantics,
        "shift amounts are unsigned bitvectors; amounts at least the value width saturate to the operation's documented fill"
    );
    assert_eq!(
        CANONICAL_BITBLAST_POLICY.traversal_order,
        "depth-first-left-to-right-after-whole-tree-manifest-preflight"
    );
    assert_eq!(
        CANONICAL_BITBLAST_POLICY.input_bit_order,
        "least-significant-bit-first"
    );

    let expected = [
        BitblastConstruct::BooleanConstant,
        BitblastConstruct::BooleanInput,
        BitblastConstruct::BooleanNot,
        BitblastConstruct::BooleanAnd,
        BitblastConstruct::BooleanOr,
        BitblastConstruct::BooleanXor,
        BitblastConstruct::BooleanImplication,
        BitblastConstruct::BooleanIff,
        BitblastConstruct::BitvectorConstant,
        BitblastConstruct::BitvectorInput,
        BitblastConstruct::BitwiseNot,
        BitblastConstruct::BitwiseAnd,
        BitblastConstruct::BitwiseOr,
        BitblastConstruct::BitwiseXor,
        BitblastConstruct::TwosComplementNegation,
        BitblastConstruct::WrappingAddition,
        BitblastConstruct::WrappingSubtraction,
        BitblastConstruct::WrappingMultiplication,
        BitblastConstruct::ShiftLeft,
        BitblastConstruct::LogicalShiftRight,
        BitblastConstruct::ArithmeticShiftRight,
        BitblastConstruct::Equality,
        BitblastConstruct::Inequality,
        BitblastConstruct::UnsignedLessThan,
        BitblastConstruct::UnsignedLessOrEqual,
        BitblastConstruct::UnsignedGreaterThan,
        BitblastConstruct::UnsignedGreaterOrEqual,
        BitblastConstruct::SignedLessThan,
        BitblastConstruct::SignedLessOrEqual,
        BitblastConstruct::SignedGreaterThan,
        BitblastConstruct::SignedGreaterOrEqual,
        BitblastConstruct::RotateLeft,
        BitblastConstruct::RotateRight,
        BitblastConstruct::UnsignedDivision,
        BitblastConstruct::UnsignedRemainder,
        BitblastConstruct::SignedDivision,
        BitblastConstruct::SignedRemainder,
        BitblastConstruct::Concatenation,
        BitblastConstruct::Extraction,
        BitblastConstruct::ZeroExtension,
        BitblastConstruct::SignExtension,
    ];
    assert_eq!(BITBLAST_MANIFEST_ROWS.len(), expected.len());
    assert_eq!(
        BITBLAST_MANIFEST_ROWS
            .iter()
            .map(|row| row.construct)
            .collect::<Vec<_>>(),
        expected
    );
    assert_eq!(
        BITBLAST_MANIFEST_ROWS
            .iter()
            .map(|row| row.construct)
            .collect::<BTreeSet<_>>()
            .len(),
        expected.len(),
        "a construct must have exactly one manifest row"
    );
    assert!(
        BITBLAST_MANIFEST_ROWS
            .iter()
            .all(|row| !row.semantics.is_empty()),
        "every support decision must state its semantics"
    );
    assert_eq!(
        BITBLAST_MANIFEST_ROWS
            .iter()
            .filter(|row| row.support == BitblastSupport::Supported)
            .count(),
        31
    );
    assert_eq!(
        BITBLAST_MANIFEST_ROWS
            .iter()
            .filter(|row| matches!(row.support, BitblastSupport::Refused { .. }))
            .count(),
        UnsupportedBvOp::ALL.len()
    );
}

#[test]
fn every_refused_construct_is_rejected_even_in_a_dead_boolean_branch() {
    for operation in UnsupportedBvOp::ALL {
        let construct = operation.construct();
        let row = BITBLAST_MANIFEST
            .row(construct)
            .expect("every unsupported operation has a manifest row");
        assert!(
            matches!(row.support, BitblastSupport::Refused { .. }),
            "{construct:?} was accidentally promoted to supported"
        );
        let BitblastSupport::Refused { code } = row.support else {
            continue;
        };
        let dead_branch = BoolExpr::binary(
            BoolBinaryOp::And,
            BoolExpr::Constant(false),
            BoolExpr::compare(
                BvComparison::Equal,
                BvExpr::unsupported(operation, 4),
                zero(4),
            ),
        );
        let outcome = bitblast(&dead_branch, BitblastLimits::default());
        assert_eq!(
            outcome,
            BitblastOutcome::Refused(BitblastRefusal::UnsupportedConstruct {
                construct,
                reason_code: code,
            }),
            "{construct:?} must be refused before Boolean simplification"
        );
        assert!(
            outcome.artifact().is_none(),
            "a refused construct must publish no CNF"
        );
    }
}

#[test]
fn width_and_source_symbol_mismatches_are_typed_refusals() {
    let width_mismatch = BoolExpr::compare(
        BvComparison::Equal,
        BvExpr::input(symbol(1), 4),
        BvExpr::input(symbol(2), 5),
    );
    assert_eq!(
        bitblast(&width_mismatch, BitblastLimits::default()),
        BitblastOutcome::Refused(BitblastRefusal::WidthMismatch {
            construct: BitblastConstruct::Equality,
            left: 4,
            right: 5,
        })
    );

    let kind_conflict = BoolExpr::binary(
        BoolBinaryOp::And,
        BoolExpr::Input(symbol(3)),
        BoolExpr::compare(BvComparison::Equal, BvExpr::input(symbol(3), 1), zero(1)),
    );
    assert_eq!(
        bitblast(&kind_conflict, BitblastLimits::default()),
        BitblastOutcome::Refused(BitblastRefusal::InputKindConflict {
            symbol: symbol(3),
            first: BitblastInputKind::Boolean,
            later: BitblastInputKind::Bitvector { width: 1 },
        })
    );

    let width_reuse = BoolExpr::binary(
        BoolBinaryOp::And,
        BoolExpr::compare(BvComparison::Equal, BvExpr::input(symbol(4), 1), zero(1)),
        BoolExpr::compare(BvComparison::Equal, BvExpr::input(symbol(4), 2), zero(2)),
    );
    assert_eq!(
        bitblast(&width_reuse, BitblastLimits::default()),
        BitblastOutcome::Refused(BitblastRefusal::InputKindConflict {
            symbol: symbol(4),
            first: BitblastInputKind::Bitvector { width: 1 },
            later: BitblastInputKind::Bitvector { width: 2 },
        })
    );
}

#[test]
fn zero_width_is_supported_and_boundaries_are_explicit() {
    let equality = BoolExpr::compare(BvComparison::Equal, zero(0), zero(0));
    let equality_outcome = bitblast(&equality, BitblastLimits::default());
    let artifact = equality_outcome
        .artifact()
        .expect("zero-width equality is in the supported manifest");
    assert_eq!(artifact.cnf().variable_count(), 0);
    assert!(artifact.cnf().clauses().is_empty());
    assert_eq!(artifact.manifest_id(), BITBLAST_MANIFEST_ID);
    assert_eq!(artifact.manifest_version(), BITBLAST_MANIFEST_VERSION);
    assert_eq!(artifact.policy_id(), CANONICAL_BITBLAST_POLICY_ID);
    assert_eq!(artifact.facts().encoded_bytes, 25);

    let signed_less = BoolExpr::compare(BvComparison::SignedLessThan, zero(0), zero(0));
    let signed_outcome = bitblast(&signed_less, BitblastLimits::default());
    let artifact = signed_outcome
        .artifact()
        .expect("zero-width signed comparison is supported");
    assert_eq!(artifact.cnf().clauses().len(), 1);
    assert!(artifact.cnf().clauses()[0].clause().is_empty());
}

#[test]
fn cancellation_and_every_exhaustion_class_are_non_artifact_outcomes() {
    let expression = BoolExpr::binary(
        BoolBinaryOp::Xor,
        BoolExpr::Input(symbol(10)),
        BoolExpr::Input(symbol(11)),
    );

    let cancelled = bitblast_with_cancel(&expression, BitblastLimits::default(), || true);
    assert_eq!(
        cancelled,
        BitblastOutcome::Inconclusive(BitblastInconclusive::Cancelled)
    );
    assert!(cancelled.artifact().is_none());

    let no_work = bitblast(
        &expression,
        BitblastLimits {
            max_work_units: 0,
            ..BitblastLimits::default()
        },
    );
    assert!(matches!(
        no_work,
        BitblastOutcome::Inconclusive(BitblastInconclusive::ResourceExhausted {
            resource: BitblastResource::WorkUnits,
            limit: 0,
            ..
        })
    ));
    assert!(no_work.artifact().is_none());

    let no_clauses = bitblast(
        &expression,
        BitblastLimits {
            max_clauses: 0,
            ..BitblastLimits::default()
        },
    );
    assert!(matches!(
        no_clauses,
        BitblastOutcome::Inconclusive(BitblastInconclusive::ResourceExhausted {
            resource: BitblastResource::Clauses,
            limit: 0,
            ..
        })
    ));
    assert!(no_clauses.artifact().is_none());

    let too_wide = BoolExpr::compare(BvComparison::Equal, BvExpr::input(symbol(12), 33), zero(33));
    let width_limited = bitblast(
        &too_wide,
        BitblastLimits {
            max_width: 32,
            ..BitblastLimits::default()
        },
    );
    assert_eq!(
        width_limited,
        BitblastOutcome::Inconclusive(BitblastInconclusive::ResourceExhausted {
            resource: BitblastResource::Width,
            limit: 32,
            actual: 33,
        })
    );
    assert!(width_limited.artifact().is_none());

    let mut deep = BoolExpr::Constant(true);
    for _ in 0..64 {
        deep = BoolExpr::logical_not(deep);
    }
    let depth_limited = bitblast(
        &deep,
        BitblastLimits {
            max_depth: 32,
            ..BitblastLimits::default()
        },
    );
    assert!(matches!(
        depth_limited,
        BitblastOutcome::Inconclusive(BitblastInconclusive::ResourceExhausted {
            resource: BitblastResource::Depth,
            limit: 32,
            actual: 33,
        })
    ));
    assert!(depth_limited.artifact().is_none());
}
