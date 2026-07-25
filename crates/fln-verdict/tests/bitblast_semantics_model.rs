//! Independent semantic model for the canonical bitblaster.
//!
//! The production encoder is not its own oracle. Each generated proposition is
//! evaluated here with direct small-width integer semantics, while the emitted CNF
//! is solved with every source input fixed. SAT models are checked against the CNF
//! and UNSAT proofs are replayed by Verdict's independent streaming checker.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln_verdict::{
    BitblastArtifact, BitblastInputKind, BitblastSymbol, BoolBinaryOp, BoolExpr, BvBinaryOp,
    BvComparison, BvExpr, BvShiftOp, BvUnaryOp, Clause, ClauseId, Cnf, InputClause, Literal,
    Polarity, ProofCheckLimits, ProofCheckOutcome, SchemaLimits, SolverLimits, SolverOutcome,
    bitblast, check_unsat_streams, solve,
};

const GENERATED_SEEDS: u64 = 256;

#[derive(Debug, Default)]
struct InputValues {
    boolean: BTreeMap<BitblastSymbol, bool>,
    bitvector: BTreeMap<BitblastSymbol, u64>,
}

impl InputValues {
    fn boolean(mut self, symbol: BitblastSymbol, value: bool) -> Self {
        self.boolean.insert(symbol, value);
        self
    }

    fn bitvector(mut self, symbol: BitblastSymbol, value: u64) -> Self {
        self.bitvector.insert(symbol, value);
        self
    }
}

#[derive(Debug, Clone, Copy)]
struct DeterministicRng {
    state: u64,
}

impl DeterministicRng {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.state
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }
}

fn symbol(raw: u32) -> BitblastSymbol {
    BitblastSymbol::new(raw).expect("test symbols are nonzero")
}

fn clause_id(raw: u64) -> ClauseId {
    ClauseId::new(raw).expect("test clause ids are nonzero")
}

fn constant(width: u32, value: u64) -> BvExpr {
    BvExpr::constant((0..width).map(|bit| value & (1_u64 << bit) != 0).collect())
}

fn mask(width: u32) -> u64 {
    match width {
        0 => 0,
        64.. => u64::MAX,
        width => (1_u64 << width) - 1,
    }
}

fn signed(width: u32, value: u64) -> i128 {
    if width == 0 {
        return 0;
    }
    let value = value & mask(width);
    let modulus = 1_i128 << width;
    if value & (1_u64 << (width - 1)) == 0 {
        i128::from(value)
    } else {
        i128::from(value) - modulus
    }
}

fn direct_binary(op: BvBinaryOp, width: u32, left: u64, right: u64) -> u64 {
    let width_mask = mask(width);
    match op {
        BvBinaryOp::And => left & right & width_mask,
        BvBinaryOp::Or => (left | right) & width_mask,
        BvBinaryOp::Xor => (left ^ right) & width_mask,
        BvBinaryOp::Add => left.wrapping_add(right) & width_mask,
        BvBinaryOp::Subtract => left.wrapping_sub(right) & width_mask,
        BvBinaryOp::Multiply => left.wrapping_mul(right) & width_mask,
    }
}

fn direct_unary(op: BvUnaryOp, width: u32, value: u64) -> u64 {
    let width_mask = mask(width);
    match op {
        BvUnaryOp::Not => !value & width_mask,
        BvUnaryOp::Negate => value.wrapping_neg() & width_mask,
    }
}

fn direct_shift(op: BvShiftOp, width: u32, value: u64, amount: u64) -> u64 {
    let width_mask = mask(width);
    if width == 0 {
        return 0;
    }
    if amount >= u64::from(width) {
        return match op {
            BvShiftOp::Left | BvShiftOp::LogicalRight => 0,
            BvShiftOp::ArithmeticRight => {
                if value & (1_u64 << (width - 1)) == 0 {
                    0
                } else {
                    width_mask
                }
            }
        };
    }
    let amount = u32::try_from(amount).expect("amount below width fits u32");
    match op {
        BvShiftOp::Left => value.checked_shl(amount).unwrap_or(0) & width_mask,
        BvShiftOp::LogicalRight => (value & width_mask).checked_shr(amount).unwrap_or(0),
        BvShiftOp::ArithmeticRight => {
            let shifted = signed(width, value) >> amount;
            (shifted as u64) & width_mask
        }
    }
}

fn direct_compare(op: BvComparison, width: u32, left: u64, right: u64) -> bool {
    let left = left & mask(width);
    let right = right & mask(width);
    match op {
        BvComparison::Equal => left == right,
        BvComparison::NotEqual => left != right,
        BvComparison::UnsignedLessThan => left < right,
        BvComparison::UnsignedLessOrEqual => left <= right,
        BvComparison::UnsignedGreaterThan => left > right,
        BvComparison::UnsignedGreaterOrEqual => left >= right,
        BvComparison::SignedLessThan => signed(width, left) < signed(width, right),
        BvComparison::SignedLessOrEqual => signed(width, left) <= signed(width, right),
        BvComparison::SignedGreaterThan => signed(width, left) > signed(width, right),
        BvComparison::SignedGreaterOrEqual => signed(width, left) >= signed(width, right),
    }
}

fn bound_cnf(artifact: &BitblastArtifact, values: &InputValues) -> Cnf {
    let mut clauses = artifact.cnf().clauses().to_vec();
    let mut next_id = clauses.last().map_or(1, |clause| {
        clause.id().get().checked_add(1).expect("test id space")
    });
    for binding in artifact.inputs() {
        match binding.kind() {
            BitblastInputKind::Boolean => {
                let value = values
                    .boolean
                    .get(&binding.symbol())
                    .copied()
                    .expect("Boolean input has an independent assignment");
                let variable = binding.variables_lsb_first()[0];
                clauses.push(InputClause::new(
                    clause_id(next_id),
                    Clause::new(vec![Literal::new(
                        variable,
                        if value {
                            Polarity::Positive
                        } else {
                            Polarity::Negative
                        },
                    )])
                    .expect("unit clause is canonical"),
                ));
                next_id += 1;
            }
            BitblastInputKind::Bitvector { width } => {
                let value = values
                    .bitvector
                    .get(&binding.symbol())
                    .copied()
                    .expect("bitvector input has an independent assignment");
                assert_eq!(
                    binding.variables_lsb_first().len(),
                    width as usize,
                    "input binding width must be exact"
                );
                for (bit, variable) in binding.variables_lsb_first().iter().copied().enumerate() {
                    let bit_is_set = value & (1_u64 << bit) != 0;
                    clauses.push(InputClause::new(
                        clause_id(next_id),
                        Clause::new(vec![Literal::new(
                            variable,
                            if bit_is_set {
                                Polarity::Positive
                            } else {
                                Polarity::Negative
                            },
                        )])
                        .expect("unit clause is canonical"),
                    ));
                    next_id += 1;
                }
            }
        }
    }
    Cnf::new(
        artifact.cnf().variable_count(),
        clauses,
        SchemaLimits::default(),
    )
    .expect("bound generated CNF is canonical")
}

fn is_conclusive(outcome: &SolverOutcome) -> bool {
    matches!(
        outcome,
        SolverOutcome::Sat { .. } | SolverOutcome::Unsat { .. }
    )
}

fn assert_matches_direct_model(seed: u64, expr: &BoolExpr, values: &InputValues, expected: bool) {
    let outcome = bitblast(expr, fln_verdict::BitblastLimits::default());
    let artifact = outcome
        .artifact()
        .expect("supported expression must produce a CNF");
    let formula = bound_cnf(artifact, values);
    let solver_outcome = solve(&formula, SolverLimits::default());
    assert!(
        is_conclusive(&solver_outcome),
        "seed 0x{seed:016x}: generated comparison did not produce a verdict: {solver_outcome:?}"
    );
    let checked = match solver_outcome {
        SolverOutcome::Sat { artifact, .. } => {
            assert_eq!(
                artifact.model().satisfies(&formula),
                Ok(true),
                "seed 0x{seed:016x}: SAT certificate does not satisfy bound CNF"
            );
            true
        }
        SolverOutcome::Unsat { artifact, .. } => {
            assert!(
                matches!(
                    check_unsat_streams(
                        artifact.cnf_bytes(),
                        artifact.proof_bytes(),
                        ProofCheckLimits::default()
                    ),
                    ProofCheckOutcome::Verified(_)
                ),
                "seed 0x{seed:016x}: independent checker refused UNSAT certificate"
            );
            false
        }
        SolverOutcome::Inconclusive { .. } | SolverOutcome::InternalFault { .. } => return,
    };
    assert_eq!(
        checked, expected,
        "seed 0x{seed:016x}: direct model and checked CNF disagree"
    );
}

#[test]
fn boolean_connectives_and_root_sign_match_direct_model() {
    let left_symbol = symbol(1);
    let right_symbol = symbol(2);
    let operations = [
        BoolBinaryOp::And,
        BoolBinaryOp::Or,
        BoolBinaryOp::Xor,
        BoolBinaryOp::Implication,
        BoolBinaryOp::Iff,
    ];
    for left in [false, true] {
        for right in [false, true] {
            for (index, operation) in operations.iter().copied().enumerate() {
                let expected = match operation {
                    BoolBinaryOp::And => left && right,
                    BoolBinaryOp::Or => left || right,
                    BoolBinaryOp::Xor => left ^ right,
                    BoolBinaryOp::Implication => !left || right,
                    BoolBinaryOp::Iff => left == right,
                };
                let expr = BoolExpr::binary(
                    operation,
                    BoolExpr::Input(left_symbol),
                    BoolExpr::Input(right_symbol),
                );
                let values = InputValues::default()
                    .boolean(left_symbol, left)
                    .boolean(right_symbol, right);
                assert_matches_direct_model(index as u64, &expr, &values, expected);
            }
        }
    }

    let input = BoolExpr::Input(left_symbol);
    assert_matches_direct_model(
        0x51_67_6e,
        &input,
        &InputValues::default().boolean(left_symbol, true),
        true,
    );
    assert_matches_direct_model(
        0x51_67_6f,
        &input,
        &InputValues::default().boolean(left_symbol, false),
        false,
    );
}

#[test]
fn generated_arithmetic_bitwise_and_shift_semantics_match_independent_model() {
    let left_symbol = symbol(11);
    let right_symbol = symbol(12);
    let amount_symbol = symbol(13);
    let widths = [0_u32, 1, 2, 3, 4, 5, 8];
    let binary_operations = [
        BvBinaryOp::And,
        BvBinaryOp::Or,
        BvBinaryOp::Xor,
        BvBinaryOp::Add,
        BvBinaryOp::Subtract,
        BvBinaryOp::Multiply,
    ];
    let unary_operations = [BvUnaryOp::Not, BvUnaryOp::Negate];
    let shift_operations = [
        BvShiftOp::Left,
        BvShiftOp::LogicalRight,
        BvShiftOp::ArithmeticRight,
    ];

    for seed in 0..GENERATED_SEEDS {
        let mut rng = DeterministicRng::new(seed ^ 0x8f3d_6c21_947a_e501);
        let width = widths[rng.below(widths.len() as u64) as usize];
        let left = rng.next() & mask(width);
        let right = rng.next() & mask(width);
        let amount = rng.below(20);
        let category = seed % 3;
        let (value_expr, expected) = match category {
            0 => {
                let operation =
                    binary_operations[rng.below(binary_operations.len() as u64) as usize];
                (
                    BvExpr::binary(
                        operation,
                        BvExpr::input(left_symbol, width),
                        BvExpr::input(right_symbol, width),
                    ),
                    direct_binary(operation, width, left, right),
                )
            }
            1 => {
                let operation = unary_operations[rng.below(unary_operations.len() as u64) as usize];
                (
                    BvExpr::unary(operation, BvExpr::input(left_symbol, width)),
                    direct_unary(operation, width, left),
                )
            }
            _ => {
                let operation = shift_operations[rng.below(shift_operations.len() as u64) as usize];
                (
                    BvExpr::shift(
                        operation,
                        BvExpr::input(left_symbol, width),
                        BvExpr::input(amount_symbol, 5),
                    ),
                    direct_shift(operation, width, left, amount),
                )
            }
        };
        let expr = BoolExpr::compare(
            BvComparison::Equal,
            value_expr.clone(),
            constant(width, expected),
        );
        let values = InputValues::default()
            .bitvector(left_symbol, left)
            .bitvector(right_symbol, right)
            .bitvector(amount_symbol, amount);
        assert_matches_direct_model(seed, &expr, &values, true);
        if width > 0 {
            let wrong = BoolExpr::compare(
                BvComparison::Equal,
                value_expr,
                constant(width, expected ^ 1),
            );
            assert_matches_direct_model(seed ^ 0xffff_ffff_0000_0000, &wrong, &values, false);
        }
    }
}

#[test]
fn every_signed_and_unsigned_comparison_matches_direct_model() {
    let left_symbol = symbol(21);
    let right_symbol = symbol(22);
    let operations = [
        BvComparison::Equal,
        BvComparison::NotEqual,
        BvComparison::UnsignedLessThan,
        BvComparison::UnsignedLessOrEqual,
        BvComparison::UnsignedGreaterThan,
        BvComparison::UnsignedGreaterOrEqual,
        BvComparison::SignedLessThan,
        BvComparison::SignedLessOrEqual,
        BvComparison::SignedGreaterThan,
        BvComparison::SignedGreaterOrEqual,
    ];
    let widths = [0_u32, 1, 2, 4, 8];
    for seed in 0..GENERATED_SEEDS {
        let mut rng = DeterministicRng::new(seed ^ 0x61a4_c8d9_b537_2ef0);
        let width = widths[rng.below(widths.len() as u64) as usize];
        let left = rng.next() & mask(width);
        let right = rng.next() & mask(width);
        let operation = operations[(seed as usize) % operations.len()];
        let expr = BoolExpr::compare(
            operation,
            BvExpr::input(left_symbol, width),
            BvExpr::input(right_symbol, width),
        );
        let values = InputValues::default()
            .bitvector(left_symbol, left)
            .bitvector(right_symbol, right);
        assert_matches_direct_model(
            seed ^ 0xc0_6d_70,
            &expr,
            &values,
            direct_compare(operation, width, left, right),
        );
    }
}

#[test]
fn wrong_bit_order_signedness_and_overflow_mutants_are_killed() {
    let value_symbol = symbol(31);
    let zero_symbol = symbol(32);

    let one_is_not_eight = BoolExpr::compare(
        BvComparison::NotEqual,
        BvExpr::input(value_symbol, 4),
        constant(4, 8),
    );
    assert_matches_direct_model(
        0xb170,
        &one_is_not_eight,
        &InputValues::default().bitvector(value_symbol, 1),
        true,
    );

    let signed_negative = BoolExpr::compare(
        BvComparison::SignedLessThan,
        BvExpr::input(value_symbol, 4),
        BvExpr::input(zero_symbol, 4),
    );
    let unsigned_negative = BoolExpr::compare(
        BvComparison::UnsignedLessThan,
        BvExpr::input(value_symbol, 4),
        BvExpr::input(zero_symbol, 4),
    );
    let signed_values = InputValues::default()
        .bitvector(value_symbol, 0b1111)
        .bitvector(zero_symbol, 0);
    assert_matches_direct_model(0x0005_19ed, &signed_negative, &signed_values, true);
    assert_matches_direct_model(0x0005_19ee, &unsigned_negative, &signed_values, false);

    for (seed, operation, left, right, expected) in [
        (0x0f10, BvBinaryOp::Add, 15, 1, 0),
        (0x0f11, BvBinaryOp::Subtract, 0, 1, 15),
        (0x0f12, BvBinaryOp::Multiply, 8, 2, 0),
        (0x0f13, BvBinaryOp::Multiply, 15, 15, 1),
    ] {
        let expr = BoolExpr::compare(
            BvComparison::Equal,
            BvExpr::binary(
                operation,
                BvExpr::input(value_symbol, 4),
                BvExpr::input(zero_symbol, 4),
            ),
            constant(4, expected),
        );
        let values = InputValues::default()
            .bitvector(value_symbol, left)
            .bitvector(zero_symbol, right);
        assert_matches_direct_model(seed, &expr, &values, true);
    }
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

#[test]
fn canonical_bytes_kill_clause_order_mutant_and_close_1_8_32_matrix() {
    let expr = BoolExpr::binary(
        BoolBinaryOp::Xor,
        BoolExpr::Input(symbol(1)),
        BoolExpr::Input(symbol(2)),
    );
    let baseline_outcome = bitblast(&expr, fln_verdict::BitblastLimits::default());
    let baseline = baseline_outcome
        .artifact()
        .expect("canonical XOR fixture must translate");
    let expected = baseline.cnf_bytes();
    assert_eq!(
        baseline
            .cnf()
            .clauses()
            .iter()
            .map(|clause| clause.id().get())
            .collect::<Vec<_>>(),
        vec![1, 2, 3, 4, 5],
        "clause ids must preserve fixed Tseitin emission order"
    );
    assert_eq!(
        hex(&expected),
        "464c4e5652444354010100000003000000050000000000000001000000000000000300000000000000010000000002000000000300000000020000000000000003000000000000000100000001020000000103000000000300000000000000030000000000000001000000010200000000030000000104000000000000000300000000000000010000000002000000010300000001050000000000000001000000000000000300000001",
        "the canonical fixture is a byte contract, not a regenerated expectation"
    );

    for workers in [1_usize, 8, 32] {
        let handles: Vec<_> = (0..workers)
            .map(|_| {
                let expr = expr.clone();
                std::thread::spawn(move || {
                    let outcome = bitblast(&expr, fln_verdict::BitblastLimits::default());
                    outcome.artifact().map(BitblastArtifact::cnf_bytes)
                })
            })
            .collect();
        for handle in handles {
            assert_eq!(
                handle
                    .join()
                    .expect("bitblast worker joins")
                    .expect("thread-matrix fixture must translate"),
                expected,
                "canonical CNF changed at worker count {workers}"
            );
        }
    }
}
