//! Deterministic metamorphic campaign for the public Verdict trust boundary.
//!
//! The solver is not its own oracle. Every result admitted to a relation below
//! first carries independently checkable evidence: SAT model bytes are decoded
//! and evaluated against the exact CNF, while UNSAT proof bytes are replayed by
//! the independent streaming checker.

use fln_verdict::{
    Assignment, Clause, ClauseId, Cnf, InputClause, Literal, Polarity, ProofCheckLimits,
    ProofCheckOutcome, SatModel, SchemaLimits, SolverLimits, SolverOutcome, VariableId,
    check_unsat_streams, solve, solve_with_cancel,
};
use std::collections::BTreeSet;

const LAW_COUNT: usize = 6;
const CASES_PER_LAW: u64 = 128;
const CERTIFICATE_CHECKED_LAWS: usize = 6;
const SELF_CONSISTENCY_ONLY_LAWS: usize = 0;
const EXPECTED_VIOLATIONS: u64 = 0;

// Relation strength matrix. Score = fault sensitivity * oracle independence / cost.
//
// relation                         category       sensitivity independence cost score
// bijective variable renaming      permutative        3            3        2     4
// clause and literal ordering      permutative        2            3        1     6
// subsumed-clause addition         inclusive          3            3        2     4
// satisfying-model blocking        exclusive          3            3        2     4
// unit and pure preprocessing      equivalence        3            3        3     3
// minimal UNSAT core subsets       reductive           3            3        3     3
//
// All selected relations score at least two, span five categories, use generated
// inputs, and include two compositions: rename+reorder and unit+pure preprocessing.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CertifiedKind {
    Sat,
    Unsat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ComparisonStop {
    Inconclusive,
    InternalFault,
}

#[derive(Debug)]
enum Certified<'a> {
    Sat(&'a SatModel),
    Unsat,
}

impl Certified<'_> {
    const fn kind(&self) -> CertifiedKind {
        match self {
            Self::Sat(_) => CertifiedKind::Sat,
            Self::Unsat => CertifiedKind::Unsat,
        }
    }
}

fn certify<'a>(formula: &Cnf, outcome: &'a SolverOutcome) -> Result<Certified<'a>, ComparisonStop> {
    match outcome {
        SolverOutcome::Sat { artifact, .. } => {
            assert_eq!(
                artifact.cnf_bytes(),
                formula.to_canonical_bytes(),
                "SAT artifact must bind the exact transformed formula"
            );
            let decoded =
                SatModel::from_canonical_bytes(artifact.model_bytes(), SchemaLimits::default())
                    .expect("published SAT model bytes must decode canonically");
            assert_eq!(
                &decoded,
                artifact.model(),
                "published SAT bytes and typed artifact diverged"
            );
            assert!(
                independently_satisfies(&decoded, formula),
                "SAT certificate does not satisfy its exact formula"
            );
            Ok(Certified::Sat(artifact.model()))
        }
        SolverOutcome::Unsat { artifact, .. } => {
            assert_eq!(
                artifact.cnf_bytes(),
                formula.to_canonical_bytes(),
                "UNSAT artifact must bind the exact transformed formula"
            );
            assert!(
                matches!(
                    check_unsat_streams(
                        artifact.cnf_bytes(),
                        artifact.proof_bytes(),
                        ProofCheckLimits::default()
                    ),
                    ProofCheckOutcome::Verified(_)
                ),
                "independent streaming checker refused an emitted proof"
            );
            Ok(Certified::Unsat)
        }
        SolverOutcome::Inconclusive { .. } => Err(ComparisonStop::Inconclusive),
        SolverOutcome::InternalFault { .. } => Err(ComparisonStop::InternalFault),
    }
}

fn must_certify<'a>(
    law: &str,
    case_index: u64,
    formula: &Cnf,
    outcome: &'a SolverOutcome,
) -> Certified<'a> {
    match certify(formula, outcome) {
        Ok(certified) => certified,
        Err(stop) => {
            panic!("{law} case {case_index} produced non-comparable outcome {stop:?}")
        }
    }
}

fn compare_checked(
    left_formula: &Cnf,
    left: &SolverOutcome,
    right_formula: &Cnf,
    right: &SolverOutcome,
) -> Result<bool, ComparisonStop> {
    Ok(certify(left_formula, left)?.kind() == certify(right_formula, right)?.kind())
}

fn variable(raw: u32) -> VariableId {
    VariableId::new(raw).expect("generated variable ids are non-zero")
}

fn clause_id(raw: u64) -> ClauseId {
    ClauseId::new(raw).expect("generated clause ids are non-zero")
}

fn literal(raw: i64) -> Literal {
    Literal::from_dimacs(raw).expect("generated DIMACS literals are valid")
}

fn clause(values: &[i64]) -> Clause {
    Clause::new(values.iter().copied().map(literal).collect())
        .expect("generated clauses are non-tautological")
}

fn formula_from_clauses(variable_count: u32, clauses: Vec<Clause>) -> Cnf {
    let inputs = clauses
        .into_iter()
        .enumerate()
        .map(|(index, clause)| InputClause::new(clause_id(index as u64 + 1), clause))
        .collect();
    formula_from_inputs(variable_count, inputs)
}

fn formula_from_inputs(variable_count: u32, inputs: Vec<InputClause>) -> Cnf {
    Cnf::new(variable_count, inputs, SchemaLimits::default())
        .expect("generated formula is schema-valid")
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
        assert!(bound > 0, "generated range must be non-empty");
        self.next() % bound
    }

    fn shuffle<T>(&mut self, values: &mut [T]) {
        for end in (1..values.len()).rev() {
            let selected = self.below((end + 1) as u64) as usize;
            values.swap(end, selected);
        }
    }
}

fn literal_is_true(literal: Literal, values: &[bool]) -> bool {
    let value = values[literal.variable().get() as usize];
    match literal.polarity() {
        Polarity::Negative => !value,
        Polarity::Positive => value,
    }
}

fn independently_satisfies(model: &SatModel, formula: &Cnf) -> bool {
    model.variable_count() == formula.variable_count()
        && formula.clauses().iter().all(|input| {
            input.clause().literals().iter().copied().any(|literal| {
                model
                    .assignments()
                    .iter()
                    .copied()
                    .find(|assignment| assignment.variable() == literal.variable())
                    .is_some_and(|assignment| {
                        assignment_satisfies_literal(assignment.value(), literal)
                    })
            })
        })
}

fn generated_formula(case_index: u64, rng: &mut DeterministicRng, force_satisfiable: bool) -> Cnf {
    let variable_count = 2 + rng.below(5) as u32;
    let mut witness = vec![false; variable_count as usize + 1];
    for raw in 1..=variable_count {
        witness[raw as usize] = rng.next() & 1 != 0;
    }

    let row_count = 3 + rng.below(6) as usize;
    let mut rows = Vec::with_capacity(row_count + 2);
    for _ in 0..row_count {
        let max_width = usize::min(3, variable_count as usize - 1);
        let width = 1 + rng.below(max_width as u64) as usize;
        let mut selected = BTreeSet::new();
        while selected.len() < width {
            selected.insert(1 + rng.below(u64::from(variable_count)) as u32);
        }

        let mut literals = selected
            .into_iter()
            .map(|raw| {
                Literal::new(
                    variable(raw),
                    if rng.next() & 1 == 0 {
                        Polarity::Negative
                    } else {
                        Polarity::Positive
                    },
                )
            })
            .collect::<Vec<_>>();
        if !literals
            .iter()
            .copied()
            .any(|candidate| literal_is_true(candidate, &witness))
        {
            let raw = literals[0].variable().get();
            literals[0] = Literal::new(
                variable(raw),
                if witness[raw as usize] {
                    Polarity::Positive
                } else {
                    Polarity::Negative
                },
            );
        }
        rows.push(Clause::new(literals).expect("generated witness clause"));
    }

    if !force_satisfiable && case_index % 2 == 1 {
        rows.push(clause(&[1]));
        rows.push(clause(&[-1]));
    }
    formula_from_clauses(variable_count, rows)
}

fn non_identity_bijection(variable_count: u32, rng: &mut DeterministicRng) -> Vec<u32> {
    let mut mapping = (1..=variable_count).collect::<Vec<_>>();
    rng.shuffle(&mut mapping);
    if mapping.iter().copied().eq(1..=variable_count) {
        mapping.rotate_left(1);
    }
    mapping
}

fn rename_formula(formula: &Cnf, mapping: &[u32]) -> Cnf {
    assert_eq!(mapping.len(), formula.variable_count() as usize);
    let inputs = formula
        .clauses()
        .iter()
        .map(|input| {
            let literals = input
                .clause()
                .literals()
                .iter()
                .copied()
                .map(|source| {
                    let target = mapping[source.variable().get() as usize - 1];
                    Literal::new(variable(target), source.polarity())
                })
                .collect();
            InputClause::new(
                input.id(),
                Clause::new(literals).expect("bijection preserves non-tautology"),
            )
        })
        .collect();
    formula_from_inputs(formula.variable_count(), inputs)
}

fn reorder_formula(formula: &Cnf, rng: &mut DeterministicRng) -> Cnf {
    let mut inputs = formula
        .clauses()
        .iter()
        .map(|input| {
            let mut literals = input.clause().literals().to_vec();
            rng.shuffle(&mut literals);
            InputClause::new(
                input.id(),
                Clause::new(literals).expect("literal permutation preserves the clause"),
            )
        })
        .collect::<Vec<_>>();
    rng.shuffle(&mut inputs);
    formula_from_inputs(formula.variable_count(), inputs)
}

fn map_renamed_model_back(model: &SatModel, mapping: &[u32]) -> SatModel {
    let assignments = mapping
        .iter()
        .copied()
        .enumerate()
        .map(|(source_index, target)| {
            Assignment::new(
                variable(source_index as u32 + 1),
                model
                    .value(variable(target))
                    .expect("renamed model is complete"),
            )
        })
        .collect();
    SatModel::new(model.variable_count(), assignments, SchemaLimits::default())
        .expect("inverse-renamed model is canonical")
}

fn artifact_bytes(outcome: &SolverOutcome) -> &[u8] {
    match outcome {
        SolverOutcome::Sat { artifact, .. } => artifact.model_bytes(),
        SolverOutcome::Unsat { artifact, .. } => artifact.proof_bytes(),
        SolverOutcome::Inconclusive { .. } | SolverOutcome::InternalFault { .. } => {
            panic!("non-verdict has no semantic artifact bytes")
        }
    }
}

#[test]
fn bijective_variable_renaming_preserves_certified_verdict_and_maps_models_back() {
    let mut rng = DeterministicRng::new(0xa0d3_f762_15ce_49b1);
    for case_index in 0..CASES_PER_LAW {
        let original = generated_formula(case_index, &mut rng, false);
        let mapping = non_identity_bijection(original.variable_count(), &mut rng);
        let renamed = rename_formula(&original, &mapping);
        let composed = reorder_formula(&renamed, &mut rng);

        let original_outcome = solve(&original, SolverLimits::default());
        let renamed_outcome = solve(&renamed, SolverLimits::default());
        let composed_outcome = solve(&composed, SolverLimits::default());
        let original_certified = must_certify(
            "variable-renaming",
            case_index,
            &original,
            &original_outcome,
        );
        let renamed_certified =
            must_certify("variable-renaming", case_index, &renamed, &renamed_outcome);
        let composed_certified = must_certify(
            "rename-then-reorder",
            case_index,
            &composed,
            &composed_outcome,
        );

        assert_eq!(original_certified.kind(), renamed_certified.kind());
        assert_eq!(original_certified.kind(), composed_certified.kind());
        if let Certified::Sat(model) = renamed_certified {
            let mapped_back = map_renamed_model_back(model, &mapping);
            assert!(
                independently_satisfies(&mapped_back, &original),
                "renamed SAT model did not map back in case {case_index}"
            );
        }
        if let Certified::Sat(model) = composed_certified {
            let mapped_back = map_renamed_model_back(model, &mapping);
            assert!(
                independently_satisfies(&mapped_back, &original),
                "composed SAT model did not map back in case {case_index}"
            );
        }
    }
}

#[test]
fn clause_and_literal_order_preserve_certified_verdict_and_artifact_bytes() {
    let mut rng = DeterministicRng::new(0x65c1_8e90_b742_ad3f);
    for case_index in 0..CASES_PER_LAW {
        let original = generated_formula(case_index, &mut rng, false);
        let reordered = reorder_formula(&original, &mut rng);
        assert_eq!(
            original.to_canonical_bytes(),
            reordered.to_canonical_bytes(),
            "canonical formula drifted under ordering in case {case_index}"
        );

        let original_outcome = solve(&original, SolverLimits::default());
        let reordered_outcome = solve(&reordered, SolverLimits::default());
        let original_certified = must_certify("ordering", case_index, &original, &original_outcome);
        let reordered_certified =
            must_certify("ordering", case_index, &reordered, &reordered_outcome);
        assert_eq!(original_certified.kind(), reordered_certified.kind());
        assert_eq!(
            artifact_bytes(&original_outcome),
            artifact_bytes(&reordered_outcome),
            "deterministic artifact drifted under ordering in case {case_index}"
        );
    }
}

fn add_subsumed_clause(formula: &Cnf, rng: &mut DeterministicRng) -> Cnf {
    let basis = formula
        .clauses()
        .first()
        .expect("generated formula has a basis clause")
        .clause();
    let used = basis
        .literals()
        .iter()
        .map(|literal| literal.variable().get())
        .collect::<BTreeSet<_>>();
    let extra = (1..=formula.variable_count())
        .find(|raw| !used.contains(raw))
        .expect("generated basis leaves a variable for strict subsumption");
    let mut literals = basis.literals().to_vec();
    literals.push(Literal::new(
        variable(extra),
        if rng.next() & 1 == 0 {
            Polarity::Negative
        } else {
            Polarity::Positive
        },
    ));
    let added = Clause::new(literals).expect("strictly subsumed clause");
    assert!(
        basis
            .literals()
            .iter()
            .all(|literal| added.literals().contains(literal))
    );
    assert!(added.literals().len() > basis.literals().len());

    let mut inputs = formula.clauses().to_vec();
    let next_id = inputs
        .iter()
        .map(|input| input.id().get())
        .max()
        .expect("generated formula has clause ids")
        + 1;
    inputs.push(InputClause::new(clause_id(next_id), added));
    formula_from_inputs(formula.variable_count(), inputs)
}

#[test]
fn adding_a_strictly_subsumed_clause_preserves_the_certified_verdict() {
    let mut rng = DeterministicRng::new(0x2fb7_4c18_93da_60e5);
    for case_index in 0..CASES_PER_LAW {
        let original = generated_formula(case_index, &mut rng, false);
        let extended = add_subsumed_clause(&original, &mut rng);
        let original_outcome = solve(&original, SolverLimits::default());
        let extended_outcome = solve(&extended, SolverLimits::default());
        let original_certified =
            must_certify("subsumption", case_index, &original, &original_outcome);
        let extended_certified =
            must_certify("subsumption", case_index, &extended, &extended_outcome);
        assert_eq!(original_certified.kind(), extended_certified.kind());
    }
}

fn block_model(formula: &Cnf, model: &SatModel) -> Cnf {
    let blocking = model
        .assignments()
        .iter()
        .copied()
        .map(|assignment| {
            Literal::new(
                assignment.variable(),
                if assignment.value() {
                    Polarity::Negative
                } else {
                    Polarity::Positive
                },
            )
        })
        .collect();
    let blocking = Clause::new(blocking).expect("complete model blocking clause");
    let mut inputs = formula.clauses().to_vec();
    let next_id = inputs
        .iter()
        .map(|input| input.id().get())
        .max()
        .unwrap_or(0)
        + 1;
    inputs.push(InputClause::new(clause_id(next_id), blocking));
    formula_from_inputs(formula.variable_count(), inputs)
}

#[test]
fn blocking_a_satisfying_model_yields_unsat_or_a_different_checked_model() {
    let mut rng = DeterministicRng::new(0xde61_03b8_7ac4_f925);
    for case_index in 0..CASES_PER_LAW {
        let original = generated_formula(case_index, &mut rng, true);
        let original_outcome = solve(&original, SolverLimits::default());
        let Certified::Sat(original_model) =
            must_certify("model-blocking", case_index, &original, &original_outcome)
        else {
            panic!("generated model-blocking source case {case_index} was not SAT");
        };
        let blocked = block_model(&original, original_model);
        let blocked_outcome = solve(&blocked, SolverLimits::default());
        match must_certify("model-blocking", case_index, &blocked, &blocked_outcome) {
            Certified::Unsat => {}
            Certified::Sat(next_model) => {
                assert!(
                    original_model
                        .assignments()
                        .iter()
                        .zip(next_model.assignments())
                        .any(|(before, after)| before.value() != after.value()),
                    "blocking clause admitted the same model in case {case_index}"
                );
                assert!(independently_satisfies(next_model, &blocked));
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum PreprocessMode {
    Units,
    Pure,
    UnitsAndPure,
}

impl PreprocessMode {
    const fn units(self) -> bool {
        matches!(self, Self::Units | Self::UnitsAndPure)
    }

    const fn pure(self) -> bool {
        matches!(self, Self::Pure | Self::UnitsAndPure)
    }
}

#[derive(Debug)]
struct Preprocessed {
    formula: Cnf,
    fixed: Vec<Option<bool>>,
    unit_assignments: u64,
    pure_assignments: u64,
}

fn assignment_satisfies_literal(value: bool, literal: Literal) -> bool {
    match literal.polarity() {
        Polarity::Negative => !value,
        Polarity::Positive => value,
    }
}

fn conflict_formula(variable_count: u32) -> Cnf {
    formula_from_clauses(
        variable_count,
        vec![Clause::new(Vec::new()).expect("empty conflict clause")],
    )
}

fn preprocess(formula: &Cnf, mode: PreprocessMode) -> Preprocessed {
    let mut fixed = vec![None; formula.variable_count() as usize + 1];
    let mut rows = formula
        .clauses()
        .iter()
        .map(|input| (input.id(), input.clause().literals().to_vec()))
        .collect::<Vec<_>>();
    let mut unit_assignments = 0_u64;
    let mut pure_assignments = 0_u64;

    loop {
        let mut simplified = Vec::new();
        for (id, literals) in rows {
            let mut residual = Vec::new();
            let mut satisfied = false;
            for literal in literals {
                match fixed[literal.variable().get() as usize] {
                    Some(value) if assignment_satisfies_literal(value, literal) => {
                        satisfied = true;
                        break;
                    }
                    Some(_) => {}
                    None => residual.push(literal),
                }
            }
            if satisfied {
                continue;
            }
            if residual.is_empty() {
                return Preprocessed {
                    formula: conflict_formula(formula.variable_count()),
                    fixed,
                    unit_assignments,
                    pure_assignments,
                };
            }
            simplified.push((id, residual));
        }
        rows = simplified;

        let mut changed = false;
        if mode.units() {
            for (_, literals) in &rows {
                if literals.len() != 1 {
                    continue;
                }
                let unit = literals[0];
                let index = unit.variable().get() as usize;
                let value = unit.polarity() == Polarity::Positive;
                match fixed[index] {
                    Some(previous) if previous != value => {
                        return Preprocessed {
                            formula: conflict_formula(formula.variable_count()),
                            fixed,
                            unit_assignments,
                            pure_assignments,
                        };
                    }
                    Some(_) => {}
                    None => {
                        fixed[index] = Some(value);
                        unit_assignments += 1;
                        changed = true;
                    }
                }
            }
            if changed {
                continue;
            }
        }

        if mode.pure() {
            let mut polarities = vec![(false, false); formula.variable_count() as usize + 1];
            for (_, literals) in &rows {
                for literal in literals {
                    let slot = &mut polarities[literal.variable().get() as usize];
                    match literal.polarity() {
                        Polarity::Negative => slot.0 = true,
                        Polarity::Positive => slot.1 = true,
                    }
                }
            }
            for raw in 1..=formula.variable_count() {
                let index = raw as usize;
                if fixed[index].is_some() {
                    continue;
                }
                let value = match polarities[index] {
                    (true, false) => Some(false),
                    (false, true) => Some(true),
                    (false, false) | (true, true) => None,
                };
                if let Some(value) = value {
                    fixed[index] = Some(value);
                    pure_assignments += 1;
                    changed = true;
                }
            }
            if changed {
                continue;
            }
        }

        break;
    }

    let inputs = rows
        .into_iter()
        .map(|(id, literals)| {
            InputClause::new(
                id,
                Clause::new(literals).expect("preprocessing preserves non-tautology"),
            )
        })
        .collect();
    Preprocessed {
        formula: formula_from_inputs(formula.variable_count(), inputs),
        fixed,
        unit_assignments,
        pure_assignments,
    }
}

fn lift_preprocessed_model(model: &SatModel, fixed: &[Option<bool>]) -> SatModel {
    let assignments = (1..=model.variable_count())
        .map(|raw| {
            let variable = variable(raw);
            Assignment::new(
                variable,
                fixed[raw as usize]
                    .unwrap_or_else(|| model.value(variable).expect("reduced model is complete")),
            )
        })
        .collect();
    SatModel::new(model.variable_count(), assignments, SchemaLimits::default())
        .expect("lifted preprocessing model is canonical")
}

fn generated_preprocessing_formula(case_index: u64, rng: &mut DeterministicRng) -> Cnf {
    let variable_count = 6;
    let mut rows = Vec::new();
    rows.push(clause(&[1]));
    rows.push(clause(&[-1, 2]));

    let witness = [
        false,
        true,
        true,
        rng.next() & 1 != 0,
        rng.next() & 1 != 0,
        false,
        true,
    ];
    for _ in 0..(2 + rng.below(5)) {
        let first = 2 + rng.below(4) as u32;
        let mut second = 2 + rng.below(4) as u32;
        if second == first {
            second = 2 + (second - 1) % 4;
        }
        let first_literal = Literal::new(
            variable(first),
            if witness[first as usize] {
                Polarity::Positive
            } else {
                Polarity::Negative
            },
        );
        let second_literal = Literal::new(
            variable(second),
            if rng.next() & 1 == 0 {
                Polarity::Positive
            } else {
                Polarity::Negative
            },
        );
        rows.push(
            Clause::new(vec![first_literal, second_literal]).expect("preprocessing fixture clause"),
        );
    }
    rows.push(clause(&[3, 6]));
    if case_index % 2 == 1 {
        rows.push(clause(&[-2]));
    }
    formula_from_clauses(variable_count, rows)
}

#[test]
fn pure_literal_and_unit_preprocessing_preserve_the_certified_verdict() {
    let mut rng = DeterministicRng::new(0x7b19_eca4_52d0_36f8);
    let mut observed_unit_assignments = 0_u64;
    let mut observed_pure_assignments = 0_u64;
    for case_index in 0..CASES_PER_LAW {
        let original = generated_preprocessing_formula(case_index, &mut rng);
        let original_outcome = solve(&original, SolverLimits::default());
        let original_kind =
            must_certify("preprocessing", case_index, &original, &original_outcome).kind();

        for mode in [
            PreprocessMode::Units,
            PreprocessMode::Pure,
            PreprocessMode::UnitsAndPure,
        ] {
            let transformed = preprocess(&original, mode);
            observed_unit_assignments += transformed.unit_assignments;
            observed_pure_assignments += transformed.pure_assignments;
            let transformed_outcome = solve(&transformed.formula, SolverLimits::default());
            let transformed_certified = must_certify(
                "preprocessing",
                case_index,
                &transformed.formula,
                &transformed_outcome,
            );
            assert_eq!(
                original_kind,
                transformed_certified.kind(),
                "preprocessing changed the verdict in case {case_index} under {mode:?}"
            );
            if let Certified::Sat(model) = transformed_certified {
                let lifted = lift_preprocessed_model(model, &transformed.fixed);
                assert!(
                    independently_satisfies(&lifted, &original),
                    "preprocessed model did not lift in case {case_index} under {mode:?}"
                );
            }
        }
    }
    assert!(
        observed_unit_assignments > 0,
        "campaign did not exercise unit propagation"
    );
    assert!(
        observed_pure_assignments > 0,
        "campaign did not exercise pure-literal elimination"
    );
}

fn generated_unsat_superformula(case_index: u64, rng: &mut DeterministicRng) -> Cnf {
    let variable_count = 1 + case_index as u32 % 4;
    let mapping = non_identity_bijection(variable_count, rng);
    let mapped = |raw: u32| mapping[raw as usize - 1];
    let mut rows = Vec::new();
    rows.push(clause(&[i64::from(mapped(1))]));
    for raw in 1..variable_count {
        rows.push(clause(&[
            -i64::from(mapped(raw)),
            i64::from(mapped(raw + 1)),
        ]));
    }
    rows.push(clause(&[-i64::from(mapped(variable_count))]));
    rows.push(rows[0].clone());
    rng.shuffle(&mut rows);
    formula_from_clauses(variable_count, rows)
}

fn minimal_unsat_core(formula: &Cnf, case_index: u64) -> Cnf {
    let mut inputs = formula.clauses().to_vec();
    let mut index = 0;
    while index < inputs.len() {
        let mut candidate_inputs = inputs.clone();
        candidate_inputs.remove(index);
        let candidate = formula_from_inputs(formula.variable_count(), candidate_inputs);
        let outcome = solve(&candidate, SolverLimits::default());
        match must_certify("core-minimization", case_index, &candidate, &outcome) {
            Certified::Unsat => inputs = candidate.clauses().to_vec(),
            Certified::Sat(_) => index += 1,
        }
    }
    formula_from_inputs(formula.variable_count(), inputs)
}

#[test]
fn minimal_unsat_core_is_checked_and_every_proper_subset_is_checked_sat() {
    let mut rng = DeterministicRng::new(0x9f42_16d8_c5a7_30eb);
    let mut proper_subsets_checked = 0_u64;
    for case_index in 0..CASES_PER_LAW {
        let formula = generated_unsat_superformula(case_index, &mut rng);
        let formula_outcome = solve(&formula, SolverLimits::default());
        assert!(matches!(
            must_certify("minimal-core", case_index, &formula, &formula_outcome),
            Certified::Unsat
        ));

        let core = minimal_unsat_core(&formula, case_index);
        assert!(
            core.clauses().len() < formula.clauses().len(),
            "duplicate clause was not removed in case {case_index}"
        );
        let core_outcome = solve(&core, SolverLimits::default());
        assert!(matches!(
            must_certify("minimal-core", case_index, &core, &core_outcome),
            Certified::Unsat
        ));

        assert!(core.clauses().len() < 64);
        let full_mask = (1_u64 << core.clauses().len()) - 1;
        for mask in 0..full_mask {
            let subset = core
                .clauses()
                .iter()
                .enumerate()
                .filter(|(index, _)| mask & (1_u64 << index) != 0)
                .map(|(_, input)| input.clone())
                .collect();
            let subset = formula_from_inputs(core.variable_count(), subset);
            let subset_outcome = solve(&subset, SolverLimits::default());
            assert!(matches!(
                must_certify("minimal-core-subset", case_index, &subset, &subset_outcome),
                Certified::Sat(_)
            ));
            proper_subsets_checked += 1;
        }
    }
    assert!(
        proper_subsets_checked >= CASES_PER_LAW,
        "campaign did not enumerate proper core subsets"
    );
}

fn planted_mutant_promotes_inconclusive(outcome: &SolverOutcome) -> CertifiedKind {
    match outcome {
        SolverOutcome::Sat { .. } => CertifiedKind::Sat,
        SolverOutcome::Unsat { .. }
        | SolverOutcome::Inconclusive { .. }
        | SolverOutcome::InternalFault { .. } => CertifiedKind::Unsat,
    }
}

#[test]
fn inconclusive_promotion_mutant_is_killed_before_metamorphic_comparison() {
    let formula = formula_from_clauses(
        2,
        vec![
            clause(&[1, 2]),
            clause(&[1, -2]),
            clause(&[-1, 2]),
            clause(&[-1, -2]),
        ],
    );
    let checked_unsat = solve(&formula, SolverLimits::default());
    assert!(matches!(
        must_certify("inconclusive-mutant", 0, &formula, &checked_unsat),
        Certified::Unsat
    ));

    let exhausted = solve(
        &formula,
        SolverLimits {
            max_decisions: 0,
            ..SolverLimits::default()
        },
    );
    let cancelled = solve_with_cancel(&formula, SolverLimits::default(), || true);
    for non_verdict in [&exhausted, &cancelled] {
        assert_eq!(
            compare_checked(&formula, &checked_unsat, &formula, non_verdict),
            Err(ComparisonStop::Inconclusive),
            "FL-INV-07 comparison admitted an Inconclusive outcome"
        );
        assert!(
            checked_unsat.checked_artifact().is_some(),
            "baseline must carry checked evidence"
        );
        assert_eq!(
            non_verdict.checked_artifact(),
            None,
            "Inconclusive outcome unexpectedly carried an artifact"
        );
        assert_eq!(
            planted_mutant_promotes_inconclusive(&checked_unsat),
            planted_mutant_promotes_inconclusive(non_verdict),
            "fixture must demonstrate the false equality admitted by the mutant"
        );
        assert_ne!(
            certify(&formula, non_verdict).map(|certified| certified.kind()),
            Ok(planted_mutant_promotes_inconclusive(non_verdict)),
            "certificate gate failed to kill the Inconclusive-promotion mutant"
        );
    }
}

#[test]
fn campaign_reporting_contract_is_pinned() {
    assert_eq!(LAW_COUNT, 6);
    assert_eq!(CASES_PER_LAW, 128);
    assert_eq!(CERTIFICATE_CHECKED_LAWS, LAW_COUNT);
    assert_eq!(SELF_CONSISTENCY_ONLY_LAWS, 0);
    assert_eq!(EXPECTED_VIOLATIONS, 0);
}
