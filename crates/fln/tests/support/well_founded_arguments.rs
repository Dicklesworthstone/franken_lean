//! Changing source arguments use a checked PSigma state, with fixed parameters
//! removed before the explicit decreasing script receives its local context.
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, SourceCheckLimits};

const PROGRAMS: &[(&str, &str, &str)] = &[
    (
        "gcd",
        r#"def gcd (a b : Nat) : Nat :=
  if h : 0 < b then gcd b (a % b) else a
termination_by b
decreasing_by exact Nat.mod_lt a h"#,
        "gcd 126 84",
    ),
    (
        "accumulator",
        r#"def accumulator (acc n : Nat) : Nat :=
  if h : 0 < n then accumulator (acc + 2) (n - 1) else acc
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "accumulator 0 21",
    ),
    (
        "fixedMiddle",
        r#"def fixedMiddle (n step acc : Nat) : Nat :=
  if h : 0 < n then fixedMiddle (n - 1) step (acc + 1) else acc + step
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "fixedMiddle 21 0 21",
    ),
    (
        "fixedAfter",
        r#"def fixedAfter (n step : Nat) : Nat :=
  if h : 0 < n then fixedAfter (n - 1) step + step else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "fixedAfter 21 2",
    ),
    (
        "fixedAlias",
        r#"def fixedAlias (n step : Nat) : Nat :=
  let copy := step
  if h : 0 < n then fixedAlias (n - 1) copy + step else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "fixedAlias 21 2",
    ),
    (
        "matchAccumulator",
        r#"def matchAccumulator (acc n : Nat) : Nat := match n with
  | 0 => acc
  | k + 1 => matchAccumulator (acc + 1) k
termination_by n
decreasing_by exact Nat.lt_succ_self k"#,
        "matchAccumulator 0 42",
    ),
    (
        "sumAccumulator",
        r#"def sumAccumulator (xs : List Nat) (acc : Nat) : Nat := match xs with
  | List.nil => acc
  | List.cons value tail => sumAccumulator tail (acc + value)
termination_by xs.length
decreasing_by exact Nat.lt_succ_self tail.length"#,
        "sumAccumulator (List.cons 19 (List.cons 23 List.nil)) 0",
    ),
    (
        "rotate",
        r#"def rotate (a b n : Nat) : Nat :=
  if h : 0 < n then rotate b (a + 1) (n - 1) else a + b
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "rotate 0 0 42",
    ),
    (
        "polymorphicCount",
        r#"def polymorphicCount (A : Type) (xs : List A) (acc : Nat) : Nat := match xs with
  | List.nil => acc
  | List.cons _ tail => polymorphicCount A tail (acc + 1)
termination_by xs.length
decreasing_by exact Nat.lt_succ_self tail.length"#,
        "polymorphicCount Nat (List.cons 19 (List.cons 23 List.nil)) 40",
    ),
    (
        "lambdaArguments",
        r#"def lambdaArguments : Nat -> Nat -> Nat := fun acc n =>
  if h : 0 < n then lambdaArguments (acc + 1) (n - 1) else acc
termination_by initial remaining => remaining
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "lambdaArguments 0 42",
    ),
    (
        "samePackedCall",
        r#"def samePackedCall (a b : Nat) : Nat :=
  if h : 0 < b then samePackedCall b 0 + samePackedCall b 0 + 42 else 0
termination_by b
decreasing_by exact h"#,
        "samePackedCall 1 42",
    ),
    (
        "fixedPair",
        r#"def fixedPair (p : Nat × Nat) (n : Nat) : Nat :=
  if h : 0 < n then fixedPair (p.1, p.2) (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "fixedPair (1, 2) 42",
    ),
    (
        "fixedProof",
        r#"def fixedProof (p : True) (n : Nat) : Nat :=
  if h : 0 < n then fixedProof True.intro (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "fixedProof True.intro 42",
    ),
    (
        "fixedAliasCalls",
        r#"def fixedAliasCalls (step n : Nat) : Nat :=
  let copy := step
  if h : 0 < n then fixedAliasCalls step 0 + fixedAliasCalls copy 0 + 42 else 0
termination_by n
decreasing_by
  exact h
  exact h"#,
        "fixedAliasCalls 0 42",
    ),
    (
        "suffixCalls",
        r#"def suffixCalls (n step : Nat) : Nat :=
  let copy := step
  if h : 0 < n then suffixCalls 0 step + suffixCalls 0 copy + 42 else 0
termination_by n
decreasing_by exact h"#,
        "suffixCalls 42 0",
    ),
    (
        "packedCalls",
        r#"def packedCalls (step a b : Nat) : Nat :=
  let copy := step
  if h : 0 < b then packedCalls step b 0 + packedCalls copy b 0 + 42 else 0
termination_by b
decreasing_by exact h"#,
        "packedCalls 0 1 42",
    ),
];

const REFUSALS: &[&str] = &[
    // Changing arguments do not make a nondecreasing call or a wrong proof valid.
    "def bad (a b : Nat) : Nat := if h : 0 < b then bad b b else a\ntermination_by b\ndecreasing_by exact Nat.mod_lt a h",
    "def bad (a b : Nat) : Nat := if h : 0 < b then bad b (a % b) else a\ntermination_by b\ndecreasing_by exact Nat.succ_pos b",
    // Fixed parameters at any telescope position stay out of unrelated goals.
    "def bad (n step acc : Nat) : Nat := if h : 0 < n then bad (n - 1) step (acc + 1) else acc + step\ntermination_by n\ndecreasing_by\n  have unused : Nat := step\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n step : Nat) : Nat := if h : 0 < n then bad (n - 1) step + step else 0\ntermination_by n\ndecreasing_by\n  have unused : Nat := step\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n step : Nat) : Nat := let copy := step; if h : 0 < n then bad (n - 1) copy + step else 0\ntermination_by n\ndecreasing_by\n  have unused : Nat := copy\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    // Reducible record eta and unitlike equality also remove fixed parameters.
    "def bad (p : Nat × Nat) (n : Nat) : Nat := if h : 0 < n then bad (p.1, p.2) (n - 1) + 1 else 0\ntermination_by n\ndecreasing_by\n  have unused : Nat × Nat := p\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (p : True) (n : Nat) : Nat := if h : 0 < n then bad True.intro (n - 1) + 1 else 0\ntermination_by n\ndecreasing_by\n  have unused : True := p\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    // Only identical complete recursive applications share an obligation.
    "def bad (a b : Nat) : Nat := if h : 0 < b then bad b 0 + bad (b + 1) 0 + 42 else 0\ntermination_by b\ndecreasing_by exact h",
    "def bad (a b : Nat) : Nat := if h : 0 < b then bad b 0 + bad b 0 + 42 else 0\ntermination_by b\ndecreasing_by\n  exact h\n  exact h",
    // PackMutual removes fixed args before caching except for its original
    // unary/fixed-prefix optimization; the resulting proof counts differ.
    "def bad (step n : Nat) : Nat := let copy := step; if h : 0 < n then bad step 0 + bad copy 0 + 42 else 0\ntermination_by n\ndecreasing_by exact h",
    "def bad (n step : Nat) : Nat := let copy := step; if h : 0 < n then bad 0 step + bad 0 copy + 42 else 0\ntermination_by n\ndecreasing_by\n  exact h\n  exact h",
    "def bad (step a b : Nat) : Nat := let copy := step; if h : 0 < b then bad step b 0 + bad copy b 0 + 42 else 0\ntermination_by b\ndecreasing_by\n  exact h\n  exact h",
    // Post-colon lambda names remain inaccessible to decreasing_by.
    "def bad : Nat -> Nat -> Nat := fun acc n => if h : 0 < n then bad (acc + 1) (n - 1) else acc\ntermination_by initial remaining => remaining\ndecreasing_by exact @Nat.sub_lt n 1 h (Nat.succ_pos 0)",
];

// Accepted by the pin, but intentionally outside this independent-telescope
// slice: the type of p depends on a different varying argument.
const DEPENDENT: &str = r#"def dependentArguments (n : Nat) (p : Fin (Nat.succ n)) : Nat :=
  if h : 0 < n then dependentArguments (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#;

// The pin can distinguish varying proof arguments without general proof
// irrelevance. This boundary is kept explicit while its special proof-field
// and implicit-argument conversion rules are not all available natively.
const PROOF_CONVERSION: &str = r#"def proofArguments (P : Prop) (p q : P) (n : Nat) : Nat :=
  if h : 0 < n then proofArguments P q p (n - 1) + 1 else 0
termination_by n
decreasing_by
  have retained : P := p
  exact Nat.sub_lt h (Nat.succ_pos 0)"#;

// Unitlike eta must establish equality of parameterized types too. Missing
// proof conversion in that comparison cannot justify treating p as varying.
const UNIT_PROOF_CONVERSION: &str = r#"structure Ghost (p : True) : Type where

def unitTypeProofs (h : True) (p : Ghost h) (q : Ghost True.intro) (n : Nat) : Nat :=
  if hn : 0 < n then unitTypeProofs h q q (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt hn (Nat.succ_pos 0)"#;

pub(super) fn assert_argument_programs(base: &Engine) {
    let mut failures = Vec::new();
    // All sixteen accepted sources compute 42 on the live v4.32.0 pin; each
    // refusal above was independently rejected with its intended diagnostic.
    for (name, definition, application) in PROGRAMS {
        let source = format!("{definition}\ndef answer : Nat := {application}");
        match base.execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        ) {
            Ok(result) => {
                let result = result
                    .into_complete()
                    .expect("packed computation completes");
                let values: Vec<_> = result
                    .executions
                    .iter()
                    .filter_map(|execution| {
                        fln::closed_vm_value(&execution.exit).expect("normal VM exit")
                    })
                    .collect();
                if values != vec![ClosedVmValue::Scalar(42)] {
                    failures.push(format!("{name}: unexpected computation {values:?}"));
                }
            }
            Err(error) => failures.push(format!("{name}: {error:?}")),
        }
    }
    for source in REFUSALS {
        if base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(super::limits()),
            )
            .is_ok()
        {
            failures.push(format!("incorrectly accepted: {source}"));
        }
    }
    for (source, diagnostic) in [
        (DEPENDENT, "DependentWellFoundedArguments"),
        (PROOF_CONVERSION, "FixedArgumentConversionUnsupported"),
        (UNIT_PROOF_CONVERSION, "FixedArgumentConversionUnsupported"),
    ] {
        match base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(super::limits()),
        ) {
            Err(error) if format!("{error:?}").contains(diagnostic) => {}
            result => failures.push(format!("{diagnostic} refusal: {result:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
