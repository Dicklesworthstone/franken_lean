//! Changing source arguments use a checked PSigma state, with fixed parameters
//! removed before the explicit decreasing script receives its local context.
#![forbid(unsafe_code)]
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
    (
        // Unitlike eta at types that differ only in a proof: the pin fixes both
        // `p` and `q` and recurses on `n` alone (no `_unary`).
        "unitTypeProofs",
        r#"structure Ghost (p : True) : Type where

def unitTypeProofs (h : True) (p : Ghost h) (q : Ghost True.intro) (n : Nat) : Nat :=
  if hn : 0 < n then unitTypeProofs h q q (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt hn (Nat.succ_pos 0)"#,
        "unitTypeProofs True.intro Ghost.mk Ghost.mk 42",
    ),
];

const DEPENDENT_PROGRAMS: &[(&str, &str, &str)] = &[
    (
        "dependentArguments",
        DEPENDENT,
        "dependentArguments 42 (Fin.mk 0 (Nat.succ_pos 42)) + 42",
    ),
    (
        "dependentAccum",
        r#"def dependentAccum (n : Nat) (p : Fin (Nat.succ n)) : Nat :=
  if h : 0 < n then dependentAccum (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) + p.val + 1 else p.val
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentAccum 21 (Fin.mk 21 (by decide))",
    ),
    (
        "dependentChain",
        r#"def dependentChain (n : Nat) (p : Fin (Nat.succ n)) (q : Fin (Nat.succ p.val)) : Nat :=
  if h : 0 < n then dependentChain (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) (Fin.mk 0 (Nat.succ_pos 0)) + p.val + q.val else p.val + q.val
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentChain 42 (Fin.mk 21 (by decide)) (Fin.mk 21 (by decide))",
    ),
    (
        "dependentFixed",
        r#"def dependentFixed (n step : Nat) (p : Fin (Nat.succ n)) : Nat :=
  if h : 0 < n then dependentFixed (n - 1) step (Fin.mk 0 (Nat.succ_pos (n - 1))) + p.val + step else p.val
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentFixed 20 2 (Fin.mk 2 (by decide))",
    ),
    (
        "dependentResult",
        r#"def dependentResult (n : Nat) (p : Fin (Nat.succ n)) : Fin (Nat.succ n) := match n with
  | 0 => p
  | k + 1 =>
    let r := dependentResult k (Fin.mk 0 (Nat.succ_pos k))
    Fin.mk (Nat.succ r.val) (Nat.succ_lt_succ r.isLt)
termination_by n
decreasing_by exact Nat.lt_succ_self k"#,
        "(dependentResult 42 (Fin.mk 0 (Nat.succ_pos 42))).val",
    ),
    (
        "dependentProofParam",
        r#"def dependentProofParam (n : Nat) (h : 0 < Nat.succ n) : Nat :=
  let p := Fin.mk 0 h
  if hn : 0 < n then dependentProofParam (n - 1) (Nat.succ_pos (n - 1)) + p.val + 1 else p.val
termination_by n
decreasing_by exact Nat.sub_lt hn (Nat.succ_pos 0)"#,
        "dependentProofParam 42 (Nat.succ_pos 42)",
    ),
    (
        "dependentContext",
        r#"def dependentContext (n : Nat) (p : Fin (Nat.succ n)) : Nat :=
  if h : 0 < n then dependentContext (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) + p.val + 1 else p.val
termination_by n
decreasing_by
  have retained : Fin (Nat.succ n) := p
  exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentContext 21 (Fin.mk 21 (by decide))",
    ),
    (
        "dependentLambda",
        r#"def dependentLambda : (n : Nat) -> Fin (Nat.succ n) -> Nat := fun n p =>
  if h : 0 < n then dependentLambda (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) + p.val + 1 else p.val
termination_by remaining position => remaining
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentLambda 21 (Fin.mk 21 (by decide))",
    ),
    (
        "dependentTwice",
        r#"def dependentTwice (n : Nat) (p : Fin (Nat.succ n)) : Nat :=
  if h : 0 < n then dependentTwice (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) + dependentTwice (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) + p.val else 21 + p.val
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "dependentTwice 1 (Fin.mk 0 (Nat.succ_pos 1))",
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
    "structure Ghost (p : True) : Type where\n\ndef bad (h : True) (p : Ghost h) (q : Ghost True.intro) (n : Nat) : Nat :=\n  if hn : 0 < n then bad h q q (n - 1) + 1 else 0\ntermination_by n\ndecreasing_by\n  have unused : Ghost True.intro := q\n  exact Nat.sub_lt hn (Nat.succ_pos 0)",
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

const DEPENDENT_REFUSALS: &[&str] = &[
    // A dependent argument must have the new index, even when its old value
    // happens to fit some smaller inputs at runtime.
    "def bad (n : Nat) (p : Fin (Nat.succ n)) : Nat := if h : 0 < n then bad (n - 1) p else p.val\ntermination_by n\ndecreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n : Nat) (p : Fin (Nat.succ n)) (q : Fin (Nat.succ p.val)) : Nat := if h : 0 < n then bad (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) q else p.val + q.val\ntermination_by n\ndecreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)",
    // Correctly packed arguments do not discharge false decreasing goals.
    "def bad (n : Nat) (p : Fin (Nat.succ n)) : Nat := if h : 0 < n then bad n (Fin.mk 0 (Nat.succ_pos n)) else p.val\ntermination_by n\ndecreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n : Nat) (p : Fin (Nat.succ n)) : Nat := if h : 0 < n then bad (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) else p.val\ntermination_by n\ndecreasing_by exact Nat.succ_pos n",
    // Post-colon names and independent fixed parameters stay inaccessible.
    "def bad : (n : Nat) -> Fin (Nat.succ n) -> Nat := fun n p => if h : 0 < n then bad (n - 1) (Fin.mk 0 (Nat.succ_pos (n - 1))) else p.val\ntermination_by remaining position => remaining\ndecreasing_by\n  have inaccessible : Fin (Nat.succ n) := p\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n step : Nat) (p : Fin (Nat.succ n)) : Nat := if h : 0 < n then bad (n - 1) step (Fin.mk 0 (Nat.succ_pos (n - 1))) + step else p.val\ntermination_by n\ndecreasing_by\n  have inaccessible : Nat := step\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
];

// This original pin-accepted frontier now runs beside the programs that use
// their dependent values, dependent result types, and branch proof contexts.
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

pub(super) fn assert_argument_programs(base: &Engine) {
    let mut failures = Vec::new();
    // Every accepted source computes 42 on the live v4.32.0 pin; each refusal
    // was independently rejected with its intended diagnostic.
    for (name, definition, application) in PROGRAMS.iter().chain(DEPENDENT_PROGRAMS) {
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
    for source in REFUSALS.iter().chain(DEPENDENT_REFUSALS) {
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
    match base.check_source_files(
        &[PROOF_CONVERSION.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(super::limits()),
    ) {
        Err(error) if format!("{error:?}").contains("FixedArgumentConversionUnsupported") => {}
        result => failures.push(format!(
            "FixedArgumentConversionUnsupported refusal: {result:?}"
        )),
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
