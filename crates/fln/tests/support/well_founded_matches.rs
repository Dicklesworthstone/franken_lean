//! Ordinary matches specialize the checked well-founded continuation while
//! retaining the original values of captured source variables and lets.
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, SourceCheckLimits};

const PROGRAMS: &[(&str, &str, &str)] = &[
    (
        "matchCountdown",
        r#"def matchCountdown (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => matchCountdown k + 1
termination_by n
decreasing_by exact Nat.lt_succ_self k"#,
        "matchCountdown 42",
    ),
    (
        "matchSkipTwo",
        r#"def matchSkipTwo (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => if h : 0 < k then matchSkipTwo (k - 1) + 2 else 1
termination_by n
decreasing_by exact Nat.lt_trans (@Nat.sub_lt k 1 h (Nat.succ_pos 0)) (Nat.lt_succ_self k)"#,
        "matchSkipTwo 42",
    ),
    (
        "matchScale",
        r#"def matchScale (step n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => matchScale step k + step
termination_by n
decreasing_by exact Nat.lt_succ_self k"#,
        "matchScale 2 21",
    ),
    (
        "matchPair",
        r#"def matchPair (p : Nat × Nat) : Nat := match p with
  | (0, step) => 0
  | (k + 1, step) => matchPair (k, step) + step
termination_by p.1
decreasing_by exact Nat.lt_succ_self k"#,
        "matchPair (21, 2)",
    ),
    (
        "matchCapture",
        r#"def matchCapture (n : Nat) : Nat :=
  let saved := n
  match n with
  | 0 => 0
  | k + 1 => matchCapture k + (saved - k)
termination_by n
decreasing_by exact Nat.lt_succ_self k"#,
        "matchCapture 42",
    ),
    (
        "capturedHyp",
        r#"def capturedHyp (n : Nat) : Nat :=
  if h : 0 < n then
    match n with
    | 0 => 0
    | k + 1 => capturedHyp 0 + 42
  else 0
termination_by n
decreasing_by exact h"#,
        "capturedHyp 42",
    ),
    (
        "branchLet",
        r#"def branchLet (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => let smaller := k; branchLet smaller + 1
termination_by n
decreasing_by
  have retained : Nat := smaller
  exact Nat.lt_succ_self k"#,
        "branchLet 42",
    ),
    (
        "measuredSum",
        r#"def measuredSum (xs : List Nat) : Nat := match xs with
  | List.nil => 0
  | List.cons value tail => measuredSum tail + value
termination_by xs.length
decreasing_by exact Nat.lt_succ_self tail.length"#,
        "measuredSum (List.cons 19 (List.cons 23 List.nil))",
    ),
    (
        "scopedHave",
        r#"def scopedHave (n : Nat) : Nat :=
  have p : True := True.intro
  if h : 0 < n then
    scopedHave 0 + ((by revert p; intro q; exact scopedHave 0) : Nat) + 42
  else 0
termination_by n
decreasing_by exact h"#,
        "scopedHave 42",
    ),
    (
        "earlierCall",
        r#"def earlierCall (n : Nat) : Nat :=
  if h : 0 < n then
    earlierCall 0 + (match n with | 0 => 0 | k + 1 => earlierCall 0) + 42
  else 0
termination_by n
decreasing_by exact h"#,
        "earlierCall 42",
    ),
    (
        "laterCall",
        r#"def laterCall (n : Nat) : Nat :=
  if h : 0 < n then
    (match n with | 0 => 0 | k + 1 => laterCall 0) + laterCall 0 + 42
  else 0
termination_by n
decreasing_by
  exact Nat.succ_pos k
  exact h"#,
        "laterCall 42",
    ),
];

const REFUSALS: &[&str] = &[
    // Actual nondecreasing calls and wrong propositions remain rejected.
    "def bad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => bad (k + 1)\ntermination_by n\ndecreasing_by exact Nat.lt_succ_self k",
    "def bad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => bad k\ntermination_by n\ndecreasing_by exact Nat.succ_pos k",
    "def bad (p : Nat × Nat) : Nat := match p with | (0, step) => 0 | (k + 1, step) => bad (k, step)\ntermination_by p.1\ndecreasing_by exact Nat.succ_pos k",
    // The cleaned goal does not expose unrelated original names or values.
    "def bad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => bad k\ntermination_by n\ndecreasing_by exact Nat.lt_succ_self n",
    "def bad (step n : Nat) : Nat := match n with | 0 => 0 | k + 1 => bad step k\ntermination_by n\ndecreasing_by\n  have unused : Nat := step\n  exact Nat.lt_succ_self k",
    "def bad (n : Nat) : Nat := let saved := n; match n with | 0 => 0 | k + 1 => bad k + (saved - k)\ntermination_by n\ndecreasing_by\n  have unused : Nat := saved\n  exact Nat.lt_succ_self k",
    // Original recursive arguments retain their original dependency on n.
    "def bad (n : Nat) : Nat := let saved := n; match n with | 0 => 0 | k + 1 => bad (saved - 1)\ntermination_by n\ndecreasing_by exact Nat.lt_succ_self k",
    "def bad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => bad (n - 1)\ntermination_by n\ndecreasing_by exact Nat.lt_succ_self k",
    "def bad (n : Nat) : Nat := let saved := n; match saved with | 0 => 0 | k + 1 => bad k\ntermination_by n\ndecreasing_by exact Nat.lt_succ_self k",
    // Retaining an old identity for a cached transport does not expose its proof.
    "def bad (n : Nat) : Nat := if h : 0 < n then (match n with | 0 => 0 | k + 1 => let old : 0 < n := (by assumption); bad 0 + 42) else 0\ntermination_by n\ndecreasing_by exact h",
    // Match/proof scopes must not manufacture or merge an extra proof goal.
    "def bad (n : Nat) : Nat := have p : True := True.intro; if h : 0 < n then bad 0 + ((by revert p; intro q; exact bad 0) : Nat) + 42 else 0\ntermination_by n\ndecreasing_by\n  exact h\n  exact h",
    "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 + (match n with | 0 => 0 | k + 1 => bad 0) + 42 else 0\ntermination_by n\ndecreasing_by\n  exact h\n  exact h",
    "def bad (n : Nat) : Nat := if h : 0 < n then (match n with | 0 => 0 | k + 1 => bad 0) + bad 0 + 42 else 0\ntermination_by n\ndecreasing_by exact Nat.succ_pos k",
];

pub(super) fn assert_match_programs(base: &Engine) {
    let mut failures = Vec::new();
    // All programs and refusal controls are checked against live v4.32.0.
    // Each accepted program computes 42 on the native VM after both checkers.
    for (name, definition, application) in PROGRAMS {
        let source = format!("{definition}\ndef answer : Nat := {application}");
        match base.execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        ) {
            Ok(result) => {
                let result = result.into_complete().expect("match computation completes");
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
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
