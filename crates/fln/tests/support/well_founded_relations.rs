//! Explicit measures use their selected checked well-founded relation, including
//! lexicographic products and locally supplied inverse-image relations.
#![forbid(unsafe_code)]
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, SourceCheckLimits};

// Every source/application pair was evaluated by the pinned Reference. Its
// harness imports Init.WFComputable; Init.Data.Repr serves only #eval printing.
const PROGRAMS: &[(&str, &str, &str, usize)] = &[
    (
        "lexCount",
        r#"def lexCount (a b : Nat) : Nat :=
  if hb : 0 < b then lexCount a (b - 1) + 1
  else if ha : 0 < a then lexCount (a - 1) 6 + 1 else 0
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))
  exact Prod.Lex.left 6 b (Nat.sub_lt ha (Nat.succ_pos 0))"#,
        "lexCount 5 7",
        42,
    ),
    (
        "pairMeasure",
        r#"def pairMeasure (a b : Nat) : Nat :=
  if h : 0 < a then pairMeasure 0 (b + 1) + 42 else 0
termination_by (a, b)
decreasing_by exact Prod.Lex.left (b + 1) b h"#,
        "pairMeasure 7 3",
        42,
    ),
    (
        "lexFixed",
        r#"def lexFixed (step a b : Nat) : Nat :=
  if hb : 0 < b then lexFixed step a (b - 1) + step
  else if ha : 0 < a then lexFixed step (a - 1) 6 + step else 0
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))
  exact Prod.Lex.left 6 b (Nat.sub_lt ha (Nat.succ_pos 0))"#,
        "lexFixed 2 2 7",
        42,
    ),
    (
        "lexDependentArgs",
        r#"def lexDependentArgs (a b : Nat) (p : Fin (Nat.succ b)) : Nat :=
  if hb : 0 < b then
    lexDependentArgs a (b - 1) (Fin.mk 0 (Nat.succ_pos (b - 1))) + p.val + 1
  else if ha : 0 < a then
    lexDependentArgs (a - 1) 6 (Fin.mk 0 (Nat.succ_pos 6)) + p.val + 1
  else p.val
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))
  exact Prod.Lex.left 6 b (Nat.sub_lt ha (Nat.succ_pos 0))"#,
        "lexDependentArgs 5 7 (Fin.mk 0 (Nat.succ_pos 7))",
        42,
    ),
    (
        "lexDependent",
        r#"def lexDependent (a b : Nat) : Fin (Nat.succ a) :=
  if hb : 0 < b then lexDependent a (b - 1)
  else
    match a with
    | 0 => Fin.mk 0 (Nat.succ_pos 0)
    | k + 1 =>
      let prior := lexDependent k 6
      Fin.mk (Nat.succ prior.val) (Nat.succ_lt_succ prior.isLt)
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))
  exact Prod.Lex.left 6 b (Nat.lt_succ_self k)"#,
        "(lexDependent 6 2).val",
        6,
    ),
    (
        "customGrow",
        r#"local instance : WellFoundedRelation Nat :=
  invImage (fun n : Nat => 2 - n) Nat.lt_wfRel
def customGrow (n : Nat) : Nat :=
  if h : 0 < 2 - n then customGrow 2 + 42 else 0
termination_by n
decreasing_by exact h"#,
        "customGrow 0",
        42,
    ),
    (
        "fixedFin",
        r#"local instance (bound : Nat) : WellFoundedRelation (Fin bound) :=
  invImage (fun p : Fin bound => p.val) Nat.lt_wfRel
def fixedFin (bound : Nat) (p : Fin (Nat.succ bound)) : Nat :=
  if h : 0 < p.val then fixedFin bound (Fin.mk 0 (Nat.succ_pos bound)) + 42 else 0
termination_by p
decreasing_by exact h"#,
        "fixedFin 7 (Fin.mk 3 (by decide))",
        42,
    ),
    (
        "ackermann",
        r#"def ackermann (a b : Nat) : Nat := match a with
  | 0 => b + 1
  | x + 1 => match b with
    | 0 => ackermann x 1
    | y + 1 => ackermann x (ackermann (x + 1) y)
termination_by (a, b)
decreasing_by
  exact Prod.Lex.left 1 0 (Nat.lt_succ_self x)
  exact Prod.Lex.right (x + 1) (Nat.lt_succ_self y)
  exact Prod.Lex.left _ _ (Nat.lt_succ_self x)"#,
        "ackermann 2 2",
        7,
    ),
    (
        "lexTwice",
        r#"def lexTwice (a b : Nat) : Nat :=
  if hb : 0 < b then lexTwice a 0 + lexTwice a (b - 1) + 1
  else if ha : 0 < a then lexTwice (a - 1) 0 + 1 else 0
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a hb
  exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))
  exact Prod.Lex.left 0 b (Nat.sub_lt ha (Nat.succ_pos 0))"#,
        "lexTwice 1 3",
        7,
    ),
    (
        "canonicalNat",
        r#"def canonicalNat (n : Nat) : Nat :=
  if h : 0 < n then canonicalNat (n - 1) + 1 else 0
termination_by n
decreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)"#,
        "canonicalNat 42",
        42,
    ),
    (
        "directLex",
        r#"def directLex (a b : Nat) : Nat :=
  WellFounded.fix (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
    (fun p recur =>
      if hb : 0 < p.2 then
        recur (p.1, p.2 - 1) (Prod.Lex.right p.1 (Nat.sub_lt hb (Nat.succ_pos 0))) + 1
      else if ha : 0 < p.1 then
        recur (p.1 - 1, 6) (Prod.Lex.left 6 p.2 (Nat.sub_lt ha (Nat.succ_pos 0))) + 1
      else 0)
    (a, b)"#,
        "directLex 5 7",
        42,
    ),
    (
        "directCaptured",
        r#"def directCaptured (step : Nat) : Nat -> Nat :=
  WellFounded.fix Nat.lt_wfRel.wf
    (fun n recur =>
      if h : 0 < n then recur (n - 1) (Nat.sub_lt h (Nat.succ_pos 0)) + step else 0)"#,
        "directCaptured 2 21",
        42,
    ),
    (
        "explicitApply",
        r#"def explicitApply (a b : Nat) : Nat :=
  if hb : 0 < b then explicitApply a (b - 1) + 1
  else if ha : 0 < a then explicitApply (a - 1) 6 + 1 else 0
termination_by (a, b)
decreasing_by
  apply Prod.Lex.right
  exact Nat.sub_lt hb (Nat.succ_pos 0)
  apply Prod.Lex.left
  exact Nat.sub_lt ha (Nat.succ_pos 0)"#,
        "explicitApply 5 7",
        42,
    ),
    (
        "boolShared",
        r#"def boolShared (flag : Bool) (a b : Nat) : Nat :=
  if h : 0 < b then
    (if flag then boolShared flag a 0 else boolShared flag a (b - 1))
      + boolShared flag a 0 + 1
  else 0
termination_by (a, b)
decreasing_by
  exact Prod.Lex.right a h
  exact Prod.Lex.right a (Nat.sub_lt h (Nat.succ_pos 0))
  exact Prod.Lex.right a h"#,
        "boolShared false 3 41 + boolShared true 9 100",
        42,
    ),
];

const REFUSALS: &[(&str, &str)] = &[
    (
        "samePair",
        r#"def bad (a b : Nat) : Nat := if hb : 0 < b then bad a b else 0
termination_by (a, b)
decreasing_by exact Prod.Lex.right a hb"#,
    ),
    (
        "increasingFirst",
        r#"def bad (a b : Nat) : Nat := if hb : 0 < b then bad (a + 1) (b - 1) else 0
termination_by (a, b)
decreasing_by exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))"#,
    ),
    (
        "missingSecondProof",
        r#"def bad (a b : Nat) : Nat := if hb : 0 < b then bad a 0 + bad a (b - 1) else 0
termination_by (a, b)
decreasing_by exact Prod.Lex.right a hb"#,
    ),
    (
        "scalarProofForPair",
        r#"def bad (a b : Nat) : Nat := if h : 0 < a then bad 0 (b + 1) else 0
termination_by (a, b)
decreasing_by exact h"#,
    ),
    (
        "unusedRecursiveValue",
        r#"def bad (a b : Nat) : Nat := let unused := bad a b; 42
termination_by (a, b)
decreasing_by exact Prod.Lex.right a (Nat.succ_pos b)"#,
    ),
    (
        "uncheckedMeasure",
        r#"def bad (a b : Nat) : Nat := if h : 0 < a then bad 0 (b + 1) else 0
termination_by (a, missing)
decreasing_by exact Prod.Lex.left (b + 1) b h"#,
    ),
    (
        "changingMeasureType",
        r#"local instance (bound : Nat) : WellFoundedRelation (Fin bound) :=
  invImage (fun p : Fin bound => p.val) Nat.lt_wfRel
def bad (bound : Nat) (p : Fin (Nat.succ bound)) : Nat :=
  if h : 0 < bound then bad 0 (Fin.mk 0 (Nat.succ_pos 0)) else 0
termination_by p
decreasing_by exact h"#,
    ),
    (
        "selectedEmptyRelation",
        r#"local instance : WellFoundedRelation Nat :=
  invImage (fun _ : Nat => 0) Nat.lt_wfRel
def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0
termination_by n
decreasing_by exact h"#,
    ),
    (
        "staleDependentArgument",
        r#"def bad (a b : Nat) (p : Fin (Nat.succ b)) : Nat :=
  if hb : 0 < b then bad a (b - 1) p else 0
termination_by (a, b)
decreasing_by exact Prod.Lex.right a (Nat.sub_lt hb (Nat.succ_pos 0))"#,
    ),
    (
        "proofHole",
        r#"def bad (a b : Nat) : Nat := if h : 0 < a then bad 0 (b + 1) else 0
termination_by (a, b)
decreasing_by exact _"#,
    ),
    (
        "opaqueApplyMeasure",
        r#"@[irreducible] def opaqueMeasure (n : Nat) : Nat := n
def bad (a b : Nat) : Nat :=
  if h : 0 < a then bad 0 (b + 1) + 42 else 0
termination_by (opaqueMeasure a, b)
decreasing_by
  apply Prod.Lex.left
  exact h"#,
    ),
];

pub(super) fn assert_relation_programs(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    let mut failures = Vec::new();
    for (name, definition, application, expected) in PROGRAMS {
        let source = format!("{definition}\ndef answer : Nat := {application}");
        match base.execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        ) {
            Ok(result) => {
                let result = result
                    .into_complete()
                    .expect("relation computation finishes");
                let values: Vec<_> = result
                    .executions
                    .iter()
                    .filter_map(|execution| {
                        fln::closed_vm_value(&execution.exit).expect("normal native VM exit")
                    })
                    .collect();
                if values != vec![ClosedVmValue::Scalar(*expected)] {
                    failures.push(format!("{name}: unexpected computation {values:?}"));
                }
                // The packed continuation and its staged callback interface
                // must survive serialization without the source Engine.
                let replayed: Vec<_> = result
                    .executions
                    .iter()
                    .filter_map(|execution| {
                        let replay = fln::execute_flbc_artifact(
                            &execution.flbc_artifact,
                            &KVMap::new(),
                            Default::default(),
                        )
                        .unwrap_or_else(|error| panic!("{name}: FLBC decoding failed: {error:?}"))
                        .into_complete()
                        .unwrap_or_else(|stop| panic!("{name}: FLBC replay stopped: {stop:?}"));
                        fln::closed_vm_value(&replay)
                            .unwrap_or_else(|error| panic!("{name}: FLBC replay exit: {error:?}"))
                    })
                    .collect();
                if replayed != vec![ClosedVmValue::Scalar(*expected)] {
                    failures.push(format!("{name}: unexpected FLBC replay {replayed:?}"));
                }
            }
            Err(error) => failures.push(format!("{name}: {error:?}")),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    for (name, definition) in REFUSALS {
        // Even a valid declaration before the bad recursive definition cannot
        // expose a partially admitted successor when the batch fails.
        let source = format!("def prepared : Nat := 42\n{definition}");
        match base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(super::limits()),
        ) {
            Ok(_) => failures.push(format!("{name}: invalid relation definition was accepted")),
            Err(error) if format!("{error:?}").contains("Frontend(Parse(") => {
                failures.push(format!("{name}: refusal failed to parse: {error:?}"));
            }
            Err(error)
                if matches!(
                    error.disposition().0,
                    "resource" | "inconclusive" | "internal-fault"
                ) =>
            {
                failures.push(format!("{name}: expected a semantic refusal: {error:?}"));
            }
            Err(error)
                if *name == "changingMeasureType"
                    && !format!("{error:?}")
                        .contains("WellFoundedMeasureDependsOnVaryingParameter") =>
            {
                failures.push(format!(
                    "{name}: expected the varying measure-codomain refusal: {error:?}"
                ));
            }
            Err(_) => {}
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

pub(super) fn assert_relation_execution_budget(base: &Engine) {
    let (_, definition, application, expected) = PROGRAMS[0];
    let source = format!("{definition}\ndef answer : Nat := {application}");
    let root = base.logical_root(&KVMap::new());
    let idle_source = format!("{definition}\ndef answer : Nat := lexCount 0 0");
    let idle = base
        .execute_source_definitions(
            &[idle_source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        )
        .expect("the same checked fixpoint executes its base case")
        .into_complete()
        .expect("the base case finishes");
    let idle_exit = &idle.executions.last().expect("base-case execution").exit;
    assert_eq!(
        fln::closed_vm_value(idle_exit).expect("normal base-case exit"),
        Some(ClosedVmValue::Scalar(0))
    );
    let fln::VmExit::Returned(idle_result) = idle_exit else {
        panic!("the base case must return")
    };
    let idle_steps = idle_result.usage.steps;
    let mut bounded = EngineExecutionLimits::new(super::limits().kernel);
    bounded.vm.max_steps = idle_steps;
    let stopped = base
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), bounded)
        .expect("the well-founded proof checks before the VM budget is reached");
    assert!(matches!(
        stopped,
        fln::Outcome::Inconclusive(stop) if matches!(stop.cause,
            fln_core::outcome::InconclusiveCause::ResourceExhausted { ref usage }
                if usage.reason == fln_core::diag::ResourceReason::ExecutionSteps
                    && usage.allowed == idle_steps && usage.observed == idle_steps + 1)
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    let recovered = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        )
        .expect("a bounded stop leaves a clean retry")
        .into_complete()
        .expect("the same relation computation completes with its normal budget");
    let values: Vec<_> = recovered
        .executions
        .iter()
        .filter_map(|execution| {
            fln::closed_vm_value(&execution.exit).expect("normal native VM exit")
        })
        .collect();
    assert_eq!(values, vec![ClosedVmValue::Scalar(expected)]);
    let fln::VmExit::Returned(recovered_result) = &recovered.executions.last().unwrap().exit else {
        panic!("the recovered computation must return")
    };
    assert!(recovered_result.usage.steps > idle_steps);
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

pub(super) fn assert_relation_requires_computability(base: &Engine) {
    // With only Init.WFTactics, the Reference refuses to compile this same
    // direct application of WellFounded.fix (pinned lean v4.32.0, `prelude`,
    // `import Init.WFTactics`): "failed to compile definition, consider marking
    // it as 'noncomputable' because it depends on 'WellFounded.fix', which is
    // 'noncomputable'". The checked fix_eq_fixC theorem and its executable
    // implementation must be present before native lowering.
    let (_, definition, application, _) = PROGRAMS[11];
    let source = format!("{definition}\ndef answer : Nat := {application}");
    let root = base.logical_root(&KVMap::new());
    let error = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        )
        .expect_err("generic fix execution requires its imported checked computability rule");
    assert!(
        error.to_string().contains(
            "failed to compile definition, consider marking it as 'noncomputable' because it \
             depends on 'WellFounded.fix', which is 'noncomputable'"
        ),
        "the missing checked executable rule is refused as the pin refuses it: {error}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
