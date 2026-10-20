//! The bounded default decreasing prover shares the existing checked Nat
//! fixpoint and ordinary source arithmetic. Explicit scripts retain priority.
#![forbid(unsafe_code)]
use super::limits;
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::outcome::InconclusiveCause;
use fln_elab::NatDefinitionElabError;
use fln_elab::arithmetic::{
    ArithmeticProvider, LinearConstraint, OmegaCertificate, OmegaLimits, OmegaOutcome,
};
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;

const COUNTDOWN: &str = "def countdownAuto (n : Nat) : Nat :=\n  if h : 0 < n then countdownAuto (n - 1) + 1 else 0\ntermination_by n";

fn computation(base: &Engine, source: &str, call: &str, expected: usize) {
    let before = base.logical_root(&KVMap::new());
    let source = format!("{source}\ndef automaticAnswer : Nat := {call}");
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{call}: {error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{call}: incomplete execution: {reason:?}"));
    let values: Vec<_> = result
        .executions
        .iter()
        .filter_map(|execution| fln::closed_vm_value(&execution.exit).expect("normal VM exit"))
        .collect();
    assert_eq!(values, vec![ClosedVmValue::Scalar(expected)], "{call}");
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["automaticAnswer"]))
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

pub(super) fn assert_arithmetic_proofs(base: &Engine) {
    for (source, call, expected) in [
        (COUNTDOWN, "countdownAuto 42", 42),
        (
            "def accumulateAuto (acc n : Nat) : Nat :=\n  if h : 0 < n then accumulateAuto (acc + 2) (n - 1) else acc\ntermination_by n",
            "accumulateAuto 0 21",
            42,
        ),
        // Written Omega proofs see the same reduced argument-pack operands.
        (
            "def explicitPacked (acc n : Nat) : Nat :=\n  if h : 0 < n then explicitPacked (acc + 2) (n - 1) else acc\ntermination_by n\ndecreasing_by omega",
            "explicitPacked 0 21",
            42,
        ),
        (
            "def smallFibAuto (n : Nat) : Nat :=\n  if h : 1 < n then smallFibAuto (n - 1) + smallFibAuto (n - 2) else 1\ntermination_by n",
            "smallFibAuto 5",
            8,
        ),
        (
            "def lambdaCountdownAuto : Nat → Nat := fun n =>\n  if h : 0 < n then lambdaCountdownAuto (n - 1) + 1 else 0\ntermination_by size => size",
            "lambdaCountdownAuto 42",
            42,
        ),
        (
            "def dependentAuto (n : Nat) (p : Fin (n + 1)) : Nat :=\n  if h : 0 < n then dependentAuto (n - 1) ⟨0, Nat.succ_pos (n - 1)⟩ + 1 else p.val\ntermination_by n",
            "dependentAuto 42 ⟨0, Nat.succ_pos 42⟩",
            42,
        ),
        (
            "def nonzeroAuto (n : Nat) : Nat :=\n  if h : n = 0 then 0 else nonzeroAuto (n - 1) + 1\ntermination_by n",
            "nonzeroAuto 42",
            42,
        ),
        // An inactive scoped SizeOf override must not affect inference.
        (
            "namespace ZeroMeasure\nscoped instance zeroSize : SizeOf Nat := ⟨fun _ => 0⟩\nend ZeroMeasure\ndef scopedCountdown (n : Nat) : Nat := if h : 0 < n then scopedCountdown (n - 1) + 1 else 0",
            "scopedCountdown 42",
            42,
        ),
    ] {
        computation(base, source, call, expected);
    }
}

pub(super) fn assert_refusals_and_recovery(base: &Engine) {
    let before = base.logical_root(&KVMap::new());
    for source in [
        "def unchangedAuto (n : Nat) : Nat := if h : 0 < n then unchangedAuto n else 0\ntermination_by n",
        "def increasingAuto (n : Nat) : Nat := increasingAuto (n + 1)\ntermination_by n",
        "def unguardedAuto (n : Nat) : Nat := unguardedAuto (n - 1)\ntermination_by n",
        "def constantMeasureAuto (n : Nat) : Nat := if h : 0 < n then constantMeasureAuto (n - 1) else 0\ntermination_by 0",
        "def secondCallAuto (n : Nat) : Nat := if h : 1 < n then secondCallAuto (n - 1) + secondCallAuto n else 0\ntermination_by n",
        "def explicitBadProof (n : Nat) : Nat := if h : 0 < n then explicitBadProof (n - 1) else 0\ntermination_by n\ndecreasing_by exact h",
        "def wrongMeasureAuto (n : Nat) : Nat := if h : 0 < n then wrongMeasureAuto (n - 1) else 0\ntermination_by (n : Bool)",
        "def unrelatedFalseAuto (impossible : False) (n : Nat) : Nat := if h : 0 < n then unrelatedFalseAuto impossible (n - 1) else 0\ntermination_by 0",
        // A valid first call does not excuse another nondecreasing call or an
        // invalid initializer whose value the recursive result never uses.
        "def badSecond (n : Nat) : Nat := if h : 0 < n then badSecond (n - 1) + badSecond n else 0",
        "def badBody (n : Nat) : Nat := if h : 0 < n then let answer := badBody (n - 1); let ignored : String := (0 : Nat); answer else 0",
        // Opening the same scoped override changes the selected dictionary.
        "namespace ZeroMeasure\nscoped instance zeroSize : SizeOf Nat := ⟨fun _ => 0⟩\nend ZeroMeasure\nopen scoped ZeroMeasure\ndef scopedCountdown (n : Nat) : Nat := if h : 0 < n then scopedCountdown (n - 1) + 1 else 0",
    ] {
        let refusal = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert!(
            !matches!(
                refusal.disposition().0,
                "resource" | "inconclusive" | "internal-fault"
            ),
            "{source}: {refusal:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    computation(base, COUNTDOWN, "countdownAuto 42", 42);
}

fn cancelled(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    fln_anvil::omega::solve_with_cancel(inputs, limits, &mut || true)
}

fn exhausted(inputs: &[LinearConstraint], mut limits: OmegaLimits) -> OmegaOutcome {
    limits.max_steps = 0;
    fln_anvil::omega::solve(inputs, limits)
}

fn malformed(inputs: &[LinearConstraint], _: OmegaLimits) -> OmegaOutcome {
    OmegaOutcome::Unsat {
        certificate: OmegaCertificate {
            version: 1,
            inputs: inputs.to_vec(),
            steps: Vec::new(),
            conclusion: 0,
        },
        steps_used: 1,
    }
}

pub(super) fn assert_provider_stops(base: &Engine) {
    let before = base.logical_root(&KVMap::new());
    let parsed = fln_parse::parse_definition(COUNTDOWN.as_bytes())
        .expect("automatic decreasing source parses");
    for (provider, label) in [
        (
            cancelled as fn(&[LinearConstraint], OmegaLimits) -> OmegaOutcome,
            "cancelled",
        ),
        (exhausted, "resource"),
        (malformed, "certificate"),
    ] {
        let result = fln_elab::elaborate_definition_in_scope_with_budget(
            parsed.syntax(),
            base.environment(),
            limits().kernel,
            &SourceScope {
                arithmetic: Some(ArithmeticProvider(provider)),
                ..SourceScope::default()
            },
        );
        match (label, result) {
            (
                "cancelled",
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ArithmeticInconclusive(reason),
                )),
            ) => {
                assert!(matches!(reason.cause, InconclusiveCause::Cancelled { .. }));
            }
            (
                "resource",
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ArithmeticInconclusive(reason),
                )),
            ) => {
                assert!(
                    matches!(reason.cause, InconclusiveCause::ResourceExhausted { usage } if usage.is_genuine_exhaustion())
                );
            }
            (
                "certificate",
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(reason))),
            ) => {
                assert_eq!(
                    reason.to_string(),
                    "native arithmetic returned an invalid certificate"
                );
            }
            (_, result) => panic!("automatic decreasing {label} must propagate: {result:?}"),
        }
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    computation(base, COUNTDOWN, "countdownAuto 42", 42);
}
