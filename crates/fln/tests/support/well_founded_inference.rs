//! Nat measure inference and default proofs reuse the imported checked fixpoint.
//! These source cases follow the pinned WF/GuessLex and WFTactics definitions.
#![forbid(unsafe_code)]
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, SourceCheckLimits};
use fln_core::outcome::InconclusiveCause;
use fln_elab::NatDefinitionElabError;
use fln_elab::arithmetic::{
    ArithmeticProvider, LinearConstraint, OmegaCertificate, OmegaLimits, OmegaOutcome,
};
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;

const PROGRAMS: &[(&str, &str, &str)] = &[
    (
        "suppliedProof",
        "def suppliedProof (n : Nat) : Nat := if h : 0 < n then suppliedProof 0 + 42 else 0\ndecreasing_by exact h",
        "suppliedProof 42",
    ),
    (
        "suppliedMeasure",
        "def suppliedMeasure (n : Nat) : Nat := if h : 0 < n then suppliedMeasure (n - 1) + 1 else 0\ntermination_by n",
        "suppliedMeasure 42",
    ),
    (
        "automaticCountdown",
        "def automaticCountdown (n : Nat) : Nat := if h : 0 < n then automaticCountdown (n - 1) + 1 else 0",
        "automaticCountdown 42",
    ),
    (
        "laterMeasure",
        "def laterMeasure (acc n : Nat) : Nat := if h : 0 < n then laterMeasure (acc + 1) (n - 1) else acc",
        "laterMeasure 0 42",
    ),
    (
        "fixedCandidate",
        "def fixedCandidate (step n : Nat) : Nat := if h : 0 < n then fixedCandidate step 0 + step else 0\ndecreasing_by exact h",
        "fixedCandidate 42 1",
    ),
    (
        "packedProof",
        "def packedProof (acc n : Nat) : Nat := if h : 0 < n then packedProof (acc + 1) (n - 1) else acc\ndecreasing_by exact Nat.sub_lt h (Nat.succ_pos 0)",
        "packedProof 0 42",
    ),
    (
        "fixedMiddleAutomatic",
        "def fixedMiddleAutomatic (n step acc : Nat) : Nat := if h : 0 < n then fixedMiddleAutomatic (n - 1) step (acc + step) else acc",
        "fixedMiddleAutomatic 21 2 0",
    ),
    (
        "lambdaAutomatic",
        "def lambdaAutomatic : Nat -> Nat -> Nat := fun acc n => if h : 0 < n then lambdaAutomatic (acc + 1) (n - 1) else acc",
        "lambdaAutomatic 0 42",
    ),
    (
        "matchFallback",
        "def matchFallback (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => if h : 0 < k then matchFallback (k - 1) + 2 else 1",
        "matchFallback 42",
    ),
    (
        "projectedMeasure",
        "def projectedMeasure (p : Nat × Nat) : Nat := if h : 0 < p.1 then projectedMeasure (p.1 - 1, p.2) + p.2 else 0\ntermination_by p.1",
        "projectedMeasure (21, 2)",
    ),
    (
        "severalCalls",
        "def severalCalls (n : Nat) : Nat := if h : 0 < n then severalCalls 0 + severalCalls (n - 1) + 1 else 0",
        "severalCalls 42",
    ),
    (
        "singleCandidateScript",
        "def singleCandidateScript (n : Nat) : Nat := if h : 0 < n then singleCandidateScript 0 + singleCandidateScript (n - 1) + 1 else 0\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
        "singleCandidateScript 42",
    ),
    (
        "automaticLet",
        "def automaticLet (n : Nat) : Nat := if h : 0 < n then let smaller := n - 1; automaticLet smaller + 1 else 0",
        "automaticLet 42",
    ),
    (
        "identitySize",
        "local instance : SizeOf Nat := ⟨fun n => n⟩\ndef identitySize (n : Nat) : Nat := if h : 0 < n then identitySize (n - 1) + 1 else 0",
        "identitySize 42",
    ),
    (
        "ordinaryRelation",
        "local instance : WellFoundedRelation Nat := Nat.lt_wfRel\ndef ordinaryRelation (n : Nat) : Nat := if h : 0 < n then ordinaryRelation (n - 1) + 1 else 0",
        "ordinaryRelation 42",
    ),
    (
        "explicitProofContext",
        "def explicitProofContext (n : Nat) (xs : List Nat) : Nat := if h : 0 < n then explicitProofContext 0 (0 :: xs) + 42 else 0\ntermination_by n\ndecreasing_by\n  have copied : List Nat := xs\n  exact h",
        "explicitProofContext 42 []",
    ),
];

const REFUSALS: &[&str] = &[
    "def bad (n : Nat) : Nat := if h : 0 < n then bad n else 0",
    "def bad (n : Nat) : Nat := bad (n + 1)",
    // An explicit measure is not replaced by a better inferred one.
    "def bad (a n : Nat) : Nat := if h : 0 < n then bad (a + 1) (n - 1) else a\ntermination_by a",
    // A supplied proof is not repaired by automatic proof search.
    "def bad (n : Nat) : Nat := if h : 0 < n then bad (n - 1) else 0\ntermination_by n\ndecreasing_by exact Nat.succ_pos n",
    "def bad (n : Nat) : Nat := if h : 0 < n then bad (n - 1) else 0\ndecreasing_by exact Nat.succ_pos n",
    "def bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ndecreasing_by exact missing",
    // A structural hint still requires structural recursion.
    "def bad (n : Nat) : Nat := match n with | 0 => 0 | k + 1 => if h : 0 < k then bad (k - 1) else 0\ntermination_by structural n",
    // Multiple plausible measures require the supplied script to work on one call.
    "def bad (a n : Nat) : Nat := if h : 0 < n then bad (a + 1) 0 + bad (a + 1) (n - 1) else a\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    // Unsupported SizeOf and derived candidates also disable the singleton shortcut.
    "def bad (n : Nat) (xs : List Nat) : Nat := if h : 0 < n then bad 0 (0 :: xs) + bad (n - 1) (0 :: xs) else 0\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    "def bad (n : Nat) : Nat := if h : 0 < n then if h' : 0 < n + 1 then bad 0 + bad (n - 1) else 0 else 0\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    // A fixed-parameter comparison may contribute a measure before cleanup drops it.
    "def bad (k n : Nat) : Nat := if h : 0 < n then if h' : 0 < k + 1 then bad k 0 + bad k (n - 1) else 0 else 0\ndecreasing_by\n  exact h\n  exact Nat.sub_lt h (Nat.succ_pos 0)",
    // The first measure passes single-goal probes but fails the final script.
    // That final failure must not trigger a successful retry using n.
    "def bad (a n : Nat) : Nat := if ha : 0 < a then if hn : 0 < n then bad 0 0 + bad (a - 1) (n - 1) else 0 else 0\ndecreasing_by\n  first\n  | exact ha\n    done\n  | exact Nat.sub_lt ha (Nat.succ_pos 0)\n    done\n  | all_goals\n      first\n      | exact hn\n      | exact Nat.sub_lt hn (Nat.succ_pos 0)",
    // A viable earlier lexicographic prefix cannot be skipped for a later Nat measure.
    "def bad (a n : Nat) : Nat := if ha : 0 < a then if hn : 0 < n then bad a 0 + bad (a - 1) (n - 1) else 0 else 0\ndecreasing_by all_goals first | exact hn | exact Nat.sub_lt hn (Nat.succ_pos 0) | exact Nat.sub_lt ha (Nat.succ_pos 0)",
    // Inference cleans the direct comparison; the final packed relation retains more data.
    "def bad (n : Nat) (xs : List Nat) : Nat := if h : 0 < n then bad 0 (0 :: xs) else 0\ndecreasing_by\n  have copied : List Nat := xs\n  exact h",
    // This bounded supplied-script path cannot skip earlier non-Nat SizeOf candidates.
    "def unsupportedLeadingSizeOf (xs : List Nat) (n : Nat) : Nat := if h : 0 < n then unsupportedLeadingSizeOf (0 :: xs) 0 else 0\ndecreasing_by exact h",
    // The pin's search also tries `n - i` for the hypothesis `i < n` (accepted there,
    // `termination_by (b, n - i)`); this one does not.
    "def needsDifference (i n b : Nat) : Nat := if hb : 0 < b then needsDifference i n (b - 1) else if h : i < n then needsDifference (i + 1) n b else 0",
    // Both measure selection and the final relation honor instance shadowing.
    "def bad [SizeOf Nat] (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ndecreasing_by exact h",
    "local instance : SizeOf Nat := ⟨fun _ => 0⟩\ndef bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ndecreasing_by exact h",
    "local instance : SizeOf Nat := ⟨fun _ => 0⟩\ndef bad (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by n\ndecreasing_by exact h",
    "def bad [WellFoundedRelation Nat] (n : Nat) : Nat := if h : 0 < n then bad 0 else 0\ntermination_by n\ndecreasing_by exact h",
];

pub(super) fn assert_automatic_termination(base: &Engine) {
    let mut failures = Vec::new();
    let root = base.logical_root(&KVMap::new());
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
                    .expect("termination checking finishes");
                let values: Vec<_> = result
                    .executions
                    .iter()
                    .filter_map(|execution| {
                        fln::closed_vm_value(&execution.exit).expect("normal native VM exit")
                    })
                    .collect();
                if values != vec![ClosedVmValue::Scalar(42)] {
                    failures.push(format!("{name}: unexpected computation {values:?}"));
                }
            }
            Err(error) => failures.push(format!("{name}: {error:?}")),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    for source in REFUSALS {
        match base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(super::limits()),
        ) {
            Ok(_) => failures.push(format!("incorrectly accepted: {source}")),
            Err(error) if format!("{error:?}").contains("Frontend(Parse(") => {
                failures.push(format!("refusal case failed to parse: {source}\n{error:?}"));
            }
            Err(error)
                if matches!(
                    error.disposition().0,
                    "resource" | "inconclusive" | "internal-fault"
                ) =>
            {
                failures.push(format!("expected a semantic refusal: {source}\n{error:?}"));
            }
            Err(_) => {}
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    // The ordinary structural result keeps its definitional equation, even
    // under instances that would prevent the well-founded fallback.
    base.check_source_files(
        &["local instance : SizeOf Nat := ⟨fun _ => 0⟩\ndef structuralFirst : Nat -> Nat | 0 => 0 | n + 1 => structuralFirst n + 1\ntheorem structuralStep (n : Nat) : structuralFirst (n + 1) = structuralFirst n + 1 := by rfl".as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(super::limits()),
    )
    .expect("structural elaboration remains the first candidate")
    .into_complete()
    .expect("structural source proof finishes");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

pub(super) fn assert_omitted_result_types(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    let mut failures = Vec::new();
    for (definition, answer, expected) in [
        (
            "def steps (n : Nat) : Nat := if h : n < 99 then n else steps (n - 99)",
            "def answer : Nat := steps 250",
            ClosedVmValue::Scalar(52),
        ),
        (
            "def steps (n : Nat) := if h : n < 99 then n else steps (n - 99)",
            "def answer : Nat := steps 250",
            ClosedVmValue::Scalar(52),
        ),
        (
            "def steps (n : Nat) := if h : n < 99 then n else steps (n - 99)\ntermination_by n",
            "def answer : Nat := steps 250",
            ClosedVmValue::Scalar(52),
        ),
        (
            "def carry (text : String) (n : Nat) := if h : 0 < n then carry text (n - 1) else text\ntermination_by n",
            "def answer : String := carry \"inferred\" 3",
            ClosedVmValue::String("inferred".to_string()),
        ),
        (
            "def indeterminate (n : Nat) := if h : 0 < n then indeterminate (n - 1) else (fun (x : Nat) => x)\ntermination_by n",
            "def answer : Nat := indeterminate 3 52",
            ClosedVmValue::Scalar(52),
        ),
    ] {
        let source = format!("{definition}\n{answer}");
        match base.execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(super::limits().kernel),
        ) {
            Ok(result) => {
                let result = result
                    .into_complete()
                    .expect("inferred computation finishes");
                let values: Vec<_> = result
                    .executions
                    .iter()
                    .filter_map(|execution| {
                        fln::closed_vm_value(&execution.exit).expect("normal native VM exit")
                    })
                    .collect();
                assert_eq!(values, vec![expected], "{source}");
            }
            Err(error) => failures.push(format!("{source}\n{error:?}")),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let unknown = b"def indeterminate (n : Nat) := if h : 0 < n then indeterminate (n - 1) else (fun x => x)\ntermination_by n";
    let error = base
        .check_source_files(
            &[unknown],
            &KVMap::new(),
            SourceCheckLimits::new(super::limits()),
        )
        .expect_err("an unconstrained binder cannot supply a recursive result type");
    if !format!("{error:?}").contains("UnresolvedHoles") {
        failures.push(format!(
            "the refusal must identify an unresolved type, not termination or resource exhaustion: {error:?}"
        ));
    }
    let non_decreasing = b"def bad (n : Nat) := if h : 0 < n then bad n else 0";
    let error = base
        .check_source_files(
            &[non_decreasing],
            &KVMap::new(),
            SourceCheckLimits::new(super::limits()),
        )
        .expect_err("inference cannot admit a non-decreasing recursive call");
    assert!(
        !matches!(
            error.disposition().0,
            "resource" | "inconclusive" | "internal-fault"
        ),
        "a non-decreasing definition must be refused semantically: {error:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
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

pub(super) fn assert_search_stops(base: &Engine) {
    // The first candidate needs arithmetic, while a later one is provable by
    // assumption. An accelerator stop cannot become a successful later choice.
    let source = b"def boundary (a n : Nat) : Nat := if h : 0 < n then boundary (a + 1) 0 else a";
    let parsed = fln_parse::parse_definition(source).expect("termination boundary source parses");
    let root = base.logical_root(&KVMap::new());
    for (provider, label) in [
        (
            cancelled as fn(&[LinearConstraint], OmegaLimits) -> OmegaOutcome,
            "cancelled",
        ),
        (exhausted, "resource"),
        (malformed, "certificate"),
    ] {
        let scope = SourceScope {
            arithmetic: Some(ArithmeticProvider(provider)),
            ..SourceScope::default()
        };
        let result = fln_elab::elaborate_definition_in_scope_with_budget(
            parsed.syntax(),
            base.environment(),
            super::limits().kernel,
            &scope,
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
            (_, result) => panic!("candidate search must propagate {label}: {result:?}"),
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    base.check_source_files(
        &[source],
        &KVMap::new(),
        SourceCheckLimits::new(super::limits()),
    )
    .expect("the ordinary arithmetic provider permits a later valid measure")
    .into_complete()
    .expect("ordinary inference recovers after isolated provider failures");
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
