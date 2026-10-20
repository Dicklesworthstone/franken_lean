//! Occurrence-first synthesis of simplifier theorem parameters.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

use fln::source_check::SourceCheckError;
use fln::{DefinitionFrontendError, EngineExecutionError};
use fln_elab::{NatDefinitionElabError, source::SourceInferenceError};
const DECLARATIONS: &str = r#"
class Choice where
  marker : Nat
axiom observe [c : Choice] : Nat
axiom observe_eq [c : Choice] : @observe c = c.marker
abbrev other : Choice := { marker := 42 }
"#;

fn check(tail: &str, expected: bool) {
    let source = format!("{DECLARATIONS}\n{tail}\n");
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let actual = match engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    ) {
        Ok(outcome) => {
            outcome
                .into_complete()
                .expect("both checking engines complete");
            true
        }
        Err(error) => {
            eprintln!("{source}\n{error:?}");
            let SourceCheckError::Command { error, .. } = error else {
                panic!("not a completed tactic refusal: {error:?}");
            };
            let EngineExecutionError::Frontend(DefinitionFrontendError::Elaborate(
                NatDefinitionElabError::Inference(reason),
            )) = *error
            else {
                panic!("not an elaborator refusal: {error:?}");
            };
            match reason {
                SourceInferenceError::InstanceSynthesisRequired => {}
                SourceInferenceError::Tactic(reason) => assert!(
                    matches!(
                        format!("{reason:?}").as_str(),
                        "SimplificationNoProgress"
                            | "DefinitionalSimplificationNoProgress"
                            | "RewriteNoMatch"
                            | "UnsolvedGoals { count: 1 }"
                    ),
                    "not a completed nonmatch: {reason:?}"
                ),
                _ => {
                    panic!("resource failure or other fault is not a negative control: {reason:?}")
                }
            }
            false
        }
    };
    assert_eq!(actual, expected, "{source}");
    reference_verdict(&source, expected);
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn theorem_instance_is_inferred_without_a_global_instance() {
    check(
        "theorem test : @observe other = @Choice.marker other := by simp only [observe_eq]",
        true,
    );
}
#[test]
fn an_explicit_dictionary_is_not_replaced_by_a_competing_global_instance() {
    check(
        "instance : Choice := { marker := 7 }\ntheorem test : @observe other = @Choice.marker other := by simp only [observe_eq]",
        true,
    );
}
#[test]
fn a_missing_synthesis_only_premise_does_not_block_a_later_rule() {
    check(
        "class Permission where\n  marker : Nat\naxiom guarded [c : Choice] [Permission] : @observe c = @Choice.marker c\ntheorem test : @observe other = @Choice.marker other := by simp only [guarded, observe_eq]",
        true,
    );
}
#[test]
fn matching_does_not_invent_missing_class_evidence() {
    check(
        "class Permission where\n  marker : Nat\naxiom guarded [c : Choice] [Permission] : @observe c = @Choice.marker c\ntheorem test : @observe other = @Choice.marker other := by simp only [guarded]",
        false,
    );
}
#[test]
fn remaining_instance_parameters_are_synthesized_after_matching() {
    check(
        "class Permission where\n  marker : Nat\ninstance : Permission := { marker := 0 }\naxiom guarded [c : Choice] [Permission] : @observe c = @Choice.marker c\ntheorem test : @observe other = @Choice.marker other := by simp only [guarded]",
        true,
    );
}
#[test]
fn assigned_instance_option_rechecks_the_selected_dictionary() {
    check(
        "set_option tactic.skipAssignedInstances false in\ntheorem test : @observe other = @Choice.marker other := by simp only [observe_eq]",
        false,
    );
    check(
        "instance : Choice := { marker := 7 }\nset_option tactic.skipAssignedInstances false in\ntheorem test : @observe other = @Choice.marker other := by simp only [observe_eq]",
        false,
    );
    check(
        "instance : Choice := other\nset_option tactic.skipAssignedInstances false in\ntheorem test : @observe other = @Choice.marker other := by simp only [observe_eq]",
        true,
    );
}
#[test]
fn simpa_matches_dictionaries_but_plain_rw_keeps_its_boundary() {
    check(
        "theorem test : @observe other = @Choice.marker other := by simpa only [observe_eq]",
        true,
    );
    check(
        "theorem test : @observe other = @Choice.marker other := by rw [@observe_eq other]",
        true,
    );
    check(
        "theorem test : @observe other = @Choice.marker other := by rw [observe_eq]",
        false,
    );
}

#[test]
fn proof_valued_classes_can_be_discharged_from_local_evidence() {
    check(
        "class Evidence : Prop where\n  witness : True\naxiom guarded [c : Choice] (h : Evidence) : @observe c = @Choice.marker c\ntheorem test (h : Evidence) : @observe other = @Choice.marker other := by simp only [guarded, h]",
        true,
    );
}
#[test]
fn ordinary_class_parameters_are_synthesized_without_instance_binder_syntax() {
    check(
        "class Permission where\n  marker : Nat\ninstance : Permission := { marker := 0 }\naxiom guarded (c : Choice) (p : Permission) : @observe c = @Choice.marker c\ntheorem test : @observe other = @Choice.marker other := by simp only [guarded]",
        true,
    );
}
#[test]
fn an_unmatched_rule_does_not_demand_its_dictionary() {
    check(
        "class Permission where\n  marker : Nat\naxiom unrelated : Nat\naxiom unrelated_eq [Permission] : unrelated = 0\ntheorem test : @observe other = @Choice.marker other := by simp only [unrelated_eq, observe_eq]",
        true,
    );
}
#[test]
fn polymorphic_dictionary_inputs_come_from_the_occurrence() {
    check(
        "class Holder (A : Type) where\n  value : A\naxiom see {A : Type} [h : Holder A] : A\naxiom see_eq {A : Type} [h : Holder A] : @see A h = h.value\nabbrev dict : Holder Nat := { value := 42 }\ntheorem test : @see Nat dict = @Holder.value Nat dict := by simp only [see_eq]",
        true,
    );
}

fn reference_verdict(source: &str, expected: bool) {
    use std::path::PathBuf;
    use std::process::Command;
    use std::sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    };
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let reference = REFERENCE.get_or_init(|| {
        let pin = include_str!("../../../SUITE.lock")
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .unwrap();
        let field = |key: &str| {
            pin.split_whitespace()
                .find_map(|w| w.strip_prefix(key))
                .unwrap()
        };
        let tag = field("tag=");
        let commit = field("commit=");
        let lib = std::env::var_os("FLN_REFERENCE_LIB")
            .map(PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    PathBuf::from(home)
                        .join(".elan/toolchains")
                        .join(format!("leanprover--lean4---{tag}"))
                        .join("lib/lean")
                })
            });
        let executable = lib
            .and_then(|lib| lib.parent()?.parent().map(|p| p.join("bin/lean")))
            .filter(|p| p.is_file());
        let Some(executable) = executable else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference required"
            );
            eprintln!("SKIP: dictionary differential requires the pinned Reference");
            return None;
        };
        let result = Command::new(&executable).arg("--version").output().unwrap();
        let version = String::from_utf8(result.stdout).unwrap();
        assert!(
            result.status.success()
                && version.contains(tag.trim_start_matches('v'))
                && version.contains(commit),
            "wrong Reference: {version}"
        );
        Some(executable)
    });
    let Some(reference) = reference else {
        return;
    };
    let dir = std::env::temp_dir().join(format!("fln-simp-dictionaries-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let result = Command::new(reference).arg(&path).output().unwrap();
    assert_eq!(
        result.status.code(),
        Some(if expected { 0 } else { 1 }),
        "Reference disagrees: {source}\n{}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
