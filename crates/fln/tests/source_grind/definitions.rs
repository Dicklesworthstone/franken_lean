//! Definition parameters use checked equation families and their left-hand
//! triggers, including ground constants; they never enable general unfolding.
#![forbid(unsafe_code)]

use super::*;

const LOGICAL_ROOTS: &[&str] = &["Init.Grind.Tactics", "Init.Classical"];

const ACCEPT: &[(&str, &str, &[&str])] = &[
    (
        "nested_definition",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip (strip n) = n := by grind [strip]",
        &["strip.eq_1"],
    ),
    (
        "explicit_left_and_default",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [= strip]\nexample (n : Nat) : strip n = n := by grind only [. strip]\nexample (n : Nat) : strip n = n := by grind only [· strip]",
        &["strip.eq_1"],
    ),
    (
        "ground_constant",
        "def token : Nat := 7\nexample : token = 7 := by grind only [token]",
        &["token.eq_1"],
    ),
    (
        "ground_constant_chain",
        "def first : Nat := 7\ndef second : Nat := first\nexample : second = 7 := by grind only [first, second]",
        &["first.eq_1", "second.eq_1"],
    ),
    (
        "ground_proposition",
        "def Yes : Prop := True\nexample : Yes := by grind only [Yes]",
        &["Yes.eq_1"],
    ),
    (
        "predicate_definition",
        "def W (n : Nat) : Prop := n = n\nexample (n : Nat) : W n := by grind only [W]",
        &["W.eq_1"],
    ),
    (
        "definition_and_selected_theorem",
        "def strip (n : Nat) : Nat := n\nopaque stamp : Nat → Nat := fun n => n\naxiom stamp_eq (n : Nat) : stamp n = n\nexample (n : Nat) : stamp (strip (stamp n)) = n := by grind only [strip, = stamp_eq]",
        &["strip.eq_1"],
    ),
    (
        "polymorphic_definition",
        "universe u\ndef idValue {α : Sort u} (x : α) : α := x\nexample {α : Sort u} (x : α) : idValue (idValue x) = x := by grind only [idValue]\nexample (n : Nat) : idValue n = n := by grind only [idValue]",
        &["idValue.eq_1"],
    ),
    (
        "type_valued_definition",
        "def Same (α : Type) : Type := α\nexample : Same Nat = Nat := by grind only [Same]",
        &["Same.eq_1"],
    ),
    (
        "namespace_resolution",
        "namespace Helpers\ndef strip (n : Nat) : Nat := n\nend Helpers\nopen Helpers\nexample (n : Nat) : strip n = n := by grind only [strip]\nexample (n : Nat) : Helpers.strip n = n := by grind only [Helpers.strip]",
        &["Helpers.strip.eq_1"],
    ),
    (
        "unused_parameter_keeps_full_trigger",
        "def chooseFirst (x y : Nat) : Nat := x\nexample (a b : Nat) : chooseFirst a b = a := by grind only [chooseFirst]",
        &["chooseFirst.eq_1"],
    ),
    (
        "pattern_equation_family",
        "def flip : Bool → Bool\n  | false => true\n  | true => false\nexample : flip (flip true) = true := by grind only [flip]",
        &["flip.eq_1", "flip.eq_2"],
    ),
    (
        "structural_recursive_equation_family",
        "def carry : Nat → Nat\n  | 0 => 0\n  | Nat.succ n => Nat.succ (carry n)\nexample (n : Nat) (h : carry n = n) : carry (Nat.succ n) = Nat.succ n := by grind only [carry]",
        &["carry.eq_1", "carry.eq_2"],
    ),
    (
        "previously_realized_equation",
        "def strip (n : Nat) : Nat := n\ntheorem already (n : Nat) : strip n = n := strip.eq_1 n\nexample (n : Nat) : strip (strip n) = n := by grind only [strip]",
        &["strip.eq_1"],
    ),
    (
        "irreducible_definition",
        "@[irreducible] def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [strip]",
        &["strip.eq_1"],
    ),
];

const REFUSE: &[(&str, &str)] = &[
    (
        "unselected_definition",
        "def token : Nat := 7\nexample : token = 7 := by grind only",
    ),
    (
        "unrelated_definition",
        "def first : Nat := 7\ndef second : Nat := 8\nexample : first = 7 := by grind only [second]",
    ),
    (
        "abbreviation_parameter_is_redundant",
        "abbrev strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [strip]",
    ),
    (
        "reducible_parameter_is_redundant",
        "@[reducible] def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [strip]",
    ),
    (
        "unsafe_definition",
        "unsafe def strip (n : Nat) : Nat := n\nexample : True := by grind only [strip]",
    ),
    (
        "opaque_definition",
        "opaque strip : Nat → Nat := fun n => n\nexample : True := by grind only [strip]",
    ),
    (
        "proof_valued_definition",
        "def proof : True := True.intro\nexample : True := by grind only [proof]",
    ),
    (
        "definition_equality_right",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [=_ strip]",
    ),
    (
        "definition_equality_both",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [_=_ strip]",
    ),
    (
        "definition_forward",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [→ strip]",
    ),
    (
        "definition_backward",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [← strip]",
    ),
    (
        "definition_left_right",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [⇒ strip]",
    ),
    (
        "definition_right_left",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [⇐ strip]",
    ),
    (
        "late_unknown_parameter",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by grind only [strip, absent]",
    ),
    (
        "parenthesized_data_is_not_a_proof",
        "def token : Nat := 7\nexample : token = 7 := by grind only [(token)]",
    ),
    (
        "fabricated_equation_name",
        "def strip (n : Nat) : Nat := n\naxiom strip.eq_1 (n : Nat) : strip n = 0\nexample : strip 1 = 0 := by grind only [strip]",
    ),
    (
        "false_goal",
        "def strip (n : Nat) : Nat := n\nexample : strip 1 = 0 := by grind only [strip]",
    ),
];

const GOALS: &[(&str, &str, &str, &str)] = &[
    (
        "definition_closes_before_next_tactic",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by\n  try grind only [strip]\n  rfl",
        "No goals to be solved",
        "NoGoals",
    ),
    (
        "definition_try_sequence_rolls_back",
        "def strip (n : Nat) : Nat := n\nexample (n : Nat) : strip n = n := by try grind only [strip]; rfl",
        "unsolved goals",
        "UnsolvedGoals",
    ),
];

#[test]
fn definition_equations_match_pinned_lean() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
            else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "Reference required"
                );
                eprintln!("SKIP: locked Reference absent");
                return;
            };
            let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
            let version = Command::new(&compiler).arg("--version").output().unwrap();
            assert!(version.status.success());
            assert!(
                String::from_utf8_lossy(&version.stdout)
                    .contains("8c9756b28d64dab099da31a4c09229a9e6a2ef35")
            );
            let directory =
                std::env::temp_dir().join(format!("fln-grind-definitions-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            for (label, source, success, diagnostic) in
                ACCEPT
                    .iter()
                    .map(|(label, source, _)| (*label, *source, true, None))
                    .chain(
                        REFUSE
                            .iter()
                            .map(|(label, source)| (*label, *source, false, None)),
                    )
                    .chain(GOALS.iter().map(|(label, source, expected, _)| {
                        (*label, *source, false, Some(*expected))
                    }))
            {
                let path = directory.join(format!("{label}.lean"));
                std::fs::write(&path, format!("{HEADER}{source}\n")).unwrap();
                let output = Command::new(&compiler)
                    .arg("-j1")
                    .arg(&path)
                    .output()
                    .unwrap();
                let message = format!(
                    "{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                assert_eq!(output.status.success(), success, "pin {label}: {message}");
                if let Some(expected) = diagnostic {
                    assert!(
                        message.contains(expected),
                        "pin {label}: expected {expected:?}, got {message}"
                    );
                }
            }
            let engine = base_with_roots(&library, LOGICAL_ROOTS, 1);
            let options = KVMap::new();
            let before = engine.logical_root(&options);
            let mut failures = Vec::new();
            for (label, source, equations) in ACCEPT {
                eprintln!("grind definition: native {label}");
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Ok(Outcome::Complete(checked)) => {
                        for equation in *equations {
                            assert!(
                                matches!(
                                    checked.engine.environment().find(&name(equation)),
                                    Some(fln_env::constants::ConstantInfo::Thm(_))
                                ),
                                "{label}: {equation} must be an admitted theorem"
                            );
                        }
                    }
                    result => record_failure(&mut failures, label, format!("{result:?}")),
                }
                assert_eq!(engine.logical_root(&options), before, "{label}");
            }
            for (label, source) in REFUSE {
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Err(error)
                        if error.disposition().0 == "elaboration" && error.disposition().2 == 1 => {
                    }
                    result => record_failure(&mut failures, label, format!("{result:?}")),
                }
                assert_eq!(engine.logical_root(&options), before, "{label}");
            }
            for (label, source, _, expected) in GOALS {
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Err(error) if format!("{error:?}").contains(*expected) => {}
                    result => record_failure(&mut failures, label, format!("{result:?}")),
                }
                assert_eq!(engine.logical_root(&options), before, "{label}");
            }
            // Realize on a later source batch as well: the admitted definition
            // is stable, and a resource stop must publish none of its equations.
            let defined = engine
                .check_source_files(&[b"def strip (n : Nat) : Nat := n"], &options, limits())
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            let defined_root = defined.logical_root(&options);
            assert!(!defined.environment().contains(&name("strip.eq_1")));
            let recovery = "example (n : Nat) : strip (strip n) = n := by grind only [strip]";
            let mut exhausted = limits();
            exhausted.admission.kernel.steps = 1;
            match defined.check_source_files(&[recovery.as_bytes()], &options, exhausted) {
                Err(error) if error.disposition().2 == 3 => {}
                Ok(Outcome::Inconclusive(_)) => {}
                result => record_failure(
                    &mut failures,
                    "equation_resource_nonanswer",
                    format!("{result:?}"),
                ),
            }
            assert_eq!(defined.logical_root(&options), defined_root);
            assert!(!defined.environment().contains(&name("strip.eq_1")));
            assert_eq!(engine.logical_root(&options), before);
            let first = defined.check_source_files(&[recovery.as_bytes()], &options, limits());
            let second = defined.check_source_files(&[recovery.as_bytes()], &options, limits());
            match (first, second) {
                (Ok(Outcome::Complete(first)), Ok(Outcome::Complete(second))) => {
                    assert_eq!(first.result_logical_root, second.result_logical_root);
                }
                results => {
                    record_failure(&mut failures, "definition_recovery", format!("{results:?}"))
                }
            }
            assert_eq!(defined.logical_root(&options), defined_root);
            assert!(!defined.environment().contains(&name("strip.eq_1")));
            assert_eq!(engine.logical_root(&options), before);
            assert!(
                failures.is_empty(),
                "grind definition failures: {failures:?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
