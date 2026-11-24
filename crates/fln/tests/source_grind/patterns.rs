//! User trigger groups select real theorem instances without changing their
//! proofs or hiding premises. Compare source behavior with the locked Reference.
#![forbid(unsafe_code)]

use super::*;

const LOGICAL_ROOTS: &[&str] = &["Init.Grind.Tactics", "Init.Classical"];
const PATTERN_HEADER: &str = "prelude\nimport Init.Grind.Tactics\nimport Init.Classical\n";

const ACCEPT: &[(&str, &str)] = &[
    (
        "global_trigger_introduces_missing_function",
        "opaque f : Nat → Nat := fun x => x\nopaque g : Nat → Nat := fun x => x\naxiom inverse (x : Nat) : g (f x) = x\ngrind_pattern inverse => f x\nexample (a b c : Nat) (hb : f b = a) (hc : f c = a) : b = c := by grind",
    ),
    (
        "only_usr_reactivates_registered_trigger",
        "opaque f : Nat → Nat := fun x => x\nopaque g : Nat → Nat := fun x => x\naxiom inverse (x : Nat) : g (f x) = x\ngrind_pattern inverse => f x\nexample (a b c : Nat) (hb : f b = a) (hc : f c = a) : b = c := by grind only [usr inverse]",
    ),
    (
        "simultaneous_patterns_keep_both_proof_premises",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\naxiom transitive (x y z : Nat) : R x y → R y z → R x z\ngrind_pattern transitive => R x y, R y z\nexample (a b c d : Nat) (hab : R a b) (hbc : R b c) (hcd : R c d) : R a d := by grind",
    ),
    (
        "simultaneous_patterns_join_modulo_equalities",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\naxiom transitive (x y z : Nat) : R x y → R y z → R x z\ngrind_pattern transitive => R x y, R y z\nexample (a b c d : Nat) (hbc : b = c) (hab : R a b) (hcd : R c d) : R a d := by grind only [usr transitive]",
    ),
    (
        "every_trigger_in_a_group_must_be_present",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x, mark x\nexample (a b : Nat) (h : mark a = b) : stamp a = a := by grind",
    ),
    (
        "separate_registrations_are_alternatives",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\nopaque other : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x, mark x\ngrind_pattern stamp_eq => stamp x, other x\nexample (a b : Nat) (h : mark a = b) : stamp a = a := by grind only [usr stamp_eq]\nexample (a b : Nat) (h : other a = b) : stamp a = a := by grind only [usr stamp_eq]",
    ),
    (
        "polymorphic_pattern_universes_are_instantiated",
        "universe u\nopaque stamp {α : Type u} (x : α) : α := x\naxiom stamp_eq {α : Type u} (x : α) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nexample (a : Nat) : stamp (stamp a) = a := by grind\nexample {α : Type u} (a : α) : stamp a = a := by grind only [usr stamp_eq]",
    ),
    (
        "ground_constant_trigger",
        "opaque P : Prop := True\naxiom witness : P\ngrind_pattern witness => P\nexample : P := by grind\nexample : P := by grind only [usr witness]",
    ),
    (
        "opaque_proof_uses_registered_trigger",
        "opaque P : Nat → Prop := fun _ => True\naxiom witness (x : Nat) : P x\nopaque sealed (x : Nat) : P x := witness x\ngrind_pattern sealed => P x\nexample (a : Nat) : P a := by grind only [usr sealed]",
    ),
    (
        "proof_definition_uses_original_checked_body",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom both (x : Nat) : P x ∧ Q x\ndef selected (x : Nat) : P x := (both x).left\ngrind_pattern selected => Q x\nexample (a : Nat) (ha : Q a) : P a := by grind only [usr selected]",
    ),
    (
        "checked_projection_trigger_binds_its_receiver",
        "structure Box where\n  value : Nat\nopaque mark : Box → Box := fun x => x\naxiom mark_eq (x : Box) : mark x = x\ngrind_pattern mark_eq => x.value\nexample (x : Box) (v : Nat) (hv : x.value = v) : mark x = x := by grind only [usr mark_eq]",
    ),
    (
        "registered_theorem_keeps_a_required_premise",
        "opaque P : Nat → Prop := fun _ => True\nopaque stamp : Nat → Nat := fun x => x\naxiom conditional (x : Nat) : P x → stamp x = x\ngrind_pattern conditional => stamp x\nexample (a : Nat) (ha : P a) : stamp a = a := by grind",
    ),
    (
        "namespace_registration_and_selection",
        "namespace Helpers\nopaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nend Helpers\nopen Helpers\nexample (a : Nat) : stamp a = a := by grind only [usr stamp_eq]",
    ),
    (
        "repeated_pattern_variable_respects_equality",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\nopaque P : Nat → Prop := fun _ => True\naxiom diagonal (x : Nat) : R x x → P x\ngrind_pattern diagonal => R x x\nexample (a b : Nat) (hab : a = b) (hr : R a b) : P b := by grind",
    ),
];

const REFUSE: &[(&str, &str)] = &[
    (
        "unregistered_theorem_is_not_activated",
        "opaque f : Nat → Nat := fun x => x\nopaque g : Nat → Nat := fun x => x\naxiom inverse (x : Nat) : g (f x) = x\nexample (a b c : Nat) (hb : f b = a) (hc : f c = a) : b = c := by grind",
    ),
    (
        "only_excludes_registered_patterns",
        "opaque f : Nat → Nat := fun x => x\nopaque g : Nat → Nat := fun x => x\naxiom inverse (x : Nat) : g (f x) = x\ngrind_pattern inverse => f x\nexample (a b c : Nat) (hb : f b = a) (hc : f c = a) : b = c := by grind only",
    ),
    (
        "ordinary_selection_infers_patterns",
        "opaque f : Nat → Nat := fun x => x\nopaque g : Nat → Nat := fun x => x\naxiom inverse (x : Nat) : g (f x) = x\ngrind_pattern inverse => f x\nexample (a b c : Nat) (hb : f b = a) (hc : f c = a) : b = c := by grind only [inverse]",
    ),
    (
        "usr_requires_only",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nexample (a : Nat) : stamp a = a := by grind [usr stamp_eq]",
    ),
    (
        "usr_requires_registered_patterns",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by grind only [usr stamp_eq]",
    ),
    (
        "usr_requires_a_global_identifier",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nexample (a : Nat) : stamp a = a := by grind only [usr (stamp_eq)]",
    ),
    (
        "half_of_a_simultaneous_group_is_insufficient",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x, mark x\nexample (a : Nat) : stamp a = a := by grind",
    ),
    (
        "matching_does_not_fabricate_proof_premises",
        "opaque P : Nat → Prop := fun _ => True\nopaque stamp : Nat → Nat := fun x => x\naxiom conditional (x : Nat) : P x → stamp x = x\ngrind_pattern conditional => stamp x\nexample (a : Nat) : stamp a = a := by grind",
    ),
    (
        "repeated_pattern_variable_cannot_match_distinct_arguments",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\nopaque P : Nat → Prop := fun _ => True\naxiom diagonal (x : Nat) : R x x → P x\ngrind_pattern diagonal => R x x\nexample (a b : Nat) (hr : R a b) : P a := by grind",
    ),
];

const GOALS: &[(&str, &str, &str, &str)] = &[
    (
        "registered_pattern_closes_before_next_tactic",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nexample (a : Nat) : stamp a = a := by\n  try grind\n  rfl",
        "No goals to be solved",
        "NoGoals",
    ),
    (
        "registered_pattern_sequence_preserves_goal_accounting",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\ngrind_pattern stamp_eq => stamp x\nexample (a : Nat) : stamp a = a := by try grind; rfl",
        "unsolved goals",
        "UnsolvedGoals",
    ),
];

#[test]
fn registered_patterns_match_the_live_pin() {
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
                std::env::temp_dir().join(format!("fln-grind-patterns-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            for (success, cases) in [(true, ACCEPT), (false, REFUSE)] {
                for (label, source) in cases {
                    let path = directory.join(format!("{label}.lean"));
                    std::fs::write(&path, format!("{PATTERN_HEADER}{source}\n")).unwrap();
                    let output = Command::new(&compiler)
                        .arg("-j1")
                        .arg(&path)
                        .output()
                        .unwrap();
                    assert_eq!(
                        output.status.success(),
                        success,
                        "pin {label}: {}{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    );
                }
            }
            for (label, source, expected, _) in GOALS {
                let path = directory.join(format!("{label}.lean"));
                std::fs::write(&path, format!("{PATTERN_HEADER}{source}\n")).unwrap();
                let output = Command::new(&compiler)
                    .arg("-j1")
                    .arg(&path)
                    .output()
                    .unwrap();
                let diagnostic = format!(
                    "{}{}",
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                assert!(
                    !output.status.success() && diagnostic.contains(*expected),
                    "pin {label}: expected {expected:?}, got {diagnostic}"
                );
            }
            let engine = base_with_roots(&library, LOGICAL_ROOTS, 1);
            let options = KVMap::new();
            let before = engine.logical_root(&options);
            let mut failures = Vec::new();
            for (success, cases) in [(true, ACCEPT), (false, REFUSE)] {
                for (label, source) in cases {
                    eprintln!("grind pattern: native {label} (accept={success})");
                    match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                        Ok(Outcome::Complete(_)) if success => {}
                        Err(error)
                            if !success
                                && error.disposition().0 == "elaboration"
                                && error.disposition().2 == 1 => {}
                        result => record_failure(&mut failures, label, format!("{result:?}")),
                    }
                    assert_eq!(engine.logical_root(&options), before, "{label}");
                }
            }
            for (label, source, _, expected) in GOALS {
                match engine.check_source_files(&[source.as_bytes()], &options, limits()) {
                    Err(error) if format!("{error:?}").contains(*expected) => {}
                    result => record_failure(&mut failures, label, format!("{result:?}")),
                }
                assert_eq!(engine.logical_root(&options), before, "{label}");
            }
            let recovery = ACCEPT[0].1;
            let first = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            let second = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            match (first, second) {
                (Ok(Outcome::Complete(first)), Ok(Outcome::Complete(second))) => {
                    assert_eq!(first.result_logical_root, second.result_logical_root);
                }
                results => record_failure(
                    &mut failures,
                    "registered_pattern_recovery",
                    format!("{results:?}"),
                ),
            }
            assert_eq!(engine.logical_root(&options), before);
            assert!(failures.is_empty(), "grind pattern failures: {failures:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}
