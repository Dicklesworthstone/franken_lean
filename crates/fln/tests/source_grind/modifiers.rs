//! Selected theorem directions must change matching, preserve their original
//! proofs, and reject directions that cannot cover the theorem's parameters.
use super::*;

const LOGICAL_ROOTS: &[&str] = &["Init.Grind.Tactics", "Init.Classical"];

const ACCEPT: &[(&str, &str)] = &[
    (
        "equality_left_nested",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp (stamp a) = a := by grind only [= stamp_eq]",
    ),
    (
        "equality_right_nested",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_rev (x : Nat) : x = stamp x\nexample (a : Nat) : stamp (stamp a) = a := by grind only [=_ stamp_rev]",
    ),
    (
        "equality_both_directions",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom stamp_mark (x : Nat) : stamp x = mark x\nexample (a : Nat) : mark (mark a) = stamp (stamp a) := by grind only [_=_ stamp_mark]",
    ),
    (
        "equality_local_proof_term",
        "example (f : Nat → Nat) (a : Nat) (h : ∀ x, f x = x) : f (f a) = a := by grind only [= (h)]",
    ),
    (
        "equality_polymorphic",
        "universe u\nopaque marker {α : Type u} (x : α) : α := x\naxiom marker_eq {α : Type u} (x : α) : marker x = x\nexample (a : Nat) : marker (marker a) = a := by grind only [= marker_eq]\nexample {α : Type u} (a : α) : marker a = a := by grind only [= marker_eq]",
    ),
    (
        "equality_iff_sides",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x : Nat) : P x ↔ Q x\nexample (a : Nat) (ha : P a) : Q a := by grind only [= pq]\nexample (a : Nat) (ha : P a) : Q a := by grind only [=_ pq]\nexample (a : Nat) (ha : P a) : Q a := by grind only [_=_ pq]",
    ),
    (
        "equality_with_proved_premise",
        "opaque P : Nat → Prop := fun _ => True\nopaque stamp : Nat → Nat := fun x => x\naxiom stamp_if (x : Nat) : P x → stamp x = x\nexample (a : Nat) (ha : P a) : stamp a = a := by grind only [= stamp_if]",
    ),
    (
        "forward_direction_and_alias",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x : Nat) : P x → Q x\nexample (a : Nat) (ha : P a) : Q a := by grind only [→ pq]\nexample (a : Nat) (ha : P a) : Q a := by grind only [-> pq]",
    ),
    (
        "backward_direction_and_alias",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x : Nat) : P x → Q x\nexample (a : Nat) (ha : P a) : Q a := by grind only [← pq]\nexample (a : Nat) (ha : P a) : Q a := by grind only [<- pq]",
    ),
    (
        "forward_multi_pattern",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\naxiom step (x y z : Nat) : R x y → R y z → R x z\nexample (a b c : Nat) (hab : R a b) (hbc : R b c) : R a c := by grind only [→ step]",
    ),
    (
        "forward_matches_through_equality",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\nopaque P : Nat → Prop := fun _ => True\naxiom step (x : Nat) : R x x → P x\nexample (a b : Nat) (hab : a = b) (hr : R a b) : P b := by grind only [→ step]",
    ),
    (
        "left_right_multi_pattern_and_alias",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\naxiom step (x y z : Nat) : R x y → R y z → R x z\nexample (a b c : Nat) (hab : R a b) (hbc : R b c) : R a c := by grind only [⇒ step]\nexample (a b c : Nat) (hab : R a b) (hbc : R b c) : R a c := by grind only [=> step]",
    ),
    (
        "right_left_multi_pattern_and_alias",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\naxiom step (x y z : Nat) : R x y → R y z → R x z\nexample (a b c : Nat) (hab : R a b) (hbc : R b c) : R a c := by grind only [⇐ step]\nexample (a b c : Nat) (hab : R a b) (hbc : R b c) : R a c := by grind only [<= step]",
    ),
    (
        "explicit_default_and_alias",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by grind only [. stamp_eq]\nexample (a : Nat) : stamp a = a := by grind only [· stamp_eq]",
    ),
];

const REFUSE: &[(&str, &str)] = &[
    (
        "equality_requires_equality_conclusion",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x : Nat) : P x → Q x\nexample (a : Nat) (ha : P a) : Q a := by grind only [= pq]",
    ),
    (
        "equality_left_must_cover_every_parameter",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom pair_eq (x y : Nat) : stamp x = mark y\nexample (a b : Nat) : stamp a = mark b := by grind only [= pair_eq]",
    ),
    (
        "equality_right_must_cover_every_parameter",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom pair_eq (x y : Nat) : stamp x = mark y\nexample (a b : Nat) : stamp a = mark b := by grind only [=_ pair_eq]",
    ),
    (
        "equality_both_cannot_drop_invalid_side",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by grind only [_=_ stamp_eq]",
    ),
    (
        "equality_direction_is_not_default_inference",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_rev (x : Nat) : x = stamp x\nexample (a : Nat) : stamp a = a := by grind only [= stamp_rev]",
    ),
    (
        "forward_requires_a_propositional_premise",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by grind only [→ stamp_eq]",
    ),
    (
        "forward_cannot_use_conclusion_to_cover_parameter",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x y : Nat) : P x → Q y\nexample (a b : Nat) (ha : P a) : Q b := by grind only [→ pq]",
    ),
    (
        "backward_cannot_use_premise_to_cover_parameter",
        "opaque P : Nat → Prop := fun _ => True\nopaque Q : Nat → Prop := fun _ => True\naxiom pq (x y : Nat) : P x → Q y\nexample (a b : Nat) (ha : P a) : Q b := by grind only [← pq]",
    ),
    (
        "selected_equality_keeps_proof_premise",
        "opaque P : Nat → Prop := fun _ => True\nopaque stamp : Nat → Nat := fun x => x\naxiom stamp_if (x : Nat) : P x → stamp x = x\nexample (a : Nat) : stamp a = a := by grind only [= stamp_if]",
    ),
    (
        "selected_equality_does_not_match_unrelated_head",
        "opaque stamp : Nat → Nat := fun x => x\nopaque mark : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : mark a = a := by grind only [= stamp_eq]",
    ),
    (
        "ground_proof_rejects_modifier",
        "example (a : Nat) (h : a = a) : a = a := by grind only [= (h)]",
    ),
    (
        "ground_proof_rejects_explicit_default",
        "example (a : Nat) (h : a = a) : a = a := by grind only [. (h)]",
    ),
    (
        "bare_local_name_is_still_redundant",
        "example (f : Nat → Nat) (a : Nat) (h : ∀ x, f x = x) : f a = a := by grind only [= h]",
    ),
    (
        "forward_repeated_variable_is_consistent",
        "opaque R : Nat → Nat → Prop := fun _ _ => True\nopaque P : Nat → Prop := fun _ => True\naxiom step (x : Nat) : R x x → P x\nexample (a b : Nat) (hab : R a b) : P a := by grind only [→ step]",
    ),
];

const GOALS: &[(&str, &str, &str, &str)] = &[
    (
        "selected_theorem_closes_goal_before_next_tactic",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by\n  try grind only [= stamp_eq]\n  rfl",
        "No goals to be solved",
        "NoGoals",
    ),
    (
        "selected_theorem_try_sequence_rolls_back",
        "opaque stamp : Nat → Nat := fun x => x\naxiom stamp_eq (x : Nat) : stamp x = x\nexample (a : Nat) : stamp a = a := by try grind only [= stamp_eq]; rfl",
        "unsolved goals",
        "UnsolvedGoals",
    ),
];

const EXHAUST: &str = "opaque P : Nat → Prop := fun _ => True\nopaque f : Nat → Nat := fun x => x\naxiom step (x : Nat) : P x → P (f x)\nexample (a : Nat) (ha : P a) : False := by grind only [→ step]";

#[test]
fn selected_theorem_directions_match_the_live_pin() {
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
                std::env::temp_dir().join(format!("fln-grind-modifiers-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            for (success, cases) in [
                (true, ACCEPT),
                (false, REFUSE),
                (false, &[("selected_theorem_exhaustion", EXHAUST)][..]),
            ] {
                for (label, source) in cases {
                    let path = directory.join(format!("{label}.lean"));
                    std::fs::write(&path, format!("{HEADER}{source}\n")).unwrap();
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
                std::fs::write(&path, format!("{HEADER}{source}\n")).unwrap();
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
                    eprintln!("grind modifier: native {label} (accept={success})");
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
            match engine.check_source_files(&[EXHAUST.as_bytes()], &options, limits()) {
                Err(error) if error.disposition().2 == 3 => {}
                Ok(Outcome::Inconclusive(_)) => {}
                result => record_failure(
                    &mut failures,
                    "selected_theorem_exhaustion",
                    format!("typed resource non-answer required: {result:?}"),
                ),
            }
            assert_eq!(engine.logical_root(&options), before);
            let recovery = ACCEPT[0].1;
            let first = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            let second = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            match (first, second) {
                (Ok(Outcome::Complete(first)), Ok(Outcome::Complete(second))) => {
                    assert_eq!(first.result_logical_root, second.result_logical_root);
                }
                results => {
                    record_failure(&mut failures, "modifier_recovery", format!("{results:?}"))
                }
            }
            assert_eq!(engine.logical_root(&options), before);
            assert!(failures.is_empty(), "grind modifier failures: {failures:?}");
        })
        .unwrap()
        .join()
        .unwrap();
}
