//! Synthetic proof holes remain explicit scoped obligations.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
    use std::io::Write;
    use std::process::{Command, Stdio};
    // Re-judge each source the helper actually receives, including programs
    // assembled from shared prefixes. A copied expectation is not an oracle.
    let lib = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from);
    let lib = lib.filter(|path| path.join("Init.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("REFERENCE_UNRUN: pinned SDK absent; checking only the native source path");
    }
    let oracle = lib.map(|lib| {
        let pinned = lib.parent().unwrap().parent().unwrap().join("bin/lean");
        let mut child = Command::new(pinned)
            .arg("--stdin")
            .env("LEAN_PATH", &lib)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(source.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let code = output.status.code();
        eprintln!("refinement oracle exit={code:?} source={source:?}\n{stdout}{stderr}");
        assert!(matches!(code, Some(0 | 1)), "{stdout}{stderr}");
        code.unwrap()
    });
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let checked = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
    if let Some(oracle) = oracle {
        let native = match &checked {
            Ok(fln::Outcome::Complete(_)) => Some(0),
            Err(error) if error.disposition().2 == 1 => Some(1),
            _ => None,
        };
        assert_eq!(native, Some(oracle), "source: {source}");
    }
    checked
        .map_err(|error| format!("{error:?}"))?
        .into_complete()
        .map(|_| ())
        .map_err(|error| format!("{error:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted {source}");
}
const BOTH: &str = "inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)\n";

#[test]
fn refinement_keeps_its_new_implicit_hole_unassigned_against_an_older_goal() {
    // All five programs were judged by the actual v4.32.0 pin before this test.
    let prefix = "inductive Ex (p : Nat → Prop) : Prop where\n  | intro (w : Nat) (h : p w)\n";
    let original = format!(
        "{prefix}theorem older : Ex (fun n => n = n) := by apply Ex.intro; refine rfl; exact 0"
    );
    let error = run(&original).expect_err(&original);
    assert!(error.contains("UnassignedNaturalHole"), "{error}");
    reject(&format!(
        "{prefix}theorem older : Ex (fun n => n = n) := by apply Ex.intro; exact Eq.refl ?_; exact 0"
    ));
    for body in [
        "apply Ex.intro; refine Eq.refl ?_; exact 0",
        "apply Ex.intro; refine' rfl; exact 0",
        "refine Ex.intro ?_ ?_; exact 0; rfl",
    ] {
        check(&format!(
            "{prefix}theorem older : Ex (fun n => n = n) := by {body}"
        ));
    }
}

/// Each program was executed by the actual v4.32.0 pin before changing the
/// native path. Its final tactic comparison assigns the opaque `?_`; ordinary
/// term elaboration must still leave that same kind of hole opaque.
#[test]
fn final_tactic_unification_assigns_refine_and_exact_holes() {
    for tactic in ["refine", "exact"] {
        check(&format!(
            "theorem simple (n : Nat) : n = n := by {tactic} Eq.refl ?_"
        ));
        check(&format!(
            "def identity {{A : Type}} (x : A) : A := x\ntheorem same (n : Nat) : identity n = n := by {tactic} Eq.refl ?_"
        ));
    }
    reject("theorem bad (n : Nat) : n = n := Eq.refl ?_");
    reject("theorem bad (n m : Nat) : n = m := by exact Eq.refl ?_");
}

#[test]
fn a_refinement_that_assigned_its_hole_leaves_no_goal_for_the_next_tactic() {
    for source in [
        "theorem simple (n : Nat) : n = n := by refine Eq.refl ?_; exact n",
        "def identity {A : Type} (x : A) : A := x\ntheorem same (n : Nat) : identity n = n := by refine Eq.refl ?_; exact n",
    ] {
        let error = run(source).expect_err(source);
        assert!(error.contains("NoGoals"), "{source}\n{error}");
    }
}

#[test]
fn the_first_no_goals_error_points_at_the_extra_tactic() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    for source in [
        "theorem simple (n : Nat) : n = n := by refine Eq.refl ?_; exact n",
        "def identity {A : Type} (x : A) : A := x\ntheorem same (n : Nat) : identity n = n := by refine Eq.refl ?_; exact n",
        "def annotated : Nat := by refine (7 : ?_); exact Nat\ntheorem computes : annotated = 7 := by rfl",
    ] {
        let problem = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .expect_err(source);
        assert_eq!(
            problem.disposition(),
            ("elaboration", false, 1),
            "{problem:?}"
        );
        let fln::SourceCheckError::Command { offset, error, .. } = problem else {
            panic!("expected a located tactic error: {problem:?}");
        };
        assert_eq!(
            offset,
            source.find("exact ").unwrap(),
            "{source}\n{error:?}"
        );
        assert!(
            error.to_string().contains("tactic has no remaining goal"),
            "{error:?}"
        );
    }
}

#[test]
fn partial_proof_terms_expose_only_the_requested_holes() {
    check(&format!(
        "{BOTH} theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by refine Both.intro p ?_; exact q"
    ));
    check(&format!(
        "{BOTH} theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by refine Both.intro ?_ ?_; exact p; exact q"
    ));
}
#[test]
fn repeated_named_holes_share_one_goal_in_the_same_scope() {
    check(
        "structure Pair where\n first : Nat\n second : Nat\ndef pair : Pair := by refine Pair.mk ?same ?same; exact 7\ntheorem first : pair.first = 7 := by rfl\ntheorem second : pair.second = 7 := by rfl",
    );
}
#[test]
fn holes_under_lambdas_capture_their_entire_dependent_context() {
    check(
        "def identity : forall A : Type, A -> A := by refine fun A x => ?_; exact x\ntheorem computes : identity Nat 7 = 7 := by rfl",
    );
    check("theorem refl (A : Type) : forall x : A, x = x := by refine fun x => ?_; rfl");
}
#[test]
fn lambda_holes_keep_separate_shadowed_variable_identities() {
    check(
        "structure Pair where\n first : Nat -> Nat\n second : Nat -> Nat\ndef pair : Pair := by refine Pair.mk (fun x => ?_) (fun x => ?_); exact x + 1; exact x + 2\ntheorem first : pair.first 7 = 8 := by rfl\ntheorem second : pair.second 7 = 9 := by rfl",
    );
}
#[test]
fn dependent_holes_schedule_type_and_witness_before_consumers() {
    // The pin refuses OfNat synthesis through package.carrier. Preserve that
    // original program as a control, and check the explicitly typed witness.
    reject(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by refine Package.mk ?_ ?_; exact Nat; exact 7\ntheorem checked : package.value = 7 := by rfl",
    );
    check(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by refine Package.mk ?_ ?_; exact Nat; exact 7\ntheorem checked : package.value = (7 : Nat) := by rfl",
    );
    check(
        "inductive Witness (P : Nat -> Prop) : Prop where | intro (n : Nat) (proof : P n)\ntheorem existsLemma : Witness (fun n => n = 7) := by refine Witness.intro ?w ?p; exact 7; rfl",
    );
}
#[test]
fn refinement_composes_with_intro_constructor_and_nested_local_proofs() {
    // The pin accepts these. Exercise the complete source door alongside
    // the direct introduction-frontier rollback tests.
    for source in [
        "theorem t : Nat → True := by intro (x : Nat); exact True.intro",
        "theorem t : And True True → True := by intro ⟨p, q⟩; exact p",
        "theorem t (f g : Nat → Nat) (h : ∀ n, f n = g n) : f = g := by funext (x : Nat); exact h x",
        "theorem t : And True True → True := by refine fun ⟨p, q⟩ => ?_; exact p",
        "theorem t (h : And True True) : True := by refine (match h with | And.intro p q => ?_); exact p",
    ] {
        check(source);
    }
    check(&format!(
        "{BOTH} theorem nested (P Q : Prop) : P -> Q -> Both P (Both Q P) := by intro p q; refine Both.intro p ?_; constructor; exact q; exact p"
    ));
    // The original body is aligned with an indented command. The pin treats
    // `have` as the start of another command, not this theorem's tactic body.
    reject(&format!(
        "{BOTH} theorem loc (P : Prop) (p : P) : Both P P := by\n have h : Both P P := by\n  refine Both.intro ?_ ?_\n  exact p\n  exact p\n exact h"
    ));
    check(&format!(
        "{BOTH}theorem loc (P : Prop) (p : P) : Both P P := by\n have h : Both P P := by\n  refine Both.intro ?_ ?_\n  exact p\n  exact p\n exact h"
    ));
}
#[test]
fn captured_let_definitions_keep_values_instead_of_becoming_assumptions() {
    check(
        "def selected (n : Nat) : Nat := by let x := n + 1; refine ?_; exact x\ntheorem checked : selected 7 = 8 := by rfl",
    );
    check(
        "def function : Nat -> Nat := by refine fun n => ?_; let x := n + 1; refine ?_; exact x\ntheorem checked : function 7 = 8 := by rfl",
    );
}
#[test]
fn unused_synthetic_holes_are_still_obligations() {
    let prefix = "def ignore (unused : Nat) : 0 = 0 := rfl\n";
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignore ?_"
    ));
    check(&format!(
        "{prefix} theorem good : 0 = 0 := by refine ignore ?_; exact 7"
    ));
    let prefix = "def ignoreProof (unused : 0 = 1) : 0 = 0 := rfl\n";
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignoreProof ?_"
    ));
    reject(&format!(
        "{prefix} theorem bad : 0 = 0 := by refine ignoreProof ?_; rfl"
    ));
}
#[test]
fn unresolved_holes_and_invalid_annotations_never_close_a_declaration() {
    for source in [
        "theorem bad : 0 = 1 := by refine ?_",
        "theorem bad : 0 = 1 := by refine ?_; rfl",
        "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore (1 : String) ?_; rfl",
        "theorem bad : 0 = 0 := by exact ?_",
        "def bad : Nat := ?_",
        "theorem bad : 0 = 1 := by refine ?self; exact ?self",
    ] {
        reject(source);
    }
}
#[test]
fn named_holes_cannot_capture_another_scope_or_take_incompatible_types() {
    reject(
        "structure Pair where\n first : Nat -> Nat\n second : Nat -> Nat\ndef bad : Pair := by refine Pair.mk (fun x => ?same) (fun y => ?same); exact x",
    );
    reject(
        "structure Pair where\n first : Nat\n second : String\ndef bad : Pair := by refine Pair.mk ?same ?same; exact 7",
    );
}
/// `Eq.trans`, which the source seed lacks (`Init/Prelude.lean`).
const CHAIN: &str = "theorem chain {a b c : Nat} (h₁ : a = b) (h₂ : b = c) : a = c := h₂ ▸ h₁\n";
/// The pin's `refine` aborts when an implicit argument it made is still unassigned, as when
/// `chain ?_ ?_` leaves its middle term `b` open ("don't know how to synthesize implicit
/// argument"); it never becomes a goal. Each program was judged by pinned lean v4.32.0 first.
/// (`refine Eq.refl ?_; exact n` was here as accepted: the pin assigns `?_ := n` at the refine
/// and refuses `exact n` with "No goals to be solved".)
#[test]
fn implicit_inference_holes_are_not_promoted_to_tactic_goals() {
    check(&format!(
        "{CHAIN}theorem simple (n : Nat) : n = n := by refine chain ?_ (Eq.refl n); exact Eq.refl n"
    ));
    check(&format!(
        "{CHAIN}def identity {{A : Type}} (x : A) : A := x\ntheorem same (n : Nat) : identity n = n := by refine chain ?_ (Eq.refl n); exact Eq.refl n"
    ));
    check(&format!(
        "{CHAIN}theorem named (n : Nat) : n = n := by refine chain (b := n) ?_ ?_; exact Eq.refl n; exact Eq.refl n"
    ));
    reject(&format!(
        "{CHAIN}theorem unassigned (n : Nat) : n = n := by refine chain ?_ ?_; exact n; exact Eq.refl n; exact Eq.refl n"
    ));
    reject(
        "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore _ ?_; rfl",
    );
    // A witness `_` that only a later tactic could assign: the pin refuses at the refine ("don't
    // know how to synthesize placeholder for argument `w`"); a given witness is accepted.
    let ex = "inductive Ex (p : Nat -> Prop) : Prop where\n  | intro (w : Nat) (h : p w)\n";
    reject(&format!(
        "{ex}theorem witness : Ex (fun n => n = 3) := by refine Ex.intro _ ?_; rfl"
    ));
    check(&format!(
        "{ex}theorem witness : Ex (fun n => n = 3) := by refine Ex.intro 3 ?_; rfl"
    ));
}
#[test]
fn synthetic_hole_spelling_uses_the_pins_identifier_and_trivia_parser() {
    for spelling in ["?", "?7"] {
        reject(&format!("def bad : Nat := by refine {spelling}; exact 7"));
    }
    // Preserve all four original programs; the live pin accepts these two.
    for spelling in ["? _", "?a.b", "?/-gap-/_"] {
        check(&format!("def bad : Nat := by refine {spelling}; exact 7"));
    }
}

#[test]
fn later_explicit_goals_cannot_be_solved_by_inference_or_ignored_by_conversion() {
    // A match branch may expose holes to its enclosing refine. The same
    // syntax under exact must still close every hole that exact owns.
    reject("theorem t : And True True → True := by exact fun ⟨p, q⟩ => ?_");
    reject("theorem t (h : And True True) : True := by exact (match h with | And.intro p q => ?_)");
    reject("theorem bad (n m : Nat) : n = n := by refine Eq.refl ?_; exact m");
    reject("def ignore (n : Nat) : 0 = 0 := rfl\ntheorem bad : 0 = 0 := by refine ignore ?_");
    check("theorem good (n : Nat) : n = n := by refine Eq.refl _");
    reject("theorem extra (n : Nat) : n = n := by refine Eq.refl _; exact n");
}

#[test]
fn holes_in_annotations_are_real_type_obligations() {
    // The pin's final comparison assigns this annotation hole to Nat. The
    // original source with `exact Nat` is retained as the no-goals control.
    check("def annotated : Nat := by refine (7 : ?_)\ntheorem computes : annotated = 7 := by rfl");
    let original = "def annotated : Nat := by refine (7 : ?_); exact Nat\ntheorem computes : annotated = 7 := by rfl";
    let error = run(original).expect_err(original);
    assert!(error.contains("NoGoals"), "{original}\n{error}");
    reject("def bad : Nat := by refine (7 : ?_); exact String");
}

#[test]
fn named_refinement_goals_are_shared_across_frames() {
    // Preserve the original program. The second use is already solved, so
    // the pin refuses its extra `exact`; distinct names give two obligations.
    reject(&format!(
        "{BOTH} theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?goal\n exact p\n refine ?goal\n exact p"
    ));
    reject(&format!(
        "{BOTH}theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?goal\n exact p\n refine ?goal\n exact p"
    ));
    // This first distinct-name control had the same invalid indentation;
    // retain it too and use the correctly aligned declaration for acceptance.
    reject(&format!(
        "{BOTH} theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?first\n exact p\n refine ?goal\n exact p"
    ));
    check(&format!(
        "{BOTH}theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?first\n exact p\n refine ?goal\n exact p"
    ));
    check(&format!(
        "{BOTH}theorem twice (P : Prop) (p : P) : Both P P := by\n constructor\n refine ?goal\n exact p\n refine ?goal"
    ));
    reject(&format!(
        "{BOTH} theorem bad : Both (0 = 0) (0 = 1) := by\n constructor\n refine ?goal\n rfl\n refine ?goal\n rfl"
    ));
    reject(&format!(
        "{BOTH}theorem bad : Both (0 = 0) (0 = 1) := by\n constructor\n refine ?goal\n rfl\n refine ?goal\n rfl"
    ));
}

#[test]
fn branch_scopes_do_not_leak_synthetic_holes_or_local_assumptions() {
    // Reusing the assigned name also reuses its proof and type. The original
    // false-branch proof cannot prove the true branch's different equality.
    reject(
        "theorem same (b : Bool) : b = b := by\n cases b with\n | false =>\n  refine ?same\n  rfl\n | true =>\n  refine ?same\n  rfl",
    );
    check(
        "theorem same (b : Bool) : b = b := by\n cases b with\n | false =>\n  refine ?first\n  rfl\n | true =>\n  refine ?same\n  rfl",
    );
    check(
        "theorem same (P : Prop) (p : P) (b : Bool) : P := by\n cases b with\n | false =>\n  refine ?same\n  exact p\n | true =>\n  refine ?same",
    );
    check("def same : Nat := by refine (fun (n : Nat) => ?same) ?same; exact 7");
    check("def same : Nat := by\n refine (fun (n : Nat) => ?same) ?same\n case same => exact 7");
    reject("def same : Nat := by refine (fun (n : Nat) => ?same) ?same; exact n");
    reject(
        "theorem bad (b : Bool) : 0 = 0 := by\n cases b with\n | false =>\n  refine ?_\n  have secret : 0 = 0 := rfl\n  exact secret\n | true =>\n  refine ?_\n  exact secret",
    );
}

#[test]
fn dependent_substitution_rebuilds_refined_hole_contexts() {
    check(
        "theorem move (n m : Nat) (h : n = m) (P : Nat -> Prop) (p : P n) : P m := by refine ?_; subst h; exact p",
    );
    // The pin substitutes an `HEq` only when its two types are definitionally equal: the
    // same-type case is accepted and the two-type case refused, each run at the pin (lean
    // v4.32.0, 2026-10-06), the refusal with exactly this first error.
    check(
        "theorem t (x y : Nat) (h : HEq x y) (P : Nat -> Prop) (p : P x) : P y := by refine ?_; subst h; exact p",
    );
    let source = "theorem move (A B : Type) (a : A) (b : B) (h : HEq a b) (P : forall T : Type, T -> Prop) (p : P A a) : P B b := by refine ?_; subst h; exact p";
    reject(source);
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let error = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect_err(source)
        .to_string();
    assert!(
        error.contains("Tactic `subst` failed: did not find equation for eliminating 'h'"),
        "{source}\nmust be refused as the pin refuses it: {error}"
    );
}

#[test]
fn refinement_holes_preserve_hidden_hypotheses_and_recursion_restrictions() {
    reject(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem bad (n : Nat) : copy n = n := by\n cases n with\n | zero => rfl\n | succ k =>\n  refine ?_\n  assumption",
    );
    reject(
        "def bad (n : Nat) : Nat := match n with | .zero => 0 | .succ k => by refine ?_; exact bad n",
    );
    check(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem correct (n : Nat) : copy n = n := by\n induction n with\n | zero => rfl\n | succ k ih =>\n  refine ?_\n  simp only [copy, ih]",
    );
}

#[test]
fn irrelevant_ill_typed_arguments_are_actually_refused() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let run = |source: &str| {
        engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
    };
    // The pin refuses `(1 : String)` while elaborating (no `OfNat String 1`), and
    // the `Nat` twin must check.
    let source = "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore (1 : String) ?_; rfl";
    let problem = run(source).unwrap_err();
    assert_eq!(
        problem.disposition(),
        ("elaboration", false, 1),
        "{problem:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    assert!(matches!(
        run(
            "def ignore (n : Nat) (h : 0 = 0) : 0 = 0 := h\ntheorem bad : 0 = 0 := by refine ignore (1 : Nat) ?_; rfl"
        ),
        Ok(fln::Outcome::Complete(_))
    ));
    // The pin refuses this while elaborating: `refine Eq.refl ?_` closes the goal, and
    // `exact m` is "No goals to be solved" (v4.32.0, 2026-10-06). FrankenLean refuses
    // it at the same stage since 5a3ff40e, though by a conversion refusal (NotDefEq)
    // rather than the pin's "No goals"; that difference in reason is not asserted here.
    let source = "def identity (n : Nat) : Nat := n\ntheorem bad (n m : Nat) : identity n = n := by refine Eq.refl ?_; exact m";
    let problem = run(source).unwrap_err();
    assert_eq!(
        problem.disposition(),
        ("elaboration", false, 1),
        "{problem:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn refinement_exhaustion_and_failure_do_not_publish_a_prefix() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = format!(
        "{CHAIN}theorem same (n : Nat) : n = n := by refine chain ?_ (Eq.refl n); exact Eq.refl n"
    );
    let source = source.as_str();
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected resource stop, got {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    for valid in [true, false, true] {
        let suffix = if valid {
            "theorem second : 0 = 0 := by refine ?_; rfl"
        } else {
            "theorem second : 0 = 1 := by refine ?_; rfl"
        };
        let outcome = engine.check_source_files(
            &[source.as_bytes(), suffix.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert_eq!(outcome.is_ok(), valid, "{outcome:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn captured_goals_compose_with_function_valued_recursive_constructors() {
    check(
        "inductive Tree where | leaf (value : Nat) | node (children : Nat -> Tree)\ndef generated : Tree := by right; refine fun i => ?_; left; exact i\ntheorem canonical : generated = Tree.node (fun i => Tree.leaf i) := by rfl",
    );
    check(
        "inductive Impossible : Prop where\ninductive Accessible (r : Nat -> Nat -> Prop) : Nat -> Prop where | intro (x : Nat) (children : forall y : Nat, r y x -> Accessible r y) : Accessible r x\ntheorem well : Accessible (fun x y => Impossible) 7 := by constructor; refine fun y h => ?_; cases h",
    );
}
