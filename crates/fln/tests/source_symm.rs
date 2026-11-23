//! Source symmetry attributes select checked proof applications. The controls
//! distinguish registration order, lexical lifetime and real Prelude bootstrap.
#![forbid(unsafe_code)]
use fln::source_check::SourceFileCheck;
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanWriteBudget, Outcome,
    SourceCheckError, SourceCheckLimits, SourceModuleInput,
};

const RELATION: &str = "inductive R : Nat → Nat → Prop where\n  | mk (a b : Nat) : R a b\n";
const SWAP: &str = "theorem swap {a b : Nat} (h : R a b) : R b a := R.mk b a\n";
const KEEP: &str = "theorem keep {a b : Nat} (h : R a b) : R a b := h\n";
const GOAL: &str = "theorem goal {a b : Nat} (h : R a b) : R b a := by symm; exact h\n";
const HYPOTHESIS: &str =
    "theorem hypothesis {a b : Nat} (h : R a b) : R b a := by symm at h; exact h\n";

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(engine: &Engine, source: &str) -> SourceFileCheck {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn check(source: &str) -> SourceFileCheck {
    checked(&base(), source)
}

fn reject_in(engine: &Engine, source: &str) -> SourceCheckError {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "{source}\n{error:?}"
    );
    assert_eq!(before, engine.logical_root(&options));
    error
}

#[test]
fn inline_symmetry_drives_goals_and_hypotheses_through_checked_applications() {
    let result = check(&format!("{RELATION}@[symm] {SWAP}{GOAL}{HYPOTHESIS}"));
    let entries = fln_elab::symm::read(result.engine.environment()).unwrap();
    assert_eq!(entries.len(), 1);
    assert_eq!(
        entries[0].lemma.declaration,
        Name::from_components(["swap"])
    );
    assert!(entries[0].namespace.is_none());
}

#[test]
fn standalone_registration_can_tag_an_imported_lemma_and_retains_repeated_rows() {
    let producer = check(&format!("{RELATION}{SWAP}"));
    let consumer = checked(
        &producer.engine,
        &format!("attribute [symm] swap\nattribute [symm] swap\n{GOAL}{HYPOTHESIS}"),
    );
    assert_eq!(
        fln_elab::symm::read(consumer.engine.environment())
            .unwrap()
            .len(),
        2
    );
    assert_eq!(
        fln_elab::symm::read_with_scopes(
            consumer.engine.environment(),
            &consumer.scope.symm_scopes
        )
        .unwrap()
        .len(),
        1
    );
}

#[test]
fn failed_candidate_application_restores_constraints_before_the_next_lemma() {
    check(&format!(
        "{RELATION}@[symm] theorem zeroOnly (h : R 0 0) : R 0 0 := h\n\
        @[symm] {SWAP}{GOAL}{HYPOTHESIS}"
    ));
}

#[test]
fn seed_equality_fallback_stops_at_a_real_declaration_or_registered_candidate() {
    let source = "theorem Eq.symm {a b : Nat} (h : Eq a b) : Eq b a := Eq.rec rfl h";
    let producer = check(source);
    reject_in(
        &producer.engine,
        "theorem unregistered {a b : Nat} (h : Eq a b) : Eq b a := by symm; exact h",
    );
    let producer = check("@[symm] theorem tooSpecific (h : Eq 0 0) : Eq 0 0 := h");
    reject_in(
        &producer.engine,
        "theorem failedCandidate {a b : Nat} (h : Eq a b) : Eq b a := by symm; exact h",
    );
}

#[test]
fn registration_is_shallow_and_first_applicable_lemma_controls_the_goal() {
    // The pin permits this non-swapping lemma. Its first position must not be
    // replaced by a hardcoded reversal or by the most recently registered row.
    let declarations = format!("{RELATION}@[symm] {KEEP}@[symm] {SWAP}");
    check(&format!(
        "{declarations}theorem unchanged {{a b : Nat}} (h : R a b) : R a b := by symm; exact h"
    ));
    reject_in(&base(), &format!("{declarations}{GOAL}"));
    check(&format!("{RELATION}@[symm] {SWAP}@[symm] {KEEP}{GOAL}"));
}

#[test]
fn local_inline_and_standalone_rules_end_with_their_lexical_scope() {
    for registration in [
        format!("@[local symm] {SWAP}"),
        format!("{SWAP}attribute [local symm] swap\n"),
    ] {
        let source = format!("{RELATION}section\n{registration}{GOAL}{HYPOTHESIS}end\n");
        let result = check(&source);
        assert!(
            fln_elab::symm::read(result.engine.environment())
                .unwrap()
                .is_empty()
        );
        assert!(
            fln_elab::symm::read_with_scopes(
                result.engine.environment(),
                &result.scope.symm_scopes
            )
            .unwrap()
            .is_empty()
        );
        reject_in(
            &base(),
            &format!("{source}theorem after {{a b : Nat}} (h : R a b) : R b a := by symm; exact h"),
        );
    }
}

#[test]
fn namespace_rules_activate_on_entry_and_both_open_forms_and_restore_on_end() {
    let source = format!("{RELATION}namespace Rules\n@[scoped symm] {SWAP}{GOAL}end Rules\n");
    let result = check(&source);
    assert_eq!(
        fln_elab::symm::read(result.engine.environment())
            .unwrap()
            .len(),
        1
    );
    assert!(
        fln_elab::symm::read_with_scopes(result.engine.environment(), &result.scope.symm_scopes)
            .unwrap()
            .is_empty()
    );
    for enter in ["open scoped Rules", "open Rules", "namespace Rules"] {
        let leave = if enter == "namespace Rules" {
            "end Rules"
        } else {
            "end"
        };
        let section = if enter == "namespace Rules" {
            ""
        } else {
            "section\n"
        };
        checked(
            &result.engine,
            &format!("{section}{enter}\n{HYPOTHESIS}{leave}"),
        );
    }
    checked(
        &result.engine,
        &format!("open scoped Rules in\n{HYPOTHESIS}"),
    );
    reject_in(&result.engine, GOAL);
    reject_in(
        &result.engine,
        &format!("section\nopen scoped Rules\n{HYPOTHESIS}end\n{GOAL}"),
    );
}

#[test]
fn local_and_scoped_activation_preserves_registration_chronology() {
    let prefix = format!(
        "{RELATION}{KEEP}{SWAP}section\nattribute [local symm] keep\nattribute [symm] swap\n"
    );
    check(&format!(
        "{prefix}theorem localFirst {{a b : Nat}} (h : R a b) : R a b := by symm; exact h\nend\n{GOAL}"
    ));
    reject_in(&base(), &format!("{prefix}{GOAL}end"));
    let scoped = format!(
        "{RELATION}{KEEP}{SWAP}namespace Rules\nattribute [scoped symm] keep\nend Rules\nattribute [symm] swap\nopen scoped Rules\n"
    );
    check(&format!("{scoped}{GOAL}"));
}

#[test]
fn local_selection_does_not_cross_source_file_boundaries() {
    let source = format!("{RELATION}@[local symm] {SWAP}{GOAL}");
    let engine = base();
    let result = engine.check_source_files(
        &[source.as_bytes(), HYPOTHESIS.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(result, Err(SourceCheckError::Command { file: 1, .. })),
        "{result:?}"
    );
    let source = format!("{RELATION}@[symm] {SWAP}{GOAL}");
    engine
        .check_source_files(
            &[source.as_bytes(), HYPOTHESIS.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn invalid_shapes_erasure_and_late_bad_targets_are_atomic_refusals() {
    let producer = check(&format!(
        "{RELATION}{SWAP}theorem unary (h : True) : True := h\n"
    ));
    for source in [
        "@[symm] theorem noBinder : R 0 0 := R.mk 0 0",
        "attribute [symm] unary",
        "attribute [symm] swap missing",
        "attribute [symm] swap unary",
        "attribute [-symm] swap",
        "attribute [scoped symm] swap",
    ] {
        reject_in(&producer.engine, source);
        assert!(
            fln_elab::symm::read(producer.engine.environment())
                .unwrap()
                .is_empty()
        );
    }
}

#[test]
fn shallow_binary_conclusions_need_not_be_propositions_or_swapped() {
    check(
        "abbrev DataRel (a b : Nat) := Nat\n\
        @[symm] def identityRule (n : Nat) : DataRel n n := n\n\
        def result : DataRel 3 3 := by symm\n\
        theorem computes : result = 3 := by rfl",
    );
}

#[test]
fn an_unsafe_selected_constant_cannot_enter_a_safe_proof() {
    let producer = check(&format!(
        "{RELATION}unsafe def unsafeSwap {{a b : Nat}} (h : R a b) : R b a := R.mk b a\nattribute [symm] unsafeSwap\n"
    ));
    reject_in(&producer.engine, GOAL);
}

#[test]
fn symmetry_use_kernel_exhaustion_is_an_inconclusive_result() {
    let producer = check(&format!("{RELATION}@[symm] {SWAP}"));
    let options = KVMap::new();
    let root = producer.engine.logical_root(&options);
    let mut starved = limits();
    starved.kernel.steps = 0;
    let result = producer
        .engine
        .check_source_files(
            &[GOAL.as_bytes()],
            &options,
            SourceCheckLimits::new(starved),
        )
        .map(|outcome| outcome.map_complete(|_| ()));
    assert!(matches!(result, Ok(Outcome::Inconclusive(_))), "{result:?}");
    assert_eq!(root, producer.engine.logical_root(&options));
}

#[test]
fn the_unmodified_prelude_symmetry_declaration_bootstraps_and_drives_both_tactics() {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let declaration =
        "@[symm] theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=\n  h ▸ rfl";
    let end = prelude.find(declaration).expect("pinned Prelude Eq.symm") + declaration.len();
    let source = format!(
        "{}\ntheorem sourceSymmetry {{A : Sort u}} {{a b : A}} (h : Eq a b) : Eq b a := by symm; exact h\n\
        theorem sourceHypothesis {{A : Sort u}} {{a b : A}} (h : Eq a b) : Eq b a := by symm at h; exact h\n",
        &prelude[..end],
    );
    let name = Name::from_components(["Init", "Prelude"]);
    let result = Engine::builder().build_empty().compile_source_modules(
        &[SourceModuleInput {
            name: &name,
            source: source.as_bytes(),
        }],
        &name,
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        OleanWriteBudget::default(),
    );
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
}
