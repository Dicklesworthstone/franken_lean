//! Native source dsimp must change the actual proof state before admission.
//! The same fixture bytes can be run by scripts/check_dsimp_reference.py.
//! These are authored expectations; neither native nor Reference execution is
//! asserted by this test source itself.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn accepted(name: &str, source: &str) {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let checked = base
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{name}: {error:?}\n{source}"))
        .into_complete()
        .unwrap_or_else(|outcome| panic!("{name}: {outcome:?}"));
    assert!(checked.theorems > 0, "fixture must admit actual proofs");
    assert_eq!(
        base.logical_root(&options),
        before,
        "checking mutated its input"
    );
}

macro_rules! accepted_fixture {
    ($name:ident) => {
        #[test]
        fn $name() {
            accepted(
                stringify!($name),
                include_str!(concat!("source_dsimp/accept/", stringify!($name), ".lean")),
            );
        }
    };
}

accepted_fixture!(beta_zeta);
accepted_fixture!(selected_definitions);
accepted_fixture!(dependent_binders);
accepted_fixture!(locations);
accepted_fixture!(wildcard);
accepted_fixture!(data_location);
accepted_fixture!(closure);
accepted_fixture!(default_rules);
accepted_fixture!(explicit_rfl_rule);
accepted_fixture!(untagged_rfl_rule);
accepted_fixture!(default_transparency_rule);
accepted_fixture!(partial_application);
accepted_fixture!(rollback);
accepted_fixture!(projection_eta);
accepted_fixture!(local_equality);
accepted_fixture!(erasure);
accepted_fixture!(local_definition);
accepted_fixture!(repeat_no_progress);
accepted_fixture!(structure_projection);
accepted_fixture!(ascription_beta);

#[test]
fn refusals_never_publish_a_false_or_partial_declaration() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for (name, source) in [
        ("false", include_str!("source_dsimp/refuse/false.lean")),
        (
            "nonreflexive",
            include_str!("source_dsimp/refuse/nonreflexive.lean"),
        ),
        (
            "no_progress",
            include_str!("source_dsimp/refuse/no_progress.lean"),
        ),
        (
            "unknown_rule",
            include_str!("source_dsimp/refuse/unknown_rule.lean"),
        ),
        (
            "unknown_location",
            include_str!("source_dsimp/refuse/unknown_location.lean"),
        ),
        (
            "late_invalid_location",
            include_str!("source_dsimp/refuse/late_invalid_location.lean"),
        ),
        (
            "class_projection",
            include_str!("source_dsimp/refuse/class_projection.lean"),
        ),
        (
            "ascription_no_progress",
            include_str!("source_dsimp/refuse/ascription_no_progress.lean"),
        ),
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{name} unexpectedly completed: {source}",
        );
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
        assert_eq!(base.logical_root(&options), before);
    }
}

#[test]
fn imported_reflexivity_tags_follow_module_edits_and_cache_invalidation() {
    use fln::SourceModuleInput;
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    let base_name = Name::from_components(["Base"]);
    let main_name = Name::from_components(["Main"]);
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    let base = "@[implicit_reducible] def wrapped (A : Type) (x : A) : A := x\ntheorem unwrap (A : Type) (x : A) : wrapped A x = x := rfl\n";
    let main = "import Base\ntheorem use (A : Type) (x : A) (P : A → Prop) (h : P x) : P (wrapped A x) := by\n  dsimp only [unwrap]\n  guard_target =ₛ P x\n  exact h\n";
    let check = |session: &mut SourceModuleSession, source: &str| {
        session.check_with_cancel(
            &[
                SourceModuleInput {
                    name: &base_name,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &main_name,
                    source: main.as_bytes(),
                },
            ],
            &main_name,
            None,
        )
    };
    let cold = check(&mut session, base).unwrap().into_complete().unwrap();
    let warm = check(&mut session, base).unwrap().into_complete().unwrap();
    assert_eq!(warm.reused_modules, 2);
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );
    let untagged = base.replace(":= rfl", ":= (rfl)");
    assert!(
        check(&mut session, &untagged).is_err(),
        "an old module's tag leaked into the replacement"
    );
    let recovered = check(&mut session, base).unwrap().into_complete().unwrap();
    assert_eq!(
        cold.checked.checked.result_logical_root,
        recovered.checked.checked.result_logical_root
    );
}

#[test]
fn large_default_set_ignores_unkeyed_nondefeq_theorems_without_elaborating_them() {
    let mut source = String::new();
    for index in 0..2000 {
        source.push_str(&format!("@[simp] theorem noise_{index} (f : Nat -> Nat) (h : forall n, f n = n) (n : Nat) : f n = n := h n\n"));
    }
    source.push_str("@[reducible, simp] def eval {A : Type} {B : A -> Type} (x : A) (f : (x : A) -> B x) : B x := f x\ntheorem t (A B : Type) (x : A) (f : A -> B) (P : B -> Prop) (h : P (f x)) : P (eval x f) := by\n  dsimp\n  guard_target =ₛ P (f x)\n  exact h\n");
    accepted("large_default_set", &source);
}
