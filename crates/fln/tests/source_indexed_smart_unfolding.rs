//! Regression for fln-simp-unfold-indexed-4v9t: preserve recursive calls across
//! the dependent equality transports inserted by the source match compiler.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

const SOURCE: &str = include_str!("../../../examples/native_indexed_smart_unfolding.lean");

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20)))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("both admission seats must complete")
        .engine
}

#[test]
fn selected_unfolding_keeps_the_child_call_available_to_the_induction_hypothesis() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, SOURCE);
    for name in ["copy_identity", "copy_step"] {
        assert!(
            result
                .environment()
                .contains(&Name::from_components([name]))
        );
        assert!(!base.environment().contains(&Name::from_components([name])));
    }
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn universe_polymorphic_selected_unfolding_keeps_dependent_indices_typed() {
    // Independent carrier and field universes must not be defaulted to Type 0
    // while the selected endpoint check closes its local telescope.
    let source = SOURCE
        .replace(
            "Trace (A : Type) (P : A -> Type)",
            "Trace.{u,v} (A : Type u) (P : A -> Type v)",
        )
        .replace("P a -> Type where", "P a -> Type (max u v) where")
        .replace(
            "{A : Type} {P : A -> Type}",
            "{A : Type u} {P : A -> Type v}",
        );
    checked(&engine(), &source);
}

#[test]
fn unknown_majors_and_wrong_branches_cannot_publish_a_proof() {
    let base = checked(&engine(), SOURCE);
    let before = base.logical_root(&KVMap::new());
    for source in [
        "theorem unknown {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = t := by simp only [copyTrace]",
        "theorem wrong {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = Trace.stop a v := by induction t with | stop x vx => rfl | step x y vx vy child ih => simp only [copyTrace, ih]",
    ] {
        let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
        assert!(result.is_err(), "unproved branch was admitted: {source}");
        assert_eq!(base.logical_root(&KVMap::new()), before);
    }
    checked(&base, "theorem recovery : (0 : Nat) = 0 := by rfl");
}
