//! Zero-field record conversion reaches source inference and both checker seats.
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
fn checked(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
}
const TYPES: &str = r#"structure Marker where
class Keyed (key : Marker) where
  value : Nat
structure Phantom (A : Type) where
class Tagged (A : Type) (key : Phantom A) where
  value : A
"#;

#[test]
fn neutral_unit_indices_reuse_checked_local_instances() {
    let base = checked(&engine(), TYPES).engine;
    let result = checked(
        &base,
        r#"def reuse (a b : Marker) [i : Keyed a] : Keyed b := inferInstance
theorem selected (a b : Marker) [i : Keyed a] : reuse a b = i := by rfl
"#,
    );
    assert_eq!((result.commands, result.theorems), (2, 1));
}

#[test]
fn neutral_empty_records_compare_below_dependent_arguments() {
    let base = checked(&engine(), TYPES).engine;
    checked(
        &base,
        r#"def transport (F : Marker -> Type) (a b : Marker) (x : F a) : F b := x
theorem transport_eq (F : Marker -> Type) (a b : Marker) (x : F a) : transport F a b x = x := by rfl
def taggedReuse (A : Type) (a b : Phantom A) [i : Tagged A a] : Tagged A b := inferInstance
"#,
    );
}

#[test]
fn instance_priority_survives_unit_like_comparison() {
    let base = checked(&engine(), TYPES).engine;
    checked(
        &base,
        r#"def newest (a b : Marker) (first : Keyed a) (second : Keyed b) : Keyed a := inferInstance
theorem newest_selected (a b : Marker) (first : Keyed a) (second : Keyed b) : newest a b first second = second := by rfl
"#,
    );
    assert!(base.check_source_files(&[b"def newest (a b : Marker) (first : Keyed a) (second : Keyed b) : Keyed a := inferInstance\ntheorem wrong (a b : Marker) (first : Keyed a) (second : Keyed b) : newest a b first second = first := by rfl"], &KVMap::new(), limits()).is_err());
}

#[test]
fn nonempty_records_different_parameters_and_missing_values_are_not_erased() {
    let base = checked(&engine(), TYPES).engine;
    let root = base.logical_root(&KVMap::new());
    for bad in [
        "def bad (a : Phantom Nat) (b : Phantom Bool) [i : Tagged Nat a] : Tagged Bool b := inferInstance",
        "def bad (a b : Keyed Marker.mk) : a = b := by rfl",
        "def bad (a b : Marker) : Keyed a := _",
        "theorem bad (a b : Marker) : 0 = 1 := by rfl",
    ] {
        assert!(
            base.check_source_files(
                &[b"theorem prior : 0 = 0 := by rfl", bad.as_bytes()],
                &KVMap::new(),
                limits()
            )
            .is_err(),
            "{bad}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["prior"]))
        );
    }
    checked(&base, "theorem recovery (a b : Marker) : a = b := by rfl");
}

#[test]
fn checked_unit_like_declarations_remain_usable_across_source_files() {
    let result = engine()
        .check_source_files(
            &[
                TYPES.as_bytes(),
                b"def reuse (a b : Marker) [i : Keyed a] : Keyed b := inferInstance",
            ],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        result
            .engine
            .environment()
            .contains(&Name::from_components(["reuse"]))
    );
}
