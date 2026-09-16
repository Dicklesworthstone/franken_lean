//! Universe-polymorphic source declarations pass the native elaborator and both
//! independent admission engines. All computations below are checked proofs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}: {e:?}"))
    .into_complete()
    .expect("both checkers must answer")
    .engine
}

#[test]
fn explicit_polymorphism_instantiates_at_data_type_and_higher_universes() {
    let result = checked(
        &engine(),
        "def identity.{u} {A : Sort u} (a : A) : A := a\ndef scalar : Nat := identity 37\ndef types : Type := identity Nat\ndef higher : Type 1 := identity Type\ntheorem scalar_ok : scalar = 37 := by rfl\ntheorem types_ok : types = Nat := by rfl\ntheorem higher_ok : higher = Type := by rfl",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("identity"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("u")]
    );
}

#[test]
fn inferred_parameters_are_sorted_but_explicit_parameters_keep_user_order() {
    let result = checked(
        &engine(),
        "def automatic (A : Sort z) (B : Sort a) (x : A) : A := x\ndef explicit.{z,a} (A : Sort z) (B : Sort a) (x : A) : A := x\ndef data : Nat := explicit.{1,1} Nat Bool 7\ndef inferred : Nat := automatic.{1,_} Nat Bool 9\ntheorem value : data = 7 := by rfl\ntheorem other : inferred = 9 := by rfl",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("automatic"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("a"), n("z")]
    );
    assert_eq!(
        result
            .environment()
            .find(&n("explicit"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("z"), n("a")]
    );
}

#[test]
fn polymorphic_theorems_can_quantify_over_propositions_and_data() {
    checked(
        &engine(),
        "theorem identityProof.{u} (A : Sort u) (x : A) : x = x := by rfl\ntheorem data : 7 = 7 := identityProof Nat 7\ntheorem proof : True.intro = True.intro := identityProof True True.intro\ndef impredicative.{u} (A : Sort u) (P : Prop) : Prop := A -> P",
    );
}

#[test]
fn level_expressions_preserve_max_imax_and_literal_offsets() {
    checked(
        &engine(),
        "def productType.{u,v} (A : Type u) (B : Type v) : Type (max u v) := A -> B\ndef dependentSort.{u,v} (A : Sort u) (B : Sort v) : Sort (imax u v) := A -> B\ndef shifted.{u} : Type (u + 1) := Type u\ndef concrete : Type 2 := Type 1\ndef bareSort : Type := Sort\ndef literalSort : Type := Sort 0",
    );
}

#[test]
fn polymorphic_records_defaults_and_parent_projections_keep_universes() {
    let result = checked(
        &engine(),
        "structure Box.{u} (A : Type u) where\n  value : A\n  backup : A := value\nstructure Child.{u} (A : Type u) extends Box A where\n  tag : Nat\ndef scalar : Child Nat := { value := 13, tag := 17 }\ndef higher : Child (Type 1) := { value := Type, tag := 19 }\ntheorem data_ok : scalar.backup = 13 := by rfl\ntheorem higher_ok : higher.backup = Type := by rfl",
    );
    for name in [
        "Box",
        "Box.mk",
        "Box.value",
        "Box.backup._default",
        "Child",
        "Child.toBox",
    ] {
        assert_eq!(
            result
                .environment()
                .find(&n(name))
                .unwrap()
                .constant_val()
                .level_params,
            vec![n("u")],
            "{name}"
        );
    }
}

#[test]
fn polymorphic_class_instances_infer_universes_and_preserve_dictionaries() {
    checked(
        &engine(),
        "class Chosen.{u} (A : Type u) where\n  value : A\ninstance choose.{u} {A : Type u} [d : Inhabited A] : Chosen A := Chosen.mk default\ndef scalar : Nat := Chosen.value\ntheorem value_ok : scalar = 0 := by rfl",
    );
}

#[test]
fn recursive_inductives_and_structural_recursion_are_universe_polymorphic() {
    let result = checked(
        &engine(),
        "inductive Sequence.{u} (A : Type u) where\n  | nil\n  | cons (head : A) (tail : Sequence A)\ndef size.{u} {A : Type u} (xs : Sequence A) : Nat := match xs with | Sequence.nil => 0 | Sequence.cons x rest => size rest + 1\ndef data : Sequence Nat := Sequence.cons 7 (Sequence.cons 9 Sequence.nil)\ndef types : Sequence (Type 1) := Sequence.cons (Type) Sequence.nil\ntheorem data_size : size data = 2 := by rfl\ntheorem type_size : size types = 1 := by rfl",
    );
    let Some(ConstantInfo::Induct(family)) = result.environment().find(&n("Sequence")) else {
        panic!("family");
    };
    assert_eq!(family.base.level_params, vec![n("u")]);
}

#[test]
fn invalid_universes_never_publish_a_partial_source_file() {
    let base = checked(&engine(), "def identity.{u} {A : Sort u} (x : A) : A := x");
    let before = base.logical_root(&KVMap::new());
    for source in [
        "def prefix := 1\ndef bad.{u,u} (A : Sort u) : Sort u := A",
        "def prefix := 1\ndef bad.{u} := 7",
        "def prefix := 1\ndef bad := Type missing",
        "def prefix := 1\ndef bad := identity.{1,2} 7",
        "def prefix := 1\ndef bad (identity : Nat) : Nat := identity.{1}",
        "def prefix := 1\ndef bad : Type 1 := Nat",
        "def prefix := 1\ndef bad : Type := Type",
        "def prefix := 1\ndef bad := Type 33",
        "def prefix := 1\ndef bad := Type (1 + 18446744073709551616)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&n("prefix")));
        assert!(!base.environment().contains(&n("bad")));
    }
    checked(&base, "theorem recovery : identity 9 = 9 := by rfl");
}

#[test]
fn explicit_universe_commas_do_not_split_match_columns_or_tactic_arguments() {
    checked(
        &engine(),
        "def first.{u,v} (A : Sort u) (B : Sort v) (x : A) : A := x\ndef matched : Nat := match first.{1,1} Bool Nat true with | true => 7 | false => 9\ntheorem match_ok : matched = 7 := by rfl\ntheorem proof_ok : 13 = 13 := by exact Eq.refl.{1} 13\ndef tacticValue : Nat := by\n  let x := first.{1,1} Nat Bool 23\n  exact x\ntheorem value_ok : tacticValue = 23 := by rfl",
    );
}

#[test]
fn universe_instantiations_work_in_rewrite_and_simp_rule_lists() {
    checked(
        &engine(),
        "def first.{u,v} (A : Sort u) (B : Sort v) (x : A) : A := x\ntheorem first_eq.{u,v} (A : Sort u) (B : Sort v) (x : A) : first A B x = x := by rfl\ntheorem rewrite_ok : first Nat Bool 7 = 7 := by rw [first_eq.{1,1}]\ntheorem simp_ok : first Nat Bool 7 = 7 := by simp only [first_eq.{1,1}]",
    );
}
