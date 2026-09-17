//! Real native source telescopes cross both independent declaration checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};
use fln_core::name::Name;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(source: &str) -> Engine {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .expect("both checkers answer")
        .engine
}
fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

#[test]
fn typed_lambdas_infer_functions_without_an_expected_type() {
    checked(
        "def id := fun (x : Nat) => x\ndef value : Nat := id 19\ntheorem ok : value = 19 := by rfl",
    );
    checked("def add := fun (x y : Nat) => x + y\ntheorem ok : add 2 3 = 5 := by rfl");
}
#[test]
fn later_domains_depend_on_earlier_binders() {
    checked(
        "def id := fun (A : Type) (x : A) => x\ndef answer : Nat := id Nat 7\ntheorem ok : answer = 7 := by rfl",
    );
    checked("def dep := fun (A : Type) (P : A -> Type) (x : A) (p : P x) => p");
}
#[test]
fn explicit_binder_annotations_and_expected_types_cooperate() {
    checked("def id : Nat -> Nat := fun (x : _) => x\ntheorem ok : id 3 = 3 := by rfl");
    checked("def id : Nat -> Nat := fun (x : Nat) => x");
}
#[test]
fn implicit_and_strict_implicit_lambdas_retain_their_binder_kinds() {
    for (binder, style) in [
        ("{A : Type}", BinderInfo::Implicit),
        ("⦃A : Type⦄", BinderInfo::StrictImplicit),
    ] {
        let result = checked(&format!(
            "def id := fun {binder} (x : A) => x\ndef answer : Nat := id 7\ntheorem ok : answer = 7 := by rfl"
        ));
        let ty = &result
            .environment()
            .find(&n("id"))
            .unwrap()
            .constant_val()
            .type_;
        assert!(
            matches!(ty.node(), ExprNode::ForallE { binder_info, .. } if *binder_info == style)
        );
    }
}
#[test]
fn implicit_binder_domains_can_come_from_the_expected_pi_type() {
    checked(
        "def id : forall {A : Type}, A -> A := fun {A} x => x\ntheorem ok : id 7 = 7 := by rfl",
    );
}
#[test]
fn quantified_telescopes_preserve_dependency_and_impredicativity() {
    checked("def Pi := forall (A : Type) (P : A -> Type) (x : A), P x");
    checked("def proposition (A : Type) (P : A -> Prop) : Prop := forall (x : A), P x");
    checked(
        "theorem ident : forall (A : Type) (P : A -> Prop) (x : A) (h : P x), P x := fun (A : Type) (P : A -> Prop) (x : A) (h : P x) => h",
    );
}
#[test]
fn shared_ascriptions_type_the_binders_not_the_result() {
    checked("def comparison := fun x y : Nat => x = y");
    checked("def id := fun x : Nat => x\ntheorem ok : id 8 = 8 := by rfl");
}
#[test]
fn anonymous_binders_do_not_shadow_named_locals() {
    checked("def keep (x : Nat) := fun (_ : Bool) => x\ntheorem ok : keep 7 true = 7 := by rfl");
    checked("def ignore : Nat -> Nat := fun _ => 2\ntheorem ok : ignore 8 = 2 := by rfl");
}
#[test]
fn nested_annotation_lambdas_and_quantifiers_use_the_same_worklist() {
    checked(
        "def use := fun (f : forall (x : Nat), Nat) => f 7\ntheorem ok : use (fun (x : Nat) => x) = 7 := by rfl",
    );
    checked("def id := fun (x : (fun (A : Type) => A) Nat) => x\ntheorem ok : id 7 = 7 := by rfl");
}
#[test]
fn classes_in_lambda_telescopes_drive_local_instance_search() {
    checked(
        "class Item (A : Type) where\n  value : A\ndef select := fun {A : Type} [d : Item A] => d.value\ninstance natItem : Item Nat := { value := 7 }\ndef seven : Nat := select\ntheorem ok : seven = 7 := by rfl",
    );
}
#[test]
fn anonymous_universes_in_lambda_domains_generalize() {
    checked(
        "def id := fun (A : Sort _) (x : A) => x\ndef low : Nat := id Nat 7\ndef high : Type := id (Type) Nat",
    );
}
#[test]
fn lambda_scope_is_restored_before_elaborating_siblings() {
    checked(
        "def keep (x : Nat) : Nat := (fun (x : Nat) => x) x\ntheorem ok : keep 7 = 7 := by rfl",
    );
}
#[test]
fn wrong_annotations_holes_and_scope_escapes_never_publish() {
    for source in [
        "def wrong : Nat -> Nat := fun (x : Bool) => 7",
        "def wrong := fun (x : 7) => x",
        "def wrong : Nat -> Nat := fun (x : Nat) => true",
        "def wrong := fun (x : Nat) (p : (Nat : Prop)) => x",
        "def wrong := fun (x : _) => x",
        "def wrong := fun (x : Nat) => _",
        "def wrong := (fun (x : Nat) => x) x",
        "def wrong := fun (x : Nat) : Nat => x",
        "def wrong := forall (x : Nat) : Nat, Nat",
        "def wrong : Prop := forall (A : Type), Nat",
    ] {
        let base = engine();
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert!(!base.environment().contains(&n("wrong")));
    }
}

#[test]
fn dependent_arrows_work_in_signatures_arguments_and_constructor_fields() {
    checked(
        "def id : (A : Type) -> A -> A := fun (A : Type) (x : A) => x\ntheorem ok : id Nat 7 = 7 := by rfl",
    );
    checked("def id : {A : Type} -> A -> A := fun {A} x => x\ntheorem ok : id 7 = 7 := by rfl");
    checked("def apply (A : Type) (P : A -> Type) (f : (x : A) -> P x) (x : A) : P x := f x");
    checked("structure Dep where\n  A : Type\n  P : A -> Type\n  value : (x : A) -> P x");
}

#[test]
fn expected_implicit_prefixes_are_inserted_before_written_lambdas() {
    checked("def id : {A : Type} -> A -> A := fun x => x\ntheorem ok : id 7 = 7 := by rfl");
    checked("def id : {A : Sort _} -> A -> A := fun x => x");
    checked(
        "def first : {A : Type} -> {B : Type} -> A -> B -> A := fun x y => x\ntheorem ok : first 7 true = 7 := by rfl",
    );
    checked(
        "def first : {A : Type} -> ⦃B : Type⦄ -> A -> B -> A := fun x y => x\ntheorem ok : first 7 true = 7 := by rfl",
    );
}

#[test]
fn expected_instance_prefixes_feed_body_instance_synthesis() {
    checked(
        "class Item (A : Type) where\n  value : A\ndef get : {A : Type} -> [d : Item A] -> Nat -> A := fun (_ : Nat) => Item.value\ninstance natItem : Item Nat := { value := 7 }\ntheorem ok : get 0 = 7 := by rfl",
    );
}

#[test]
fn implicit_prefix_insertion_preserves_source_hygiene_and_scope() {
    checked("def keep (A : Nat) : {A : Type} -> Nat -> Nat := fun x => A + x");
}

#[test]
fn implicit_annotations_suppress_automatic_lambda_insertion() {
    checked(
        "def id : {A : Type} -> A -> A := fun {B : Type} (x : B) => x\ntheorem ok : id 7 = 7 := by rfl",
    );
    checked("def id : ⦃A : Type⦄ -> A -> A := fun A x => x");
}

#[test]
fn grouped_annotations_observe_preceding_binder_shadowing() {
    checked("def keep (A : Type) := fun (x y : A) => x");
    for source in [
        "def wrong (A : Type) := fun (A x : A) => x",
        "def wrong (A : Type) := forall (A x : A), A",
        "def wrong (A : Type) := fun A x : A => x",
    ] {
        assert!(
            engine()
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                )
                .is_err(),
            "{source}"
        );
    }
}

#[test]
fn failed_tactic_alternatives_do_not_leak_implicit_binders() {
    checked(
        "theorem keep : forall {P : Prop}, P -> P := by\n  first | exact fun (h : Nat) => h | exact fun h => h",
    );
}
