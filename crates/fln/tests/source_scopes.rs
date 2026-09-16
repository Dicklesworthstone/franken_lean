//! File scopes use the real parser, native elaborator, and both checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::name::Name;
use fln_elab::instances::InstanceRegistry;

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
fn nested_namespaces_reopen_and_resolve_relative_and_absolute_names() {
    let result = checked(
        &engine(),
        "def value : Nat := 1\nnamespace A\ndef value : Nat := 7\nnamespace B\ndef answer : Nat := value + _root_.value\nend B\nend A\nnamespace A.B\ntheorem answer_ok : answer = 8 := by rfl\nend A.B\ntheorem outside : A.B.answer = 8 := by rfl",
    );
    assert!(result.environment().contains(&n("A.B.answer")));
    assert!(!result.environment().contains(&n("answer")));
}
#[test]
fn section_open_state_is_restored_but_checked_declarations_survive() {
    let base = checked(
        &engine(),
        "namespace A\ndef a : Nat := 7\nend A\nsection Local\nopen A\ndef inside : Nat := a\nend Local\ntheorem persisted : inside = A.a := by rfl",
    );
    assert!(
        base.check_source_files(
            &[b"def bad : Nat := a"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
#[test]
fn universe_commands_work_in_bodies_and_restore_with_scope_exit() {
    let result = checked(
        &engine(),
        "section\nuniverse u\ndef lifted : Type (u + 1) := Type u\nnamespace A\nuniverse v\ndef identity (B : Sort v) (b : B) : B := b\nend A\nend\ntheorem value : A.identity Nat 7 = 7 := by rfl",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("lifted"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("u")]
    );
    assert_eq!(
        result
            .environment()
            .find(&n("A.identity"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("v")]
    );
    assert!(
        result
            .check_source_files(
                &[b"def bad := Type u"],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}
#[test]
fn namespaced_recursive_families_and_functions_use_canonical_constructor_names() {
    checked(
        &engine(),
        "namespace Lists\ninductive Seq (A : Type) where\n  | nil\n  | cons (head : A) (tail : Seq A)\ndef size {A : Type} (xs : Seq A) : Nat := match xs with | Seq.nil => 0 | Seq.cons x rest => size rest + 1\ndef sample : Seq Nat := Seq.cons 7 Seq.nil\ntheorem length : size sample = 1 := by rfl\nend Lists\nopen Lists\ntheorem outside : size sample = 1 := by rfl",
    );
}
#[test]
fn namespaced_records_inheritance_and_field_access_compute() {
    checked(
        &engine(),
        "namespace Data\nstructure Base where\n  value : Nat\nstructure Child extends Base where\n  backup : Nat := value\ndef chosen : Child := { value := 23 }\ntheorem qualified : chosen.value = 23 := by rfl\ntheorem inherited : chosen.backup = 23 := by rfl\nend Data\nopen Data\ntheorem outside : chosen.value = 23 := by rfl",
    );
}
#[test]
fn namespaced_class_registrations_and_explicit_universe_applications_compute() {
    let result = checked(
        &engine(),
        "namespace Classes\nclass Chosen (A : Type) where\n  value : A\ninstance natural : Chosen Nat := Chosen.mk 31\ndef result : Nat := Chosen.value\ndef identity.{u} {A : Sort u} (a : A) : A := a\ntheorem result_ok : identity.{1} result = 31 := by rfl\nend Classes\nopen Classes\ntheorem outside : identity.{1} result = 31 := by rfl",
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .candidates(&n("Classes.Chosen"))
            .iter()
            .any(|row| row.declaration == n("Classes.natural"))
    );
}
#[test]
fn locals_shadow_namespaces_and_root_escape_changes_the_declaration_namespace() {
    let result = checked(
        &engine(),
        "namespace A\ndef x : Nat := 7\ndef local (x : Nat) : Nat := x\ndef _root_.rootValue : Nat := A.x\nend A\ntheorem local_ok : A.local 23 = 23 := by rfl\ntheorem root_ok : rootValue = 7 := by rfl",
    );
    assert!(!result.environment().contains(&n("A.rootValue")));
}
#[test]
fn invalid_scopes_and_ambiguous_opens_never_publish_a_prefix() {
    let base = checked(
        &engine(),
        "namespace A\ndef value : Nat := 7\nend A\nnamespace B\ndef value : Nat := 9\nend B",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def prefix := 1\nend",
        "def prefix := 1\nnamespace A\nend B",
        "def prefix := 1\nnamespace A\nend",
        "def prefix := 1\nsection\nend A",
        "def prefix := 1\nopen Missing",
        "def prefix := 1\nopen A B\ndef bad := value",
        "def prefix := 1\nuniverse u u",
        "def prefix := 1\nsection\nuniverse u\nend\ndef bad := Type u",
        "def prefix := 1\nopen A in",
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
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&n("prefix")));
    }
    checked(&base, "open A A\ntheorem recovery : value = 7 := by rfl");
}
#[test]
fn file_boundary_closes_scopes_without_discarding_declarations() {
    let result = engine()
        .check_source_files(
            &[
                b"namespace A\ndef value := 7",
                b"def rootValue := A.value\ntheorem root_ok : rootValue = 7 := by rfl",
            ],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.engine.environment().contains(&n("rootValue")));
    assert!(!result.engine.environment().contains(&n("A.rootValue")));
    assert_eq!(result.commands, 4);
}
#[test]
fn comments_only_files_and_scoped_command_limits_are_real_boundaries() {
    let base = engine();
    let result = base
        .check_source_files(
            &[b"/- namespace A -/", b"-- empty"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.commands, 0);
    let mut bound = SourceCheckLimits::new(limits());
    bound.max_commands = 2;
    assert!(
        base.check_source_files(
            &[b"section\nnamespace A\ndef over := 7"],
            &KVMap::new(),
            bound
        )
        .is_err()
    );
}

#[test]
fn used_scope_universes_keep_declaration_order_before_local_and_inferred_levels() {
    let result = checked(
        &engine(),
        "universe z a unused\ndef choose.{v} (A : Sort z) (B : Sort a) (C : Sort v) (D : Sort b) (x : A) : A := x",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("choose"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("z"), n("a"), n("v"), n("b")]
    );
}
#[test]
fn dotted_end_closes_only_its_named_suffix_and_anonymous_scopes_are_barriers() {
    let base = checked(
        &engine(),
        "namespace A.B\nend B\ndef outer := 7\nnamespace C.D\ndef inner := 9\nend C.D\nend A",
    );
    assert!(base.environment().contains(&n("A.outer")));
    assert!(base.environment().contains(&n("A.C.D.inner")));
    assert!(
        base.check_source_files(
            &[b"namespace A\nsection\nend A"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
#[test]
fn scope_exhaustion_is_a_typed_non_rejection_and_does_not_publish() {
    let base = engine();
    let source = format!("{}def neverPublished := 7", "section\n".repeat(257));
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert!(!base.environment().contains(&n("neverPublished")));
    checked(&base, "def recovered := 7");
}
