//! Named applications are ordinary proof terms, checked by both admission seats.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits,
    SourceModuleInput,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn base() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let result = engine.check_source_files(&[source.as_bytes()], &options, limits());
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{source}\n{result:?}"
    );
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn labels_reorder_explicit_arguments_and_mix_with_positionals() {
    check(
        "def pair (x y : Nat) : Nat := Nat.add (Nat.mul x 10) y\n\
        theorem reordered : pair (y := 2) (x := 4) = 42 := by rfl\n\
        theorem mixed : pair (y := 2) 4 = 42 := by rfl\n\
        theorem trailing : pair 4 (y := 2) = 42 := by rfl\n\
        theorem positional : pair 4 2 = 42 := by rfl",
    );
}

#[test]
fn named_implicit_types_support_polymorphism_and_explicit_application() {
    check(
        "def ident.{u} {A : Sort u} (x : A) : A := x\n\
        theorem named : ident (A := Nat) (x := 7) = 7 := by rfl\n\
        theorem inferred : ident (x := 7) = 7 := by rfl\n\
        theorem explicit : @ident (x := 7) Nat = 7 := by rfl\n\
        theorem universe : ident.{1} (x := 7) (A := Nat) = 7 := by rfl\n\
        theorem generic.{u} (A : Sort u) (x : A) : ident (x := x) (A := A) = x := by rfl",
    );
}

#[test]
fn later_dependent_arguments_infer_missing_explicit_parameters() {
    check(
        "def choose (A : Type) (x : A) : A := x\n\
        def selected : Nat := choose (x := 7)\n\
        theorem selected_value : selected = 7 := by rfl\n\
        def chooseBoth (A : Type) (x y : A) : A := y\n\
        theorem both : chooseBoth (y := 2) (x := 1) = 2 := by rfl\n\
        theorem inferred_type (A : Type) (x : A) : choose (x := x) = x := by rfl",
    );
}

#[test]
fn missing_independent_parameters_eta_expand_without_capturing_source_names() {
    check(
        "def pair (x y : Nat) : Nat := Nat.add (Nat.mul x 10) y\n\
        def right : Nat -> Nat := pair (y := 2)\n\
        theorem right_value : right 4 = 42 := by rfl\n\
        def captured (x : Nat) : Nat -> Nat := pair (y := x)\n\
        theorem capture_free : captured 2 4 = 42 := by rfl\n\
        def triple (x y z : Nat) : Nat := Nat.add (Nat.add x y) z\n\
        def last : Nat -> Nat -> Nat := triple (z := 3)\n\
        theorem several : last 1 2 = 6 := by rfl",
    );
}

#[test]
fn local_function_telescope_and_nested_named_values_use_the_same_worklist() {
    check(
        "def call (f : (a : Nat) -> (b : Nat) -> Nat) : Nat := f (b := 2) (a := 40)\n\
        theorem local_call : call Nat.add = 42 := by rfl\n\
        def plus (a b : Nat) : Nat := Nat.add a b\n\
        theorem nested : plus (b := plus (b := 1) (a := 1)) (a := 40) = 42 := by rfl\n\
        def closure : Nat := let plus (a b : Nat) : Nat := Nat.add a b; plus (b := 2) 40\n\
        theorem closure_value : closure = 42 := by rfl",
    );
}

#[test]
fn named_instance_arguments_override_search_without_changing_other_calls() {
    check(
        "def read [dict : Inhabited Nat] (x : Nat) : Nat := Nat.add default x\n\
        theorem chosen : read (dict := Inhabited.mk 7) (x := 2) = 9 := by rfl\n\
        theorem normal : read (x := 2) = 2 := by rfl\n\
        theorem explicit : @read (x := 2) (dict := Inhabited.mk 7) = 9 := by rfl",
    );
}

#[test]
fn labels_preserve_quoted_names_and_partial_function_heads() {
    check(
        "def weird («a.b» «end» : Nat) : Nat := Nat.add «a.b» «end»\n\
        theorem quoted : weird («end» := 2) («a.b» := 40) = 42 := by rfl\n\
        def three (x y z : Nat) : Nat := Nat.add (Nat.add x y) z\n\
        theorem partial : (three 1) (z := 3) (y := 2) = 6 := by rfl",
    );
}

#[test]
fn theorem_arguments_are_checked_and_failed_alternatives_restore_the_context() {
    check(
        "theorem reflNamed (n : Nat) : n = n := by rfl\n\
        theorem use : 3 = 3 := by exact reflNamed (n := 3)\n\
        theorem alternative : 3 = 3 := by first | exact reflNamed (n := 4) | exact reflNamed (n := 3)",
    );
}

#[test]
fn invalid_labels_values_and_unresolved_dependencies_publish_no_prefix() {
    let engine = base();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for bad in [
        "def bad := pair (missing := 1)",
        "def bad := pair (x := 1) (x := 2)",
        "def bad := pair (x := \"not Nat\") (y := 2)",
        "def bad := pair (x := 1) (y := 2) 3",
        "def bad : Nat := choose (x := _)",
        "theorem bad : pair (x := 1) (y := 2) = 0 := by rfl",
    ] {
        let sources = [
            b"def pair (x y : Nat) : Nat := Nat.add x y\ndef choose (A : Type) (x : A) : A := x"
                .as_slice(),
            bad.as_bytes(),
        ];
        let result = engine.check_source_files(&sources, &options, limits());
        assert!(
            !matches!(result, Ok(Outcome::Complete(_))),
            "{bad}: {result:?}"
        );
        assert_eq!(engine.logical_root(&options), root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["pair"]))
        );
    }
    let repaired = b"def pair (x y : Nat) : Nat := Nat.add x y\ntheorem repaired : pair (y := 2) (x := 1) = 3 := by rfl";
    assert!(matches!(
        engine.check_source_files(&[repaired], &options, limits()),
        Ok(Outcome::Complete(_))
    ));
}

#[test]
fn named_applications_cross_isolated_import_admission() {
    let engine = base();
    let main = Name::from_components(["Main"]);
    let lib = Name::from_components(["Lib"]);
    let modules = [
        SourceModuleInput { name: &main, source: b"import Lib\ntheorem use : Library.ident (x := 7) (A := Nat) = 7 := by exact Library.same (A := Nat) (x := 7)" },
        SourceModuleInput { name: &lib, source: b"namespace Library\ndef ident.{u} {A : Sort u} (x : A) : A := x\ntheorem same.{u} {A : Sort u} (x : A) : ident (x := x) = x := by rfl\nend Library" },
    ];
    let result = engine.check_source_modules(
        &modules,
        &main,
        &KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
    );
    assert!(matches!(result, Ok(Outcome::Complete(_))), "{result:?}");
}
