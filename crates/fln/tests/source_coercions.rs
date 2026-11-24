//! Source-level coercions are ordinary terms checked by both engines.
#![forbid(unsafe_code)]
use fln::{
    Budget, ConstantInfo, DataValue, Engine, EngineAdmissionLimits, Expr, KVMap, Name,
    SourceCheckLimits,
};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
#[test]
fn staged_coercion_library_is_admitted_by_both_checkers() {
    let base = seed();
    checked(
        &base,
        "structure Box where\n  value : Nat\ninstance boxToNat : Coe Box Nat := Coe.mk (fun x => x.value)\ndef unpack (x : Box) : Nat := Coe.coe x",
    );
    checked(
        &base,
        include_str!("../../../examples/native_conditionals.lean"),
    );
    checked(
        &base,
        include_str!("../../../examples/native_collections.lean"),
    );
}

#[test]
fn direct_coercions_check_arguments_results_and_let_annotations() {
    checked(
        &seed(),
        r#"structure Box where
  value : Nat
instance boxToNat : Coe Box Nat := Coe.mk (fun b => b.value)
def value : Box := Box.mk 17
def asResult : Nat := value
def take (n : Nat) : Nat := n + 2
def asArgument := take value
def inLet : Nat := let n : Nat := value; n
theorem result_ok : asResult = 17 := by rfl
theorem argument_ok : asArgument = 19 := by rfl
theorem let_ok : inLet = 17 := by rfl"#,
    );
}

#[test]
fn function_coercions_apply_real_record_fields() {
    checked(
        &seed(),
        r#"structure FnBox where
  run : Nat -> Nat
instance callable : CoeFun FnBox (fun f => Nat -> Nat) := CoeFun.mk (fun f => f.run)
def boxed : FnBox := FnBox.mk (fun n => n + 3)
def applied := boxed 9
theorem works : applied = 12 := by rfl"#,
    );
}

#[test]
fn sort_coercions_elaborate_bundled_type_annotations() {
    checked(
        &seed(),
        r#"structure Bundle where
  carrier : Type
instance bundled : CoeSort Bundle Type := CoeSort.mk (fun b => b.carrier)
def numbers : Bundle := Bundle.mk Nat
def number : numbers := (7 : Nat)
theorem works : number = (7 : Nat) := by rfl"#,
    );
}

#[test]
fn type_coercions_compose_through_intermediate_types() {
    checked(
        &seed(),
        r#"structure A where
  value : Nat
structure B where
  value : Nat
instance ab : Coe A B := Coe.mk (fun a => B.mk (a.value + 1))
instance bn : Coe B Nat := Coe.mk (fun b => b.value + 2)
def converted : Nat := A.mk 7
theorem works : converted = 10 := by rfl"#,
    );
}

#[test]
fn dependent_coercions_match_the_value_not_just_its_type() {
    let base = checked(
        &seed(),
        r#"instance oneBool : CoeDep Nat 1 Bool := CoeDep.mk true
def one : Nat := 1
def answer : Bool := (1 : Nat)
theorem works : answer = true := by rfl"#,
    );
    assert!(
        base.check_source_files(&[b"def other : Bool := (2 : Nat)"], &KVMap::new(), limits())
            .is_err()
    );
}

#[test]
fn coercion_search_backtracks_a_successful_edge_when_the_rest_of_the_path_fails() {
    checked(
        &seed(),
        r#"structure A where
  value : Nat
structure B where
  value : Nat
structure C where
  value : Nat
instance ac : Coe A C := Coe.mk (fun a => C.mk a.value)
instance cn : Coe C Nat := Coe.mk (fun c => c.value + 2)
instance (priority := 2000) deadEnd : Coe B Nat := Coe.mk (fun b => b.value + 99)
def converted : Nat := A.mk 7
theorem works : converted = 9 := by rfl"#,
    );
}

#[test]
fn definitional_equality_precedes_nonidentity_conversion() {
    checked(
        &seed(),
        r#"structure Indexed (n : Nat) where
  value : Nat
instance shouldNotRun : Coe (Indexed (2 + 3)) (Indexed 5) := Coe.mk (fun a => Indexed.mk 999)
def original : Indexed (2 + 3) := Indexed.mk 17
def unchanged : Indexed 5 := original
theorem works : unchanged.value = 17 := by rfl"#,
    );
}

#[test]
fn callable_records_coerce_to_function_arguments() {
    checked(
        &seed(),
        r#"structure FnBox where
  run : Nat -> Nat
instance callable : CoeFun FnBox (fun f => Nat -> Nat) := CoeFun.mk (fun f => f.run)
def use (f : Nat -> Nat) : Nat := f 9
def boxed : FnBox := FnBox.mk (fun n => n + 3)
def applied := use boxed
theorem works : applied = 12 := by rfl"#,
    );
}

/// `↑e` (`coeNotation`) elaborates `e` with no expected type and coerces it to the expected type,
/// including as an operator's leaf, which waits for the type the other leaves give it.
#[test]
fn the_coercion_arrow_coerces_to_the_expected_type() {
    checked(
        &seed(),
        r#"structure Box where
  value : Nat
instance boxToNat : Coe Box Nat := Coe.mk (fun b => b.value)
def value : Box := Box.mk 17
def unboxed : Nat := ↑value
def bumped : Nat := ↑value + 1
theorem unboxed_ok : unboxed = 17 := by rfl
theorem bumped_ok : bumped = 18 := by rfl"#,
    );
}

fn printed_definition(engine: &Engine, declaration: &str, options: &[(&str, bool)]) -> String {
    let mut scope = fln_elab::source::scope::SourceScope::default();
    for (key, value) in options {
        scope.options.insert(
            Name::from_components(key.split('.')),
            DataValue::OfBool(*value),
        );
    }
    let environment = engine.environment();
    let Some(ConstantInfo::Defn(definition)) =
        environment.find(&Name::from_components(declaration.split('.')))
    else {
        panic!("missing checked definition {declaration}");
    };
    fln::pretty::Printer::in_scope(environment, &scope)
        .expr(&definition.value, 0)
        .unwrap_or_else(|error| panic!("{declaration}: {error:?}"))
}

/// The `[coe]` attribute controls delaboration independently of instance search.
/// None of these functions is a coercion instance, and a familiar name alone is
/// insufficient to authorize coercion notation.
#[test]
fn native_coe_attributes_control_custom_functions_without_name_special_cases() {
    let engine = checked(
        &seed(),
        r#"inductive A where | mk
def a : A := A.mk
@[coe] def custom (x : A) : A := x
def another (x : A) : A := x
attribute [coe] another another
def ordinary (x : A) : A := x
def customValue := custom a
def anotherValue := another a
def ordinaryValue := ordinary a
"#,
    );
    assert_eq!(printed_definition(&engine, "customValue", &[]), "↑a");
    assert_eq!(printed_definition(&engine, "anotherValue", &[]), "↑a");
    assert_eq!(
        printed_definition(&engine, "ordinaryValue", &[]),
        "ordinary a"
    );
    let familiar_name = checked(
        &Engine::builder().build_empty(),
        "prelude\ninductive A where | mk\ndef a : A := A.mk\ndef Nat.cast (x : A) : A := x\ndef familiarNameValue := Nat.cast a",
    );
    assert_eq!(
        printed_definition(&familiar_name, "familiarNameValue", &[]),
        "Nat.cast a"
    );
}

#[test]
fn registered_coercions_respect_display_options_and_remaining_arguments() {
    let engine = checked(
        &seed(),
        r#"inductive A where | mk
def a : A := A.mk
@[coe] def custom (x : A) : A := x
@[coe] def generic {X : Type} (x : X) : X := x
@[coe] def toFunction (x : A) : A -> A := fun y => y
@[coe] def genericResult (x : A) {X : Type} (y : X) : X := y
def customValue := custom a
def genericValue := generic a
def partialGeneric := @generic A
def appliedValue := toFunction a a
def genericResultValue := genericResult a a
"#,
    );
    for (declaration, options, expected) in [
        ("customValue", &[][..], "↑a"),
        ("customValue", &[("pp.coercions", false)][..], "custom a"),
        ("customValue", &[("pp.notation", false)][..], "↑a"),
        ("customValue", &[("pp.explicit", true)][..], "↑a"),
        (
            "customValue",
            &[("pp.coercions.types", true)][..],
            "(↑a : A)",
        ),
        ("genericValue", &[][..], "↑a"),
        ("genericValue", &[("pp.explicit", true)][..], "@generic A a"),
        ("partialGeneric", &[][..], "generic"),
        ("appliedValue", &[][..], "↑a a"),
        (
            "appliedValue",
            &[("pp.coercions.types", true)][..],
            "(↑a : A → A) a",
        ),
        ("genericResultValue", &[][..], "↑a a"),
        (
            "genericResultValue",
            &[("pp.explicit", true)][..],
            "@genericResult a A a",
        ),
    ] {
        assert_eq!(
            printed_definition(&engine, declaration, options),
            expected,
            "{declaration} under {options:?}"
        );
    }
}

#[test]
fn invalid_coercion_attributes_leave_the_original_environment_unchanged() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "prelude\n@[coe] axiom A : Type",
        "prelude\naxiom A : Type\n@[coe] def noExplicit {X : Type} : Type := X",
        "prelude\naxiom A : Type\nattribute [coe] A",
        "prelude\n@[local coe] def f (A : Type) : Type := A",
        "prelude\n@[scoped coe] def f (A : Type) : Type := A",
        "prelude\ndef f (A : Type) : Type := A\nattribute [local coe] f",
        "prelude\ndef f (A : Type) : Type := A\nattribute [scoped coe] f",
        "prelude\ndef f (A : Type) : Type := A\nattribute [coe] f missing",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let recovered = checked(
        &base,
        "inductive A where | mk\ndef a : A := A.mk\n@[coe] def f (x : A) : A := x\ndef value := f a",
    );
    assert_eq!(printed_definition(&recovered, "value", &[]), "↑a");
}

/// Imported `coeExt` entries can describe coercions to functions and sorts,
/// or consume arguments after the coercee. Their recorded arity is authoritative.
#[test]
fn coercion_kinds_and_registered_arities_drive_the_printer() {
    use fln_elab::delaborator_tags::{CoeFnInfo, CoeFnKind, coercions};

    let engine = checked(
        &seed(),
        r#"inductive A where | mk
def a : A := A.mk
def toFunction (x : A) : A -> A := fun y => y
def toSort (x : A) : Type := A
def choose (x : A) (ignored : A) : A := x
"#,
    );
    let environment = coercions::register(
        engine.environment(),
        &[
            (
                Name::from_components(["toFunction"]),
                CoeFnInfo {
                    num_args: 1,
                    coercee: 0,
                    kind: CoeFnKind::CoeFun,
                },
            ),
            (
                Name::from_components(["toSort"]),
                CoeFnInfo {
                    num_args: 1,
                    coercee: 0,
                    kind: CoeFnKind::CoeSort,
                },
            ),
            (
                Name::from_components(["choose"]),
                CoeFnInfo {
                    num_args: 2,
                    coercee: 0,
                    kind: CoeFnKind::Coe,
                },
            ),
        ],
    )
    .unwrap();
    for (typed, cases) in [
        (
            false,
            [
                ("toFunction", 1, "⇑a"),
                ("toFunction", 2, "a a"),
                ("toSort", 1, "↥a"),
                ("choose", 1, "choose a"),
                ("choose", 2, "↑a"),
            ],
        ),
        (
            true,
            [
                ("toFunction", 1, "(⇑a : A → A)"),
                ("toFunction", 2, "(a : A → A) a"),
                ("toSort", 1, "(↥a : Type)"),
                ("choose", 1, "choose a"),
                ("choose", 2, "(↑a : A)"),
            ],
        ),
    ] {
        let mut scope = fln_elab::source::scope::SourceScope::default();
        scope.options.insert(
            Name::from_components(["pp", "coercions", "types"]),
            DataValue::OfBool(typed),
        );
        let mut printer = fln::pretty::Printer::in_scope(&environment, &scope);
        for (function, arity, expected) in cases {
            let term = (0..arity).fold(
                Expr::const_(Name::from_components([function]), Vec::new()),
                |function, _| {
                    Expr::app(
                        function,
                        Expr::const_(Name::from_components(["a"]), Vec::new()),
                    )
                },
            );
            assert_eq!(printer.expr(&term, 0).unwrap(), expected);
        }
    }
    let corrupt = environment
        .push_extension_entry(&coercions::journal_name(), b"invalid".to_vec())
        .unwrap();
    let term = Expr::app(
        Expr::const_(Name::from_components(["toFunction"]), Vec::new()),
        Expr::const_(Name::from_components(["a"]), Vec::new()),
    );
    assert_eq!(
        fln::pretty::Printer::new(&corrupt).expr(&term, 0),
        Err(fln::pretty::Unsupported(
            "a malformed delaborator tag journal"
        ))
    );
}

#[test]
fn coercion_result_aliases_reveal_implicit_parameters_in_the_native_reducer() {
    let engine = checked(
        &seed(),
        r#"inductive A where | mk
def a : A := A.mk
def Alias := {X : Type} -> X -> X
@[coe] def result (x : A) : Alias := fun {X} y => y
def applied := result a a
def underBinder (x : A) := result x x
"#,
    );
    assert_eq!(printed_definition(&engine, "applied", &[]), "↑a a");
    assert_eq!(
        printed_definition(&engine, "applied", &[("pp.explicit", true)]),
        "@result a A a"
    );
    assert_eq!(
        printed_definition(&engine, "underBinder", &[]),
        "fun x => ↑x x"
    );
}
