//! Hygienic sequential do quotations through the native source pipeline.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    seed.check_source_files(
        &[br#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
instance idOfNat {A : Type} {n : Nat} [inst : OfNat A n] : OfNat (Id A) n := inst
"#],
        &KVMap::new(),
        limits(),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}

fn checked(source: &str, theorems: usize) {
    let result = engine()
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(result.theorems, theorems);
}

#[test]
fn sequential_let_and_bind_shadow_definition_site_globals() {
    checked(
        r#"
def value : Nat := 100
macro "letOnce " n:term:max : term => `(do { let value : Nat := $n; return Nat.add value 1 })
macro "bindOnce " n:term:max : term => `(do { let value ← ($n : Id Nat); return Nat.add value 1 })
def a : Id Nat := letOnce (41 : Nat)
def b : Id Nat := bindOnce (41 : Nat)
theorem av : a = 42 := rfl
theorem bv : b = 42 := rfl
"#,
        2,
    );
}

#[test]
fn local_functions_bind_parameters_only_in_their_own_declaration() {
    checked(
        r#"
def n : Nat := 7
def f : Nat := 99
macro "localFn " input:term:max : term => `(do { let f (n : Nat) : Nat := Nat.add n $input; return Nat.add (f $input) n })
def result : Id Nat := localFn (5 : Nat)
theorem result_value : result = 17 := rfl
"#,
        1,
    );
}

#[test]
fn sequential_initializer_reads_previous_binding_not_its_own_name() {
    checked(
        r#"
def value : Nat := 3
macro "shadow " : term => `(do { let value : Nat := Nat.add value 1; let value : Nat := Nat.add value 2; return value })
def result : Id Nat := shadow
theorem result_value : result = 6 := rfl
"#,
        1,
    );
}

#[test]
fn do_binders_do_not_capture_antiquoted_consumer_names() {
    checked(
        r#"
def value : Nat := 99
macro "keepInput " n:term:max : term => `(do { let value : Nat := 1; return Nat.add value $n })
def result (value : Nat) : Id Nat := keepInput value
theorem result_value : result 41 = 42 := rfl
"#,
        1,
    );
}

#[test]
fn bare_nested_do_extends_the_sequence_but_term_do_does_not() {
    let source = r#"
def value : Nat := 7
macro "bareNested " : term => `(do { do { let value : Nat := 42; (Pure.pure PUnit.unit : Id PUnit) }; return value })
macro "termNested " : term => `(do { let result ← (do { let value : Nat := 42; return value }); return Nat.add result value })
def a : Id Nat := bareNested
def b : Id Nat := termNested

"#;
    for (name, expected) in [("a", "42"), ("b", "49")] {
        let program = format!("{source}\n#eval {name}");
        let result = engine()
            .execute_source_commands_with_checks(
                program.as_bytes(),
                &KVMap::new(),
                fln::EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let fln::VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
            panic!("VM must return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn branch_bindings_are_local_and_named_haves_survive() {
    checked(
        r#"
def value : Nat := 7
def h : Nat := 100
macro "chooseBranch " flag:term:max : term => `(do { let value ← (if $flag then (do { let value : Nat := 42; return value }) else (do { let value : Nat := 5; return value })); have h : value = value := rfl; return Nat.add value 1 })
def a : Id Nat := chooseBranch true
def b : Id Nat := chooseBranch false
theorem av : a = 43 := rfl
theorem bv : b = 6 := rfl
"#,
        2,
    );
}

#[test]
fn quoted_do_compiles_and_runs_on_golem() {
    let result = engine()
        .execute_source_commands_with_checks(
            r#"def value : Nat := 99
macro "runBind " n:term:max : term => `(do { let value ← ($n : Id Nat); return Nat.add value 1 })
#eval (runBind (41 : Nat) : Id Nat)
"#
            .as_bytes(),
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
        panic!("checked macro must return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn imported_do_macros_keep_definition_globals_and_consumer_variables_distinct() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let lib = fln::Name::from_components(["Library"]);
    let main = fln::Name::from_components(["Main"]);
    let modules = [
        fln::SourceModuleInput {
            name: &lib,
            source: br#"namespace Lib
def value : Nat := 7
macro "runLocal " n:term:max : term => `(do { let value : Nat := Nat.add value $n; return value })
end Lib
"#,
        },
        fln::SourceModuleInput {
            name: &main,
            source: br#"import Library
def value : Nat := 99
def result (value : Nat) : Id Nat := runLocal value
theorem result_value : result 35 = 42 := rfl
"#,
        },
    ];
    let result = base
        .check_source_modules(
            &modules,
            &main,
            &options,
            fln::source_check::modules::SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.checked.theorems, 1);
    assert_eq!(base.logical_root(&options), before);
    // Reloading the journal must retain lexical scopes, not resolve anew at use.
    let reentry = result
        .checked
        .engine
        .check_source_files(
            &[b"theorem again (value : Nat) : (runLocal value : Id Nat) = Nat.add 7 value := rfl"],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(reentry.theorems, 1);
}

#[test]
fn rejected_macro_use_never_changes_the_base_and_a_clean_retry_succeeds() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for source in [
        "def value : Nat := 99\nmacro \"runLocal \" : term => `(do { let value : Nat := 42; return value })\ndef result : Id Nat := runLocal\ntheorem bad : result = 99 := rfl",
        "macro \"unknownAction \" : term => `(do { let value ← missing; return value })\ndef result : Id Nat := unknownAction",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), before);
    }
    let result = base
        .check_source_files(
            &[
                r#"macro "unusedUnknown " : term => `(do { let value ← missing; return value })
macro "runLocal " : term => `(do { let value : Nat := 42; return value })
def result : Id Nat := runLocal
theorem good : result = 42 := rfl
"#
                .as_bytes(),
            ],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.theorems, 1);
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn checked_notation_does_not_acquire_an_unimplemented_do_precheck() {
    let base = engine();
    let result = base.check_source_files(
        &[b"notation \"notChecked\" => do { let value : Nat := 42; return value }"],
        &KVMap::new(),
        limits(),
    );
    assert!(result.is_err());
}

#[test]
fn ordinary_bare_blocks_keep_locals_and_early_returns_without_macro_help() {
    checked(
        r#"
def value : Nat := 7
def ordinary : Id Nat := do
  do
    let value : Nat := 40
    let f (x : Nat) : Nat := Nat.add value x
    (Pure.pure PUnit.unit : Id PUnit)
  return f 2
def early : Id Nat := do
  do
    let value : Nat := 42
    return value
  return 7
theorem ordinary_value : ordinary = 42 := rfl
theorem early_value : early = 42 := rfl
"#,
        2,
    );
}
