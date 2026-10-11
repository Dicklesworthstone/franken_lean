//! Binding notation templates through the ordinary checker, VM and module importer.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckError,
    SourceCheckLimits, SourceModuleInput, VmExit,
};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(source: &str) -> Result<usize, SourceCheckError> {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .map(|result| result.into_complete().unwrap().theorems)
}

fn accepted(source: &str, expected: usize) {
    assert_eq!(
        check(source).unwrap_or_else(|error| panic!("{source}\n{error:?}")),
        expected
    );
}

#[test]
fn lambda_templates_elaborate_to_checked_terms() {
    accepted(
        "notation \"idFn\" => fun (x : Nat) => x\n\
         theorem identity : (idFn) 7 = 7 := rfl\n\
         notation \"⟪\" x \"⟫\" => (fun y => Nat.add y y) x\n\
         theorem double : ⟪(3 : Nat)⟫ = 6 := rfl\n",
        2,
    );
}

#[test]
fn substituted_notation_arguments_cannot_be_captured_by_template_binders() {
    accepted(
        "notation \"constantFn\" y => fun (x : Nat) => y\n\
         theorem capture (x : Nat) : (constantFn x) 0 = x := rfl\n\
         macro \"same \" y:term:max : term => `((fun (x : Nat) => $y) 0)\n\
         theorem macro_capture (x : Nat) : same x = x := rfl\n",
        2,
    );
}

#[test]
fn quantified_templates_build_real_proofs_and_reject_false_ones() {
    accepted(
        "notation \"allSelf\" => ∀ (n : Nat), n = n\n\
         theorem reflexive : allSelf := by intro n; rfl\n\
         notation \"allEqual\" => ∀ x y : Nat, x = y → x = y\n\
         theorem reuse : allEqual := by intro x y h; exact h\n",
        2,
    );
    assert!(
        check(
            "notation \"allZero\" => ∀ (n : Nat), n = 0\ntheorem bad : allZero := by intro n; rfl\n"
        )
        .is_err()
    );
}

#[test]
fn dependent_arrow_templates_keep_their_telescope_dependencies() {
    accepted(
        "notation \"identityType\" => (α : Type) → α → α\n\
         def identity : identityType := fun (α : Type) (x : α) => x\n\
         theorem applied : identity Nat 7 = 7 := rfl\n",
        1,
    );
}

#[test]
fn nested_lambdas_restore_outer_bindings() {
    accepted(
        "notation \"nestedFn\" => fun (x : Nat) => (fun (x : Nat) => x) x\n\
         theorem nested : (nestedFn) 42 = 42 := rfl\n",
        1,
    );
}

#[test]
fn free_template_names_keep_their_declaration_namespace_under_binders() {
    let library = "namespace A\ndef value : Nat := 7\nnotation \"valueFn\" => fun (n : Nat) => Nat.add value n\nend A\ndef value : Nat := 99\n";
    accepted(
        &format!("{library}theorem right (value : Nat) : (valueFn) 3 = 10 := rfl\n"),
        1,
    );
    assert!(
        check(&format!(
            "{library}theorem wrong : (valueFn) 3 = 102 := rfl\n"
        ))
        .is_err()
    );
}

#[test]
fn unknown_free_names_are_refused_even_when_the_notation_is_unused() {
    for source in [
        "notation \"badFn\" => fun (n : Nat) => missing\ntheorem t : True := True.intro\n",
        "notation \"badType\" => ∀ (n : Missing), True\ntheorem t : True := True.intro\n",
        "notation \"escaped\" => (fun (x : Nat) => x) x\ntheorem t : True := True.intro\n",
    ] {
        assert!(
            matches!(
                check(source),
                Err(SourceCheckError::Command { command: 0, .. })
            ),
            "{source}"
        );
    }
}

#[test]
fn lambda_notation_compiles_and_executes_on_golem() {
    let result = engine()
        .execute_source_commands_with_checks(
            b"notation \"idFn\" => fun (x : Nat) => x\n#eval (idFn) 42\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
        panic!("the VM must return the checked term's value");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn imported_binding_templates_keep_library_globals_and_consumer_locals_distinct() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let library_name = Name::from_components(["Library"]);
    let main_name = Name::from_components(["Main"]);
    let library = "namespace A\ndef value : Nat := 7\nnotation \"valueFn\" => fun (n : Nat) => Nat.add value n\nnotation \"allSelf\" => ∀ (n : Nat), n = n\nend A\n";
    let main = "import Library\ndef value : Nat := 99\ntheorem imported (value : Nat) : (valueFn) 3 = 10 := rfl\ntheorem universal : allSelf := by intro n; rfl\n";
    let modules = [
        SourceModuleInput {
            name: &main_name,
            source: main.as_bytes(),
        },
        SourceModuleInput {
            name: &library_name,
            source: library.as_bytes(),
        },
    ];
    let result = base
        .check_source_modules(
            &modules,
            &main_name,
            &options,
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.checked.theorems, 2);
    assert_eq!(result.module_order, [library_name, main_name]);
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn grouped_and_shared_domains_rebind_each_copy_without_changing_the_program() {
    accepted(
        "namespace A\ndef T : Type 1 := Type\n\
         notation \"idGroup\" => fun (T x : T) => x\n\
         notation \"idShared\" => fun T x : T => x\n\
         notation \"typeGroup\" => ∀ (T x : T), x = x\n\
         notation \"typeShared\" => ∀ T x : T, x = x\n\
         notation \"typeArrow\" => (T x : T) → x = x\nend A\n\
         def T : Type := Nat\n\
         theorem grouped : (idGroup) Nat 7 = 7 := rfl\n\
         theorem shared : (idShared) Nat 7 = 7 := rfl\n\
         theorem all_grouped : typeGroup := by intro T x; rfl\n\
         theorem all_shared : typeShared := by intro T x; rfl\n\
         theorem all_arrow : typeArrow := by intro T x; rfl\n",
        5,
    );
}
