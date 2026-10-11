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

#[test]
fn user_macros_can_bind_local_values_without_capturing_their_arguments() {
    accepted(
        "macro \"plusOne \" n:term:max : term => `(let value : Nat := $n; Nat.add value 1)\n\
         theorem capture (value : Nat) : plusOne value = Nat.add value 1 := rfl\n\
         theorem result : plusOne (41 : Nat) = 42 := rfl\n",
        2,
    );
}

#[test]
fn user_macro_local_functions_close_over_inputs_and_keep_parameter_scope() {
    accepted(
        "namespace A\ndef n : Nat := 9\n\
         macro \"twice \" input:term:max : term => `(let f (n : Nat) : Nat := Nat.add n $input; f $input)\n\
         macro \"outside \" : term => `(let f (n : Nat) : Nat := n; n)\nend A\n\
         def n : Nat := 99\n\
         theorem doubled (n : Nat) : twice n = Nat.add n n := rfl\n\
         theorem outside_parameter : outside = 9 := rfl\n",
        2,
    );
}

#[test]
fn user_macros_can_introduce_proof_bindings_without_capturing_proof_arguments() {
    accepted(
        "macro \"keepProof \" p:term:max : term => `(have h : True := True.intro; $p)\n\
         theorem preserved (P : Prop) (h : P) : P := keepProof h\n",
        1,
    );
    assert!(
        check(
            "macro \"keepProof \" p:term:max : term => `(have h : True := True.intro; $p)\n\
             theorem bad : False := keepProof True.intro\n"
        )
        .is_err()
    );
}

#[test]
fn macro_local_initializers_keep_the_declaration_site_global() {
    accepted(
        "namespace A\ndef x : Nat := 7\n\
         macro \"shadowValue\" : term => `(let x : Nat := x; x)\nend A\n\
         def x : Nat := 99\ntheorem shadow : shadowValue = 7 := rfl\n",
        1,
    );
}

#[test]
fn a_local_binding_macro_runs_on_golem_after_module_import() {
    let base = engine();
    let library_name = Name::from_components(["Library"]);
    let main_name = Name::from_components(["Main"]);
    let library =
        "macro \"plusOne \" n:term:max : term => `(let value : Nat := $n; Nat.add value 1)\n";
    let main = "import Library\ndef answer : Nat := plusOne (41 : Nat)\ntheorem verified : answer = 42 := rfl\n";
    let modules = [
        SourceModuleInput {
            name: &library_name,
            source: library.as_bytes(),
        },
        SourceModuleInput {
            name: &main_name,
            source: main.as_bytes(),
        },
    ];
    let checked = base
        .check_source_modules(
            &modules,
            &main_name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.checked.theorems, 1);
    let result = checked
        .checked
        .engine
        .execute_source_commands_with_checks(
            b"#eval plusOne (41 : Nat)\n",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
        panic!("the compiled local binding must return its value");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn unused_macros_defer_unknown_names_but_checked_notations_still_refuse_lets() {
    let prefix = "macro \"unknownLocal\" : term => `(let x : Nat := missing; x)\n";
    accepted(&format!("{prefix}theorem okay : True := True.intro\n"), 1);
    assert!(check(&format!("{prefix}def bad : Nat := unknownLocal\n")).is_err());
    assert!(matches!(
        check("notation \"letNotation\" => let x : Nat := 1; x\n"),
        Err(SourceCheckError::Command { command: 0, .. })
    ));
}
