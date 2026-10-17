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

#[test]
fn macro_field_labels_and_named_arguments_are_not_global_references() {
    accepted(
        "structure Cell where\n  value : Nat\n\
         def choose (left right : Nat) : Nat := left\n\
         namespace A\ndef value : Nat := 99\ndef left : Nat := 88\n\
         macro \"cellOf \" x:term:max : term => `({ value := $x : Cell })\n\
         macro \"readCell \" x:term:max : term => `(($x).value)\n\
         macro \"chooseLeft \" x:term:max : term => `(choose (right := 0) (left := $x))\n\
         end A\n\
         theorem field : readCell (cellOf (42 : Nat)) = 42 := rfl\n\
         theorem named : chooseLeft (37 : Nat) = 37 := rfl\n",
        2,
    );
}

#[test]
fn macro_record_method_parameters_are_local_to_their_field() {
    accepted(
        "structure Operations where\n  run : Nat → Nat\n  other : Nat\n\
         namespace A\ndef n : Nat := 7\n\
         macro \"operations \" x:term:max : term => `({ run (n : Nat) := Nat.add n $x, other := n : Operations })\n\
         end A\ndef n : Nat := 99\n\
         theorem runMethod (n : Nat) : (operations n).run 2 = Nat.add 2 n := rfl\n\
         theorem otherField : (operations (1 : Nat)).other = 7 := rfl\n",
        2,
    );
}

#[test]
fn macro_record_update_and_abbreviation_keep_definition_site_values() {
    accepted(
        "structure Cell where\n  value : Nat\n\
         namespace A\ndef value : Nat := 7\n\
         macro \"defaultCell\" : term => `({ value : Cell })\n\
         macro \"updateCell \" x:term:max : term => `({ $x with value := value })\n\
         end A\ndef value : Nat := 99\n\
         theorem abbreviation : (defaultCell).value = 7 := rfl\n\
         theorem update : (updateCell ({ value := 42 : Cell })).value = 7 := rfl\n",
        2,
    );
}

#[test]
fn checked_notations_support_named_arguments_but_do_not_admit_unknown_values() {
    accepted(
        "def choose (left right : Nat) : Nat := left\n\
         notation \"seven\" => choose (right := 0) (left := 7)\n\
         theorem result : seven = 7 := rfl\n",
        1,
    );
    assert!(check("def choose (left right : Nat) : Nat := left\nnotation \"bad\" => choose (left := missing) (right := 0)\n").is_err());
    assert!(check("structure Cell where\n  value : Nat\nnotation \"notPrechecked\" => { value := 1 : Cell }\n").is_err());
}

#[test]
fn field_macros_execute_after_native_module_journal_replay() {
    let base = engine();
    let library = Name::from_components(["Fields"]);
    let main = Name::from_components(["Main"]);
    let source = "structure Cell where\n  value : Nat\n\
        macro \"cellOf \" x:term:max : term => `({ value := $x : Cell })\n\
        macro \"readCell \" x:term:max : term => `(($x).value)\n";
    let consumer = "import Fields\ndef answer : Nat := readCell (cellOf (42 : Nat))\n";
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let result = base
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: source.as_bytes(),
                },
                SourceModuleInput {
                    name: &main,
                    source: consumer.as_bytes(),
                },
            ],
            &main,
            &options,
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let execution = result
        .checked
        .engine
        .execute_source_definitions(
            &[b"def run : Nat := answer"],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(returned) = &execution.executions[0].exit else {
        panic!("native return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("42")
    );
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn field_macros_do_not_hide_invalid_labels_values_or_parameter_escapes() {
    for source in [
        "structure Cell where\n  value : Nat\nmacro \"bad\" : term => `({ missing := 1 : Cell })\ndef x : Cell := bad\n",
        "structure Cell where\n  value : Nat\nmacro \"bad\" : term => `({ value := True.intro : Cell })\ndef x : Cell := bad\n",
        "structure Cell where\n  value : Nat\nmacro \"bad\" : term => `({ value := 1, value := 2 : Cell })\ndef x : Cell := bad\n",
        "structure Ops where\n  run : Nat → Nat\n  other : Nat\nmacro \"bad\" : term => `({ run (n : Nat) := n, other := n : Ops })\ndef x : Ops := bad\n",
        "def choose (left right : Nat) : Nat := left\nmacro \"bad\" : term => `(choose (missing := 7) (right := 0))\ndef x : Nat := bad\n",
    ] {
        assert!(check(source).is_err(), "must reject {source}");
    }
}

#[test]
fn quoted_matches_bind_only_branch_patterns_and_preserve_caller_arguments() {
    accepted(
        "macro \"matchAdd \" input:term:max \" plus \" extra:term:max : term => `(match $input:term with | Nat.zero => $extra | Nat.succ n => Nat.add n $extra)\n\
         theorem zero : (matchAdd (0 : Nat) plus (7 : Nat)) = 7 := rfl\n\
         theorem successor : (matchAdd (4 : Nat) plus (7 : Nat)) = 10 := rfl\n\
         theorem hygiene (n : Nat) : (matchAdd (1 : Nat) plus n) = Nat.add 0 n := rfl\n",
        3,
    );
}

#[test]
fn quoted_match_proofs_are_checked_in_each_refined_branch() {
    accepted(
        "macro \"selfProof \" a:term:max : term => `(match $a:term with | Nat.zero => by rfl | Nat.succ n => by rfl)\n\
         theorem reflexive (n : Nat) : n = n := selfProof n\n",
        1,
    );
    let bad = "macro \"badProof \" a:term:max : term => `(match $a:term with | Nat.zero => by rfl | Nat.succ n => Nat.zero)\ntheorem wrong : (0 : Nat) = 0 := badProof (0 : Nat)\n";
    assert!(
        matches!(
            check(bad),
            Err(SourceCheckError::Command { command: 1, .. })
        ),
        "an unselected branch must still have a proof of the expected type"
    );
}

#[test]
fn quoted_match_notation_prechecks_branches_in_their_own_scope() {
    accepted(
        "namespace Library\ndef value : Nat := 11\n\
         notation:max \"pick \" input:max => match input with | Nat.zero => value | Nat.succ value => value\n\
         end Library\ndef value : Nat := 99\n\
         theorem zero : pick (0 : Nat) = 11 := rfl\n\
         theorem successor : pick (8 : Nat) = 7 := rfl\n",
        2,
    );
    assert!(
        check("notation \"bad \" input => match input with | Nat.succ n => n | Nat.zero => n\n")
            .is_err()
    );
}

#[test]
fn quoted_matches_support_nested_patterns_and_multiple_discriminants() {
    accepted(
        "inductive Cell where | empty : Cell | one : Nat → Cell\n\
         macro \"sumCells \" a:term:max b:term:max : term => `(match $a:term, $b:term with | .one x, .one y => Nat.add x y | _, _ => 0)\n\
         theorem both : (sumCells (Cell.one 4) (Cell.one 5)) = 9 := rfl\n\
         theorem absent : (sumCells Cell.empty (Cell.one 5)) = 0 := rfl\n\
         macro \"nestedCell \" a:term:max : term => `(match $a:term with | .one (Nat.succ n) => n | _ => 0)\n\
         theorem nested : (nestedCell (Cell.one 8)) = 7 := rfl\n",
        3,
    );
}

#[test]
fn quoted_matches_cannot_hide_invalid_or_nonexhaustive_branches() {
    for source in [
        "macro \"badMatch \" a:term:max : term => `(match ($a) with | Nat.zero => 0 | Nat.succ n => missing)\ndef bad : Nat := badMatch (0 : Nat)\n",
        "macro \"badMatch \" a:term:max : term => `(match ($a) with | Nat.zero => 0)\ndef bad : Nat := badMatch (0 : Nat)\n",
        "macro \"badMatch \" a:term:max : term => `(match ($a) with | Nat.zero => 0 | Nat.succ n => \"wrong\")\ndef bad : Nat := badMatch (0 : Nat)\n",
        "macro \"badMatch \" a:term:max : term => `(match ($a) with | Nat.zero => n | Nat.succ n => n)\ndef bad : Nat := badMatch (1 : Nat)\n",
    ] {
        let (declaration, _) = source.split_once('\n').unwrap();
        assert_eq!(check(declaration).unwrap(), 0, "unused macro: {source}");
        let error = check(source).expect_err("invalid quoted match must be refused at use");
        assert!(
            matches!(error, SourceCheckError::Command { command: 1, .. }),
            "{source}: {error:?}"
        );
    }
}

#[test]
fn quoted_matches_restore_outer_and_sibling_scopes() {
    accepted(
        "def n : Nat := 41\n\
         macro \"branchValue \" a:term:max : term => `(match $a:term with | Nat.succ n => n | Nat.zero => n)\n\
         theorem local_branch : (branchValue (8 : Nat)) = 7 := rfl\n\
         theorem global_branch : (branchValue (0 : Nat)) = 41 := rfl\n\
         macro \"nestedBind \" a:term:max : term => `(match $a:term with | Nat.zero => n | Nat.succ n => Nat.add (match n with | Nat.zero => 1 | Nat.succ n => n) n)\n\
         theorem nested : (nestedBind (8 : Nat)) = 13 := rfl\n\
         theorem outer (n : Nat) : (branchValue (0 : Nat)) = 41 := rfl\n",
        4,
    );
    assert!(check("notation:max \"escape \" a:max => (match a with | Nat.zero => 0 | Nat.succ fresh => fresh, fresh)\n").is_err());
}

#[test]
fn quoted_grouped_and_anonymous_constructor_patterns_bind_consistently() {
    accepted(
        "inductive Choice where | left : Nat → Choice | right : Nat → Choice\n\
         macro \"payload \" a:term:max : term => `(match $a:term with | .left n | .right n => n)\n\
         theorem left : (payload (Choice.left 4)) = 4 := rfl\n\
         theorem right : (payload (Choice.right 7)) = 7 := rfl\n\
         structure Pair where\n  first : Nat\n  second : Nat\n\
         macro \"sumPair \" a:term:max : term => `(match $a:term with | ⟨n, m⟩ => Nat.add n m)\n\
         theorem pair : (sumPair (Pair.mk 4 5)) = 9 := rfl\n",
        3,
    );
    for source in [
        "macro \"bad \" a:term:max : term => `(match $a:term with | .left n | .right m => n)",
        "macro \"bad \" a:term:max : term => `(match $a:term with | ⟨n, n⟩ => n)",
        "macro \"bad \" a:term:max : term => `(match $a:term with | Nat.succ invalid.name => 0)",
        "macro \"bad \" a:term:max p:term:max : term => `(match $a:term with | $p => 0)",
    ] {
        assert!(
            check(source).is_err(),
            "unsupported or inconsistent binding: {source}"
        );
    }
}

#[test]
fn imported_match_macros_compile_and_execute_with_their_definition_site_world() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let library_name = Name::from_components(["Library"]);
    let main_name = Name::from_components(["Main"]);
    let library = "namespace A\ndef fallback : Nat := 41\nmacro \"valueOf \" input:term:max : term => `(match $input:term with | Nat.zero => fallback | Nat.succ n => Nat.add n 1)\nend A\n";
    let main = "import Library\ndef fallback : Nat := 99\ndef choose (n : Nat) : Nat := valueOf n\ndef answer : Nat := Nat.add (choose 0) (choose 1)\n";
    let checked = base
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &main_name,
                    source: main.as_bytes(),
                },
                SourceModuleInput {
                    name: &library_name,
                    source: library.as_bytes(),
                },
            ],
            &main_name,
            &options,
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.module_order, [library_name, main_name]);
    let execution = checked
        .checked
        .engine
        .execute_source_definitions(
            &[b"def run : Nat := answer"],
            &options,
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(returned) = &execution.executions[0].exit else {
        panic!("native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("42")
    );
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn conditional_templates_keep_pattern_fields_local_to_the_success_term() {
    accepted(
        r#"
def value : Nat := 7
macro "patternValue " arg:term:max extra:term:max : term => `(if let Nat.succ value := $arg then Nat.add value $extra else value)
def answer (value : Nat) : Nat := patternValue (Nat.succ 1) value
notation "headOrGlobal " arg:max => if let Nat.succ value := arg then value else value
theorem answer_value : answer 41 = 42 := rfl
theorem yes_value : (headOrGlobal (3 : Nat)) = 2 := rfl
theorem no_value : (headOrGlobal (0 : Nat)) = 7 := rfl
"#,
        3,
    );
}

#[test]
fn conditional_templates_keep_evidence_out_of_the_predicate_and_siblings() {
    accepted(
        r#"
def h : Nat := 7
macro "proofValue " arg:term:max : term => `(if h : $arg = 0 then (fun (p : $arg = 0) => 1) h else (fun (p : Not ($arg = 0)) => 2) h)
def zero : Nat := proofValue (0 : Nat)
def one : Nat := proofValue (1 : Nat)
notation "scopeValue" => (if h : h = 7 then 1 else 2)
theorem zero_value : zero = 1 := rfl
theorem one_value : one = 2 := rfl
theorem scope_value : scopeValue = 1 := rfl
"#,
        3,
    );
}

#[test]
fn conditional_templates_precheck_free_names_without_leaking_pattern_binders() {
    for source in [
        "notation \"leaky \" arg:max => if let Nat.succ fresh := arg then fresh else fresh",
        "notation \"badInitializer\" => if let Nat.succ fresh := fresh then fresh else 0",
        "notation \"badPredicate\" => if h : h = 0 then 1 else 2",
        "notation \"leakySibling\" => (if let Nat.succ fresh := 1 then fresh else 0, fresh)",
    ] {
        assert!(
            matches!(
                check(source),
                Err(SourceCheckError::Command { command: 0, .. })
            ),
            "{source}"
        );
    }
    accepted(
        r#"
macro "evidenceCapture " arg:term:max extra:term:max : term => `(if h : $arg = 0 then $extra else 2)
def keep (h : Nat) : Nat := evidenceCapture (0 : Nat) h
theorem kept : keep 42 = 42 := rfl
"#,
        1,
    );
}

#[test]
fn conditional_templates_execute_both_paths_and_cannot_make_false_proofs() {
    let source = r#"
def value : Nat := 7
macro "chooseValue " arg:term:max : term => `(if let Nat.succ value := $arg then value else value)
macro "chooseProof " arg:term:max : term => `(if h : $arg = 0 then (fun (proof : $arg = 0) => 42) h else 7)
#eval chooseValue (43 : Nat)
#eval chooseValue (0 : Nat)
#eval chooseProof (0 : Nat)
#eval chooseProof (1 : Nat)
"#;
    let result = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    // The command stream executes `def value` as well as the four queries.
    assert_eq!(result.batch.executions.len(), 5);
    for (execution, expected) in result
        .batch
        .executions
        .iter()
        .zip(["7", "42", "7", "42", "7"])
    {
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("native return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
            Some(expected)
        );
    }
    let bad = r#"macro "falseBranch " arg:term:max : term => `(if h : $arg = 0 then (h : False) else True.intro)"#;
    accepted(bad, 0);
    for declaration in [
        "theorem bad : True := falseBranch (1 : Nat)",
        "theorem bad : False := falseBranch (0 : Nat)",
    ] {
        let source = format!("{bad}\n{declaration}");
        let error = check(&source).unwrap_err();
        let SourceCheckError::Command { command, error, .. } = error else {
            panic!("expected a command elaboration refusal: {source}\n{error:?}");
        };
        assert_eq!(command, 1, "the use, not registration, must fail: {source}");
        assert!(
            matches!(
                error.as_ref(),
                fln::EngineExecutionError::Frontend(fln::DefinitionFrontendError::Elaborate(_))
            ),
            "expected elaboration, not a parser refusal: {source}\n{error:?}"
        );
    }
}
