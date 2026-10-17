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

#[test]
fn control_match_preserves_branch_scopes_and_spliced_arguments() {
    checked(
        r#"
def value : Nat := 90
macro "withCase " arg:term:max extra:term:max : term => `(do { match $arg:term with | Nat.zero => return value | Nat.succ value => return Nat.add value $extra })
def select (value : Nat) : Id Nat := withCase (Nat.succ 1) value
def zero : Id Nat := withCase (0 : Nat) (3 : Nat)
theorem selected : select 41 = 42 := rfl
theorem fallback : zero = 90 := rfl
"#,
        2,
    );
}

#[test]
fn control_if_let_binds_success_only_in_pure_and_monadic_conditions() {
    checked(
        r#"
inductive Choice where | no : Choice | yes : Nat -> Choice
def value : Nat := 7
macro "withTest " arg:term:max extra:term:max : term => `(do { if let Choice.yes value := $arg then return Nat.add value $extra else return value })
macro "withAction " arg:term:max extra:term:max : term => `(do { if let Choice.yes value ← ($arg : Id Choice) then return Nat.add value $extra else return value })
def pureResult (value : Nat) : Id Nat := withTest (Choice.yes 1) value
def actionResult (value : Nat) : Id Nat := withAction (Choice.yes 1) value
def pureFallback : Id Nat := withTest Choice.no (0 : Nat)
def actionFallback : Id Nat := withAction Choice.no (0 : Nat)
theorem pure_value : pureResult 41 = 42 := rfl
theorem action_value : actionResult 41 = 42 := rfl
theorem pure_fallback : pureFallback = 7 := rfl
theorem action_fallback : actionFallback = 7 := rfl
"#,
        4,
    );
}

#[test]
fn control_named_conditions_keep_positive_and_negative_evidence_local() {
    checked(
        r#"
def h : Nat := 99
macro "withEvidence " arg:term:max : term => `(do { if h : $arg = 0 then have same : $arg = 0 := h; return 1 else have different : Not ($arg = 0) := h; return 2 })
def zero : Id Nat := withEvidence (0 : Nat)
def one : Id Nat := withEvidence (1 : Nat)
theorem zero_value : zero = 1 := rfl
theorem one_value : one = 2 := rfl
"#,
        2,
    );
}

#[test]
fn control_else_if_headers_see_failure_evidence_but_not_failed_patterns() {
    checked(
        r#"
def value : Nat := 7
macro "chain " arg:term:max : term => `(do { if h : $arg = 0 then return 10 else if let Nat.succ value := $arg then have notZero : Not ($arg = 0) := h; return value else return value })
macro "fallThrough " arg:term:max : term => `(do { if let Nat.succ value := $arg then return value else if value = 7 then return value else return 99 })
def a : Id Nat := chain (0 : Nat)
def b : Id Nat := chain (2 : Nat)
def c : Id Nat := fallThrough (0 : Nat)
theorem av : a = 10 := rfl
theorem bv : b = 1 := rfl
theorem cv : c = 7 := rfl
"#,
        3,
    );
}

#[test]
fn control_nested_branches_restore_outer_bindings_and_continuation_scope() {
    checked(
        r#"
def value : Nat := 7
def h : Nat := 99
macro "nestedControl " arg:term:max : term => `(do { let value : Nat := $arg; if let Nat.succ value := value then match value with | Nat.zero => return value | Nat.succ value => return Nat.add value 1 else return value })
macro "afterBranch " : term => `(do
  if h : True then
    (Pure.pure PUnit.unit : Id PUnit)
  else
    (Pure.pure PUnit.unit : Id PUnit)
  return h)
def a : Id Nat := nestedControl (3 : Nat)
def b : Id Nat := nestedControl (0 : Nat)
def c : Id Nat := afterBranch
theorem av : a = 2 := rfl
theorem bv : b = 0 := rfl
theorem cv : c = 99 := rfl
"#,
        3,
    );
}

#[test]
fn control_imported_branch_macros_execute_without_capturing_consumer_names() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let lib = fln::Name::from_components(["Library"]);
    let main = fln::Name::from_components(["Main"]);
    let library = r#"namespace Lib
 def fallback : Nat := 7
 macro "branchRun " arg:term:max extra:term:max : term => `(do { if let Nat.succ value := $arg then match value with | Nat.zero => return $extra | Nat.succ value => return Nat.add value $extra else return fallback })
end Lib
"#;
    let consumer = r#"import Library
 def fallback : Nat := 99
 def choose (value : Nat) : Id Nat := branchRun (Nat.succ 2) value
 def result : Id Nat := choose 41
 theorem result_value : result = 42 := rfl
"#;
    let imported = base
        .check_source_modules(
            &[
                fln::SourceModuleInput {
                    name: &main,
                    source: consumer.as_bytes(),
                },
                fln::SourceModuleInput {
                    name: &lib,
                    source: library.as_bytes(),
                },
            ],
            &main,
            &options,
            fln::source_check::modules::SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.checked.theorems, 1);
    let execution = imported
        .checked
        .engine
        .execute_source_commands_with_checks(
            b"#eval result\n#eval (branchRun (0 : Nat) (1 : Nat) : Id Nat)",
            &options,
            fln::EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(execution.batch.executions.len(), 2);
    for (execution, expected) in execution.batch.executions.iter().zip(["42", "7"]) {
        let fln::VmExit::Returned(returned) = &execution.exit else {
            panic!("native return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
            Some(expected)
        );
    }
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn control_bad_branch_uses_are_rejected_atomically_and_the_engine_recovers() {
    let base = engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for declaration in [
        r#"macro "bad " arg:term:max : term => `(do { if let Nat.succ fresh := $arg then return fresh else return fresh })"#,
        r#"macro "bad " arg:term:max : term => `(do { match $arg:term with | Nat.zero => return 42 })"#,
        r#"macro "bad " arg:term:max : term => `(do { if h : $arg = 0 then have wrong : Not ($arg = 0) := h; return 1 else return 2 })"#,
        r#"macro "bad " arg:term:max : term => `(do { if $arg = 0 then return 1 else return "wrong" })"#,
    ] {
        // Registration is not proof that a macro's uses are valid. Prove the
        // refusal occurs at a use, including in a statically unselected arm.
        base.check_source_files(&[declaration.as_bytes()], &options, limits())
            .unwrap_or_else(|e| panic!("unused macro: {declaration}\n{e:?}"))
            .into_complete()
            .unwrap();
        let source = format!("{declaration}\ndef rejectedValue (n : Nat) : Id Nat := bad n");
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        let fln::SourceCheckError::Command { command, error, .. } = error else {
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
        assert_eq!(base.logical_root(&options), before);
    }
    let good = b"macro \"good \" arg:term:max : term => `(do { match $arg:term with | Nat.zero => return 0 | Nat.succ n => return Nat.add n 1 })\ndef ok : Id Nat := good (42 : Nat)\ntheorem good_value : ok = 42 := rfl";
    assert_eq!(
        base.check_source_files(&[good], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        1
    );
    assert_eq!(base.logical_root(&options), before);
}

// An ordinary checked source library, not a trusted iteration or evidence stub.
fn loop_engine() -> Engine {
    engine()
        .check_source_files(
            &[br#"
inductive ForInStep (A : Type) where
  | done (value : A)
  | yield (value : A)
class ForIn (m : Type -> Type) (R : Type) (A : outParam Type) where
  forIn : {B : Type} -> R -> B -> (A -> B -> m (ForInStep B)) -> m B
def stepValue {A : Type} (step : ForInStep A) : A :=
  match step with
  | ForInStep.done value => value
  | ForInStep.yield value => value
def boolFor {B : Type} (xs : Bool) (b : B) (f : Nat -> B -> Id (ForInStep B)) : Id B :=
  if xs then stepValue (f 42 b) else b
instance idBoolFor : ForIn Id Bool Nat := { forIn := fun xs b f => boolFor xs b f }
class Membership (A R : Type) where
  mem : R -> A -> Prop
class ForIn' (m : Type -> Type) (R : Type) (A : outParam Type) (d : outParam (Membership A R)) where
  forIn' : {B : Type} -> (xs : R) -> B -> ((a : A) -> @Membership.mem A R d xs a -> B -> m (ForInStep B)) -> m B
instance memberNat : Membership Nat Nat := { mem := fun xs a => a = xs }
def natFor {B : Type} (xs : Nat) (b : B) (f : (a : Nat) -> a = xs -> B -> Id (ForInStep B)) : Id B :=
  stepValue (f xs (by rfl) b)
instance natIteration : ForIn' Id Nat Nat memberNat := { forIn' := fun xs b f => natFor xs b f }
"#],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn loop_values(base: &Engine, source: &str, expected: &[&str]) {
    let result = base
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let evaluations: Vec<_> = result
        .outputs
        .iter()
        .filter_map(|output| match output {
            fln::SourceCommandOutput::Evaluation {
                execution_index, ..
            } => Some(&result.batch.executions[*execution_index]),
            _ => None,
        })
        .collect();
    assert_eq!(evaluations.len(), expected.len());
    for (execution, expected) in evaluations.iter().zip(expected) {
        let fln::VmExit::Returned(returned) = &execution.exit else {
            panic!("native loop must return: {:?}", execution.exit);
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
            Some(*expected)
        );
    }
}

#[test]
fn loop_control_ordinary_iteration_and_real_membership_proofs_execute() {
    loop_values(
        &loop_engine(),
        r#"
def ordinary : Id Nat := do { for x in true do { return x }; return 0 }
def witnessed (n : Nat) : Id Nat := do { for h : x in n do { have eq : x = n := h; return x }; return n }
theorem ordinary_value : ordinary = 42 := rfl
#eval ordinary
#eval witnessed 17
"#,
        &["42", "17"],
    );
}

#[test]
fn loop_quotations_resolve_headers_before_binders_and_preserve_caller_values() {
    loop_values(
        &loop_engine(),
        r#"
namespace Library
def values : Bool := true
def element : Type := Nat
macro "loopFirst " input:term:max : term => `(do { for (element : element) in values do { return Nat.add element $input }; return $input })
macro "loopSelf " : term => `(do { for values in values do { return values }; return 7 })
end Library
namespace Caller
def values : Bool := false
def element : Type := Bool
def result (element : Nat) : Id Nat := loopFirst element
def sameName : Id Nat := loopSelf
theorem result_value : result 41 = 83 := rfl
theorem same_value : sameName = 42 := rfl
#eval result 41
#eval sameName
end Caller
"#,
        &["83", "42"],
    );
}

#[test]
fn loop_quotations_restore_nested_scopes_and_ignore_wildcards() {
    loop_values(
        &loop_engine(),
        r#"
def value : Nat := 7
macro "nestedLoop " input:term:max : term => `(do { let value : Nat := $input; for value in true do { for value in false do { return 100 }; return value }; return value })
macro "afterLoop " : term => `(do { for value in true do { let value : Nat := 99; (Pure.pure PUnit.unit : Id PUnit) }; return value })
macro "emptyLoop " input:term:max : term => `(do { for _ in false do { return 99 }; return $input })
macro "loopTerm " : term => `(for value in true do { (Pure.pure PUnit.unit : Id PUnit) })
def a : Id Nat := nestedLoop (9 : Nat)
def b : Id Nat := afterLoop
def c : Id Nat := emptyLoop (17 : Nat)
def d : Id PUnit := loopTerm
theorem av : a = 42 := rfl
theorem bv : b = 7 := rfl
theorem cv : c = 17 := rfl
theorem dv : d = PUnit.unit := rfl
#eval a
#eval b
#eval c
"#,
        &["42", "7", "17"],
    );
}

#[test]
fn loop_quotations_bind_only_real_membership_evidence_without_capture() {
    loop_values(
        &loop_engine(),
        r#"
def evidence : Nat := 9
macro "witnessLoop " input:term:max extra:term:max : term => `(do { for evidence : value in $input do { have same : value = $input := evidence; return Nat.add value $extra }; return $extra })
macro "witnessAfter " input:term:max : term => `(do { for evidence : value in $input do { have same : value = $input := evidence; (Pure.pure PUnit.unit : Id PUnit) }; return evidence })
def found (evidence : Nat) : Id Nat := witnessLoop (1 : Nat) evidence
def outer : Id Nat := witnessAfter (3 : Nat)
theorem found_value : found 41 = 42 := rfl
theorem outer_value : outer = 9 := rfl
#eval found 41
#eval outer
"#,
        &["42", "9"],
    );
}

#[test]
fn loop_quotations_reject_bad_uses_atomically_and_recover() {
    let base = loop_engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    for declaration in [
        r#"macro "badLoop " : term => `(do { for fresh in true do { (Pure.pure PUnit.unit : Id PUnit) }; return fresh })"#,
        r#"macro "badLoop " : term => `(do { for (x : Bool) in true do { return 1 }; return 2 })"#,
        r#"macro "badLoop " : term => `(do { for h : x in (1 : Nat) do { have wrong : x = 0 := h; return 1 }; return 2 })"#,
        r#"macro "badLoop " : term => `(do { for x in false do { return "wrong" }; return 2 })"#,
        r#"macro "badLoop " : term => `(do { for h : x in true do { return x }; return 2 })"#,
    ] {
        base.check_source_files(&[declaration.as_bytes()], &options, limits())
            .unwrap_or_else(|e| panic!("unused macro: {declaration}\n{e:?}"))
            .into_complete()
            .unwrap();
        let source = format!("{declaration}\ndef rejected : Id Nat := badLoop");
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        let fln::SourceCheckError::Command { command, error, .. } = error else {
            panic!("command refusal: {source}\n{error:?}");
        };
        assert_eq!(command, 1, "the use must fail: {source}");
        assert!(
            matches!(
                error.as_ref(),
                fln::EngineExecutionError::Frontend(fln::DefinitionFrontendError::Elaborate(_))
            ),
            "elaboration refusal: {source}\n{error:?}"
        );
        assert_eq!(base.logical_root(&options), before);
    }
    loop_values(
        &base,
        "macro \"goodLoop \" : term => `(do { for x in true do { return x }; return 0 })\n#eval (goodLoop : Id Nat)",
        &["42"],
    );
    assert_eq!(base.logical_root(&options), before);
}

#[test]
fn loop_quotations_import_and_execute_in_the_admitted_successor() {
    let base = loop_engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let library = fln::Name::from_components(["LoopLibrary"]);
    let consumer = fln::Name::from_components(["LoopConsumer"]);
    let lib = r#"
namespace Nat
macro "constructorNamedLoop " : term => `(do { for zero in true do { return zero }; return 0 })
end Nat
namespace Lib
def enabled : Bool := true
def fallback : Nat := 7
macro "importLoop " extra:term:max : term => `(do { for value in enabled do { return Nat.add value $extra }; return fallback })
end Lib
"#;
    let source = r#"
import LoopLibrary
def enabled : Bool := false
def fallback : Nat := 99
def fromImport (value : Nat) : Id Nat := importLoop value
def result : Id Nat := fromImport 1
theorem imported_value : result = 43 := rfl
"#;
    let imported = base
        .check_source_modules(
            &[
                fln::SourceModuleInput {
                    name: &consumer,
                    source: source.as_bytes(),
                },
                fln::SourceModuleInput {
                    name: &library,
                    source: lib.as_bytes(),
                },
            ],
            &consumer,
            &options,
            fln::source_check::modules::SourceModuleCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.checked.theorems, 1);
    loop_values(
        &imported.checked.engine,
        "#eval result\n#eval (constructorNamedLoop : Id Nat)",
        &["43", "42"],
    );
    assert_eq!(base.logical_root(&options), before);
}


#[test]
fn quoted_loop_mutable_and_monadic_reassignment_preserve_hygienic_state() {
    let base = loop_engine();
    let before = base.logical_root(&KVMap::new());
    loop_values(
        &base,
        r#"
def total : Nat := 900
macro "mutableQuoted " input:term:max : term => `(do {
  let mut total : Nat := $input
  for x in true do { total ← (Nat.add total x : Id Nat) }
  return total })
def answer (total : Nat) : Id Nat := mutableQuoted total
theorem answer_value : answer 0 = 42 := rfl
#eval answer 0
"#,
        &["42"],
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn quoted_reassignment_cannot_capture_a_callers_mutable_local() {
    let base = loop_engine();
    let options = KVMap::new();
    let before = base.logical_root(&options);
    let source = br#"
macro "stealMutable " : term => `(do { total := 99; return total })
def rejectedValue : Id Nat := do
  let mut total : Nat := 42
  let n <- stealMutable
  return n
"#;
    assert!(base.check_source_files(&[source], &options, limits()).is_err());
    assert_eq!(base.logical_root(&options), before);
    loop_values(
        &base,
        r#"
macro "retryMutable " : term => `(do {
  let mut total : Nat := 0
  for x in true do { total := total + x }
  return total })
def recovered : Id Nat := retryMutable
theorem recovery_value : recovered = 42 := rfl
#eval recovered
"#,
        &["42"],
    );
}
