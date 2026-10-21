//! Native whole-sequence macros compose without inspecting or evaluating elements.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(source: &str) -> Result<fln::SourceFileCheck, String> {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map_err(|e| format!("{e:?}"))
}

const MANY: &str = r#"
syntax "consumeSeq!" "[" num* "]" : term
macro_rules
  | `(consumeSeq![4 2]) => `((42 : Nat))
  | `(consumeSeq![]) => `((0 : Nat))
  | `(consumeSeq![$xs*]) => `((7 : Nat))
syntax "forwardSeq!" "[" num* "]" : term
macro_rules | `(forwardSeq![$xs*]) => `(consumeSeq![$xs*])
"#;

#[test]
fn repeated_arguments_forward_without_scalar_reinterpretation() {
    let source = format!(
        "{MANY}\ntheorem exactItems : forwardSeq![4 2] = (42 : Nat) := rfl\n\
         theorem emptyItems : forwardSeq![] = (0 : Nat) := rfl\n\
         theorem otherItems : forwardSeq![4 3] = (7 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap().theorems, 3);
    assert!(check(&source.replace("= (42 : Nat)", "= (7 : Nat)")).is_err());
}

#[test]
fn separated_sequences_keep_values_and_caller_names() {
    let source = r#"
syntax "readSeq!" "[" term,* "]" : term
macro_rules
  | `(readSeq![$x, $y]) => `(Nat.add $x $y)
  | `(readSeq![$xs,*]) => `((0 : Nat))
syntax "forwardSep!" "[" term,* "]" : term
macro_rules | `(forwardSep![$xs,*]) => `(readSeq![$xs,*])
theorem caller (n : Nat) : forwardSep![n, 2] = Nat.add n 2 := rfl
theorem empty : forwardSep![] = (0 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap().theorems, 2);
    assert!(check(&format!("{source}\ndef bad : Nat := forwardSep![true, 2]")).is_err());
}

#[test]
fn optional_captures_preserve_absence_and_presence() {
    let source = r#"
syntax "readOpt!" "[" (num)? "]" : term
macro_rules
  | `(readOpt![]) => `((0 : Nat))
  | `(readOpt![$n:num]) => `($n)
syntax "forwardOpt!" "[" (num)? "]" : term
macro_rules | `(forwardOpt![$(xs)?]) => `(readOpt![$(xs)?])
theorem absent : forwardOpt![] = (0 : Nat) := rfl
theorem present : forwardOpt![42] = (42 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap().theorems, 2);
    assert!(check(&source.replace("= (42 : Nat)", "= (0 : Nat)")).is_err());
}

#[test]
fn forwarding_reaches_native_execution_and_refusals_leave_no_state() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[format!("{MANY}\ndef bad : False := forwardSeq![4 2]").as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    let result = base
        .execute_source_commands_with_checks(
            format!("{MANY}\n#eval forwardSeq![4 2]").as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
        panic!("expected native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}
