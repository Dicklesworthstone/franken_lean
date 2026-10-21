//! Local quoted registrations have lexical lifetimes, not global export effects.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<usize, String> {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|r| r.theorems)
        .map_err(|e| format!("{e:?}"))
}
const BASE: &str = r#"
syntax "localValue! " num : term
macro_rules | `(localValue! $n:num) => `($n)
"#;

#[test]
fn local_quoted_clauses_expire_at_the_matching_section() {
    let source = format!(
        r#"{BASE}
section Outer
local macro_rules | `(localValue! 0) => `((10 : Nat))
theorem outer_before : localValue! 0 = (10 : Nat) := rfl
section Inner
local macro_rules | `(localValue! 0) => `((20 : Nat))
theorem inner : localValue! 0 = (20 : Nat) := rfl
end Inner
theorem outer_after : localValue! 0 = (10 : Nat) := rfl
end Outer
theorem outside : localValue! 0 = (0 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 4);
    assert!(
        check(&source.replace(
            "theorem outside : localValue! 0 = (0",
            "theorem outside : localValue! 0 = (10"
        ))
        .is_err()
    );
}

#[test]
fn global_clauses_added_inside_a_local_scope_survive_its_end() {
    let source = format!(
        r#"{BASE}
section
local macro_rules | `(localValue! 0) => `((10 : Nat))
macro_rules | `(localValue! 1) => `((31 : Nat))
theorem local_fallback : localValue! 0 = (10 : Nat) := rfl
macro_rules | `(localValue! 0) => `((42 : Nat))
theorem newer_global : localValue! 0 = (42 : Nat) := rfl
end
theorem global_zero : localValue! 0 = (42 : Nat) := rfl
theorem global_one : localValue! 1 = (31 : Nat) := rfl
theorem base_fallback : localValue! 9 = (9 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 5);
    assert!(
        check(&source.replace(
            "theorem global_zero : localValue! 0 = (42",
            "theorem global_zero : localValue! 0 = (10"
        ))
        .is_err()
    );
}

#[test]
fn local_rules_can_supply_the_only_expansion_without_exporting_it() {
    let source = r#"
syntax "localOnly!" : term
section
local macro_rules | `(localOnly!) => `((42 : Nat))
theorem inside : localOnly! = (42 : Nat) := rfl
end
theorem unrelated : (3 : Nat) = 3 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(
        check(&format!(
            "{source}\ntheorem escaped : localOnly! = (42 : Nat) := rfl\n"
        ))
        .is_err()
    );
}

#[test]
fn namespace_lifetimes_keep_definition_site_names_and_caller_captures() {
    let source = format!(
        r#"{BASE}
def answer : Nat := 2
namespace Scoped
 def answer : Nat := 40
 local macro_rules | `(localValue! $n:num) => `(Nat.add answer $n)
 theorem inside : localValue! 2 = (42 : Nat) := rfl
end Scoped
theorem outside : localValue! 2 = (2 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 2);
}

fn modules(files: &[(&str, &str)]) -> Result<Engine, String> {
    use fln::source_check::modules::SourceModuleCheckLimits;
    let names: Vec<_> = files
        .iter()
        .map(|(name, _)| fln::Name::from_components([*name]))
        .collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| fln::SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    engine()
        .check_source_modules(
            &inputs,
            &fln::Name::from_components(["Main"]),
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|r| r.checked.engine)
        .map_err(|e| format!("{e:?}"))
}
fn resumes(engine: &Engine, source: &str) -> bool {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_ok_and(|r| r.into_complete().is_ok())
}

#[test]
fn file_scope_local_rules_never_enter_module_exports_or_journal_replay() {
    let library = format!(
        r#"{BASE}
local macro_rules | `(localValue! 0) => `((42 : Nat))
theorem library_check : localValue! 0 = (42 : Nat) := rfl
"#
    );
    let main = "import Library\ntheorem imported : localValue! 0 = (0 : Nat) := rfl\n";
    let result = modules(&[("Library", &library), ("Main", main)]).unwrap();
    assert!(resumes(
        &result,
        "theorem replayed : localValue! 0 = (0 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem leaked : localValue! 0 = (42 : Nat) := rfl"
    ));
    assert!(
        modules(&[
            ("Library", &library),
            ("Main", &main.replace("(0 : Nat)", "(42 : Nat)"))
        ])
        .is_err()
    );
}

#[test]
fn downstream_local_rules_do_not_replace_inherited_fallback_exports() {
    let extension = r#"import Core
local macro_rules | `(localValue! 0) => `((10 : Nat))
macro_rules | `(localValue! 1) => `((21 : Nat))
theorem inside : localValue! 0 = (10 : Nat) := rfl
"#;
    let result = modules(&[("Core", BASE), ("Extension", extension), ("Main",
        "import Extension\ntheorem zero : localValue! 0 = (0 : Nat) := rfl\ntheorem one : localValue! 1 = (21 : Nat) := rfl")]).unwrap();
    assert!(resumes(
        &result,
        "theorem replayed : localValue! 1 = (21 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem leaked : localValue! 0 = (10 : Nat) := rfl"
    ));
}

#[test]
fn local_only_rules_on_imported_syntax_leave_no_executable_export() {
    let result = modules(&[("Syntax", "syntax \"onlyHere!\" : term"),
        ("Local", "import Syntax\nlocal macro_rules | `(onlyHere!) => `((42 : Nat))\ntheorem inside : onlyHere! = (42 : Nat) := rfl"),
        ("Main", "import Local\ntheorem ordinary : (7 : Nat) = 7 := rfl")]).unwrap();
    assert!(!resumes(
        &result,
        "theorem leaked : onlyHere! = (42 : Nat) := rfl"
    ));
    assert!(resumes(
        &result,
        "local macro_rules | `(onlyHere!) => `((8 : Nat))\ntheorem fresh : onlyHere! = (8 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem still_absent : onlyHere! = (8 : Nat) := rfl"
    ));
}

#[test]
fn local_tactic_rules_are_lexical_and_do_not_turn_bad_expansions_into_fallbacks() {
    let source = r#"
syntax "localTac!" : tactic
macro_rules | `(tactic| localTac!) => `(tactic| exact 7)
section
local macro_rules | `(tactic| localTac!) => `(tactic| exact 42)
def inside : Nat := by localTac!
end
def outside : Nat := by localTac!
theorem inside_result : inside = 42 := rfl
theorem outside_result : outside = 7 := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    let bad = format!(
        r#"{BASE}
section
local macro_rules | `(localValue! 0) => `(missingLocalDefinition)
theorem no_fallback : localValue! 0 = (0 : Nat) := rfl
end
"#
    );
    assert!(check(&bad).is_err());
    let unsupported = format!("{BASE}\nlocal macro_rules | `(localValue! 0) => do pure `(0)\n");
    assert!(check(&unsupported).is_err());
    assert_eq!(
        check(&format!(
            "{BASE}\ntheorem recovery : localValue! 0 = (0 : Nat) := rfl"
        ))
        .unwrap(),
        1
    );
}

#[test]
fn native_vm_observes_local_definitions_without_retaining_local_grammar() {
    let source = format!(
        r#"{BASE}
section
local macro_rules | `(localValue! 0) => `((42 : Nat))
def local_result : Nat := localValue! 0
end
#eval local_result
#eval localValue! 0
"#
    );
    let checked = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let results: Vec<_> = checked
        .batch
        .executions
        .iter()
        .map(|run| fln::closed_vm_value(&run.exit).unwrap())
        .collect();
    assert_eq!(
        results,
        // This API also executes the definition, before the two #eval commands.
        vec![
            Some(fln::ClosedVmValue::Scalar(42)),
            Some(fln::ClosedVmValue::Scalar(42)),
            Some(fln::ClosedVmValue::Scalar(0))
        ]
    );
}

#[test]
fn local_custom_category_transformations_preserve_inherited_grammar() {
    let source = r#"
declare_syntax_cat instruction
syntax "stop" : instruction
syntax "interpret " "[" instruction "]" : term
macro_rules | `(interpret [stop]) => `((0 : Nat))
section
local macro_rules | `(interpret [stop]) => `((42 : Nat))
theorem local_value : interpret [stop] = (42 : Nat) := rfl
end
theorem global_value : interpret [stop] = (0 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
}
