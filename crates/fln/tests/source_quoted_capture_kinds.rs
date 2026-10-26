//! Explicit quotation capture kinds choose clauses, not just capture names.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) -> Result<usize, String> {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission),
        )
        .map_err(|error| format!("{error:?}"))
        .map(|result| result.into_complete().unwrap().theorems)
}

#[test]
fn quotation_section_capture_cannot_fall_back_to_a_shadowed_global() {
    for body in ["x", "Nat.add x 1"] {
        let source = format!(
            "def x : Nat := 1\nsection\nvariable (x : Nat)\nnotation \"capturedValue!\" => {body}\nend\ntheorem escaped : capturedValue! = 1 := rfl\n"
        );
        let error = check(&source).expect_err("section capture must not become global x");
        assert!(
            error.contains("quotation capture of a section variable"),
            "{error}"
        );
    }
    // The refusal is about a captured lexical identity, not the presence of a
    // section or an unrelated variable. Explicit root qualification is global.
    for variables in ["variable (y : Nat)", "variable (x : Nat)"] {
        let source = format!(
            "def x : Nat := 1\nsection\n{variables}\nnotation \"globalValue!\" => _root_.x\nend\ntheorem globalMeaning : globalValue! = 1 := rfl\n"
        );
        assert_eq!(check(&source).unwrap(), 1);
    }
}

#[test]
fn numeric_captures_do_not_match_identifiers_or_parenthesized_terms() {
    let source = r#"
syntax "numeric! " term:max : term
macro_rules
  | `(numeric! $x:num) => `((10 : Nat))
  | `(numeric! $_) => `((20 : Nat))
theorem a : numeric! 4 = (10 : Nat) := rfl
theorem b : numeric! Nat.zero = (20 : Nat) := rfl
theorem c : numeric! (4) = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("numeric! Nat.zero = (20", "numeric! Nat.zero = (10")).is_err());
}

#[test]
fn identifier_captures_do_not_match_numeric_or_string_literals() {
    let source = r#"
syntax "identifier! " term:max : term
macro_rules
  | `(identifier! $x:ident) => `((10 : Nat))
  | `(identifier! $_) => `((20 : Nat))
theorem a : identifier! Nat.zero = (10 : Nat) := rfl
theorem b : identifier! 4 = (20 : Nat) := rfl
theorem c : identifier! "value" = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("identifier! 4 = (20", "identifier! 4 = (10")).is_err());
}

#[test]
fn string_captures_do_not_match_identifiers_or_numeric_literals() {
    let source = r#"
syntax "stringKind! " term:max : term
macro_rules
  | `(stringKind! $x:str) => `((10 : Nat))
  | `(stringKind! $_) => `((20 : Nat))
theorem a : stringKind! "value" = (10 : Nat) := rfl
theorem b : stringKind! Nat.zero = (20 : Nat) := rfl
theorem c : stringKind! 4 = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("stringKind! 4 = (20", "stringKind! 4 = (10")).is_err());
}

#[test]
fn anonymous_annotated_captures_still_check_their_kind() {
    let source = r#"
syntax "wildKind! " term:max : term
macro_rules
  | `(wildKind! $_:num) => `((10 : Nat))
  | `(wildKind! $_:ident) => `((20 : Nat))
  | `(wildKind! $_) => `((30 : Nat))
theorem a : wildKind! 4 = (10 : Nat) := rfl
theorem b : wildKind! Nat.zero = (20 : Nat) := rfl
theorem c : wildKind! (4) = (30 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
}

#[test]
fn pseudo_term_annotations_remain_unconditional_captures() {
    let source = r#"
syntax "anyTerm! " term:max : term
macro_rules | `(anyTerm! $x:term) => `((10 : Nat))
theorem a : anyTerm! 4 = (10 : Nat) := rfl
theorem b : anyTerm! Nat.zero = (10 : Nat) := rfl
theorem c : anyTerm! "value" = (10 : Nat) := rfl
theorem d : anyTerm! (Nat.add 2 3) = (10 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 4);
}

#[test]
fn nested_capture_kinds_guard_the_exact_child_before_binding() {
    let source = r#"
syntax "nestedKind! " term:max : term
macro_rules
  | `(nestedKind! (Nat.add $x:num $y)) => `($x)
  | `(nestedKind! $_) => `((20 : Nat))
theorem a : nestedKind! (Nat.add 4 5) = (4 : Nat) := rfl
theorem b : nestedKind! (Nat.add Nat.zero 5) = (20 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(
        check(&source.replace(
            "nestedKind! (Nat.add Nat.zero 5) = (20",
            "nestedKind! (Nat.add Nat.zero 5) = (0"
        ))
        .is_err()
    );
}

#[test]
fn a_kind_mismatch_without_a_fallback_refuses_instead_of_expanding() {
    let source = r#"
syntax "onlyNumber! " term:max : term
macro_rules | `(onlyNumber! $x:num) => `((10 : Nat))
theorem a : onlyNumber! 4 = (10 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("onlyNumber! 4 =", "onlyNumber! Nat.zero =")).is_err());
}

#[test]
fn imported_and_replayed_rules_keep_explicit_capture_kind_guards() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let source_limits = SourceCheckLimits::new(admission);
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let library = Name::from_components(["Lib"]);
    let main = Name::from_components(["Main"]);
    let result = engine
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: br#"
syntax "fromModule! " term:max : term
macro_rules
  | `(fromModule! $x:num) => `((10 : Nat))
  | `(fromModule! $_) => `((20 : Nat))
"#,
                },
                SourceModuleInput {
                    name: &main,
                    source: b"import Lib\ntheorem t : fromModule! Nat.zero = (20 : Nat) := rfl",
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(source_limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let resumed = result.checked.engine;
    assert_eq!(
        resumed
            .check_source_files(
                &[b"theorem t2 : fromModule! 4 = (10 : Nat) := rfl\ntheorem t3 : fromModule! Nat.zero = (20 : Nat) := rfl"],
                &KVMap::new(),
                source_limits,
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        2
    );
    assert!(
        resumed
            .check_source_files(
                &[b"theorem wrong : fromModule! Nat.zero = (10 : Nat) := rfl"],
                &KVMap::new(),
                source_limits,
            )
            .is_err()
    );
}

#[test]
fn a_rule_over_an_atom_kind_expands_the_whole_literal() {
    for registration in [
        "macro_rules (kind := num)\n  | `($n:num) => `(\"number\")\n",
        "macro_rules\n  | `($n:num) => `(\"number\")\n",
        "macro_rules (kind := num)\n  | n => `(\"number\")\n",
    ] {
        let source = format!("{registration}theorem t : (2 : String) = \"number\" := rfl\n");
        assert_eq!(check(&source).unwrap(), 1, "{registration}");
        assert!(check(&source.replace("= \"number\"", "= \"wrong\"")).is_err());
    }
    assert_eq!(check("theorem t : 2 = (2 : Nat) := rfl\n").unwrap(), 1);
}

#[test]
fn atom_clauses_keep_order_and_fall_back_to_the_builtin_elaborator() {
    let source = r#"
macro_rules
  | `(num| 2) => `("two")
  | `(num| 4) => `("four")
theorem first : (2 : String) = "two" := rfl
theorem builtin : (3 : Nat) = 3 := rfl
macro_rules | `(num| 2) => `("newest")
theorem newer : (2 : String) = "newest" := rfl
section
local macro_rules
  | `(num| 2) => `("first clause")
  | `($_:num) => `("fallback clause")
theorem overlappingFirst : (2 : String) = "first clause" := rfl
theorem overlappingFallback : (5 : String) = "fallback clause" := rfl
end
macro_rules | `(str| "marked") => `(7)
theorem strings : ("marked" : Nat) = 7 := rfl
def untouched : String := "not marked"
"#;
    assert_eq!(check(source).unwrap(), 6);
    assert!(check(&source.replace("= \"newest\"", "= \"two\"")).is_err());
}

#[test]
fn identifier_rules_preserve_binder_declaration_and_field_names() {
    let source = r#"
macro_rules | `(magic) => `(7)
def magic : Nat := 9
def binder (magic : Nat) : Nat := 3
theorem expandedIdentifier : (magic : Nat) = 7 := rfl
theorem localValue : (let magic : Nat := 9; magic) = 7 := rfl
theorem parameter : (fun (magic : Nat) => magic) 9 = 7 := rfl
structure Box where
  magic : Nat
def boxed : Box := { magic := 9 }
theorem fieldLabel : boxed.magic = 9 := rfl
def punned : Box := { magic }
theorem pun : punned.magic = 7 := rfl
theorem existsBinder : (∃ magic : Nat, magic = 7) := ⟨0, rfl⟩
theorem forallBinder : ∀ magic : Nat, magic = 7 := by
  intro magic
  rfl
"#;
    assert_eq!(check(source).unwrap(), 7);
}

#[test]
fn atomic_rules_restore_lexical_scope_and_keep_global_updates() {
    let source = r#"
macro_rules | `(num| 2) => `("global")
section
local macro_rules | `(num| 2) => `("local")
theorem inside : (2 : String) = "local" := rfl
macro_rules | `(num| 3) => `("survives")
end
theorem outside : (2 : String) = "global" := rfl
theorem globalUpdate : (3 : String) = "survives" := rfl
namespace Atomic
scoped macro_rules | `(num| 4) => `("scoped")
theorem active : (4 : String) = "scoped" := rfl
end Atomic
theorem inactive : (4 : Nat) = 4 := rfl
open scoped Atomic
theorem reactivated : (4 : String) = "scoped" := rfl
"#;
    assert_eq!(check(source).unwrap(), 6);
}

#[test]
fn numeral_macros_do_not_rewrite_universes_or_quotation_data() {
    let source = r#"
syntax "quotedNumber!" : term
macro_rules | `(quotedNumber!) => `(3)
macro_rules | `($n:num) => `("number")
def universeValue : Type 1 := Type 0
theorem translated : (2 : String) = "number" := rfl
theorem nestedQuotation : (quotedNumber! : String) = "number" := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
}

#[test]
fn atomic_templates_keep_definition_site_globals_and_hygienic_binders() {
    let source = r#"
def amount : Nat := 42
macro_rules | `(str| "value") => `(amount)
macro_rules | `(str| "function") => `(fun amount : Nat => amount)
namespace Client
def amount : Nat := 99
theorem original : ("value" : Nat) = 42 := rfl
theorem underBinder : (fun amount : Nat => ("value" : Nat)) 7 = 42 := rfl
theorem bound : ("function" : Nat -> Nat) 7 = 7 := rfl
end Client
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("(\"value\" : Nat) = 42", "(\"value\" : Nat) = 99")).is_err());
}

#[test]
fn identifier_patterns_match_original_template_names_before_global_resolution() {
    let source = r#"
def magic : Nat := 9
syntax "quotedMagic!" : term
macro_rules | `(quotedMagic!) => `(magic)
syntax "qualifiedMagic!" : term
macro_rules | `(qualifiedMagic!) => `(_root_.magic)
syntax "captureMagic! " term:max : term
macro_rules | `(captureMagic! $value) => `($value)
syntax "nestedMagic!" : term
macro_rules | `(nestedMagic!) => `(captureMagic! magic)
namespace Definition
def magic : Nat := 11
syntax "namespacedMagic!" : term
macro_rules | `(namespacedMagic!) => `(magic)
end Definition
macro_rules | `(magic) => `(7)
theorem direct : (magic : Nat) = 7 := rfl
theorem quoted : (quotedMagic! : Nat) = 7 := rfl
theorem captured : (nestedMagic! : Nat) = 7 := rfl
theorem namespaceSpelling : (namespacedMagic! : Nat) = 7 := rfl
namespace Client
def magic : Nat := 99
theorem shadowed : (quotedMagic! : Nat) = 7 := rfl
theorem qualified : (qualifiedMagic! : Nat) = 9 := rfl
end Client
"#;
    assert_eq!(check(source).unwrap(), 6);
    assert!(
        check(&source.replace("(quotedMagic! : Nat) = 7", "(quotedMagic! : Nat) = 9")).is_err()
    );
    assert!(
        check(&source.replace(
            "(qualifiedMagic! : Nat) = 9",
            "(qualifiedMagic! : Nat) = 99"
        ))
        .is_err()
    );
}

#[test]
fn literal_macros_leave_tactic_data_in_its_original_kind() {
    let source = r#"
macro_rules | `(str| "diagnostic") => `(7)
theorem traced : True := by
  trace "diagnostic"
  exact True.intro
macro_rules | `($n:num) => `("number")
theorem congruent : "number" = "number" := by
  congr 1
"#;
    assert_eq!(check(source).unwrap(), 2);
}

#[test]
fn identifier_application_heads_are_resolved_before_term_macros() {
    let source = r#"
def functionMacroTarget (x : Nat) := x
macro_rules | `(functionMacroTarget) => `(fun _ : Nat => 7)
theorem directHead : functionMacroTarget 3 = 3 := rfl
theorem parenthesizedHead : (functionMacroTarget) 3 = 7 := rfl
theorem explicitHead : @functionMacroTarget 3 = 3 := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(
        check(&source.replace("functionMacroTarget 3 = 3", "functionMacroTarget 3 = 7")).is_err()
    );
}

#[test]
fn a_check_of_an_existing_global_retains_the_signature_fast_path() {
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20));
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let result = engine
        .execute_source_commands_with_checks(
            br#"
def queryMacroTarget : Nat := 9
macro_rules
  | `(queryMacroTarget) => `(7)
  | `(undeclaredMacroTarget) => `(7)
#check queryMacroTarget
#check (queryMacroTarget)
#check undeclaredMacroTarget
"#,
            &KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.checks.len(), 3);
    let value = |index: usize| match &result.checks[index].declaration {
        fln::Declaration::Defn(definition) => &definition.value,
        _ => panic!("a checked query must have a definition candidate"),
    };
    assert!(matches!(
        value(0).node(),
        fln::ExprNode::Const { name, .. }
            if *name == fln::Name::from_components(["queryMacroTarget"])
    ));
    assert_eq!(value(1), value(2));
    assert_ne!(value(0), value(1));
}

#[test]
fn unsupported_atomic_registrations_do_not_fall_through_to_old_rules() {
    for registration in [
        "macro_rules | `(num| 2) => do pure `(\"unsupported\")",
        "local macro_rules | `(num| 2) => Macro.throwUnsupported",
        "macro_rules | `(num| 2) => `(notDeclaredHere)",
        "macro_rules (kind := ident) | `(num| 2) => `(\"wrong kind\")",
    ] {
        let source = format!(
            "macro_rules | `(num| 2) => `(\"old\")\n{registration}\ntheorem stale : (2 : String) = \"old\" := rfl"
        );
        assert!(check(&source).is_err(), "{registration}");
    }
    for source in [
        "macro_rules | `($n:num) => `(\"number\")\nsyntax \"late!\" : term",
        "macro_rules | `($i:ident) => `(7)\nmacro_rules | `($n:num) => `(\"number\")",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}

#[test]
fn recursive_atomic_expansion_and_pseudo_category_registration_refuse() {
    for source in [
        "macro_rules | `($n:num) => `($n)\ndef loop : Nat := 2",
        "macro_rules | `($x) => `(7)\ndef unchanged : Nat := 2",
        "macro_rules | `($x:term) => `(7)\ndef unchanged : Nat := 2",
    ] {
        assert!(check(source).is_err(), "{source}");
    }
}

#[test]
fn atomic_rules_export_owned_clauses_and_replay_the_native_module_journal() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let limits = SourceCheckLimits::new(admission);
    let engine = Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let library = Name::from_components(["AtomLibrary"]);
    let main = Name::from_components(["AtomConsumer"]);
    let built = engine
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &library,
                    source: br#"
macro_rules | `(num| 2) => `("library")
local macro_rules | `(num| 2) => `("not exported")
namespace Atoms
scoped macro_rules | `(num| 4) => `("scoped")
end Atoms
"#,
                },
                SourceModuleInput {
                    name: &main,
                    source: br#"
import AtomLibrary
theorem exported : (2 : String) = "library" := rfl
theorem dormant : (4 : Nat) = 4 := rfl
open scoped Atoms
theorem activated : (4 : String) = "scoped" := rfl
macro_rules | `(num| 2) => `("consumer")
theorem newer : (2 : String) = "consumer" := rfl
"#,
                },
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let resumed = built.checked.engine;
    let root = resumed.logical_root(&KVMap::new());
    let checked = resumed
        .check_source_files(
            &[br#"
theorem replayed : (2 : String) = "consumer" := rfl
theorem inactiveAgain : (4 : Nat) = 4 := rfl
open scoped Atoms
theorem scopedAgain : (4 : String) = "scoped" := rfl
"#],
            &KVMap::new(),
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.theorems, 3);
    assert!(
        resumed
            .check_source_files(
                &[br#"theorem staleMeaning : (2 : String) = "library" := rfl"#],
                &KVMap::new(),
                limits,
            )
            .is_err()
    );
    assert_eq!(resumed.logical_root(&KVMap::new()), root);
}
