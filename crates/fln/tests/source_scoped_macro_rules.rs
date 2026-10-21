//! Scoped quoted clauses are activated by namespaces, never by import alone.
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
syntax (name := picked) "picked! " num : term
macro_rules | `(picked! $n:num) => `($n)
"#;

#[test]
fn scoped_rules_activate_and_expire_without_erasing_global_fallbacks() {
    let source = format!(
        r#"{BASE}
namespace Choice
scoped macro_rules | `(picked! 0) => `((10 : Nat))
theorem inside : picked! 0 = (10 : Nat) := rfl
end Choice
theorem outside : picked! 0 = (0 : Nat) := rfl
section
open scoped Choice
theorem opened : picked! 0 = (10 : Nat) := rfl
theorem fallback : picked! 4 = (4 : Nat) := rfl
end
theorem closed : picked! 0 = (0 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 5);
    assert!(
        check(&source.replace(
            "theorem closed : picked! 0 = (0",
            "theorem closed : picked! 0 = (10"
        ))
        .is_err()
    );
}

#[test]
fn activation_order_and_later_global_rules_determine_precedence() {
    let source = format!(
        r#"{BASE}
namespace A
scoped macro_rules | `(picked! 0) => `((10 : Nat))
end A
namespace B
scoped macro_rules | `(picked! 0) => `((20 : Nat))
end B
section
open scoped A B
theorem later_namespace : picked! 0 = (20 : Nat) := rfl
open scoped A
theorem reopen_is_idempotent : picked! 0 = (20 : Nat) := rfl
macro_rules | `(picked! 0) => `((30 : Nat))
theorem later_global : picked! 0 = (30 : Nat) := rfl
end
section
open scoped B A
theorem reverse_activation : picked! 0 = (10 : Nat) := rfl
local macro_rules | `(picked! 0) => `((40 : Nat))
theorem local_wins : picked! 0 = (40 : Nat) := rfl
end
theorem global_survives : picked! 0 = (30 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 6);
}

#[test]
fn scoped_rules_work_with_temporary_opens_and_namespace_reentry() {
    let source = format!(
        r#"{BASE}
namespace Choice
scoped macro_rules | `(picked! 0) => `((10 : Nat))
end Choice
open scoped Choice in
theorem temporary : picked! 0 = (10 : Nat) := rfl
theorem after_temporary : picked! 0 = (0 : Nat) := rfl
namespace Choice
namespace Inner
theorem nested : picked! 0 = (10 : Nat) := rfl
end Inner
scoped macro_rules | `(picked! 1) => `((11 : Nat))
end Choice
section
open Choice
theorem simple_open : picked! 1 = (11 : Nat) := rfl
end
"#
    );
    assert_eq!(check(&source).unwrap(), 4);
}

fn modules(files: &[(&str, &str)]) -> Result<Engine, String> {
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
            fln::source_check::modules::SourceModuleCheckLimits::new(SourceCheckLimits::new(
                limits(),
            )),
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
fn scoped_rule_only_imports_and_journal_replay_do_not_activate_namespaces() {
    let extension = r#"import Core
namespace Choice
scoped macro_rules | `(picked! 0) => `((42 : Nat))
end Choice
"#;
    let result = modules(&[
        ("Core", BASE),
        ("Rules", extension),
        (
            "Main",
            "import Rules\ntheorem inactive : picked! 0 = (0 : Nat) := rfl",
        ),
    ])
    .unwrap();
    assert!(resumes(
        &result,
        "open scoped Choice\ntheorem active : picked! 0 = (42 : Nat) := rfl"
    ));
    assert!(resumes(
        &result,
        "theorem fresh : picked! 0 = (0 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem not_leaked : picked! 0 = (42 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "open scoped Choice\ntheorem wrong : picked! 0 = (0 : Nat) := rfl"
    ));
}

#[test]
fn diamond_imports_preserve_scoped_clause_order_without_duplicate_exports() {
    let first = "import Core\nnamespace Shared\nscoped macro_rules | `(picked! 0) => `((10 : Nat))\nend Shared";
    let second = "import Core\nnamespace Shared\nscoped macro_rules | `(picked! 0) => `((20 : Nat))\nend Shared";
    for (imports, expected) in [("First\nimport Second", 20), ("Second\nimport First", 10)] {
        let main = format!(
            "import {imports}\nopen scoped Shared\ntheorem ordered : picked! 0 = ({expected} : Nat) := rfl"
        );
        // Inputs deliberately do not follow header order.
        let checked = modules(&[
            ("Core", BASE),
            ("Second", second),
            ("First", first),
            ("Main", &main),
        ])
        .unwrap();
        assert!(resumes(
            &checked,
            &format!(
                "open scoped Shared\ntheorem replay_order : picked! 0 = ({expected} : Nat) := rfl"
            )
        ));
        assert!(!resumes(
            &checked,
            "theorem inactive : picked! 0 = (10 : Nat) := rfl"
        ));
    }
}

#[test]
fn imported_scoped_templates_keep_definition_site_names_and_strip_local_clauses() {
    let library = format!(
        r#"{BASE}
namespace Choice
def amount : Nat := 42
scoped macro_rules | `(picked! 0) => `(amount)
local macro_rules | `(picked! 1) => `((91 : Nat))
theorem local_proof : picked! 1 = (91 : Nat) := rfl
end Choice
"#
    );
    let main = "import Library\ndef amount : Nat := 99\nopen scoped Choice\ntheorem scoped_name : picked! 0 = (42 : Nat) := rfl\ntheorem no_local : picked! 1 = (1 : Nat) := rfl";
    let result = modules(&[("Library", &library), ("Main", main)]).unwrap();
    assert!(resumes(
        &result,
        "open scoped Choice\ntheorem stable : picked! 0 = (42 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "open scoped Choice\ntheorem not_captured : picked! 0 = (99 : Nat) := rfl"
    ));
}

#[test]
fn scoped_tactic_expansions_reach_the_native_vm_and_reject_false_proofs() {
    let source = r#"
syntax "scopedTac!" : tactic
macro_rules | `(tactic| scopedTac!) => `(tactic| exact 7)
namespace Choice
scoped macro_rules | `(tactic| scopedTac!) => `(tactic| exact 42)
def inside : Nat := by scopedTac!
end Choice
def outside : Nat := by scopedTac!
#eval Choice.inside
#eval outside
"#;
    let result = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            fln::EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let values: Vec<_> = result
        .batch
        .executions
        .iter()
        .rev()
        .take(2)
        .map(|run| fln::closed_vm_value(&run.exit).unwrap())
        .collect();
    assert_eq!(
        values,
        vec![
            Some(fln::ClosedVmValue::Scalar(7)),
            Some(fln::ClosedVmValue::Scalar(42))
        ]
    );
    assert!(check(&source.replace("def inside : Nat", "theorem inside : False")).is_err());
}

#[test]
fn a_matched_scoped_error_is_not_permission_to_use_the_global_fallback() {
    for rhs in ["`(notDeclaredHere)", "do pure `((42 : Nat))"] {
        let source = format!(
            "{BASE}\nnamespace Broken\nscoped macro_rules | `(picked! 0) => {rhs}\ntheorem must_not_fallback : picked! 0 = (0 : Nat) := rfl\nend Broken"
        );
        assert!(check(&source).is_err());
    }
    assert!(
        check(&format!(
            "{BASE}\nscoped macro_rules | `(picked! 0) => `(42)"
        ))
        .is_err()
    );
    assert_eq!(
        check(&format!(
            "{BASE}\ntheorem recovery : picked! 0 = (0 : Nat) := rfl"
        ))
        .unwrap(),
        1
    );
}

#[test]
fn dependent_simple_opens_activate_grammar_namespaces_left_to_right() {
    let source = format!(
        r#"{BASE}
namespace Library.Parser.Term
scoped macro_rules | `(picked! 0) => `((42 : Nat))
end Library.Parser.Term
section
open Library Parser Term
theorem dependent : picked! 0 = (42 : Nat) := rfl
end
theorem restored : picked! 0 = (0 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 2);
    assert!(
        check(&source.replace("dependent : picked! 0 = (42", "dependent : picked! 0 = (0"))
            .is_err()
    );
    // A scoped-only open does not add a name-resolution prefix for a later name.
    assert!(
        check(&source.replace(
            "open Library Parser Term",
            "open scoped Library Parser Term"
        ))
        .is_err()
    );
}

#[test]
fn dependent_temporary_opens_never_escape_the_command() {
    let source = format!(
        r#"{BASE}
namespace Library.Parser
scoped macro_rules | `(picked! 0) => `((42 : Nat))
end Library.Parser
open Library Parser in
theorem temporary : picked! 0 = (42 : Nat) := rfl
theorem outside : picked! 0 = (0 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 2);
    assert!(
        check(&source.replace("outside : picked! 0 = (0", "outside : picked! 0 = (42")).is_err()
    );
}

#[test]
fn dependent_opens_retain_canonical_names_for_syntax_abbreviations() {
    let source = r#"
namespace Library.Parser
syntax word := "on"
end Library.Parser
open Library Parser
syntax "reading! " word : term
macro_rules | `(reading! on) => `((42 : Nat))
theorem abbreviation : reading! on = (42 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(
        check(&source.replace(
            "abbreviation : reading! on = (42",
            "abbreviation : reading! on = (0"
        ))
        .is_err()
    );
}

#[test]
fn dependent_rule_only_import_opens_survive_journal_reentry_without_activation_leaks() {
    let library = format!(
        "{BASE}\nnamespace Library.Parser\nscoped macro_rules | `(picked! 0) => `((42 : Nat))\nend Library.Parser"
    );
    let result = modules(&[
        ("Core", &library),
        (
            "Main",
            "import Core\ntheorem initial : picked! 0 = (0 : Nat) := rfl",
        ),
    ])
    .unwrap();
    assert!(resumes(
        &result,
        "open Library Parser\ntheorem active : picked! 0 = (42 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "open Library Parser\ntheorem wrong : picked! 0 = (0 : Nat) := rfl"
    ));
    assert!(resumes(
        &result,
        "theorem inactive : picked! 0 = (0 : Nat) := rfl"
    ));
}

#[test]
fn all_opened_namespace_candidates_keep_their_activation_order() {
    let source = format!(
        r#"{BASE}
namespace A.N
scoped macro_rules | `(picked! 0) => `((10 : Nat))
end A.N
namespace B.N
scoped macro_rules | `(picked! 0) => `((20 : Nat))
end B.N
namespace N
scoped macro_rules | `(picked! 0) => `((30 : Nat))
end N
section
open A B N
theorem pooled : picked! 0 = (10 : Nat) := rfl
end
section
open B A N
theorem reverse : picked! 0 = (20 : Nat) := rfl
end
"#
    );
    assert_eq!(check(&source).unwrap(), 2);
    for wrong in [20, 30] {
        assert!(
            check(&source.replace(
                "pooled : picked! 0 = (10",
                &format!("pooled : picked! 0 = ({wrong}")
            ))
            .is_err()
        );
    }
}

#[test]
fn scoped_syntax_and_its_scoped_macro_activate_together_after_import() {
    let library = r#"
namespace Library.Parser
scoped syntax (name := token) "token! " num : term
scoped macro_rules | `(token! $n:num) => `(Nat.add $n 1)
end Library.Parser
"#;
    let main =
        "import Library\nopen Library Parser in\ntheorem active : token! 41 = (42 : Nat) := rfl";
    let result = modules(&[("Library", library), ("Main", main)]).unwrap();
    assert!(resumes(
        &result,
        "open Library Parser\ntheorem replay : token! 41 = (42 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem not_open : token! 41 = (42 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "open Library Parser\ntheorem wrong : token! 41 = (41 : Nat) := rfl"
    ));
}
