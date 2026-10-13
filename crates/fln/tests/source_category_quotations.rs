//! Quoted user categories are executable macro data, not new kernel authority.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<usize, String> {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|r| r.theorems)
        .map_err(|e| format!("{e:?}"))
}
const CIRCUIT: &str = include_str!("../../fln-parse/tests/fixtures/native_category_circuit.lean");
#[test]
fn custom_quotations_drive_cross_category_macro_expansion() {
    let source = format!("{CIRCUIT}\ntheorem result : answerCircuit = (42 : Nat) := rfl\n");
    assert_eq!(check(&source).unwrap(), 1);
    assert!(check(&source.replace("answerCircuit = (42", "answerCircuit = (0")).is_err());
    assert!(
        check(&source.replace(
            "theorem result : answerCircuit = (42 : Nat) := rfl",
            "def bad : False := answerCircuit"
        ))
        .is_err()
    );
}
#[test]
fn dynamic_category_quotations_and_typed_macro_templates_reach_execution() {
    let source = format!(
        r#"{CIRCUIT}
macro "enabled" : circuit => `(circuit| on)
syntax "dynamicCircuit" : term
macro_rules | `(dynamicCircuit) => `(circuit | enabled)
theorem result : dynamicCircuit = (42 : Nat) := rfl
#eval dynamicCircuit
"#
    );
    let result = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            fln::EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(value) = &result.batch.executions.last().unwrap().exit else {
        panic!("VM did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}
#[test]
fn malformed_custom_captures_and_recursive_macros_do_not_publish() {
    for suffix in [
        "macro_rules | `(circuit| box [$x:missingCategory]) => `(circuit| $x)\n",
        "macro_rules | `(circuit| box [$x:circuit]) => `(circuit| $unbound)\n",
        "macro_rules | `(answerCircuit) => `(`(circuit| on))\n",
        "macro \"wrongCategory\" : circuit => `((7 : Nat))\nmacro_rules | `(answerCircuit) => `(circuit| wrongCategory)\n",
        "syntax \"forever\" : circuit\nmacro_rules | `(circuit| forever) => `(circuit| forever)\nmacro_rules | `(answerCircuit) => `(circuit| forever)\n",
    ] {
        let source = format!("{CIRCUIT}{suffix}\ndef forbidden : Nat := answerCircuit\n");
        assert!(check(&source).is_err());
    }
    assert_eq!(
        check(&format!(
            "{CIRCUIT}\ntheorem recovered : answerCircuit = (42 : Nat) := rfl\n"
        ))
        .unwrap(),
        1
    );
}

#[test]
fn imported_category_quoters_and_rule_only_overrides_survive_journal_replay() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let names = ["Main", "Extension", "Circuit"].map(|s| Name::from_components([s]));
    let main = "import Extension\ntheorem selected : answerCircuit = (7 : Nat) := rfl";
    let extension = "import Circuit\nmacro_rules | `(circuit| on) => `((7 : Nat))";
    let sources = [main, extension, CIRCUIT];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let checked = engine()
        .check_source_modules(
            &inputs,
            &names[0],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for (source, expected) in [
        ("theorem replayed : answerCircuit = (7 : Nat) := rfl", true),
        ("theorem older : answerCircuit = (42 : Nat) := rfl", false),
        ("def impossible : False := answerCircuit", false),
        (
            "macro \"fromJournal\" : circuit => `(circuit | on)\nsyntax \"journalAnswer\" : term\nmacro_rules | `(journalAnswer) => `(circuit| fromJournal)\ntheorem newRule : journalAnswer = (7 : Nat) := rfl",
            true,
        ),
    ] {
        let complete = checked
            .checked
            .engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .ok()
            .is_some_and(|r| r.into_complete().is_ok());
        assert_eq!(complete, expected, "{source}");
    }
    // A separately created grammar does not inherit this world's category or rules.
    assert!(check("def unavailable : Nat := answerCircuit").is_err());
    assert_eq!(
        check(&format!(
            "{CIRCUIT}\ntheorem original : answerCircuit = (42 : Nat) := rfl"
        ))
        .unwrap(),
        1
    );
}
