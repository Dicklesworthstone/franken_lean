//! Native macro registrations extend predecessor syntax without re-exporting its rules.
#![forbid(unsafe_code)]

use fln::source_check::modules::{SourceModuleCheck, SourceModuleCheckLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(files: &[(&str, &str)]) -> Result<SourceModuleCheck, String> {
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    engine()
        .check_source_modules(&inputs, &name("Main"), &KVMap::new(), limits())
        .map_err(|error| format!("{error:?}"))?
        .into_complete()
        .map_err(|error| format!("module checking did not complete: {error:?}"))
}
fn checked(files: &[(&str, &str)]) -> Engine {
    check(files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error}"))
        .checked
        .engine
}
fn resumes(base: &Engine, source: &str) -> bool {
    match base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source) {
        Ok(outcome) => outcome.into_complete().is_ok(),
        Err(error) => {
            eprintln!("source refusal: {error:?}\n{source}");
            false
        }
    }
}

const CORE: &str = "syntax (name := selectSyntax) \"select! \" term:max : term\n\
    macro_rules | `(select! $x) => `(Nat.add $x 1)\n";

#[test]
fn a_rule_only_module_extends_imported_syntax_and_survives_journal_reentry() {
    let result = checked(&[
        (
            "Syntax",
            "syntax (name := projectSyntax) \"project! \" term:max : term",
        ),
        (
            "Rules",
            "import Syntax\nmacro_rules (kind := projectSyntax) | `(project! (Nat.add $x $y)) => `($x)",
        ),
        (
            "Main",
            "import Rules\ntheorem initial : project! (Nat.add 7 8) = (7 : Nat) := rfl",
        ),
    ]);
    assert!(resumes(
        &result,
        "theorem later : project! (Nat.add 9 10) = (9 : Nat) := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem falseResult : project! (Nat.add 9 10) = (10 : Nat) := rfl"
    ));
    assert!(!resumes(&result, "def unmatched : Nat := project! 9"));
}

#[test]
fn imported_fallbacks_keep_their_own_definition_site_and_source_buffer() {
    let core = "namespace Original\ndef α : Nat := 10\nsyntax \"remember! \" term:max : term\nmacro_rules | `(remember! $x) => `(Nat.add $x α)\nend Original\n".replace('\n', "\r\n");
    let rules = "import Core\nnamespace New\ndef α : Nat := 90\nmacro_rules | `(remember! 0) => `(α)\nend New\n".replace('\n', "\r\n");
    let result = checked(&[
        ("Core", &core),
        ("Rules", &rules),
        (
            "Main",
            "import Rules\ntheorem newRule : remember! 0 = 90 := rfl\ntheorem oldRule : remember! 2 = 12 := rfl",
        ),
    ]);
    assert!(resumes(
        &result,
        "theorem replayNew : remember! 0 = 90 := rfl\ntheorem replayOld : remember! 3 = 13 := rfl"
    ));
    assert!(!resumes(
        &result,
        "theorem wrongScope : remember! 3 = 93 := rfl"
    ));
}

#[test]
fn sibling_registration_order_survives_a_diamond_without_reexported_base_rules() {
    for (imports, expected) in [
        ("import Left\nimport Right", 20),
        ("import Right\nimport Left", 10),
    ] {
        let main = format!(
            "{imports}\ntheorem selected : select! 0 = {expected} := rfl\ntheorem fallback : select! 4 = 5 := rfl"
        );
        let result = checked(&[
            ("Core", CORE),
            (
                "Left",
                "import Core\nmacro_rules | `(select! 0) => `((10 : Nat))",
            ),
            (
                "Right",
                "import Core\nmacro_rules | `(select! 0) => `((20 : Nat))",
            ),
            ("Main", &main),
        ]);
        assert!(resumes(
            &result,
            &format!("theorem replay : select! 0 = {expected} := rfl")
        ));
        assert!(!resumes(
            &result,
            &format!("theorem wrongOrder : select! 0 = {} := rfl", 30 - expected)
        ));
    }
}

#[test]
fn sequential_module_worlds_publish_only_their_new_clauses() {
    let mut base = checked(&[("Core", CORE), ("Main", "import Core")]);
    for (argument, value) in [(0, 10), (1, 20), (2, 30)] {
        let source = format!(
            "macro_rules | `(select! {argument}) => `(({value} : Nat))\ntheorem local{argument} : select! {argument} = {value} := rfl"
        );
        let module = name(&format!("Layer{argument}"));
        base = base
            .check_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                limits(),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .checked
            .engine;
    }
    assert!(resumes(
        &base,
        "theorem a : select! 0 = 10 := rfl\ntheorem b : select! 1 = 20 := rfl\ntheorem c : select! 2 = 30 := rfl\ntheorem d : select! 3 = 4 := rfl"
    ));
}

#[test]
fn an_imported_matched_error_never_uses_the_previous_expansion() {
    for rhs in ["`(missingDefinition)", "do pure `((99 : Nat))"] {
        let extension = format!(
            "import Core\nmacro_rules | `(select! 0) => {rhs}\ntheorem invalid : select! 0 = 1 := rfl"
        );
        assert!(
            check(&[
                ("Core", CORE),
                ("Rules", &extension),
                ("Main", "import Rules")
            ])
            .is_err()
        );
    }
}

#[test]
fn scoped_imported_syntax_still_requires_lexical_activation() {
    let core = "namespace Ops\nscoped syntax (name := wrappedSyntax) \"wrapped! \" term:max : term\nend Ops";
    let rules = "import Core\nopen scoped Ops\nmacro_rules (kind := Ops.wrappedSyntax) | `(wrapped! $x) => `($x)";
    let result = checked(&[
        ("Core", core),
        ("Rules", rules),
        (
            "Main",
            "import Rules\nopen scoped Ops\ntheorem works : wrapped! 7 = (7 : Nat) := rfl",
        ),
    ]);
    assert!(!resumes(&result, "def notOpen : Nat := wrapped! 8"));
    assert!(resumes(
        &result,
        "open scoped Ops\ntheorem opened : wrapped! 8 = (8 : Nat) := rfl"
    ));
}

#[test]
fn native_execution_uses_the_imported_override_instead_of_the_old_value() {
    let base = checked(&[
        ("Core", CORE),
        (
            "Rules",
            "import Core\nmacro_rules | `(select! 0) => `((42 : Nat))",
        ),
        ("Main", "import Rules"),
    ]);
    let result = base
        .execute_source_commands_with_checks(
            b"#eval select! 0",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&result.batch.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn shared_cross_module_source_fixture_rejects_the_shadowed_result() {
    const CORE: &str =
        include_str!("../../fln-parse/tests/fixtures/imported_macro_rules/Core.lean");
    const EXT: &str =
        include_str!("../../fln-parse/tests/fixtures/imported_macro_rules/Extension.lean");
    const GOOD: &str =
        include_str!("../../fln-parse/tests/fixtures/imported_macro_rules/Main.lean");
    const BAD: &str =
        include_str!("../../fln-parse/tests/fixtures/imported_macro_rules/FalseResult.lean");
    checked(&[("Core", CORE), ("Extension", EXT), ("Main", GOOD)]);
    assert!(check(&[("Core", CORE), ("Extension", EXT), ("Main", BAD)]).is_err());
}
