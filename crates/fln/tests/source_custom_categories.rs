//! Native user-defined categories must reach real expansion, checking and execution.
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
const ARITH: &str = include_str!("../../fln-parse/tests/fixtures/native_category_arithmetic.lean");

#[test]
fn custom_category_arithmetic_reaches_both_checkers() {
    let source = format!(
        "{ARITH}\ntheorem value : arithEval [2 + 3 * 4] = (14 : Nat) := rfl\ntheorem parentheses : arithEval [(2 + 3) * 4] = (20 : Nat) := rfl\n"
    );
    assert_eq!(check(&source).unwrap(), 2);
    assert!(check(&source.replace("(14 : Nat)", "(20 : Nat)")).is_err());
}

#[test]
fn custom_categories_support_recursive_prefix_syntax_and_exact_token_captures() {
    let source = r#"
declare_syntax_cat treeExpr
syntax "leaf " num : treeExpr
syntax "fork " "(" treeExpr "," treeExpr ")" : treeExpr
syntax "treeValue " "[" treeExpr "]" : term
macro_rules
  | `(treeValue [leaf $n:num]) => `($n)
  | `(treeValue [fork ($a:treeExpr, $b:treeExpr)]) => `(Nat.add (treeValue [$a]) (treeValue [$b]))
theorem branches : treeValue [fork (leaf 13, fork (leaf 9, leaf 20))] = (42 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("leaf 13", "leaf true")).is_err());
    assert!(check(&source.replace("$a:treeExpr", "$a:otherCategory")).is_err());
}

#[test]
fn operand_precedence_controls_left_right_and_nonassociative_syntax() {
    for (left, right, expected) in [(60, 61, 5), (61, 60, 9)] {
        let source = format!(
            r#"{ARITH}
syntax:60 arithmetic:{left} "minus" arithmetic:{right} : arithmetic
macro_rules | `(arithEval [$a:arithmetic minus $b:arithmetic]) => `(Nat.sub (arithEval [$a]) (arithEval [$b]))
theorem associated : arithEval [10 minus 3 minus 2] = ({expected} : Nat) := rfl
"#
        );
        assert_eq!(check(&source).unwrap(), 1);
        assert!(check(&source.replace(&format!("({expected} : Nat)"), "(99 : Nat)")).is_err());
    }
    let source = format!(
        r#"{ARITH}
syntax:60 arithmetic:61 "minus" arithmetic:61 : arithmetic
macro_rules | `(arithEval [$a:arithmetic minus $b:arithmetic]) => `(Nat.sub (arithEval [$a]) (arithEval [$b]))
theorem grouped : arithEval [(10 minus 3) minus 2] = (5 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 1);
    assert!(check(&source.replace("(10 minus 3) minus 2", "10 minus 3 minus 2")).is_err());
}

#[test]
fn category_expansions_execute_on_the_native_vm() {
    let source = format!("{ARITH}\n#eval arithEval [6 * (4 + 3)]\n");
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
        panic!("native program did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn category_registrations_and_captures_survive_import_and_journal_reentry() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let names = [
        Name::from_components(["Arithmetic"]),
        Name::from_components(["Main"]),
    ];
    let source = [
        ARITH.to_string(),
        "import Arithmetic\ntheorem first : arithEval [6 * 7] = (42 : Nat) := rfl\n".to_string(),
    ];
    let inputs: Vec<_> = names
        .iter()
        .zip(&source)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let result = engine()
        .check_source_modules(
            &inputs,
            &names[1],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let base = result.checked.engine;
    for (source, accepted) in [
        (
            "theorem later : arithEval [(3 + 4) * 6] = (42 : Nat) := rfl",
            true,
        ),
        (
            "theorem wrong : arithEval [3 + 4 * 6] = (42 : Nat) := rfl",
            false,
        ),
        ("def wrong : Nat := arithEval [true]", false),
        ("def wrong : False := arithEval [42]", false),
    ] {
        let completed = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .ok()
            .is_some_and(|outcome| outcome.into_complete().is_ok());
        assert_eq!(completed, accepted, "{source}");
    }
}
