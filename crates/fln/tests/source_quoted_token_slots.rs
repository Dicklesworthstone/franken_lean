//! Quoted macro patterns/templates use the token parser at each declared slot.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

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
        .map_err(|error| format!("{error:?}"))?
        .into_complete()
        .map(|check| check.theorems)
        .map_err(|error| format!("{error:?}"))
}
const NUM: &str = r#"
syntax "numSlot! " num : term
macro_rules | `(numSlot! $n) => `($n)
"#;

#[test]
fn numeric_slots_capture_in_patterns_and_nested_templates() {
    let source = format!(
        r#"{NUM}
macro "forwardNum! " n:num : term => `(numSlot! $n)
syntax "sumSlots! " num "," num : term
macro_rules | `(sumSlots! $a:num, $b:num) => `(Nat.add $a $b)
theorem direct : numSlot! 42 = (42 : Nat) := rfl
theorem forward : forwardNum! 0x2a = (42 : Nat) := rfl
theorem combined : sumSlots! 13, 29 = (42 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 3);
    assert!(check(&source.replace("numSlot! 42 = (42", "numSlot! 42 = (43")).is_err());
}

#[test]
fn string_slots_keep_literal_patterns_and_anonymous_captures_distinct() {
    let source = r#"
syntax "strSlot! " str : term
macro_rules
  | `(strSlot! "special") => `((10 : Nat))
  | `(strSlot! $_:str) => `((20 : Nat))
syntax "echoSlot! " str : term
macro_rules | `(echoSlot! $s:str) => `($s)
theorem special : strSlot! "special" = (10 : Nat) := rfl
theorem other : strSlot! "λ🙂" = (20 : Nat) := rfl
theorem echoed : echoSlot! "λ🙂" = "λ🙂" := rfl
"#;
    assert_eq!(check(source).unwrap(), 3);
    assert!(check(&source.replace("strSlot! \"λ🙂\" = (20", "strSlot! \"λ🙂\" = (10")).is_err());
}

#[test]
fn identifier_slots_retain_caller_bindings_instead_of_definition_site_names() {
    let source = r#"
def x : Nat := 90
syntax "identSlot! " ident : term
macro_rules | `(identSlot! $n:ident) => `($n)
theorem localName (x : Nat) : identSlot! x = x := rfl
theorem qualified : identSlot! Nat.zero = (0 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 2);
    assert!(
        check(&source.replace("identSlot! Nat.zero = (0", "identSlot! Nat.zero = (90")).is_err()
    );
}

#[test]
fn numeric_tactic_slots_reach_checked_proof_and_value_elaboration() {
    let source = r#"
syntax "giveNum! " num : tactic
macro_rules | `(tactic| giveNum! $n:num) => `(tactic| exact $n)
def result : Nat := by giveNum! 42
theorem result_eq : result = (42 : Nat) := rfl
"#;
    assert_eq!(check(source).unwrap(), 1);
    assert!(check(&source.replace("result : Nat", "result : False")).is_err());
}

#[test]
fn scientific_character_and_name_slots_can_participate_in_quoted_macros() {
    for (category, argument) in [
        ("scientific", "1.25e-3"),
        ("char", "'λ'"),
        ("name", "`Example.member"),
    ] {
        let source = format!(
            r#"
syntax "typedSlot! " {category} : term
macro_rules | `(typedSlot! $_:{category}) => `((42 : Nat))
theorem result : typedSlot! {argument} = (42 : Nat) := rfl
"#
        );
        assert_eq!(
            check(&source).unwrap_or_else(|error| panic!("{source}\n{error}")),
            1
        );
        assert!(
            check(&source.replace(&format!("typedSlot! {argument} ="), "typedSlot! 42 =")).is_err()
        );
    }
}

#[test]
fn slots_refuse_wrong_annotations_and_ordinary_dollar_tokens_then_recover() {
    for bad in ["$n:str", "$n:term", "$n:", "$ n", "$$n", "$ns,*", "$(f $n)"] {
        let source = format!(
            "syntax \"badSlot! \" num : term\nmacro_rules | `(badSlot! {bad}) => `((7 : Nat))\ntheorem x : badSlot! 7 = (7 : Nat) := rfl"
        );
        assert!(check(&source).is_err(), "accepted {source}");
    }
    for argument in ["\"7\"", "Nat.zero", "(7)", "$n", "7 8"] {
        assert!(
            check(&format!(
                "{NUM}\ntheorem x : numSlot! {argument} = (7 : Nat) := rfl"
            ))
            .is_err()
        );
    }
    assert_eq!(
        check(&format!(
            "{NUM}\ntheorem recovered : numSlot! 7 = (7 : Nat) := rfl"
        ))
        .unwrap(),
        1
    );
}

#[test]
fn token_captures_execute_on_the_native_vm() {
    let source = format!("{NUM}\n#eval numSlot! 42");
    let completed = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(returned) = &completed.batch.executions.last().unwrap().exit else {
        panic!("native VM did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("42")
    );
}

#[test]
fn imported_token_slot_rules_keep_their_types_across_journal_reentry() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let names = [
        Name::from_components(["Core"]),
        Name::from_components(["Rules"]),
        Name::from_components(["Main"]),
    ];
    let source = [
        "syntax \"fromNum! \" num : term\n",
        "import Core\nmacro_rules | `(fromNum! $n:num) => `($n)\n",
        "import Rules\ntheorem initial : fromNum! 41 = (41 : Nat) := rfl\n",
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
            &names[2],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let base = result.checked.engine;
    for (source, accepted) in [
        ("theorem later : fromNum! 42 = (42 : Nat) := rfl", true),
        ("theorem wrong : fromNum! 42 = (43 : Nat) := rfl", false),
        ("def wrongType : Nat := fromNum! \"42\"", false),
    ] {
        let complete = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .ok()
            .is_some_and(|outcome| outcome.into_complete().is_ok());
        assert_eq!(complete, accepted, "{source}");
    }
}

#[test]
fn token_slot_extensions_keep_their_declared_application_precedence() {
    let source = format!(
        r#"{NUM}
macro:max "maxSlot! " n:num : term => `($n)
def bump (n : Nat) : Nat := Nat.add n 1
theorem grouped : bump (numSlot! 41) = (42 : Nat) := rfl
theorem tight : bump maxSlot! 41 = (42 : Nat) := rfl
"#
    );
    assert_eq!(check(&source).unwrap(), 2);
    // Recognizing a bounded endpoint does not promote `lead` syntax to `arg`.
    assert!(check(&source.replace("bump (numSlot! 41)", "bump numSlot! 41")).is_err());
}
