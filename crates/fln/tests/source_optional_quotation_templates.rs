//! Optional quotation bodies through source expansion, both checkers and the VM.
//! Semantics: the pin's `Quotation.quoteSyntax` matches every capture as `some`
//! before emitting the complete body, including fixed atoms and multiple terms.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits};

const CORPUS: &str = include_str!("../../fln-parse/tests/fixtures/quoted_optional_templates.lean");

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

#[test]
fn optional_bodies_require_every_capture_and_preserve_caller_hygiene() {
    let checked = engine()
        .check_source_files(
            &[CORPUS.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.theorems, 10);
}

#[test]
fn optional_expansions_execute_present_and_absent_cases_natively() {
    let source = format!(
        "{CORPUS}\n#eval optionalInput![41]\n#eval optionalPair![19][23]\n#eval optionalPair![][23]"
    );
    let checked = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let results: Vec<_> = checked
        .batch
        .executions
        .iter()
        .map(|execution| {
            let fln::VmExit::Returned(value) = &execution.exit else {
                panic!("optional quotation expansion must return natively");
            };
            fln_vm::interpreter::nat_decimal(&value.value).unwrap()
        })
        .collect();
    assert_eq!(results, ["42", "42", "0"]);
}

#[test]
fn optional_templates_reject_bad_bindings_and_false_results_without_publishing() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for tail in [
        "theorem wrong : optionalPair![19][23] = (0 : Nat) := rfl",
        "theorem wrong : optionalPair![][23] = (42 : Nat) := rfl",
        "def wrong : Nat := optionalInput![true]",
        "macro \"scalarOptional!\" x:term:max : term => `(optionalOutput![$[value $x]?])\ndef wrong := scalarOptional! 42",
        "macro \"unboundOptional!\" : term => `(optionalOutput![$[value $missing]?])\ndef wrong := unboundOptional!",
        "macro \"emptyOptional!\" : term => `(optionalOutput![$[value 42]?])\ndef wrong := emptyOptional!",
        "macro \"arrayOptional!\" \"[\" xs:term,* \"]\" : term => `(optionalOutput![$[value $xs]?])\ndef wrong := arrayOptional![1, 2]",
        "macro \"arrayOptional!\" \"[\" xs:term,* \"]\" : term => `(optionalOutput![$[value $xs]?])\ndef wrong := arrayOptional![42]",
        "macro \"arrayOptional!\" \"[\" xs:term,* \"]\" : term => `(optionalOutput![$[value $xs]?])\ndef wrong := arrayOptional![]",
        "syntax \"arrayRuleOptional!\" \"[\" term,* \"]\" : term\nmacro_rules | `(arrayRuleOptional![$xs,*]) => `(optionalOutput![$[value $xs]?])\ndef wrong := arrayRuleOptional![42]",
        "syntax \"duplicateOptional!\" \"[\" (term)? \"]\" : term\nmacro_rules | `(duplicateOptional![$(x)?]) => `(optionalOutput![$[value (Nat.add $x $x)]?])\ndef wrong := duplicateOptional![21]",
    ] {
        let source = format!("{CORPUS}\ndef unpublished : Nat := 1\n{tail}");
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{tail}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert_eq!(
        base.check_source_files(
            &[CORPUS.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .theorems,
        10
    );
}

#[test]
fn optional_templates_survive_import_and_exact_journal_reentry() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};

    let names = ["OptionalTemplates", "Main"].map(|name| Name::from_components([name]));
    let sources = [
        CORPUS,
        "import OptionalTemplates\ntheorem imported : optionalPair![40][2] = (42 : Nat) := rfl",
    ];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let imported = engine()
        .check_source_modules(
            &inputs,
            &names[1],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked
        .engine;
    let source = "theorem replayed (x : Nat) : optionalPair![x][2] = Nat.add x 2 := rfl\n\
        theorem omitted : optionalPair![40][] = (0 : Nat) := rfl";
    assert_eq!(
        imported
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        2
    );
    assert!(
        imported
            .check_source_files(
                &[source.replace("Nat.add x 2", "Nat.add x 3").as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
    );
}

#[test]
fn nested_optional_splices_cannot_hide_in_discarded_syntax_or_restore_an_old_rule() {
    let declarations = "syntax \"discardOptional!\" \"[\" (term)? \"]\" : term\n\
        macro_rules | `(discardOptional![$(x)?]) => `((42 : Nat))\n\
        syntax \"nestedOptional!\" \"[\" (term)? \"]\" : term\n\
        macro_rules | `(nestedOptional![$(x)?]) => `((7 : Nat))";
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let baseline =
        format!("{declarations}\ntheorem original : nestedOptional![5] = (7 : Nat) := rfl");
    base.check_source_files(
        &[baseline.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    for result in [7, 42] {
        let source = format!(
            "{declarations}\n\
             macro_rules | `(nestedOptional![$(x)?]) =>\n\
               `(discardOptional![$[([$[$x],*] : List Nat)]?])\n\
             theorem forbidden : nestedOptional![5] = ({result} : Nat) := rfl"
        );
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}
