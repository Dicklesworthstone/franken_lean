//! Repetition captures travel through native macro matching, checking and Golem.
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

const CORPUS: &str = include_str!("../../fln-parse/tests/fixtures/quoted_repetitions.lean");
const LIST: &str =
    "syntax \"copy!\" \"[\" term,* \"]\" : term\nmacro_rules | `(copy![$xs,*]) => `([$xs,*])\n";

#[test]
fn shared_corpus_checks_empty_nested_optional_and_repeated_sequences() {
    assert_eq!(check(CORPUS).unwrap_or_else(|e| panic!("{e}")).theorems, 8);
}

#[test]
fn captured_identifiers_keep_caller_scope_in_a_hygienic_template() {
    let source = format!(
        "{LIST}\nmacro \"shadow!\" \"[\" xs:term,* \"]\" : term => `(let x := 99; [$xs,*])\n\
        theorem kept (x : Nat) : shadow![x, 2] = [x, 2] := rfl\n\
        syntax \"fromList!\" term:max : term\n\
        macro_rules | `(fromList! [$xs,*]) => `([$xs,*])\n\
        theorem trailing : fromList! [1, 2,] = [1, 2] := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 2);
}

#[test]
fn sequence_expansions_execute_without_upstream_macro_code() {
    let source = format!("{LIST}\n#eval List.foldl (fun n x => n * 10 + x) 0 (copy![4, 2])");
    let checked = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &checked.batch.executions.last().unwrap().exit else {
        panic!("expected native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

#[test]
fn bad_expansions_false_results_and_unsupported_splices_refuse() {
    assert!(
        check(LIST).is_ok(),
        "registration must succeed before testing uses"
    );
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for tail in [
        "theorem wrong : copy![1, 2] = [2, 1] := rfl",
        "def wrong : List Nat := copy![true]",
        "macro \"scalar!\" x:term:max : term => `([$x,*])\ndef wrong := scalar! 4",
        "macro \"unbound!\" : term => `([$xs,*])\ndef wrong := unbound!",
        "syntax \"mixed!\" \"[\" term,* \"]\" : term\nmacro_rules | `(mixed![0, $xs,*, 1]) => `([$xs,*])\ntheorem wrong : mixed![0, 2, 1] = [42] := rfl",
        "syntax \"noFallback!\" term:max : term\nmacro_rules | `(noFallback! $x) => `((7 : Nat))\nmacro_rules | `(noFallback! $x) => `([$x,*])\ndef wrong := noFallback! 4",
    ] {
        let source = format!("{LIST}\n{tail}");
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{tail}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let recovered = format!("{LIST}\ntheorem recovered : copy![42] = [42] := rfl");
    assert_eq!(
        base.check_source_files(
            &[recovered.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .theorems,
        1
    );
}

#[test]
fn sequence_annotations_do_not_turn_into_scalar_kind_filters() {
    let source = "syntax \"wholeKind!\" \"[\" term,* \"]\" : term\n\
        macro_rules | `(wholeKind![$xs,*]) => `((99 : Nat))\n\
        macro_rules | `(wholeKind![$xs:num,*]) => `((42 : Nat))\n\
        syntax \"discardSequence!\" \"[\" term,* \"]\" : term\n\
        macro_rules | `(discardSequence![$_,*]) => `((7 : Nat))\n\
        theorem annotation : wholeKind![true, 2] = (42 : Nat) := rfl\n\
        theorem empty : wholeKind![] = (42 : Nat) := rfl\n\
        theorem wildcard : discardSequence![noSuchName] = (7 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 3);
    assert!(check(&source.replace("= (42 : Nat)", "= (99 : Nat)")).is_err());
}

#[test]
fn bracketed_repetition_patterns_filter_each_element_and_forward_whole_arrays() {
    let source = "syntax \"bracketed!\" \"[\" term,* \"]\" : term\n\
        macro_rules\n\
        | `(bracketed![$[$x:num],*]) => `((42 : Nat))\n\
        | `(bracketed![$[$x],*]) => `((99 : Nat))\n\
        theorem nums : bracketed![4, 2] = (42 : Nat) := rfl\n\
        theorem mixed : bracketed![true, 2] = (99 : Nat) := rfl\n\
        theorem empty : bracketed![] = (42 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 3);
    assert!(check(&source.replace("bracketed![4, 2] = (42", "bracketed![4, 2] = (99")).is_err());
}

#[test]
fn bracketed_repetition_executes_natively_and_keeps_caller_identifiers() {
    let source = "syntax \"bracketed!\" \"[\" term,* \"]\" : term\n\
        macro_rules | `(bracketed![$[$x],*]) => `([$[$x],*])\n\
        def keep (x : Nat) : List Nat := bracketed![x, 2]\n\
        theorem hygienic (x : Nat) : keep x = [x, 2] := rfl\n\
        #eval List.foldl (fun n x => n * 10 + x) 0 (bracketed![4, 2])";
    let checked = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &checked.batch.executions.last().unwrap().exit else {
        panic!("expected native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

#[test]
fn bracketed_repetition_templates_map_fixed_syntax_over_captured_elements() {
    let source = concat!(
        "syntax \"mapped!\" \"[\" term,* \"]\" : term\n",
        "macro_rules | `(mapped![$[$x],*]) => `([$[Nat.succ $x],*])\n",
        "theorem mapped : mapped![0, 1, 2] = [1, 2, 3] := rfl\n",
        "theorem empty : mapped![] = ([] : List Nat) := rfl",
    );
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 2);
    let executable =
        format!("{source}\n#eval List.foldl (fun n x => n * 10 + x) 0 (mapped![0, 1, 2])");
    let checked = engine()
        .execute_source_commands_with_checks(
            executable.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &checked.batch.executions.last().unwrap().exit else {
        panic!("expected native return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("123")
    );
}

const SUM: &str = "syntax \"sumSeq!\" \"[\" num* \"]\" : term\n\
    macro_rules\n\
    | `(sumSeq![]) => `((0 : Nat))\n\
    | `(sumSeq![$n:num $tail*]) => `(Nat.add $n (sumSeq![$tail*]))\n";

#[test]
fn templates_combine_repeated_captures_with_fixed_sequence_elements() {
    let source = format!(
        "{SUM}\nsyntax \"combineSeq!\" \"[\" num* \"]\" \"[\" num* \"]\" : term\n\
        macro_rules | `(combineSeq![$xs*][$ys*]) => `(sumSeq![1 $xs* 2 $ys* 3])\n\
        theorem emptyParts : combineSeq![][] = (6 : Nat) := rfl\n\
        theorem leftPart : combineSeq![36][] = (42 : Nat) := rfl\n\
        theorem rightPart : combineSeq![][36] = (42 : Nat) := rfl\n\
        theorem bothParts : combineSeq![10 14][12] = (42 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 4);
    assert!(
        check(&source.replace(
            "combineSeq![10 14][12] = (42",
            "combineSeq![10 14][12] = (43"
        ))
        .is_err()
    );
    let result = engine()
        .execute_source_commands_with_checks(
            format!("{source}\n#eval combineSeq![10 14][12]").as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.batch.executions.last().unwrap().exit else {
        panic!("native return expected")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

#[test]
fn templates_preserve_separators_while_prepending_appending_and_joining() {
    let source = "macro \"prependSeq!\" \"[\" xs:term,* \"]\" : term => `([0, $xs,*])\n\
        macro \"appendSeq!\" \"[\" xs:term,* \"]\" : term => `([$xs,*, 9])\n\
        syntax \"joinSeq!\" \"[\" term,* \"]\" \"[\" term,* \"]\" : term\n\
        macro_rules | `(joinSeq![$xs,*][$ys,*]) => `([$xs,*, $ys,*])\n\
        theorem prepended : prependSeq![1, 2] = [0, 1, 2] := rfl\n\
        theorem emptyTail : prependSeq![] = [0] := rfl\n\
        theorem appended : appendSeq![1, 2] = [1, 2, 9] := rfl\n\
        theorem joined : joinSeq![1, 2][3, 4] = [1, 2, 3, 4] := rfl\n\
        theorem nested : joinSeq![[1]][[2, 3]] = [[1], [2, 3]] := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 5);
    assert!(check(&source.replace("[1, 2, 3, 4] := rfl", "[1, 3, 2, 4] := rfl")).is_err());
}

#[test]
fn composed_templates_preserve_definition_and_caller_names_through_imports() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let library = "namespace Library\r\ndef edge : Nat := 40\r\n\
        syntax \"frameSeq!\" \"[\" term,* \"]\" : term\r\n\
        macro_rules | `(frameSeq![$xs,*]) => `([edge, $xs,*, edge])\r\n\
        end Library\r\n";
    let main = "import Library\ndef edge : Nat := 99\n\
        theorem hygienic (edge : Nat) : frameSeq![edge] = [40, edge, 40] := rfl\n\
        theorem nested : frameSeq![Nat.succ edge] = [40, 100, 40] := rfl";
    let names = ["Library", "Main"].map(|n| Name::from_components([n]));
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: library.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: main.as_bytes(),
        },
    ];
    let exported = engine()
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
    let replay = "theorem replay (edge : Nat) : frameSeq![edge, 2] = [40, edge, 2, 40] := rfl";
    assert_eq!(
        exported
            .check_source_files(
                &[replay.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        1
    );
    assert!(
        exported
            .check_source_files(
                &[replay
                    .replace("[40, edge, 2, 40]", "[99, edge, 2, 99]")
                    .as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
    );
}

#[test]
fn invalid_composed_capture_uses_do_not_fall_back_or_publish_partial_results() {
    let declarations = "syntax \"badCompose!\" term:max : term\n\
        macro_rules | `(badCompose! $x) => `((42 : Nat))\n\
        macro_rules | `(badCompose! $x) => `([0, $x,*])\n";
    assert!(
        check(declarations).is_ok(),
        "an unused translated rule is legal"
    );
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        format!("{declarations}\ndef unpublished : Nat := 3\ndef wrong := badCompose! 4"),
        "macro \"missingSeq!\" : term => `([0, $notBound,*])\ndef wrong := missingSeq!".into(),
        "macro \"badTypeSeq!\" \"[\" xs:term,* \"]\" : term => `([0, $xs,*])\ndef wrong : List Nat := badTypeSeq![true]".into(),
    ] {
        assert!(base.check_source_files(
            &[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits()),
        ).is_err());
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert!(
        check(
            "macro \"goodCompose!\" \"[\" xs:term,* \"]\" : term => `([0, $xs,*])\n\
        theorem recovered : goodCompose![42] = [0, 42] := rfl"
        )
        .is_ok()
    );
}

#[test]
fn variadic_rules_consume_a_head_and_recurse_over_the_remaining_sequence() {
    let source = format!(
        "{SUM}\n\
        theorem empty : sumSeq![] = (0 : Nat) := rfl\n\
        theorem singleton : sumSeq![42] = (42 : Nat) := rfl\n\
        theorem several : sumSeq![10 20 12] = (42 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 3);
    assert!(check(&source.replace("sumSeq![10 20 12] = (42", "sumSeq![10 20 12] = (43")).is_err());
    let source = format!("{SUM}\n#eval sumSeq![10 20 12]");
    let result = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &result.batch.executions.last().unwrap().exit else {
        panic!("native return expected")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("42")
    );
}

#[test]
fn fixed_prefixes_are_checked_before_a_tail_rule_can_override_a_fallback() {
    let source = "syntax \"routeSeq!\" \"[\" num* \"]\" : term\n\
        macro_rules | `(routeSeq![$xs*]) => `((99 : Nat))\n\
        macro_rules | `(routeSeq![1 2 $xs*]) => `((42 : Nat))\n\
        theorem short : routeSeq![1] = (99 : Nat) := rfl\n\
        theorem wrongPrefix : routeSeq![1 3] = (99 : Nat) := rfl\n\
        theorem emptyTail : routeSeq![1 2] = (42 : Nat) := rfl\n\
        theorem fullTail : routeSeq![1 2 3 4] = (42 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 4);
    assert!(check(&source.replace("routeSeq![1 3] = (99", "routeSeq![1 3] = (42")).is_err());
}

#[test]
fn an_unused_variadic_tail_is_not_expanded_but_forwarded_recursion_still_stops() {
    let source = "syntax \"foreverSequence\" : term\n\
        macro_rules | `(foreverSequence) => `(foreverSequence)\n\
        syntax \"firstSeq!\" \"[\" term:max* \"]\" : term\n\
        macro_rules | `(firstSeq![$x:term $rest*]) => `($x)\n\
        theorem kept : firstSeq![42 foreverSequence] = (42 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 1);
    assert!(check(&source.replace("42 foreverSequence", "foreverSequence 42")).is_err());
    let deep = format!("{SUM}\ndef exhausted := sumSeq![{}]", "1 ".repeat(40));
    assert!(
        check(&deep).is_err(),
        "the existing expansion-depth bound must still stop recursion"
    );
    assert!(
        check(&format!(
            "{SUM}\ntheorem recovered : sumSeq![40 2] = (42 : Nat) := rfl"
        ))
        .is_ok()
    );
}

#[test]
fn imported_tail_captures_and_scoped_rules_survive_exact_journal_reentry() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let names = ["Core", "Rules", "Main"].map(|name| Name::from_components([name]));
    let core = SUM.replace('\n', "\r\n");
    let extension = "import Core\nnamespace Extra\n\
        def bias : Nat := 40\n\
        scoped macro_rules | `(sumSeq![4 $tail*]) => `(Nat.add bias (sumSeq![$tail*]))\n\
        end Extra\n";
    let main = "import Rules\ndef bias : Nat := 100\n\
        open scoped Extra in\n\
        theorem activated : sumSeq![4 2] = (42 : Nat) := rfl\n\
        theorem restored : sumSeq![4 2] = (6 : Nat) := rfl\n";
    let sources = [core.as_str(), extension, main];
    let inputs: Vec<_> = names
        .iter()
        .zip(sources)
        .map(|(name, source)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let exported = engine()
        .check_source_modules(
            &inputs,
            &names[2],
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked
        .engine;
    let next = "open scoped Extra in\n\
        theorem replayActive : sumSeq![4 2] = (42 : Nat) := rfl\n\
        theorem replayGlobal : sumSeq![4 2] = (6 : Nat) := rfl";
    assert_eq!(
        exported
            .check_source_files(
                &[next.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .theorems,
        2
    );
    assert!(
        exported
            .check_source_files(
                &[next.replace("(42 : Nat)", "(102 : Nat)").as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}

const SEPARATED_SUM: &str = "syntax \"sumSeparated!\" \"[\" num,* \"]\" : term\n\
    macro_rules\n\
    | `(sumSeparated![]) => `((0 : Nat))\n\
    | `(sumSeparated![$n:num]) => `($n)\n\
    | `(sumSeparated![$n:num, $tail,*]) => `(Nat.add $n (sumSeparated![$tail,*]))\n";

#[test]
fn separated_heads_recurse_over_only_the_remaining_elements() {
    let source = format!(
        "{SEPARATED_SUM}\n\
        theorem zero : sumSeparated![] = (0 : Nat) := rfl\n\
        theorem one : sumSeparated![42] = (42 : Nat) := rfl\n\
        theorem many : sumSeparated![10, 20, 12] = (42 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 3);
    assert!(check(&source.replace("[10, 20, 12] = (42", "[10, 20, 12] = (43")).is_err());
    let result = engine()
        .execute_source_commands_with_checks(
            format!("{SEPARATED_SUM}\n#eval sumSeparated![10, 20, 12]").as_bytes(),
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

#[test]
fn separated_prefixes_preserve_caller_hygiene_and_the_empty_tail_boundary() {
    let source = "syntax \"tailList!\" term:max : term\n\
        macro_rules | `(tailList! $x) => `([(99 : Nat)])\n\
        macro_rules | `(tailList! [0, $xs,*]) => `(let n := 100; [$xs,*])\n\
        theorem caller (n : Nat) : tailList! [0, n, 2] = [n, 2] := rfl\n\
        theorem missingSeparator : tailList! [0] = [99] := rfl\n\
        theorem trailingSeparator : (tailList! [0,] : List Nat) = [] := rfl\n\
        theorem otherPrefix : tailList! [1, 2] = [99] := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 4);
    assert!(check(&source.replace("[1, 2] = [99]", "[1, 2] = [2]")).is_err());
    assert!(
        check(&format!(
            "{source}\ndef illTyped : List Nat := tailList! [0, true]"
        ))
        .is_err()
    );
}

#[test]
fn imported_separated_tail_paths_survive_module_journal_reentry() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let names = ["Sequences", "Main"].map(|name| Name::from_components([name]));
    let sources = [
        SEPARATED_SUM,
        "import Sequences\ntheorem imported : sumSeparated![5, 37] = (42 : Nat) := rfl",
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
    let source = "theorem replayed : sumSeparated![10, 20, 12] = (42 : Nat) := rfl";
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
        1
    );
    assert!(
        imported
            .check_source_files(
                &[source.replace("(42 : Nat)", "(43 : Nat)").as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
    );
}

#[test]
fn scalar_prefix_annotations_still_filter_before_the_sequence_capture() {
    let source = "syntax \"typedHead!\" \"[\" term,* \"]\" : term\n\
        macro_rules | `(typedHead![$xs,*]) => `((99 : Nat))\n\
        macro_rules | `(typedHead![$n:num, $xs,*]) => `((1 : Nat))\n\
        theorem number : typedHead![4, 2] = (1 : Nat) := rfl\n\
        theorem identifier (n : Nat) : typedHead![n, 2] = (99 : Nat) := rfl\n\
        theorem parenthesized : typedHead![(4), 2] = (99 : Nat) := rfl\n\
        theorem missingComma : typedHead![4] = (99 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 4);
    assert!(check(&source.replace("typedHead![n, 2] = (99", "typedHead![n, 2] = (1")).is_err());
}
