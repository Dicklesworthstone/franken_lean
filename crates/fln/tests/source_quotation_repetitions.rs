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
        "syntax \"mixed!\" \"[\" term,* \"]\" : term\nmacro_rules | `(mixed![0, $xs,*]) => `([$xs,*])\ndef wrong := mixed![0, 1]",
        "syntax \"bracketed!\" \"[\" term,* \"]\" : term\nmacro_rules | `(bracketed![$[$x],*]) => `([$x,*])\ndef wrong := bracketed![1]",
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
