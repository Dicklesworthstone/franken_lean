//! Single variable-length slices with fixed syntax on both sides.
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
fn nat_result(source: &str) -> String {
    let batch = engine()
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let fln::VmExit::Returned(result) = &batch.batch.executions.last().unwrap().exit else {
        panic!("expected a native return");
    };
    fln_vm::interpreter::nat_decimal(&result.value).unwrap()
}

const SUM: &str = "syntax \"sliceSum!\" \"[\" num* \"]\" : term\n\
    macro_rules\n\
    | `(sliceSum![]) => `((0 : Nat))\n\
    | `(sliceSum![$n:num $tail*]) => `(Nat.add $n (sliceSum![$tail*]))\n";

#[test]
fn a_middle_capture_checks_both_ends_and_can_be_empty() {
    let source = format!(
        "{SUM}\nsyntax \"middleSum!\" \"[\" num* \"]\" : term\n\
        macro_rules | `(middleSum![$all*]) => `((99 : Nat))\n\
        macro_rules | `(middleSum![0 $xs* 9]) => `(sliceSum![$xs*])\n\
        theorem empty : middleSum![0 9] = (0 : Nat) := rfl\n\
        theorem full : middleSum![0 10 20 12 9] = (42 : Nat) := rfl\n\
        theorem short : middleSum![0] = (99 : Nat) := rfl\n\
        theorem wrongHead : middleSum![1 42 9] = (99 : Nat) := rfl\n\
        theorem wrongEnd : middleSum![0 42 8] = (99 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 5);
    assert!(check(&source.replace("[0 10 20 12 9] = (42", "[0 10 20 12 9] = (43")).is_err());
    assert_eq!(
        nat_result(&format!("{source}\n#eval middleSum![0 10 20 12 9]")),
        "42"
    );
}

#[test]
fn captures_after_a_slice_follow_actual_positions_and_scalar_kind_checks() {
    let source = "syntax \"lastIdent!\" \"[\" term:max* \"]\" : term\n\
        macro_rules | `(lastIdent![$all*]) => `((7 : Nat))\n\
        macro_rules | `(lastIdent![$xs* $last:ident]) => `($last)\n\
        theorem last (a b c : Nat) : lastIdent![a b c] = c := rfl\n\
        theorem one (a : Nat) : lastIdent![a] = a := rfl\n\
        theorem numLast (a : Nat) : lastIdent![a 42] = (7 : Nat) := rfl\n\
        theorem empty : lastIdent![] = (7 : Nat) := rfl\n\
        syntax \"rotateSeq!\" \"[\" num* \"]\" : term\n\
        macro_rules | `(rotateSeq![$first:num $xs* $last:num]) => `(Nat.add $first $last)\n\
        theorem ends : rotateSeq![10 100 200 32] = (42 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 5);
    assert!(check(&source.replace("lastIdent![a b c] = c", "lastIdent![a b c] = b")).is_err());
    assert!(check(&source.replace("lastIdent![a 42] = (7", "lastIdent![a 42] = (42")).is_err());
}

#[test]
fn separated_middle_slices_retain_exact_element_separator_boundaries() {
    let source = "syntax \"middleList!\" term:max : term\n\
        macro_rules | `(middleList! $x) => `([(99 : Nat)])\n\
        macro_rules | `(middleList! [0, $xs,*, 9]) => `([$xs,*])\n\
        theorem middle : middleList! [0, 10, 20, 12, 9] = [10, 20, 12] := rfl\n\
        theorem short : middleList! [0, 9] = [99] := rfl\n\
        theorem badEnd : middleList! [0, 42, 8] = [99] := rfl\n\
        syntax \"lastList!\" term:max : term\n\
        macro_rules | `(lastList! $x) => `((7 : Nat))\n\
        macro_rules | `(lastList! [$xs,*, $last:num]) => `($last)\n\
        theorem actualLast : lastList! [10, 20, 42] = (42 : Nat) := rfl\n\
        theorem noSeparator : lastList! [42] = (7 : Nat) := rfl\n\
        theorem notScalar : lastList! [1, true] = (7 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 6);
    assert!(check(&source.replace("[10, 20, 12] := rfl", "[10, 20, 12, 9] := rfl")).is_err());
    assert_eq!(
        nat_result(&format!("{source}\n#eval lastList! [10, 20, 42]")),
        "42"
    );
}

#[test]
fn nested_suffix_patterns_keep_relative_capture_paths_and_hygiene() {
    let source = "syntax \"nestedEnd!\" \"[\" term:max* \"]\" : term\n\
        macro_rules | `(nestedEnd![$all*]) => `((7 : Nat))\n\
        macro_rules | `(nestedEnd![$xs* (Nat.add $a $b)]) => `(Nat.add $a $b)\n\
        theorem nested (a b c : Nat) : nestedEnd![a c (Nat.add a b)] = Nat.add a b := rfl\n\
        theorem noPrefix (a b : Nat) : nestedEnd![(Nat.add a b)] = Nat.add a b := rfl\n\
        theorem mismatch : nestedEnd![1 (Nat.mul 6 7)] = (7 : Nat) := rfl\n\
        syntax \"hygienicEnd!\" \"[\" term:max* \"]\" : term\n\
        macro_rules | `(hygienicEnd![$xs* $last:term]) => `(let x := 99; $last)\n\
        theorem capture (x : Nat) : hygienicEnd![1 2 x] = x := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 4);
    assert!(
        check(&source.replace(
            "hygienicEnd![1 2 x] = x",
            "hygienicEnd![1 2 x] = (99 : Nat)"
        ))
        .is_err()
    );
}

#[test]
fn distinct_sequence_slices_can_feed_one_composed_template() {
    let source = format!(
        "{SUM}\nsyntax \"joinMiddle!\" \"[\" num* \"]\" \"[\" num* \"]\" : term\n\
        macro_rules | `(joinMiddle![0 $xs* 9][1 $ys* 8]) => `(sliceSum![$xs* $ys*])\n\
        theorem empty : joinMiddle![0 9][1 8] = (0 : Nat) := rfl\n\
        theorem combined : joinMiddle![0 10 20 9][1 12 8] = (42 : Nat) := rfl"
    );
    assert_eq!(check(&source).unwrap_or_else(|e| panic!("{e}")).theorems, 2);
    assert_eq!(
        nat_result(&format!("{source}\n#eval joinMiddle![0 10 20 9][1 12 8]")),
        "42"
    );
}

#[test]
fn imported_scoped_suffix_paths_replay_from_the_pattern_not_a_fixed_index() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Name, SourceModuleInput};
    let library = "syntax \"scopedLast!\" \"[\" term:max* \"]\" : term\r\n\
        macro_rules | `(scopedLast![$xs*]) => `((7 : Nat))\r\n\
        namespace Picks\r\ndef bias : Nat := 2\r\n\
        scoped macro_rules | `(scopedLast![$xs* $last:term]) => `(Nat.add bias $last)\r\n\
        end Picks\r\n";
    let main = "import Library\ndef bias : Nat := 100\n\
        open scoped Picks in\n\
        theorem active : scopedLast![1 2 40] = (42 : Nat) := rfl\n\
        theorem restored : scopedLast![1 2 40] = (7 : Nat) := rfl";
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
    let replay = "open scoped Picks in\n\
        theorem replay (x : Nat) : scopedLast![3 4 5 x] = Nat.add 2 x := rfl\n\
        theorem inactive : scopedLast![3 4 5 40] = (7 : Nat) := rfl";
    assert_eq!(
        exported
            .check_source_files(
                &[replay.as_bytes()],
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
                &[replay.replace("Nat.add 2 x", "Nat.add 100 x").as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}

#[test]
fn discarded_middle_arguments_stay_unexpanded_and_invalid_matches_do_not_fall_back() {
    let source = "syntax \"loopSlice\" : term\n\
        macro_rules | `(loopSlice) => `(loopSlice)\n\
        syntax \"dropMiddle!\" \"[\" term:max* \"]\" : term\n\
        macro_rules | `(dropMiddle![0 $xs* $last:term]) => `($last)\n\
        theorem discarded : dropMiddle![0 loopSlice 42] = (42 : Nat) := rfl";
    assert_eq!(check(source).unwrap_or_else(|e| panic!("{e}")).theorems, 1);
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        source.replace("0 loopSlice 42", "0 42 loopSlice"),
        "syntax \"badSlice!\" \"[\" term:max* \"]\" : term\n\
         macro_rules | `(badSlice![$all*]) => `((42 : Nat))\n\
         macro_rules | `(badSlice![$xs* $last:term]) => `(Nat.add $last true)\n\
         def prefix : Nat := 3\ndef refused : Nat := badSlice![1 2 40]"
            .into(),
        "syntax \"ambiguousSlice!\" \"[\" num* \"]\" : term\n\
         macro_rules | `(ambiguousSlice![$xs* 0 $ys*]) => `((42 : Nat))\n\
         def refused := ambiguousSlice![1 0 2]"
            .into(),
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .unwrap()
        .into_complete()
        .is_ok()
    );
}
