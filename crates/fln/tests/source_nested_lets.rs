//! Parse ordinary nested lets, check their lexical scope, then execute natively.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

fn engine() -> (Engine, EngineExecutionLimits) {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    (
        Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
            .unwrap()
            .into_complete()
            .unwrap(),
        limits,
    )
}
fn run(source: &str, expected: &str) -> u64 {
    let (engine, limits) = engine();
    let batch = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits)
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("expected returned value")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}
#[test]
fn lambda_lets_keep_lexical_shadowing_and_initializer_scope() {
    run(
        "def use (x : Nat) : Nat := (fun y => let x := x + y; let y := x + 1; y) 1\n#eval use 40",
        "42",
    );
    run(
        "def use : Nat := (fun x => let x := x + 1; x) 41\n#eval use",
        "42",
    );
}
#[test]
fn local_definitions_are_transparent_to_both_logical_checkers() {
    let (engine, limits) = engine();
    let source = "theorem transparent : (fun x : Nat => let y := x + 1; y) 41 = 42 := by rfl\ntheorem dependent (A : Type) (x : A) : (fun y : A => let B := A; let z : B := y; z) x = x := by rfl";
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(limits.kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
#[test]
fn bindings_compose_in_arguments_records_lists_and_nested_matches() {
    run(
        "structure Box where value : Nat\ndef use : Nat := (fun x => let box : Box := { value := let y := x + 1; y }; box.value) 41\n#eval use",
        "42",
    );
    run(
        "def use : Nat := (fun x => let xs : List Nat := [let y := x + 1; y]; match xs with | [] => 0 | y :: ys => y) 41\n#eval use",
        "42",
    );
    run(
        "def use : Nat := (fun x : Nat => let y := match x with | 0 => 0 | Nat.succ n => n; y + 1) 41\n#eval use",
        "41",
    );
    run(
        "def add (x : Nat) (y : Nat) : Nat := x + y\n#eval add (let x := 40; x) (let y := 2; y)",
        "42",
    );
}
#[test]
fn ordinary_lambda_let_syntax_returns_owned_multistage_callbacks() {
    run(
        "structure Box where value : Nat\ndef use (offset : Nat) : Nat :=\n  let f : Nat -> Nat -> Nat -> Box := (fun x => let a := offset + x; fun y => let b := a + y; fun z => Box.mk (b + z))\n  let g := f 1\n  let h := g 2\n  let result := h 3\n  result.value\n#eval use 36",
        "42",
    );
}
#[test]
fn multiline_lambdas_preserve_nested_initializer_boundaries() {
    run(
        "def use (offset : Nat) : Nat :=\n  let f : Nat -> Nat := (fun x =>\n    let y :=\n      let z := x + offset\n      z\n    let h : y = y := by\n      rfl\n    y)\n  f 2\n#eval use 40",
        "42",
    );
}
#[test]
fn nested_invalid_annotations_values_and_evidence_are_not_discarded() {
    let (engine, limits) = engine();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for tail in [
        "let y : Nat := \"bad\"; x",
        "let y : (Type : Nat) := Nat; x",
        "let h : False := (by rfl); x",
        "let y := missing; x",
        "let y := y; x",
    ] {
        let source = format!("def use : Nat := (fun x : Nat => {tail}) 42\n#eval use");
        assert!(
            engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits)
                .is_err(),
            "{source}"
        );
        assert_eq!(root, engine.logical_root(&options));
    }
    run(
        "def use : Nat := (fun x : Nat => let y := x; y) 42\n#eval use",
        "42",
    );
}

#[test]
fn unused_values_stay_strict_but_nested_evidence_is_erased_after_checking() {
    let slow = "def slow (n : Nat) : Nat := match n with | 0 => 0 | Nat.succ k => slow k + 1\n";
    let strict = |n| {
        run(
            &format!(
                "{slow}def use (n : Nat) : Nat := (fun x : Nat => let unused := slow n; x) 42\n#eval use {n}"
            ),
            "42",
        )
    };
    let used = |n| {
        run(
            &format!(
                "{slow}def use (n : Nat) : Nat := (fun x : Nat => let a := slow n; x + a - a) 42\n#eval use {n}"
            ),
            "42",
        )
    };
    let erased = |n| {
        run(
            &format!(
                "{slow}def use (n : Nat) : Nat := (fun x : Nat => let h : True := (let expensive := slow n; True.intro); x) 42\n#eval use {n}"
            ),
            "42",
        )
    };
    let delta = strict(20) - strict(0);
    assert!(delta > 0);
    assert_eq!(delta, used(20) - used(0));
    assert_eq!(erased(0), erased(20));
}
