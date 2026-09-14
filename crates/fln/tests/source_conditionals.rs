//! Every conditional arm remains an ordinary, independently checked core term.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
        "{source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
#[test]
fn boolean_conditionals_compute_and_compare_without_evaluating_source() {
    check(
        "def choose (b : Bool) : Nat := if b then 7 else 9\n theorem t : choose true = 7 := by rfl\n theorem f : choose false = 9 := by rfl\n def compared (n : Nat) : Nat := if n == 3 then 17 else 19\n theorem eq : compared 3 = 17 := by rfl\n theorem ne : compared 4 = 19 := by rfl",
    );
}
#[test]
fn nested_conditionals_preserve_dangling_else_and_arithmetic_precedence() {
    check(
        "def nested (a b : Bool) : Nat := if a then if b then 1 else 2 else if b then 3 else 4\n theorem a : nested true false = 2 := by rfl\n theorem b : nested false true = 3 := by rfl\n def condition : Nat := if (if true then false else true) then 0 else 9 + 3 * 2\n theorem c : condition = 15 := by rfl",
    );
}
#[test]
fn conditional_and_match_plans_share_nested_scopes() {
    check(
        "def f (b c : Bool) : Nat := if b then match c with | true => 1 | false => 2 else 3\n theorem t : f true false = 2 := by rfl\n def g (b c : Bool) : Nat := match b with | true => if c then 4 else 5 | false => 6\n theorem u : g true false = 5 := by rfl\n def q : Nat := if match false with | true => true | false => false then 0 else 7\n theorem v : q = 7 := by rfl",
    );
}
#[test]
fn conditionals_are_higher_order_arguments_and_local_values() {
    check(
        "def apply (f : Nat -> Nat) (n : Nat) : Nat := f n\n def f (b : Bool) : Nat := apply (if b then fun x => x + 1 else fun y => y + 2) 8\n theorem t : f false = 10 := by rfl\n def local : Nat := by\n let n := if true then 7 else 8\n exact n\n theorem u : local = 7 := by rfl",
    );
}
#[test]
fn branches_can_use_let_telescopes_and_nested_proofs() {
    check(
        "def local (b : Bool) : Nat := if b then let x := 5; x + 1 else let y := 7; y + 1\n theorem t : local false = 8 := by rfl\n theorem proof (b : Bool) : 0 = 0 := if b then by rfl else by rfl",
    );
}
#[test]
fn all_branches_and_conditions_keep_type_obligations() {
    for source in [
        "def bad : Nat := if true then 1 else \"wrong\"",
        "def bad : Nat := if (1 : Bool) then 7 else 8",
        "def bad : Nat := if true then 1 else let unused : String := 1; 0",
        "theorem bad : 0 = 1 := if true then by rfl else by rfl",
        "def bad (b : Bool) : Nat := if b then let local := 5; local else local",
        "def bad (n : Nat) : Nat := if true then 0 else bad n",
    ] {
        reject(source);
    }
}
#[test]
fn conditional_types_and_refined_values_share_boolean_indices() {
    check(
        "def Ty (b : Bool) : Type := if b then Nat else String\n def val (b : Bool) : Ty b := match b with | true => 7 | false => \"text\"\n theorem t : val true = 7 := by rfl\n theorem f : val false = \"text\" := by rfl",
    );
}
#[test]
fn conditional_branches_can_recurse_on_real_constructor_children() {
    check(
        "def count (n : Nat) (b : Bool) : Nat := match n with | .zero => 0 | .succ k => if b then count k b + 1 else count k b + 2\n theorem t : count 3 true = 3 := by rfl\n theorem f : count 3 false = 6 := by rfl",
    );
}
#[test]
fn checked_example_contains_generic_proofs_and_recursive_computations() {
    check(include_str!("../../../examples/native_conditionals.lean"));
}
#[test]
fn nested_conditionals_in_tactic_alternatives_do_not_escape() {
    check(
        "theorem t : 0 = 0 := by\n first\n | exact if true then (1 : String) else \"bad\"\n | exact if false then rfl else rfl",
    );
    reject("def t : Nat := if true then let private := 7; private else private");
}
