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

#[test]
fn proposition_conditions_use_checked_decision_dictionaries() {
    check(
        r#"
        theorem yes : (if True then 7 else 9) = 7 := by rfl
        theorem no : (if False then 7 else 9) = 9 := by rfl
        theorem negated : (if Not False then 11 else 13) = 11 := by rfl
        theorem nested : (if (if true then True else False) then 17 else 19) = 17 := by rfl
        def choose (p : Prop) [Decidable p] (yes no : Nat) : Nat := if p then yes else no
        theorem applied : choose (Not True) 7 23 = 23 := by rfl
    "#,
    );
}

#[test]
fn named_proposition_branches_receive_opposite_checked_evidence() {
    check(
        r#"
        def inspect (p : Prop) [Decidable p] (yes : p -> Nat) (no : Not p -> Nat) : Nat :=
          if h : p then yes h else no h
        theorem positive : inspect True (fun h => 7) (fun h => 9) = 7 := by rfl
        theorem negative : inspect False (fun h => 7) (fun h => 9) = 9 := by rfl
        theorem proof (p : Prop) [Decidable p] (hp : p) : p :=
          if h : p then h else by contradiction
        def shadow (h : Nat) (p : Prop) [Decidable p] : Nat :=
          (if h : p then 1 else 2) + h
        theorem scoped : shadow 3 True = 4 := by rfl
    "#,
    );
}

#[test]
fn named_conditionals_capture_refinement_holes_in_separate_scopes() {
    check(
        r#"
        theorem supplied (p : Prop) [Decidable p] (hp : p) : p := by
          refine if evidence : p then ?_ else ?_
          · exact evidence
          · exact hp
        theorem recovered (p : Prop) [Decidable p] (hp : p) : p := by
          first
          | exact if h : p then (1 : String) else "invalid"
          | exact if h : p then h else hp
    "#,
    );
}

#[test]
fn proposition_conditions_support_types_methods_and_nested_patterns() {
    check(
        r#"
        def Carrier : Type := if False then String else Nat
        def inhabitant : Carrier := 31
        theorem computed : inhabitant = 31 := by rfl
        def callback : Nat -> Nat := if True then fun n => n + 1 else fun n => n + 2
        theorem function_result : callback 7 = 8 := by rfl
        structure Operation where
          run : Nat -> Nat
        def operation : Operation := { run := if h : True then fun n => n + 2 else fun n => n }
        theorem method : operation.run 9 = 11 := by rfl
        def mixed (b : Bool) : Nat := if h : True then match b with | true => 17 | false => 19 else 0
        theorem nested : mixed false = 19 := by rfl
    "#,
    );
}

#[test]
fn recursive_calls_survive_proposition_branches() {
    check(
        r#"
        def count (n : Nat) (p : Prop) [Decidable p] : Nat := match n with
          | .zero => 0
          | .succ k => if h : p then count k p + 1 else count k p + 2
        theorem yes : count 3 True = 3 := by rfl
        theorem no : count 3 False = 6 := by rfl
    "#,
    );
    reject(
        "def bad (n : Nat) : Nat := match n with | .zero => 0 | .succ k => if False then bad n else 0",
    );
}

#[test]
fn propositions_do_not_invent_decisions_or_erase_branch_obligations() {
    for source in [
        "def bad (p : Prop) : Nat := if p then 1 else 2",
        "def bad : Nat := if True then 1 else \"wrong\"",
        "def bad : Nat := if True then 1 else let unused : String := 1; 0",
        "theorem bad : False := if h : False then h else True.intro",
        "def bad : Nat := if h : True then 1 else h",
        "def bad : Nat := (if h : True then 1 else 2) + h",
        "def bad : Nat := if Nat then 1 else 2",
        "def bad : Nat := let d : Decidable False := Decidable.isTrue True.intro; if False then 1 else 2",
        "def bad : Nat := if (if true then True else (1 : Prop)) then 1 else 2",
    ] {
        reject(source);
    }
}

#[test]
fn installed_proposition_conditional_example_checks() {
    check(include_str!(
        "../../../examples/native_proposition_conditionals.lean"
    ));
}
