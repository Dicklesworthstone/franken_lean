//! Generalized field notation elaborates ordinary applications through both
//! admission seats; it grants no extra authority to methods or projections.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, Outcome,
    SourceCheckLimits, VmExit,
};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn check(source: &str) {
    let result = engine().check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{source}\n{result:?}"
    );
}

#[test]
fn collections_resolve_methods_and_insert_the_receiver_after_function_arguments() {
    check(
        "def size.{u} {A : Type u} (xs : List A) : Nat := xs.length\n\
         theorem length : size [1, 2, 3] = 3 := by rfl\n\
         theorem mapped : (([1, 2, 3]).map (fun n => n + 1)).length = 3 := by rfl\n\
         theorem folded : ([1, 2, 3]).foldr (fun n acc => n + acc) 0 = 6 := by rfl\n\
         theorem string : (\"hello\").length = String.length \"hello\" := by rfl",
    );
}

#[test]
fn proof_methods_use_the_receivers_actual_dependent_type() {
    check(
        "theorem reverse.{u} {A B : Sort u} {a : A} {b : B} (h : HEq a b) : HEq b a := h.symm\n\
         theorem chain.{u} {A B C : Sort u} {a : A} {b : B} {c : C}\n\
           (h : HEq a b) (k : HEq b c) : HEq a c := h.trans k\n\
         theorem Eq.reverse.{u} {A : Sort u} {a b : A} (h : a = b) : b = a := by cases h; rfl\n\
         theorem equality.{u} {A : Sort u} {a b : A} (h : a = b) : b = a := h.reverse",
    );
}

#[test]
fn partial_methods_eta_expand_only_independent_missing_arguments() {
    check(
        "def Nat.tagged (flag : Bool) (self : Nat) : Nat := if flag then self else 0\n\
         def deferred (n : Nat) : Bool -> Nat := n.tagged\n\
         theorem selected : deferred 42 true = 42 := by rfl\n\
         theorem named : (42).tagged (flag := true) = 42 := by rfl\n\
         def choose : (Nat -> Nat) -> List Nat := ([1, 2]).map\n\
         theorem chosen : (choose (fun n => n + 1)).length = 2 := by rfl\n\
         def postponed.{u,v} {A : Type u} {B : Type v} (xs : List A) : (A -> B) -> List B := xs.map\n\
         structure Indexed (n : Nat) where\n  value : Nat\n\
         def Indexed.read (n : Nat) (self : Indexed n) : Nat := self.value\n\
         theorem inferred (x : Indexed 3) : x.read = x.value := by rfl",
    );
}

#[test]
fn first_matching_parameter_and_explicit_or_named_insertion_follow_the_telescope() {
    check(
        "def Nat.second (ignored self : Nat) : Nat := self\n\
         theorem first : (1).second 2 = 2 := by rfl\n\
         theorem supplied : (1).second (ignored := 2) = 1 := by rfl\n\
         def Nat.weighted (x y z : Nat) : Nat := x + 10 * y + 100 * z\n\
         theorem named_position : (2).weighted (x := 1) 3 = 321 := by rfl\n\
         def Nat.hidden {self : Nat} (flag : Bool) : Nat := if flag then self else 0\n\
         theorem hidden : (42).hidden true = 42 := by rfl\n\
         def Nat.repeated (x : Bool) (x : Nat) : Nat := x\n\
         theorem positional : (42).repeated true = 42 := by rfl\n\
         def Function.twice (f : Nat -> Nat) (n : Nat) : Nat := f (f n)\n\
         theorem function (f : Nat -> Nat) (n : Nat) : f.twice n = f (f n) := by rfl",
    );
}

#[test]
fn record_projections_aliases_and_method_namespaces_keep_their_priority() {
    check(
        "structure Point where\n  x : Nat\n  y : Nat\n\
         def Point.sum (p : Point) : Nat := p.x + p.y\n\
         structure Outer where\n  point : Point\n\
         theorem nested (p : Outer) : p.point.sum = p.point.x + p.point.y := by rfl\n\
         def Alias := Nat\n\
         def Alias.double (n : Alias) : Nat := n + n\n\
         theorem alias (n : Alias) : n.double = n + n := by rfl\n\
         def PointAlias := Point\n\
         def PointAlias.x (p : PointAlias) : Nat := 99\n\
         theorem alias_namespace (p : PointAlias) : p.x = 99 := by rfl\n\
         def SecondAlias := PointAlias\n\
         theorem intermediate_namespace (p : SecondAlias) : p.x = 99 := by rfl\n\
         class Factory where\n  carrier : Type\n  produce : carrier\n\
         instance aliasFactory : Factory := { carrier := SecondAlias, produce := { x := 2, y := 3 } }\n\
         def make [factory : Factory] : factory.carrier := factory.produce\n\
         theorem projected_alias : make.x = 99 := by rfl\n\
         def Shadow.List.length (xs : List Nat) : Nat := 99\n\
         namespace Shadow\n\
         theorem namespace_priority : ([1, 2]).length = 2 := by rfl\n\
         end Shadow",
    );
}

#[test]
fn invalid_receivers_do_not_select_later_parameters_or_publish_a_prefix() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def Nat.repeated (x : Bool) (x : Nat) : Nat := x\ndef bad : Bool -> Nat := (42).repeated",
        "def Nat.foreign (x : Bool) : Nat := 0\ndef bad (n : Nat) : Nat := n.foreign true",
        "structure Box (A : Type) where\n  value : A\ndef Box.take (x : Box Nat) (y : Box Bool) : Bool := y.value\ndef bad (x : Box Nat) (y : Box Bool) : Bool := y.take x",
        "def bad (xs : List Nat) : Nat := xs.nonexistent",
        "def bad (n : Nat) : Nat := n.succ true",
        "def bad (n : Nat) : Nat := n.«succ.extra»",
    ] {
        let result = base.check_source_files(&[source.as_bytes()], &options, limits());
        assert!(
            !matches!(result, Ok(Outcome::Complete(_))),
            "{source}\n{result:?}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check("theorem repaired : (41).succ = 42 := by rfl");
}

#[test]
fn methods_execute_through_the_same_compiler_and_vm() {
    let source = b"def bump (xs : List Nat) : List Nat := xs.map (fun n => n + 1)\n#eval (([1, 2, 3]).map (fun n => n + 1)).foldr (fun n acc => n + acc) 0\n#eval (\"hello\").length";
    let result = engine()
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.executions.len() >= 2);
    for (execution, expected) in result.executions.iter().rev().zip(["5", "9"]) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("VM result")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
