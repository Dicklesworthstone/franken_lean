//! Native source do -> typeclass elaboration -> both ordinary checkers.
#![forbid(unsafe_code)]
#[path = "source_do/for_loops.rs"]
mod for_loops;
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn engine() -> Engine {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    checked(
        &seed,
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
instance idOfNat {A : Type} {n : Nat} [inst : OfNat A n] : OfNat (Id A) n := inst
"#,
    )
}
/// A `do` `if` with `else if` clauses (the pin's `doIf` clause list) means the nested `if` in
/// its `else`: `de1 1` takes the second branch and `de1 7` the last, and a wrong value is refused.
#[test]
fn do_else_if_clauses_are_the_nested_conditionals() {
    let base = engine();
    let de1 = "def de1 (n : Nat) : Id Nat := do\n  if n = 0 then\n    return 1\n  \
               else if n = 1 then\n    return 2\n  else\n    return 3\n";
    checked(
        &base,
        &format!("{de1}theorem de1_one : de1 1 = 2 := by rfl\ntheorem de1_two : de1 7 = 3 := by rfl\n"),
    );
    let source = format!("{de1}theorem de1_wrong : de1 1 = 3 := by rfl\n");
    assert!(
        !matches!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}
/// `let x ← if …` and `let x ← match …` bind a do element (`leftArrow doElemParser`), which the
/// pin compiles as the nested sequence `let x ← do if …`: the branches are do sequences in the
/// surrounding control scope, so a `return` in a branch returns from the function (`ae5 true` is
/// `5`, never `15`). A nested action `(← if …)` is still refused; `bif` is a term and binds.
#[test]
fn if_and_match_after_an_arrow_bind_do_elements() {
    let base = engine();
    checked(
        &base,
        "def ae1 (c : Bool) : Id Nat := do\n  let x ← if c then (1 : Id Nat) else (2 : Id Nat)\n  return x\n\
         theorem ae1_t : ae1 true = 1 := by rfl\ntheorem ae1_f : ae1 false = 2 := by rfl\n\
         def ae2 (o : Option Nat) : Id Nat := do\n  let x ← match o with\n    | Option.some _ => (3 : Id Nat)\n    | Option.none => (0 : Id Nat)\n  return x\n\
         theorem ae2_s : ae2 (Option.some 7) = 3 := by rfl\ntheorem ae2_n : ae2 Option.none = 0 := by rfl\n\
         def ae5 (c : Bool) : Id Nat := do\n  let x ← if c then return 5 else (1 : Id Nat)\n  return x + 10\n\
         theorem ae5_t : ae5 true = 5 := by rfl\ntheorem ae5_f : ae5 false = 11 := by rfl\n",
    );
    for source in [
        "def ae1 (c : Bool) : Id Nat := do\n  let x ← if c then (1 : Id Nat) else (2 : Id Nat)\n  return x\n\
         theorem ae1_wrong : ae1 true = 2 := by rfl\n",
        "def ae5 (c : Bool) : Id Nat := do\n  let x ← if c then return 5 else (1 : Id Nat)\n  return x + 10\n\
         theorem ae5_wrong : ae5 true = 15 := by rfl\n",
        "def ae3 (c : Bool) : Id Nat := do\n  let x := (← if c then (1 : Id Nat) else (2 : Id Nat))\n  return x\n",
    ] {
        assert!(
            !matches!(
                base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
    checked(
        &base,
        "def cond {α : Type} (c : Bool) (x y : α) : α :=\n  match c with\n  | true => x\n  | false => y\n\
         def ae4 (c : Bool) : Id Nat := do\n  let x ← bif c then (1 : Id Nat) else (2 : Id Nat)\n  return x\n\
         theorem ae4_true : ae4 true = 1 := by rfl\n",
    );
}
/// A do-level `have` (`doHave`) is the term `have` over the rest of the block: the hypothesis is
/// in scope there and the block's value is unchanged; `have` binds with `:=` only.
#[test]
fn do_level_have_scopes_over_the_rest_of_the_block() {
    let base = engine();
    let hv = "def hv (n : Nat) : Id Nat := do\n  have h : n = n := rfl\n  have : n + 1 = n + 1 := rfl\n  return (n + 1)\n";
    checked(&base, &format!("{hv}theorem hv_val : hv 4 = 5 := by rfl\n"));
    for source in [
        format!("{hv}theorem hv_wrong : hv 4 = 4 := by rfl\n"),
        "def hv_arrow (n : Nat) : Id Nat := do\n  have h ← (n : Id Nat)\n  return h\n".to_string(),
    ] {
        assert!(
            !matches!(
                base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}
/// A pattern's update `(a, b) := e` parses as the pin's `doReassign` of a `letPatDecl`; the
/// elaborator refuses reassignment, as it refuses `x := e`, after parsing.
#[test]
fn pattern_reassignment_is_refused_after_parsing() {
    let source = "def tr (n : Nat) : Id Nat := do\n  let mut a := 0\n  let mut b := 0\n  (a, b) := (n, n)\n  return a\n";
    match engine().check_source_files(&[source.as_bytes()], &KVMap::new(), limits()) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}
/// A `while` loop parses as the pin's `doWhile`; the elaborator does not lower it (the pin's macro
/// is `repeat if c then s else break`), so it refuses the definition after parsing.
#[test]
fn while_loops_are_refused_after_parsing() {
    let source = "def wl (n : Nat) : Id Nat := do\n  let mut i := 0\n  while i < n do\n    i := i + 1\n  return i\n";
    match engine().check_source_files(&[source.as_bytes()], &KVMap::new(), limits()) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}
#[test]
fn named_binds_pure_lets_and_returns_are_council_checked() {
    checked(
        &engine(),
        r#"
def work : Id Nat := do
  let a ← (7 : Id Nat)
  let b : Nat := a + 1
  return b
theorem value : work = 8 := by rfl
"#,
    );
}
#[test]
fn abstract_monads_use_local_dictionary_parameters() {
    checked(
        &engine(),
        r#"
def map {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)
def seq {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (x : M A) (y : M B) : M B := do
  let ignored ← x
  y
"#,
    );
}

#[test]
fn direct_dictionary_calls_are_the_same_elaboration_path() {
    checked(
        &engine(),
        r#"
def mapping {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (f : A -> B) (action : M A) : M B := Bind.bind (m := M) action (fun x => Pure.pure (f x))
"#,
    );
}

#[test]
fn nested_do_and_shadowing_preserve_their_own_result_monads() {
    checked(
        &engine(),
        r#"
def nested : Id Nat := do
  let n : Nat ← (do
    let n ← (7 : Id Nat)
    return (n + 1))
  let n ← (n + 2 : Id Nat)
  return n
theorem nestedValue : nested = 10 := by rfl
def privateBind (bind : Nat) : Id Nat := do
  let x ← (bind : Id Nat)
  let ignored ← (1 : Id Nat)
  return x
theorem scopeValue : privateBind 7 = 7 := by rfl
"#,
    );
}

#[test]
fn state_actions_are_sequential_and_run_exactly_once() {
    checked(
        &engine(),
        r#"
structure Result (A : Type) where
  value : A
  state : Nat
def State (A : Type) : Type := Nat -> Result A
instance statePure : Pure State := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : Result A) (next : A -> State B) : Result B := next r.value r.state
instance stateBind : Bind State := { bind := fun action next state => stateNext (action state) next }
def mark (n : Nat) : State Nat := fun s => { value := s, state := s * 10 + n }
def program : State Nat := do
  let x ← mark 1
  let y ← mark 2
  return (x * 100 + y)
theorem stateOrder : (program 0).state = 12 := by rfl
theorem stateValue : (program 0).value = 1 := by rfl
"#,
    );
}

#[test]
fn failing_monadic_actions_do_not_run_the_continuation() {
    checked(
        &engine(),
        r#"
inductive Maybe (A : Type) where
  | none
  | some (value : A)
def maybeBind {A B : Type} (action : Maybe A) (next : A -> Maybe B) : Maybe B :=
  match action with
  | Maybe.none => Maybe.none
  | Maybe.some value => next value
instance maybePure : Pure Maybe := { pure := fun value => Maybe.some value }
instance maybeBinder : Bind Maybe := { bind := fun action next => maybeBind action next }
def failure : Maybe Nat := do
  let x ← (Maybe.none : Maybe Nat)
  return (x + 1)
def success : Maybe Nat := do
  let x ← Maybe.some 41
  return (x + 1)
theorem failed : failure = Maybe.none := by rfl
theorem succeeded : success = Maybe.some 42 := by rfl
"#,
    );
}

#[test]
fn discarded_polymorphic_actions_receive_the_unit_result_type() {
    let base = checked(
        &engine(),
        r#"
inductive Maybe (A : Type) where
  | none
  | some (value : A)
def maybeBind {A B : Type} (action : Maybe A) (next : A -> Maybe B) : Maybe B :=
  match action with
  | .none => Maybe.none
  | .some value => next value
instance maybePure : Pure Maybe := { pure := fun value => Maybe.some value }
instance maybeBinder : Bind Maybe := { bind := fun action next => maybeBind action next }
"#,
    );
    // The only difference is the ignored action's explicit element type.
    // Ordinary statement sequencing must supply that same unit constraint.
    checked(
        &base,
        "def annotated : Maybe Nat := do\n  (Maybe.none : Maybe PUnit)\n  return 42",
    );
    checked(
        &base,
        r#"
def discarded : Maybe Nat := do
  Maybe.none
  return 42
theorem discardedValue : discarded = Maybe.none := by rfl
"#,
    );
}

#[test]
fn invalid_actions_missing_dictionaries_and_scope_escapes_preserve_the_engine() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad {M : Type -> Type} {A : Type} (x : A) : M A := do return x",
        "def bad {M : Type -> Type} [Pure M] {A : Type} (action : M A) : M A := do let x ← action; return x",
        "def bad : Id Nat := do let x ← (true : Id Bool); return x",
        "def bad : Id Nat := do let x : Bool ← (7 : Id Nat); return 0",
        "def bad : Id Nat := do let x ← x; return x",
        "def bad : Id Nat := do let n ← (do let hidden := 7; return hidden); return hidden",
        "def bad (P : Prop) : Id Nat := do let unused : P := 0; return 7",
        "def bad : Id Nat := do return 7; return 8",
        "def bad : Id Nat := do (7 : Id Nat); return 8",
        "def bad : Id Nat := do _; return 8",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : Id Nat := do return 42");
}

#[test]
fn ordinary_conditional_and_match_terms_remain_inside_do_actions() {
    checked(
        &engine(),
        r#"
def conditional : Id Nat := do
  let x ← ((if true then 7 else 8) : Id Nat)
  return (x + 1)
theorem conditionalValue : conditional = 8 := by rfl
def matched : Id Nat := do
  let x ← ((match true with | true => 7 | false => 8) : Id Nat)
  return (x + 1)
theorem matchedValue : matched = 8 := by rfl
"#,
    );
}

#[test]
fn do_programs_execute_through_golem() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = "def runDo : Id Nat := do let x ← (17 : Id Nat); return (x + 25)\n#eval runDo";
    let result = engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("not returned")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}

#[test]
fn constructor_match_branches_preserve_reader_and_identity_monads() {
    use fln::{EngineExecutionLimits, VmExit};
    let source = r#"
def Reader (A : Type) : Type := Nat -> A
instance readerPure : Pure Reader := { pure := fun x r => x }
instance readerBind : Bind Reader := { bind := fun action next r => next (action r) r }
def ask : Reader Nat := fun r => r
def selected (flag : Bool) : Reader Nat :=
  match flag with
  | true => do
    let n ← ask
    return (n + 2)
  | false => do return 7
def nested (flag : Bool) : Id Nat :=
  match flag with
  | true => do
    let n : Nat ← (do return (40 : Nat))
    return (n + 2)
  | false => do return 7
theorem readerBranch : selected true 40 = 42 := by rfl
theorem otherReaderBranch : selected false 40 = 7 := by rfl
theorem nestedBranch : nested true = 42 := by rfl
def runNat (x : Id Nat) : Nat := x
#eval selected true 40 + runNat (nested true)
"#;
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let run = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(result) = &run.executions.last().unwrap().exit else {
        panic!("return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("84")
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
