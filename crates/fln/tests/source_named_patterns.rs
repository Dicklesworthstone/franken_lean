//! Named patterns retain both a checked whole receiver and all field bindings.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    base()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}
fn reject(source: &str) {
    let engine = base();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let error = engine
        .check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert!(
        !format!("{error:?}").contains("Frontend(Parse("),
        "negative did not reach elaboration: {source}\n{error:?}"
    );
    assert_eq!(
        error.disposition().2,
        1,
        "a bad pattern must reject, not exhaust: {error:?}"
    );
    assert_eq!(before, engine.logical_root(&options));
    engine
        .check_source_files(
            &[b"theorem recovered (n : Nat) : n = n := by rfl"],
            &options,
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn named_constructor_returns_the_whole_not_a_field() {
    check(
        "def keep : List Nat -> List Nat | whole@(x :: xs) => whole | [] => []\n\
        theorem kept : keep [4, 5] = [4, 5] := by rfl\n\
        theorem empty : keep [] = [] := by rfl",
    );
    check(
        "def head : List Nat -> Nat | l@(x :: _) => x | [] => 0\n\
        theorem first : head [7, 8] = 7 := by rfl",
    );
}

#[test]
fn named_nested_constructor_fields_keep_distinct_receivers() {
    check(
        "inductive Tree where | leaf | branch (left right : Tree)\n\
        def swap : Tree -> Tree | .branch l@(.branch a b) r@.leaf => .branch r l | t => t\n\
        theorem result : swap (Tree.branch (Tree.branch Tree.leaf Tree.leaf) Tree.leaf) = Tree.branch Tree.leaf (Tree.branch Tree.leaf Tree.leaf) := by rfl\n\
        theorem fallback : swap Tree.leaf = Tree.leaf := by rfl",
    );
}

#[test]
fn named_offsets_preserve_the_whole_and_structural_predecessor() {
    check(
        "def down : Nat -> Nat | 0 => 0 | whole@(n+1) => whole + down n\n\
        theorem result : down 4 = 10 := by rfl",
    );
}

#[test]
fn named_columns_preserve_first_row_priority_and_simultaneous_aliases() {
    check(
        "def choose (x y : Nat) : Nat := match x, y with\n\
        | y@0, x => x + y\n\
        | y@(.succ n), x@0 => y\n\
        | a@(.succ n), b@(.succ m) => a + b\n\
        theorem first : choose 0 7 = 7 := by rfl\n\
        theorem second : choose 9 0 = 9 := by rfl\n\
        theorem last : choose 9 7 = 16 := by rfl",
    );
}

#[test]
fn a_named_wildcard_or_variable_does_not_require_an_inductive_family() {
    check(
        "def keep (A : Type) (x : A) : A := match x with | whole@_ => whole\n\
        def keep2 (A : Type) (x : A) : A := match x with | whole@part => part\n\
        theorem first : keep Nat 7 = 7 := by rfl\n\
        theorem second : keep2 Nat 8 = 8 := by rfl",
    );
}

#[test]
fn named_literal_patterns_do_not_replace_the_runtime_receiver() {
    check(
        "def code : Nat -> Nat | whole@0 => whole + 7 | whole@5 => whole + 10 | other => other\n\
        theorem zero : code 0 = 7 := by rfl\n\
        theorem five : code 5 = 15 := by rfl\n\
        theorem fallback : code 9 = 9 := by rfl",
    );
}

#[test]
fn named_payloads_still_check_coverage_types_and_duplicate_variables() {
    for source in [
        "def bad (n : Nat) : Nat := match n with | whole@0 => whole",
        "def bad : List Nat -> List Nat | head@x :: xs => head | [] => []",
        "def bad : Nat := match 0 with | whole@0 => whole",
        "def bad : List Nat -> Nat | whole@(whole :: xs) => 0 | [] => 0",
        "def bad (n m : Nat) : Nat := match n, m with | x@_, x => 0",
        "def bad : Nat -> Nat | all@_ => 1 | whole@0 => 2",
        "def bad : List Nat -> Nat | whole@(x :: xs) => (whole : Nat) | [] => 0",
        "inductive Tag where | left | right\ninductive Other where | left | right\ndef bad : Tag -> Nat | whole@Other.left => 0 | .right => 1",
        "def bad : Nat -> Nat | 0 => 0 | whole@(n+1) => bad whole",
    ] {
        reject(source);
    }
}

#[test]
fn named_alias_scope_does_not_escape_a_failed_tactic_candidate() {
    check(
        "def chosen (n : Nat) : Nat := by first | exact (match n with | whole@0 => whole) | exact 7\n\
        theorem result : chosen 0 = 7 := by rfl\n\
        theorem fallback : chosen 8 = 7 := by rfl",
    );
    reject("def bad (n : Nat) : Nat := let result := (match n with | whole@_ => whole); whole");
}

const VEC: &str = "inductive Vec (A : Type) : Nat -> Type where\n | nil : Vec A 0\n | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (n + 1)\n";

#[test]
fn a_named_dependent_receiver_keeps_its_refined_type() {
    check(&format!(
        "{VEC}def keep (n : Nat) (xs : Vec Nat n) : Vec Nat n := match xs with | w@.nil => w | w@(.cons k x tail) => w\n\
        theorem empty : keep 0 (Vec.nil : Vec Nat 0) = (Vec.nil : Vec Nat 0) := by rfl\n\
        theorem cons : keep 1 (Vec.cons 0 7 Vec.nil) = (Vec.cons 0 7 Vec.nil : Vec Nat 1) := by rfl"
    ));
}

#[test]
fn a_named_wrapper_cannot_hide_a_dependent_pattern_type_mismatch() {
    for source in [
        format!("{VEC}def bad (xs : Vec Nat 2) : Nat := match xs with | whole@(.cons k x _) => x"),
        format!(
            "{VEC}def bad (n : Nat) (xs : Vec Nat n) : Nat := match xs with | whole@.nil => 0 | whole@(.cons k x .nil) => x | whole@(.cons k x (.cons j y _)) => y"
        ),
    ] {
        let error = base()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert!(
            format!("{error:?}").contains("TypeMismatch"),
            "payload's real type check must run: {error:?}"
        );
    }
    check(&format!(
        "{VEC}def good (xs : Vec Nat 2) : Nat := match xs with | whole@(.cons _ x _) => x"
    ));
}

#[test]
fn named_patterns_execute_the_checked_source_result() {
    use fln::{EngineExecutionLimits, SourceCommandOutput, VmExit};
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let result = base().execute_source_commands_with_checks(
        b"def total : Nat -> Nat | 0 => 0 | whole@(n+1) => whole + total n\n#eval total 0\n#eval total 5",
        &KVMap::new(), limits).unwrap().into_complete().unwrap();
    assert_eq!(result.outputs.len(), 2);
    for (event, expected) in result.outputs.iter().zip(["0", "15"]) {
        let SourceCommandOutput::Evaluation {
            execution_index, ..
        } = event
        else {
            panic!("expected evaluation")
        };
        let VmExit::Returned(value) = &result.batch.executions[*execution_index].exit else {
            panic!("expected returned value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn nested_names_and_outer_shadowing_bind_the_correct_receiver() {
    check(
        "def first : List Nat -> Nat | head@x :: xs => head | [] => 0\n\
         theorem picksHead : first [7, 8] = 7 := by rfl\n\
         def keep : List Nat -> List Nat | outer@(inner@(x :: xs)) => inner | [] => []\n\
         theorem keeps : keep [7, 8] = [7, 8] := by rfl\n\
         def shadow (whole : Nat) (xs : List Nat) : Nat := match xs with\n\
         | whole@(x :: rest) => x + (match whole with | [] => 0 | _ :: tail => 1)\n\
         | [] => whole\n\
         theorem empty : shadow 100 [] = 100 := by rfl\n\
         theorem nonempty : shadow 100 [7] = 8 := by rfl",
    );
}

#[test]
fn named_patterns_compose_with_pure_and_monadic_pattern_bindings() {
    check(
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
instance idOfNat {A : Type} {n : Nat} [inst : OfNat A n] : OfNat (Id A) n := inst
structure Pair where
  first : Nat
  second : Nat
def pick (action : Id Pair) : Id Pair := do
  let whole@(Pair.mk x y) <- action
  return whole
def again (value : Pair) : Id Nat := do
  let whole@(Pair.mk x y) := value
  return whole.first + y
theorem kept : (pick (Pair.mk 7 8)).second = 8 := by rfl
theorem added : again (Pair.mk 7 8) = 15 := by rfl
"#,
    );
}

#[test]
fn transparent_wrappers_cannot_exhaust_the_pattern_type_guards_depth() {
    for alias in [true, false] {
        let mut pattern = String::from(".cons k x _");
        for index in 0..128 {
            pattern = if alias {
                format!("alias{index}@({pattern})")
            } else {
                format!("({pattern})")
            };
        }
        let source =
            format!("{VEC}def bad (xs : Vec Nat 2) : Nat := match xs with | {pattern} => x");
        let engine = base();
        let before = engine.logical_root(&KVMap::new());
        let error = match engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        ) {
            Err(error) => error,
            Ok(_) => panic!("transparent wrappers hid a dependent index mismatch; alias={alias}"),
        };
        assert!(format!("{error:?}").contains("TypeMismatch"), "{error:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        // The same depth is not itself a reason to refuse a correctly typed
        // payload; only the rigid written index distinguishes these programs.
        check(
            &source
                .replace("def bad", "def good")
                .replace(".cons k x _", ".cons _ x _"),
        );
    }
}
