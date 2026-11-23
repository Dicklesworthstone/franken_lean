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
    check_in(&engine(), source);
}

fn check_in(base: &Engine, source: &str) {
    let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{source}\n{result:?}"
    );
}

#[test]
fn delayed_method_arguments_wait_for_the_receivers_inferred_type_without_imports() {
    // `resolveLValLoop` postpones unknown receivers whether or not the field
    // has arguments (vendored `Lean/Elab/App.lean`). The equality constructor
    // checks the resumed method's receiver and argument order through both
    // admission seats, with no seeded declarations or imported artifacts.
    // The raw command-stream API starts after the module header; the pin's
    // source uses `prelude` to establish the same empty environment.
    let source = r#"inductive Token where
  | mk
  | other
inductive Same (x : Token) : Token → Prop where
  | refl : Same x x
def Token.choose (x fallback : Token) : Token := x
def delayed (left right : Token) : Token :=
  let f (x : _) := x.choose right
  f left
theorem delayed_correct (left right : Token) : Same (delayed left right) left :=
  @Same.refl left
"#;
    let result = Engine::builder().build_empty().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        limits(),
    );
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
fn defaulted_callback_results_resume_chained_field_constraints() {
    // The callback's numeral defaults only after both function binders have
    // closed. Its type equations must resume before the second field lookup.
    // This is an ordinary user family; no native Thunk name selects the fix.
    let declarations = "structure Delayed (A : Type) where\n  run : Nat -> A\n\
                        def Delayed.get {A : Type} (x : Delayed A) : A := x.run 0\n\
                        def through {A : Type} (f : Nat -> A) : A := f 0\n";
    for value in [
        "let t := Delayed.mk (fun _ => Delayed.mk (fun _ => 21)); t.get.get + t.get.get",
        "let t := Delayed.mk (fun _ => through (fun _ => Delayed.mk (fun _ => 21))); t.get.get + t.get.get",
    ] {
        check(&format!(
            "{declarations}def value := {value}\ntheorem computes : value = 42 := by rfl"
        ));
    }
}

#[test]
fn delayed_projection_receiver_types_can_depend_on_outer_parameters() {
    check(
        r#"structure Pair (A B : Type) where
  first : A
  second : B
def dependentReceiver (A : Type) (pair : Pair A Bool) : Bool :=
  let getSecond (x : _) := x.second
  getSecond pair
theorem dependentReceiver_correct (A : Type) (pair : Pair A Bool) :
  dependentReceiver A pair = pair.second := Eq.refl pair.second
def dependentResult (A : Type) (pair : Pair A Bool) : A :=
  let getFirst (x : _) := x.first
  getFirst pair
theorem dependentResult_correct (A : Type) (pair : Pair A Bool) :
  dependentResult A pair = pair.first := Eq.refl pair.first
def dependentReceiverViaLet (A : Type) (pair : Pair A Bool) : A :=
  let Carrier := A
  let saved := pair
  let getFirst (_tag : Carrier) (x : _) := x.first
  getFirst pair.first saved
theorem dependentReceiverViaLet_correct (A : Type) (pair : Pair A Bool) :
  dependentReceiverViaLet A pair = pair.first := Eq.refl pair.first"#,
    );
}

#[test]
fn delayed_projection_holes_cannot_capture_later_function_parameters() {
    let options = KVMap::new();
    let base = engine()
        .check_source_files(
            &[b"structure Pair (A B : Type) where\n  first : A\n  second : B"],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    for source in [
        "def sentinelPrefix : Nat := 7\n\
         def bad : (A : Type) -> Pair A Bool -> A :=\n\
           let getFirst (x : _) := x.first\n\
           fun A pair => getFirst pair",
        "def sentinelPrefix : Nat := 7\n\
         def bad (A : Type) : A :=\n\
           let getFirst (x : _) := x.first\n\
           getFirst (Pair.mk 7 true)",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .expect_err("an inferred receiver cannot capture a later binder or change its carrier");
        assert_eq!(error.disposition().0, "elaboration", "{source}\n{error}");
        assert_eq!(base.logical_root(&options), root);
        for name in ["sentinelPrefix", "bad"] {
            assert!(!base.environment().contains(&Name::from_components([name])));
        }
    }
    let repaired = b"def repaired (A : Type) (pair : Pair A Bool) : A :=\n\
                       let getFirst (x : _) := x.first\n\
                       getFirst pair\n\
                     theorem repaired_correct (A : Type) (pair : Pair A Bool) :\n\
                       repaired A pair = pair.first := Eq.refl pair.first";
    assert!(matches!(
        base.check_source_files(&[repaired], &options, limits()),
        Ok(Outcome::Complete(_))
    ));
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

/// Each source is also executed by the exact pinned Reference when available.
/// In particular, the absent-minor case is a refusal: dropping its named
/// receiver or eta-expanding past it would accept a program the pin rejects.
const RECURSOR_METHOD_CASES: &[(&str, &str, bool)] = &[
    (
        "transport",
        r#"@[simp] abbrev transfer.{u1, u2} {A : Sort u2} {a : A} {motive : A → Sort u1} (m : motive a) {b : A} (h : Eq a b) : motive b := h.rec m
theorem transfer_refl (n : Nat) : transfer (motive := fun _ : Nat => Nat) n (Eq.refl n) = n := rfl
"#,
        true,
    ),
    (
        "eq_dependent",
        r#"theorem method_symm {a b : Nat} (h : a = b) : b = a := h.rec rfl
"#,
        true,
    ),
    (
        "named_motive",
        r#"theorem method_symm {a b : Nat} (h : a = b) : b = a := h.rec (motive := fun b _ => b = a) rfl
"#,
        true,
    ),
    (
        "explicit_motive",
        r#"theorem method_symm {a b : Nat} (h : a = b) : b = a := @h.rec Nat a (fun b _ => b = a) rfl b
"#,
        true,
    ),
    (
        "nat_deferred",
        r#"theorem count : (3).rec 0 (fun _ ih => ih + 1) = 3 := rfl
"#,
        true,
    ),
    (
        "nat_named",
        r#"theorem count : (3).rec (zero := 0) (succ := fun _ ih => ih + 1) = 3 := rfl
"#,
        true,
    ),
    (
        "nat_overapplication",
        r#"theorem count : (2).rec (fun m : Nat => m) (fun _ ih m => Nat.succ (ih m)) 3 = 5 := rfl
"#,
        true,
    ),
    (
        "custom_dependent",
        r#"inductive Chain where | nil | cons (head : Nat) (tail : Chain)
theorem self_eq (c : Chain) : c = c := c.rec rfl (fun _ _ _ => rfl)
"#,
        true,
    ),
    (
        "custom_auxiliary",
        r#"inductive Chain where | nil | cons (head : Nat) (tail : Chain)
theorem rec_on (c : Chain) : c = c := c.recOn rfl (fun _ _ _ => rfl)
theorem cases_on (c : Chain) : c = c := c.casesOn rfl (fun _ _ => rfl)
"#,
        true,
    ),
    (
        "false_noargs",
        r#"theorem absurd_method (h : False) : 1 = 2 := h.rec
"#,
        true,
    ),
    (
        "false_hole",
        r#"theorem absurd_method (h : False) : 1 = 2 := h.rec _
"#,
        true,
    ),
    (
        "deferred_expected",
        r#"inductive Chain where | nil | cons (head : Nat) (tail : Chain)
theorem pick {p : Prop} (x : p) (y : p) : p := x
theorem later (c : Chain) (h : c = c) : pick (c.rec (rfl : Chain.nil = Chain.nil) (fun hd tl _ => (rfl : Chain.cons hd tl = Chain.cons hd tl))) h = h := rfl
"#,
        true,
    ),
    (
        "receiver_once",
        r#"axiom pickReceiver : Nat → Nat
theorem receiver_once (n : Nat) : True := (pickReceiver n).rec True.intro (fun _ _ => True.intro)
"#,
        true,
    ),
    (
        "underapplication",
        r#"noncomputable def transfer {A : Type} {a b : A} {motive : A → Prop} (h : a = b) : motive a → motive b := h.rec
"#,
        false,
    ),
    (
        "no_expected_type",
        r#"inductive Chain where | nil | cons (head : Nat) (tail : Chain)
example (c : Chain) := c.rec 0 (fun _ _ ih => ih + 1)
"#,
        false,
    ),
    (
        "wrong_minor",
        r#"def sentinelPrefix : Nat := 7
theorem bad {a b : Nat} (h : a = b) : b = a := h.rec (0 : Nat)
"#,
        false,
    ),
    (
        "false_result",
        r#"def sentinelPrefix : Nat := 7
theorem bad : (3).rec 0 (fun _ ih => ih + 1) = 4 := rfl
"#,
        false,
    ),
    (
        "deferred_wrong_minor",
        r#"inductive Chain where | nil | cons (head : Nat) (tail : Chain)
theorem pick {p : Prop} (x : p) (y : p) : p := x
theorem bad (c : Chain) (h : c = c) : pick (c.rec (rfl : Chain.nil = Chain.nil) (fun _ _ _ => (rfl : Chain.nil = Chain.nil))) h = h := rfl
"#,
        false,
    ),
];

#[test]
fn recursor_methods_share_dependent_elaboration_and_match_the_pin() {
    use std::path::PathBuf;
    use std::process::Command;

    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from)?;
            Some(lib.parent()?.parent()?.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    assert!(
        reference.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference is required for recursor-method controls",
    );
    if let Some(binary) = &reference {
        let version = Command::new(binary).arg("--githash").output().unwrap();
        assert!(version.status.success(), "{version:?}");
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35",
        );
    } else {
        eprintln!("SKIP: pinned Reference absent; native recursor-method controls still run");
    }
    let directory = std::env::temp_dir().join(format!("fln-method-elim-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for &(label, source, accepts) in RECURSOR_METHOD_CASES {
        if let Some(binary) = &reference {
            let file = directory.join(format!("{label}.lean"));
            std::fs::write(&file, source).unwrap();
            let output = Command::new(binary)
                .arg("-j1")
                .arg(&file)
                .env_remove("LEAN_PATH")
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(if accepts { 0 } else { 1 }),
                "{label}: {source}\n{output:?}",
            );
        }
        let base = engine();
        let options = KVMap::new();
        let root = base.logical_root(&options);
        let result = base.check_source_files(&[source.as_bytes()], &options, limits());
        if accepts {
            let checked = result
                .unwrap_or_else(|error| panic!("{label}: {source}\n{error:?}"))
                .into_complete()
                .unwrap_or_else(|reason| panic!("{label}: {source}\n{reason:?}"));
            assert!(
                checked.theorems > 0,
                "{label}: a real proof must be checked"
            );
            if label == "receiver_once" {
                use fln::ExprNode;
                use fln_env::constants::ConstantInfo;
                let Some(ConstantInfo::Thm(theorem)) = checked
                    .engine
                    .environment()
                    .find(&Name::from_components(["receiver_once"]))
                else {
                    panic!("the admitted receiver proof must be present")
                };
                let receiver = Name::from_components(["pickReceiver"]);
                let mut occurrences = 0;
                let mut pending = vec![theorem.value.clone()];
                while let Some(expression) = pending.pop() {
                    match expression.node() {
                        ExprNode::Const { name, .. } if name == &receiver => occurrences += 1,
                        ExprNode::App { f, a } => pending.extend([f.clone(), a.clone()]),
                        ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } => {
                            pending.extend([binder_type.clone(), body.clone()]);
                        }
                        ExprNode::LetE {
                            type_, value, body, ..
                        } => {
                            pending.extend([type_.clone(), value.clone(), body.clone()]);
                        }
                        ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                            pending.push(expr.clone());
                        }
                        _ => {}
                    }
                }
                assert_eq!(occurrences, 1, "the receiver is one emitted argument");
            }
        } else {
            let error = result.expect_err("invalid eliminator application must be refused");
            assert_eq!(
                error.disposition(),
                ("elaboration", false, 1),
                "{label}: {error:?}"
            );
        }
        assert_eq!(base.logical_root(&options), root, "{label}");
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["sentinelPrefix"]))
        );
    }
}

#[test]
fn recursor_methods_elaborate_the_unmodified_prelude_equality_prefix_from_empty() {
    use fln::source_check::modules::execution::SourceProgramLimits;
    use fln::source_check::modules::imported::SourceOleanImport;
    use fln::{EvaluationPresentation, SourceModuleInput};

    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let (prefix, _) = prelude
        .split_once("/--\nHeterogeneous equality.")
        .expect("the pinned prefix ends after Eq.ndrec and before HEq");
    assert!(prefix.contains("@[simp] abbrev Eq.ndrec."));
    assert!(prefix.contains("h.rec m"));
    let options = KVMap::new();
    let module = Name::from_components(["Init", "Prelude"]);
    let imported = SourceOleanImport::empty(&options);
    assert!(imported.engine.environment().is_empty());
    let checked = imported
        .execute_lean_source_modules_with_presentation(
            &[SourceModuleInput {
                name: &module,
                source: prefix.as_bytes(),
            }],
            &module,
            &options,
            SourceProgramLimits::new(EngineExecutionLimits::new(limits().admission.kernel)),
            None,
            EvaluationPresentation::Lean,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.modules.len(), 1);
    assert!(
        checked.modules[0]
            .commands
            .batch
            .engine
            .environment()
            .contains(&Name::from_components(["Eq", "ndrec"]))
    );
    assert!(imported.engine.environment().is_empty());
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
         def Alias.double (n : Alias) : Nat := Nat.add n n\n\
         theorem alias (n : Alias) : n.double = Nat.add n n := by rfl\n\
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
fn exported_methods_use_the_alias_namespace_and_ignore_the_current_namespace() {
    check(
        "def Alias := Nat\n\
         def Nat.exportedStep (n : Alias) : Nat := Nat.add n 1\n\
         namespace Alias\nexport Nat (exportedStep)\nend Alias\n\
         theorem exported (n : Alias) : n.exportedStep = Nat.add n 1 := by rfl\n\
         namespace Shadow\n\
         def Alias.exportedStep (n : Alias) : Nat := 99\n\
         theorem rooted (n : Alias) : n.exportedStep = Nat.add n 1 := by rfl\n\
         end Shadow",
    );
}

#[test]
fn an_exported_method_cannot_fall_back_to_a_different_receiver_type() {
    let options = KVMap::new();
    let source = "def Alias := Nat\n\
                  def Nat.exportedStep (n : Nat) : Nat := Nat.add n 1\n\
                  namespace Alias\nexport Nat (exportedStep)\nend Alias";
    let base = engine()
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    let invalid = b"def sentinelPrefix : Nat := 7\ndef bad (n : Alias) : Nat := n.exportedStep";
    let error = base
        .check_source_files(&[invalid], &options, limits())
        .expect_err("the exported target has no parameter of type Alias");
    assert_eq!(error.disposition().0, "elaboration", "{error}");
    assert!(
        format!("{error:?}").contains("InvalidFieldReceiver"),
        "{error}"
    );
    assert_eq!(base.logical_root(&options), root);
    for name in ["sentinelPrefix", "bad"] {
        assert!(!base.environment().contains(&Name::from_components([name])));
    }
    // Definitional equality still permits ordinary applications, and the
    // underlying type's own field notation still names the same method.
    let repaired = b"def repaired (n : Alias) : Nat := Nat.exportedStep n\n\
                     theorem underlying (n : Nat) : n.exportedStep = Nat.add n 1 := by rfl";
    assert!(matches!(
        base.check_source_files(&[repaired], &options, limits()),
        Ok(Outcome::Complete(_))
    ));
}

#[test]
fn exported_field_methods_preserve_ambiguity_and_exact_declaration_priority() {
    let source = "def Alias := Nat\n\
                  def First.step (n : Alias) : Nat := Nat.add n 1\n\
                  def Second.step (n : Alias) : Nat := Nat.add n 2\n\
                  namespace Alias\nexport First (step)\nexport Second (step)\nend Alias";
    let options = KVMap::new();
    let base = engine()
        .check_source_files(&[source.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[b"def bad (n : Alias) : Nat := n.step"],
            &options,
            limits(),
        )
        .expect_err("two exported targets do not select an arbitrary method");
    assert_eq!(error.disposition().0, "elaboration", "{error}");
    assert_eq!(base.logical_root(&options), root);
    let recovered = b"def Alias.step (n : Alias) : Nat := 3\n\
                      theorem selected (n : Alias) : n.step = 3 := by rfl";
    assert!(matches!(
        base.check_source_files(&[recovered], &options, limits()),
        Ok(Outcome::Complete(_))
    ));
    // Failed lookup, including ambiguity, still unfolds the receiver as at
    // the pin. A successfully selected but unusable method must not do so.
    let fallback = b"def Nat.step (n : Nat) : Nat := Nat.add n 3\n\
                     theorem fallback (n : Alias) : n.step = Nat.add n 3 := by rfl";
    assert!(matches!(
        base.check_source_files(&[fallback], &options, limits()),
        Ok(Outcome::Complete(_))
    ));
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

/// Inside `T.size`'s own body, `l.size` is a recursive call: the pin finds the declaration
/// being defined in the local context before it searches the environment
/// (`LValResolution.localRec`). This is the stage-2 target I04 (bead
/// `franken_lean-z8j.1.10`) with `by rfl` for its term-mode `rfl`; the pin accepts both.
#[test]
fn field_notation_inside_a_recursive_definition_is_a_recursive_call() {
    check(
        "inductive T where\n  | leaf\n  | node (l r : T)\n\
         def T.size : T → Nat\n  | .leaf => 1\n  | .node l r => l.size + r.size + 1\n\
         theorem t : (T.node .leaf .leaf).size = 3 := by rfl",
    );
}

/// The recursive-call reading applies to the declaration's own name only, and only through
/// structural recursion. The pin refuses both of these: `l.foo` with "Invalid field `foo`:
/// The environment does not contain `T.foo`", and a self-reference that is not structural with
/// "fail to show termination for T.size".
#[test]
fn field_notation_reaches_only_the_declaration_itself_and_only_structurally() {
    for source in [
        "inductive T where\n  | leaf\n  | node (l r : T)\n\
         def T.size : T → Nat\n  | .leaf => 1\n  | .node l r => l.foo + 1",
        "inductive T where\n  | leaf\n  | node (l r : T)\n\
         def T.size (t : T) : Nat := t.size",
    ] {
        let result = engine().check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
        let error = result.expect_err(source);
        assert_eq!(error.disposition().0, "elaboration", "{source}\n{error}");
    }
}

/// A `def` alias does not inherit its target's instances: the pin refuses `n + n`
/// for `n : Alias` with "failed to synthesize HAdd Alias Alias ?m" (v4.32.0, run on
/// this declaration). This elaborator accepted it until the unifier stopped unfolding
/// `Alias` to `Nat` in order to assign the operator's type (bead fln-eeew).
#[test]
fn addition_on_a_definitional_alias_is_refused_as_the_pin_refuses_it() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = "def Alias := Nat\ndef bad (n : Alias) : Nat := n + n";
    let result = base.check_source_files(&[source.as_bytes()], &options, limits());
    assert!(
        !matches!(result, Ok(Outcome::Complete(_))),
        "{source}\n{result:?}"
    );
    assert_eq!(base.logical_root(&options), root);
    check("def Alias := Nat\ndef good (n : Alias) : Nat := Nat.add n n");
}

#[test]
fn methods_execute_through_the_same_compiler_and_vm() {
    let source = b"def bump (xs : List Nat) : List Nat := xs.map (fun n => n + 1)\n\
        def directCount (n : Nat) : Nat := Nat.rec 0 (fun _ ih => Nat.succ ih) n\n\
        def methodCount (n : Nat) : Nat := n.rec 0 (fun _ ih => Nat.succ ih)\n\
        def namedCount (n : Nat) : Nat := n.rec (zero := 0) (succ := fun _ ih => Nat.succ ih)\n\
        #eval (([1, 2, 3]).map (fun n => n + 1)).foldr (fun n acc => n + acc) 0\n\
        #eval (\"hello\").length\n\
        #eval directCount 3\n\
        #eval methodCount 7\n\
        #eval namedCount 9";
    let result = engine()
        .execute_source_definitions(
            &[source],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.executions.len() >= 5);
    for (execution, expected) in result
        .executions
        .iter()
        .rev()
        .zip(["9", "7", "3", "5", "9"])
    {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("VM result")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn delayed_methods_replay_named_expected_and_dependent_arguments() {
    // Accepted by the pinned executable over Init.Prelude. These declarations
    // use the ordinary source seed here; the separate Token test starts empty.
    check(
        r#"inductive Token where
  | mk
  | other
inductive Tag where
  | mk
inductive Same {A : Type} (x : A) : A → Prop where
  | refl : Same x x
def Token.choose (self fallback : Token) : Token := self
def Token.after (tag : Tag) (self : Token) (fallback : Token) : Token := self
def Token.expect {A : Type} (self : Token) (make : Token → A) : A := make self
structure Wrap where
  token : Token
def Token.wrap (self fallback : Token) : Wrap := { token := self }
structure Operation where
  run : Token → Token
structure Pair (A : Type) where
  value : A
def Pair.take {A : Type} (self : Pair A) (tag : Tag) : A := self.value
def delayedNamed (left right : Token) : Token :=
  let call (x : _) := x.after (fallback := right) Tag.mk
  call left
theorem delayedNamed_correct (left right : Token) : Same (delayedNamed left right) left :=
  @Same.refl Token left
def delayedExpected (left : Token) : Token :=
  let call (x : _) : Token := x.expect (fun _ => .mk)
  call left
theorem delayedExpected_correct (left : Token) : Same (delayedExpected left) Token.mk :=
  @Same.refl Token Token.mk
def delayedChain (left right : Token) : Token :=
  let call (x : _) := (x.wrap right).token
  call left
theorem delayedChain_correct (left right : Token) : Same (delayedChain left right) left :=
  @Same.refl Token left
def delayedField (operation : Operation) (value : Token) : Token :=
  let call (x : _) := x.run value
  call operation
theorem delayedField_correct (operation : Operation) (value : Token) :
    Same (delayedField operation value) (operation.run value) :=
  @Same.refl Token (operation.run value)
def delayedDependent (A : Type) (pair : Pair A) : A :=
  let Carrier := A
  let saved := pair
  let call (tag : Carrier) (x : _) := x.take Tag.mk
  call pair.value saved
theorem delayedDependent_correct (A : Type) (pair : Pair A) :
    Same (delayedDependent A pair) pair.value :=
  @Same.refl A pair.value
"#,
    );
}

#[test]
fn delayed_methods_preserve_instance_output_parameters() {
    // The class instance determines the method's result after its receiver is
    // known; replay goes through the ordinary out-parameter application path.
    // As in source_coercions, the coercion library is admitted by both checkers.
    let base = Engine::with_coercion_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    check_in(
        &base,
        r#"inductive Token where
  | mk
  | other
inductive Tag where
  | mk
inductive Same {A : Type} (x : A) : A → Prop where
  | refl : Same x x
class Convert (A : Type) (B : outParam Type) where
  convert : A → B
instance : Convert Token Tag where
  convert _ := Tag.mk
def Token.change {B : Type} [Convert Token B] (self : Token) (argument : Token) : B :=
  Convert.convert self
def delayedOutput (value : Token) : Tag :=
  let call (x : _) := x.change Token.mk
  call value
theorem delayedOutput_correct (value : Token) : Same (delayedOutput value) Tag.mk :=
  @Same.refl Tag Tag.mk
structure WrappedTag where
  value : Tag
instance : Coe Tag WrappedTag where
  coe value := { value := value }
def delayedCoercedOutput (value : Token) : WrappedTag :=
  let call (x : _) : WrappedTag := x.change Token.mk
  call value
theorem delayedCoercedOutput_correct (value : Token) :
    Same (delayedCoercedOutput value) (WrappedTag.mk Tag.mk) :=
  @Same.refl WrappedTag (WrappedTag.mk Tag.mk)
"#,
    );
}

#[test]
fn delayed_method_failures_do_not_capture_later_binders_or_publish_source() {
    let options = KVMap::new();
    let base = engine()
        .check_source_files(
            &[br#"inductive Token where
  | mk
  | other
inductive Tag where
  | mk
structure Pair (A : Type) where
  value : A
def Token.choose (x fallback : Token) : Token := x
def Pair.take {A : Type} (self : Pair A) (tag : Tag) : A := self.value
"#],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    for (source, detail) in [
        (
            r#"def sentinelPrefix : Token := Token.mk
def bad (left : Token) : Token :=
  let call (x : _) := x.choose Tag.mk
  call left"#,
            Some("TypeMismatch"),
        ),
        (
            r#"def sentinelPrefix : Token := Token.mk
def bad (left : Token) : Token :=
  let call (x : _) := x.missing Token.mk
  call left"#,
            // Token is an enum, so failed lookup reports this existing refusal.
            Some("ExpectedRecordType"),
        ),
        (
            r#"def sentinelPrefix : Token := Token.mk
def bad : (A : Type) -> Pair A -> A :=
  let call (x : _) := x.take Tag.mk
  fun A pair => call pair"#,
            None,
        ),
        (
            r#"def sentinelPrefix : Token := Token.mk
def bad (A : Type) (pair : Pair Token) : A :=
  let call (x : _) := x.take Tag.mk
  call pair"#,
            None,
        ),
        (
            r#"def sentinelPrefix : Token := Token.mk
def bad : (A : Type) -> A -> A :=
  let keep (value : _) [Inhabited Nat] := value
  fun A value => keep value"#,
            None,
        ),
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .expect_err("a delayed method must still check its arguments and captured scope");
        assert_eq!(error.disposition().0, "elaboration", "{source}\n{error}");
        if let Some(detail) = detail {
            assert!(format!("{error:?}").contains(detail), "{source}\n{error}");
        }
        assert_eq!(base.logical_root(&options), root);
        for name in ["sentinelPrefix", "bad"] {
            assert!(!base.environment().contains(&Name::from_components([name])));
        }
    }
}

#[test]
fn local_method_helpers_close_instance_goals_solved_by_their_callers() {
    // Both helper spellings keep the same local dictionary. A written receiver
    // tests ordinary local-function closure; `_` also tests field replay.
    // The second proof observes the helper's explicit dictionary (7), which
    // must override the ambient Nat default (0).
    for receiver in ["Token", "_"] {
        for argument in ["Nat.zero", "0"] {
            let source = format!(
                r#"inductive Token where
  | mk
  | other
inductive Same (x : Token) : Token → Prop where
  | refl : Same x x
def Token.keep {{A : Type}} [Inhabited A] (self : Token) (value : A) : Token := self
def delayed (token : Token) : Token :=
  let call (x : {receiver}) (value : _) [Inhabited Nat] := x.keep value
  call token {argument}
theorem delayed_correct (token : Token) : Same (delayed token) token :=
  @Same.refl token
def Token.pick {{A : Type}} [Inhabited A] (self : Token) (value : A) : A := Inhabited.default
def selected (token : Token) : Nat :=
  let call (x : {receiver}) (value : _) [Inhabited Nat] := x.pick value
  @call token {argument} ⟨7⟩
theorem selected_correct (token : Token) : selected token = 7 := by rfl
"#
            );
            check(&source);
        }
    }
}

/// `fln-dyfz`: in `Lean/Elab/App.lean:1580-1588`, a dotted identifier whose prefix resolves to a
/// declared function constant (`def f (n : Nat) : Nat := n; def g := f.nope`) reports the pin's
/// `Unknown constant \`f.nope\`` (`error(lean.unknownIdentifier)` at v4.32.0), whereas a local
/// function variable `(f : Nat → Nat)` or parenthesized projection `(f).nope` keeps field-notation
/// unknown-field refusal and genuine structure projection (`p.fst`) is unaffected.
#[test]
fn dotted_name_on_declared_function_reports_unknown_constant_as_at_the_pin() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    for (source, expected) in [
        (
            "def f (n : Nat) : Nat := n\ndef g := f.nope\n",
            "Unknown constant `f.nope`",
        ),
        (
            "namespace N\ndef f (n : Nat) : Nat := n\ndef g := f.nope\nend N\n",
            "Unknown constant `N.f.nope`",
        ),
        (
            "def f (n : Nat) : Nat := n\ndef g := f.nope.more\n",
            "Unknown constant `f.nope.more`",
        ),
        (
            "def g (f : Nat → Nat) := f.nope\n",
            "unknown record field nope",
        ),
        (
            "def f (n : Nat) : Nat := n\ndef g := (f).nope\n",
            "unknown record field nope",
        ),
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .expect_err("must be refused at elaboration");
        assert_eq!(error.disposition().0, "elaboration", "{source}\n{error}");
        let rendered = error.to_string();
        assert!(
            rendered.contains(expected),
            "expected `{expected}` in `{rendered}` for:\n{source}"
        );
    }
    check(
        "structure Pair where\n  fst : Nat\n  snd : Nat\n\
         def readFirst (p : Pair) : Nat := p.fst\n\
         theorem readFirst_eq : readFirst { fst := 3, snd := 4 } = 3 := by rfl\n",
    );
}
