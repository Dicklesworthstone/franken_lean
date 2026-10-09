//! End-to-end native propositional logic: source -> synthesis -> both checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    (
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap(),
        limits,
    )
}
fn check(source: &str) {
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn composite_decision_truth_tables_are_kernel_checked() {
    let mut source = String::new();
    for (i, (p, a)) in [("False", false), ("True", true)].into_iter().enumerate() {
        for (j, (q, b)) in [("False", false), ("True", true)].into_iter().enumerate() {
            for (label, target, truth) in [
                ("and", format!("And {p} {q}"), a && b),
                ("or", format!("Or {p} {q}"), a || b),
                ("iff", format!("Iff {p} {q}"), a == b),
                ("implies", format!("{p} -> {q}"), !a || b),
            ] {
                source.push_str(&format!(
                    "theorem {label}{i}{j} : decide ({target}) = {truth} := by rfl\n"
                ));
            }
        }
    }
    check(&source);
}

#[test]
fn decide_composes_equality_negation_and_connectives() {
    check(
        r#"
        theorem pair : And (2 + 3 = 5) (Not (3 = 4)) := by decide
        theorem choice : Or (1 = 2) (3 = 3) := by decide
        theorem same : Iff (2 = 2) (Not (3 = 4)) := by decide
        theorem vacuous : (2 = 3) -> (3 = 4) := by decide
        theorem nested : Not (And (Or (1 = 2) False) (Iff True False)) := by decide
        theorem conditional : ite (And (1 = 1) (Not False)) 17 23 = 17 := by rfl
    "#,
    );
}

#[test]
fn constructors_and_eliminators_are_usable_in_ordinary_proofs() {
    check(
        r#"
        theorem pair (p q : Prop) (hp : p) (hq : q) : And p q := by constructor; assumption; assumption
        theorem first (p q : Prop) (h : And p q) : p := And.left h
        theorem second (p q : Prop) (h : And p q) : q := And.right h
        theorem swap (p q : Prop) (h : Or p q) : Or q p := Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
        theorem equivalent (p : Prop) : Iff p p := Iff.intro (fun h => h) (fun h => h)
        theorem forwards (p q : Prop) (h : Iff p q) (hp : p) : q := Iff.mp h hp
        theorem backwards (p q : Prop) (h : Iff p q) (hq : q) : p := Iff.mpr h hq
        theorem dot_left (p q : Prop) (h : And p q) : p := h.left
        theorem dot_mp (p q : Prop) (h : Iff p q) (hp : p) : q := h.mp hp
        theorem named_pair (p q : Prop) (hp : p) (hq : q) : And p q := { right := hq, left := hp }
    "#,
    );
}

#[test]
fn short_circuit_reduction_keeps_opaque_right_dictionaries_unevaluated() {
    check(
        r#"
        theorem conjunction (p : Prop) [Decidable p] : decide (And False p) = false := by rfl
        theorem disjunction (p : Prop) [Decidable p] : decide (Or True p) = true := by rfl
        theorem implication (p : Prop) [Decidable p] : decide (False -> p) = true := by rfl
        def combine (p q : Prop) [Decidable p] [Decidable q] : Decidable (And p q) := inferInstance
        theorem instance_result : decide (And True True) = true := by rfl
    "#,
    );
}

#[test]
fn user_decisions_are_composed_without_replacing_their_proofs() {
    check(
        r#"
        inductive Holds : Prop where | yes
        instance holds : Decidable Holds := Decidable.isTrue Holds.yes
        theorem composed : And Holds (Or False Holds) := by decide
        theorem equivalent : Iff Holds True := by decide
        theorem computation : decide (Or False (And Holds True)) = true := by rfl
    "#,
    );
}

#[test]
fn false_unknown_and_ill_typed_composites_refuse_atomically_and_recover() {
    let (engine, limits) = engine();
    let root = engine.logical_root(&KVMap::new());
    for bad in [
        "theorem bad : And True False := by decide",
        "theorem bad : Or False False := by decide",
        "theorem bad : Iff True False := by decide",
        "theorem bad : True -> False := by decide",
        "def bad (p q : Prop) : Bool := decide (And p q)",
        "def bad (p : Prop) : Bool := decide (Or True p)",
        "def bad : And True False := And.intro True.intro True.intro",
        "def bad : Or False False := Or.inl True.intro",
        "def bad : Prop := And True Nat",
        "def bad (h : Or True True) : Nat := Or.elim h (fun hp => 1) (fun hq => 2)",
    ] {
        let source = format!("def earlier : Nat := 7\n{bad}\n");
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits)
                )
                .is_err(),
            "{bad}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["earlier"]))
        );
        engine
            .check_source_files(
                &[b"theorem recovered : And True True := by decide"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap();
    }
}

#[test]
fn logical_seed_additions_have_checked_bodies_or_inductive_rules_not_axioms() {
    let (engine, _) = engine();
    for name in [
        "And",
        "And.intro",
        "And.rec",
        "And.left",
        "And.right",
        "Or",
        "Or.inl",
        "Or.inr",
        "Or.rec",
        "Or.elim",
        "Iff",
        "Iff.intro",
        "Iff.rec",
        "Iff.mp",
        "Iff.mpr",
        "instDecidableAnd",
        "instDecidableOr",
        "instDecidableForall",
        "instDecidableIff",
    ] {
        assert!(
            !matches!(
                engine
                    .environment()
                    .find(&Name::from_components(name.split('.'))),
                None | Some(ConstantInfo::Axiom(_))
            ),
            "{name}"
        );
    }
}

#[test]
fn logical_notation_has_reference_precedence_associativity_and_application_scope() {
    check(
        r#"
        theorem and_assoc (p q r : Prop) : (p ∧ q ∧ r) = And p (And q r) := by rfl
        theorem or_assoc (p q r : Prop) : (p ∨ q ∨ r) = Or p (Or q r) := by rfl
        theorem mixed (p q r : Prop) : (p ∨ q ∧ r) = Or p (And q r) := by rfl
        theorem arrows (p q r : Prop) : (p ∧ q -> r) = ((And p q) -> r) := by rfl
        theorem iff_scope (p q r : Prop) : (p -> q ↔ r) = Iff (p -> q) r := by rfl
        theorem negation (p q : Prop) : (¬p ∧ q) = And (Not p) q := by rfl
        theorem negated_equality : (¬2 = 3) = Not (2 = 3) := by rfl
        theorem prefix_argument : (decide ¬False) = true := by rfl
        theorem prefix_function (p : Nat -> Prop) (n : Nat) : (¬p n) = Not (p n) := by rfl
        theorem repeated (p : Prop) : (¬¬p) = Not (Not p) := by rfl
        theorem ascii (p q r : Prop) : (p /\ q \/ r) = Or (And p q) r := by rfl
        theorem ascii_iff (p q : Prop) : (p <-> q) = Iff p q := by rfl
        theorem decided : 2 + 3 = 5 ∧ ¬3 = 4 := by decide
        theorem decided_iff : (2 = 2 ∨ False) ↔ ¬(3 = 4) := by decide
    "#,
    );
}

/// Init's plain infixes are applications of the functions they name, in the pin's operand
/// order: `a ∈ b` is `Membership.mem b a` and `a ∉ b` is `¬ (a ∈ b)`
/// (`Init/Notation.lean:272-428`). A binder group may omit its type (`{A}`).
#[test]
fn init_infixes_apply_their_functions_in_the_pins_operand_order() {
    check(
        "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n\
         def pair (A B : Type) : Type := A × B\n\
         theorem pair_is_prod (A B : Type) : pair A B = Prod A B := rfl\n\
         def Function.comp {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x)\n\
         theorem comp_applies (f g : Nat -> Nat) (x : Nat) : (f ∘ g) x = f (g x) := rfl\n\
         class Membership (A : Type) (G : Type) where\n  mem : G -> A -> Prop\n\
         structure Bag where\n  val : Nat\n\
         instance bagMembership : Membership Nat Bag := Membership.mk (fun b n => b.val = n)\n\
         theorem three_in : 3 ∈ Bag.mk 3 := rfl\n\
         theorem not_in_negates : (4 ∉ Bag.mk 3) = Not ((Bag.mk 3).val = 4) := rfl\n\
         theorem untyped {n} (h : n = 1) : n = 1 := h\n",
    );
}

/// `(a : A) × B` is the pin's dependent pair (`Init/NotationExtra.lean:93`), never `Prod` of
/// an ascription. Read as `Prod B Nat` this definition would check; the pin refuses it
/// (measured 2026-10-08: the `Sigma` over `Type` is not in `Type`).
#[test]
fn a_dependent_pair_is_not_read_as_a_product() {
    let (engine, limits) = engine();
    let source = "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n\
                  def dependent (B : Type) : Type := (B : Type) × Nat\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `∅` is `EmptyCollection.emptyCollection` (`Init/Core.lean:581`), its type and instance
/// inserted from the expected type.
#[test]
fn the_empty_collection_notation_is_its_class_constant() {
    check(
        "class EmptyCollection (A : Type) where\n  emptyCollection : A\n\
         structure Bag where\n  val : Nat\n\
         instance emptyBag : EmptyCollection Bag := EmptyCollection.mk (Bag.mk 0)\n\
         theorem empty_is_zero : (∅ : Bag) = Bag.mk 0 := rfl\n",
    );
}

/// `f <| a` is the application `f a` (`Init/Notation.lean:522`). The pin's macro also flattens
/// `f x <| a` into `f x a`; that form is refused rather than read as `(f x) a`.
#[test]
fn the_pipeline_applies_its_function_and_refuses_an_applied_one() {
    check(
        "theorem pipe : (Nat.succ <| Nat.succ <| 0) = 2 := rfl\n\
         theorem pipe_right : (0 |> Nat.succ |> Nat.succ) = 2 := rfl\n",
    );
    let (engine, limits) = engine();
    for source in [
        "theorem applied : (Nat.add 1 <| 1) = 2 := rfl\n",
        "theorem applied : (1 |> Nat.add 1) = 2 := rfl\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

const NOT: &str = "def Bool.not : Bool → Bool\n  | true => false\n  | false => true\n";
/// `&&` is `Bool.and` (`infixl:35 " && " => and`, `Init/Notation.lean`), which the source seed
/// lacks: tests that use it declare Init's (`Init/Prelude.lean`).
const AND: &str =
    "def Bool.and (x y : Bool) : Bool :=\n  match x with\n  | false => false\n  | true => y\n";

/// `!b` is `Bool.not b` with its operand at precedence 40 (`notation:max "!" b:40`), so
/// `!false && false` is `(!false) && false`, which is `false`; read as `!(false && false)` it
/// would be `true`.
#[test]
fn boolean_negation_takes_the_operand_before_a_conjunction() {
    // The source seed has no `Bool.not`: the test declares Init's (`Init/Prelude.lean`).
    check(&format!(
        "{NOT}{AND}theorem tight : (!false && false) = false := rfl\n\
         theorem whole : (!(false && false)) = true := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{NOT}{AND}theorem wrong : (!false && false) = true := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

const XOR: &str =
    "def Bool.xor (a b : Bool) : Bool :=\n  match a with\n  | true => Bool.not b\n  | false => b\n";

/// `a ^^ b` is `Bool.xor a b` at precedence 33 (`infixl:33 " ^^ " => xor` in namespace `Bool`),
/// below `&&` at 35: `true ^^ true && false` is `true ^^ (true && false)`, which is `true`; read
/// as `(true ^^ true) && false` it would be `false`.
#[test]
fn exclusive_or_takes_a_conjunction_as_its_operand() {
    // The source seed has no `Bool.xor` or `Bool.and`: the test declares them with Init's values.
    check(&format!(
        "{NOT}{AND}{XOR}theorem loose : (true ^^ true && false) = true := rfl\n\
         theorem left : (true ^^ true ^^ true) = true := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{NOT}{AND}{XOR}theorem wrong : (true ^^ true && false) = false := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `a ≍ b` is `HEq a b` (`infix:50 " ≍ " => HEq`); `(1 : Nat) ≍ (2 : Nat)` is not proved by
/// `HEq.refl 1`.
#[test]
fn heterogeneous_equality_is_heq() {
    check("theorem same (x : Nat) : x ≍ x := HEq.refl x\n");
    let (engine, limits) = engine();
    let source = "theorem bad : (1 : Nat) ≍ (2 : Nat) := HEq.refl 1\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `(n : Nat)` in a pattern parses as the pin's `Term.typeAscription`: whatever the pattern
/// compiler makes of it, it never admits a false statement about the function.
#[test]
fn ascribed_patterns_are_never_misread() {
    let (engine, limits) = engine();
    let source = "def asc : Option Nat → Nat\n  | some (n : Nat) => n\n  | none => 0\n\
                  theorem wrong : asc (some 3) = 4 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `nofun` and `nomatch h` parse as the pin's `Term.nofun` and `Term.nomatch`; the elaborator
/// does not read them, so it refuses files the pin accepts.
#[test]
fn empty_matches_are_refused_not_misread() {
    let (engine, limits) = engine();
    for source in [
        "def nf : False → Nat := nofun\n",
        "def nm (h : False) : Nat := nomatch h\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A `where` declaration's doc comment is its `letRecDecl`'s first slot and means nothing to the
/// kernel: the declaration checks with it, and a false statement about it is still refused. An
/// attribute on it (`@[specialize]`) is refused, not dropped.
#[test]
fn where_declarations_carry_doc_comments() {
    check(
        "def wd (n : Nat) : Nat := go n where\n  /-- The step. -/\n  go (k : Nat) : Nat := k + 1\n\
         theorem wd_ok : wd 2 = 3 := rfl\n",
    );
    let (engine, limits) = engine();
    for source in [
        "def wd (n : Nat) : Nat := go n where\n  /-- The step. -/\n  go (k : Nat) : Nat := k + 1\n\
         theorem wd_wrong : wd 2 = 2 := rfl\n",
        "def wa (n : Nat) : Nat := go n where\n  @[specialize] go (k : Nat) : Nat := k\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `deriving instance C for T` parses as the pin's `Command.deriving`; the checker does not derive
/// instances, so it refuses the file, which the pin accepts, rather than ignoring the command.
#[test]
fn deriving_commands_are_refused_not_ignored() {
    let (engine, limits) = engine();
    let source =
        "inductive Shade where\n  | dark\n  | light\nderiving instance Inhabited for Shade\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `l@p` parses as the pin's `Term.namedPattern`, also as a constructor argument
/// (`.inner l@(.inner ..) r@.leaf`); the pattern compiler does not bind the name, so the checker
/// refuses the file, which the pin accepts.
#[test]
fn named_patterns_are_refused_not_dropped() {
    let (engine, limits) = engine();
    for source in [
        "def np : List Nat → Nat\n  | l@(x :: _) => x\n  | [] => 0\n",
        "inductive T where\n  | leaf\n  | inner (l : T) (r : T)\n\
         def np : T → T\n  | .inner l@(.inner ..) r@.leaf => .inner r l\n  | t => t\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `f <*> x` parses as the pin's `«term_<*>_»` (`Seq.seq f fun _ => x`); the checker does not
/// read applicative sequencing, so it refuses the file, which the pin accepts.
#[test]
fn applicative_sequencing_is_refused_not_misread() {
    let (engine, limits) = engine();
    let source = "def ap (f : Option (Nat → Nat)) (x : Option Nat) : Option Nat := f <*> x\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `done` succeeds exactly when no goal is left (`evalDone`): after the last goal closes, inside a
/// parenthesized sequence, and as an alternative `first` keeps. With a goal left it fails, and
/// `first` moves on, so a proof that leaves a goal to `done` is refused, as the pin refuses it.
#[test]
fn done_succeeds_only_without_goals() {
    check(
        "theorem dn2 (p : Prop) (hp : p) : p := by\n  exact hp\n  done\n\
         theorem dn (n : Nat) : n = n := by\n  (rfl; done)\n\
         theorem fd (p : Prop) (hp : p) : p := by\n  first | (exact hp; done) | assumption\n\
         theorem fc (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  \
         first | (constructor; done) | exact ⟨hp, hq⟩\n",
    );
    let (engine, limits) = engine();
    for source in [
        "theorem db (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  done\n",
        "theorem dw (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  \
         first | (constructor; done) | constructor\n  exact hp\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `(· 1)` is the function applying its argument to `1`: `·` heads the application inside the
/// parentheses, as the pin's tree has it. The checker does not expand a `·` in head position, so it
/// refuses the file, which the pin accepts, and never reads it as something else (`ch2_bad`).
#[test]
fn a_cdot_head_is_refused_not_misread() {
    let ch2 = "def ch2 (f : Nat → Nat) : Nat := (· 1) f\n";
    let (engine, limits) = engine();
    for source in [
        format!("{ch2}theorem ch2_ok : ch2 Nat.succ = 2 := rfl\n"),
        format!("{ch2}theorem ch2_bad : ch2 Nat.succ = 1 := rfl\n"),
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `show ¬k = 0 by tac`: the prefix operand is folded before the `by` closes the annotation.
#[test]
fn show_by_after_a_negation() {
    check("theorem sh2 (k : Nat) (h : ¬k = 0) : ¬k = 0 := show ¬k = 0 by exact h\n");
}

/// A `by` owns the `<;>`s after it: `exact by constructor <;> first | …` proves the goal with the
/// whole chain inside the proof. Read as `(exact by constructor) <;> first | …`, the `by` block
/// would leave `p` and `q` open.
#[test]
fn a_chain_inside_a_by_block_is_that_blocks() {
    check(
        "theorem sx (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  \
         exact by constructor <;> first | exact hp | exact hq\n",
    );
}

/// `t <;> try u; done` is `t <;> try (u; done)`: `try`'s `tacticSeq` takes the `;`. Run on each
/// goal, it closes `p` and leaves `q` untouched for the next line; read as `(t <;> try u); done`,
/// the `done` would fail with `q` open.
#[test]
fn a_chained_try_takes_the_sequence_after_it() {
    check(
        "theorem td7 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  \
         constructor <;> try exact hp; done\n  exact hq\n",
    );
    let (engine, limits) = engine();
    let source = "theorem td8 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor <;> try exact hp; done\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A `case` body on its own line is positioned at its first token, even at the enclosing
/// sequence's column, so without a `·` it takes every line at its column: a second `case` lands
/// inside the first, where no goal has its tag, and the pin refuses the proof. The checker does
/// not run `case` yet; this proof must stay refused when it does.
#[test]
fn a_case_body_on_its_own_line_takes_the_lines_at_its_column() {
    let (engine, limits) = engine();
    let source = "theorem cb2 (n : Nat) : n = n := by\n  cases n\n  case zero =>\n  rfl\n  \
                  case succ n =>\n  rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `induction a, b using r` parses as the pin's `sepBy1(elimTarget, ", ")`; the checker reads one
/// target and no `using`, so it refuses the proof, which the pin accepts, and refuses
/// `cases a, b`, which the pin refuses too (no default eliminator for two targets).
#[test]
fn several_elimination_targets_are_refused_not_misread() {
    let two_rec = "theorem two_rec {motive : Nat → Nat → Prop} (zero : ∀ n, motive 0 n)\n    \
                   (succ : ∀ m n, motive (m + 1) n) : ∀ m n, motive m n\n  \
                   | 0, n => zero n\n  | m + 1, n => succ m n\n";
    check(two_rec);
    let (engine, limits) = engine();
    for source in [
        format!(
            "{two_rec}theorem mtc (a b : Nat) : a + 0 = a := by\n  induction a, b using two_rec <;> rfl\n"
        ),
        "theorem mtc (a b : Bool) : a = a := by\n  cases a, b <;> rfl\n".to_owned(),
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `show`, `erw`, `rw_mod_cast`, `rotate_left`, `subst_eqs`, `open … in`, and a `rw`/`simp` configuration
/// (`(occs := [1])`, `(config := …)`, `(maxSteps := 10)`) parse as the pin's trees; the checker
/// runs none of them, so it refuses each file, all of which the pin accepts.
#[test]
fn tactics_the_checker_does_not_run_are_refused_not_misread() {
    let (engine, limits) = engine();
    for source in [
        "theorem l1 (n : Nat) : n = n := by\n  show n = n\n  rfl\n",
        "theorem l2 (a b : Nat) (h : a = b) : b = a := by\n  erw [h]\n",
        "theorem l4 (p q : Prop) (hp : p) (hq : q) : p ∧ q := by\n  constructor\n  rotate_left\n  \
         exact hq\n  exact hp\n",
        "theorem l6 (a b : Nat) (h : a = b) : b = a := by\n  subst_eqs\n  rfl\n",
        "theorem l10 (a b : Nat) (h : a = b) : b = a := by\n  rw_mod_cast [h]\n",
        "theorem ro1 (a b : Nat) (h : a = b) : b = a := by\n  rw (occs := [1]) [h]\n",
        "theorem ro3 (n : Nat) : n + 0 = n := by\n  simp (config := { decide := true })\n",
        "theorem ro4 (n : Nat) : n + 0 = n := by\n  simp +arith (maxSteps := 10)\n",
        "theorem t2 : True := by\n  simpa (config := {})\n",
        "theorem oi1 (n : Nat) : n = n := by\n  open Nat in rfl\n",
        "theorem wo4 (n : Nat) : n = n := by\n  cases n with rfl\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A bracket after an operator whose right side is above precedence 25 starts no dependent arrow
/// (`leading_parser:25`): `xs = [b] → q` is `(xs = [b]) → q`, so `h e` proves `q`. Read as
/// `xs = ([b] → q)`, `[b]` would be an instance binder.
#[test]
fn a_bracket_after_a_tight_operator_is_a_list_not_a_binder() {
    check(
        "theorem m3 (xs : List Nat) (b : Nat) (q : Prop) (h : xs = [b] → q) (e : xs = [b]) : q := \
         h e\n",
    );
}

/// A binder default in a dependent arrow or a `∀` (`(h : i = i := by rfl) → Nat`) parses as the
/// pin's `binderTactic`/`binderDefault`; the binder's type is then `optParam`/`autoParam`, which the
/// checker does not build, so it refuses each file, all of which the pin accepts.
#[test]
fn binder_defaults_in_arrows_and_foralls_are_refused_not_dropped() {
    let (engine, limits) = engine();
    for source in [
        "def bt2 : (i : Nat) → (h : i = i := by rfl) → Nat := fun i _ => i\n",
        "theorem bt4 : ∀ (i : Nat) (h : i = i := by rfl), i = i := fun _ h => h\n",
        "def bt5 : (i : Nat) → (j : Nat := 3) → Nat := fun i j => i + j\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `let mut x := …` and a reassignment `x := …` / `x ← …` parse as the pin's `doLet` with its
/// `mut` slot, `doReassign` and `doReassignArrow`; the checker does not thread mutable variables,
/// so it refuses each file, all of which the pin accepts.
#[test]
fn mutable_do_variables_are_refused_not_dropped() {
    let (engine, limits) = engine();
    for source in [
        "def lm1 (n : Nat) : Id Nat := do\n  let mut x := n\n  x := x + 1\n  return x\n",
        "def lm5 (n : Nat) : Nat := Id.run do\n  let mut x : Nat := n\n  return x\n",
        "def lm6 (n : Nat) : Nat := Id.run do\n  let mut x := n\n  for i in [1, 2] do\n    \
         x := x + i\n  return x\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// Alternatives sharing a right-hand side (`| 0 | 1 => 0`) parse as the pin's `matchAlt` with two
/// pattern groups. The checker reads one group per alternative, so it refuses the file, which the
/// pin accepts; it never keeps the first group alone, which would let `sa1 1 = 1` through.
#[test]
fn shared_match_alternatives_are_refused_not_truncated() {
    let (engine, limits) = engine();
    let sa1 = "def sa1 : Nat → Nat\n  | 0 | 1 => 0\n  | _ => 1\n";
    for source in [
        format!("{sa1}theorem sa1_one : sa1 1 = 0 := rfl\n"),
        format!("{sa1}theorem sa1_wrong : sa1 1 = 1 := rfl\n"),
        "def sa2 (o : Option Nat) : Nat :=\n  match o with | none | some 0 => 0 | some _ => 1\n"
            .to_owned(),
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `h : P := by tac` is the pin's `binderTactic` (an `autoParam` field): an omitted field is filled
/// by running its tactic, as the checker read it before its tree was the pin's, and a field whose
/// tactic cannot prove it is refused.
#[test]
fn tactic_fields_are_filled_by_their_tactic() {
    check("structure BT3 where\n  x : Nat\n  h : x = x := by rfl\ndef b3 : BT3 := { x := 1 }\n");
    let (engine, limits) = engine();
    let source = "structure BT4 where\n  x : Nat\n  h : x = x + 1 := by rfl\ndef b4 : BT4 := { x := 1 }\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A local defined by equations (`let rec go : Nat → Nat | 0 => 0 | k + 1 => …`) parses as the
/// pin's `letEqnsDecl`; the checker does not read it, so it refuses each file, which the pin
/// accepts.
#[test]
fn local_equations_are_refused_not_misread() {
    let (engine, limits) = engine();
    for source in [
        "def le1 (n : Nat) : Nat :=\n  let rec go : Nat → Nat\n    | 0 => 0\n    | k + 1 => go k + 1\n  go n\n",
        "def le2 (n : Nat) : Nat :=\n  let f : Nat → Nat\n    | 0 => 1\n    | _ => 2\n  f n\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `a ≈ b` is `HasEquiv.Equiv a b` (`infix:50`, `Init/Core.lean`), never `a = b`. The source
/// seed has no `HasEquiv`: the test declares a `Prop`-valued one with a global instance whose
/// relation is `True`, so `2 ≈ 3` holds by `True.intro` and `2 ≈ 2` is not `rfl`.
#[test]
fn equivalence_is_has_equiv() {
    let class = "class HasEquiv (α : Type) where\n  Equiv : α → α → Prop\n\
                 instance trivialEquiv : HasEquiv Nat := { Equiv := fun _ _ => True }\n";
    check(&format!("{class}theorem eq1 : (2 : Nat) ≈ 3 := True.intro\n"));
    let (engine, limits) = engine();
    let source = format!("{class}theorem eq2 : (2 : Nat) ≈ 2 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A term `let ⟨a, b⟩ := p` (`letPatDecl`) is `match p with | ⟨a, b⟩ => …`, and with a type
/// `match (p : T) with …`: `lp1 ⟨2, 3⟩` is `5` and `lp2 ⟨2, 3⟩` is `1`, never `6`.
#[test]
fn a_pattern_let_destructures_its_value() {
    let lp1 = "structure Pair where\n  fst : Nat\n  snd : Nat\n\
               def lp1 (p : Pair) : Nat :=\n  let ⟨a, b⟩ := p\n  a + b\n\
               def lp2 (p : Pair) : Nat :=\n  let ⟨a, b⟩ : Pair := p; b - a\n";
    check(&format!(
        "{lp1}theorem lp1_ok : lp1 (Pair.mk 2 3) = 5 := rfl\n\
         theorem lp2_ok : lp2 (Pair.mk 2 3) = 1 := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{lp1}theorem lp1_wrong : lp1 (Pair.mk 2 3) = 6 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `if let p := e then a else b` is `match e with | p => a | _ => b`: `til1 (some 5)` is `5`,
/// `til1 none` is `0`, and a wrong value is refused.
#[test]
fn term_if_let_is_the_match_it_abbreviates() {
    let til1 = "def til1 (o : Option Nat) : Nat := if let Option.some n := o then n else 0\n";
    check(&format!(
        "{til1}theorem til1_some : til1 (Option.some 5) = 5 := rfl\n\
         theorem til1_none : til1 Option.none = 0 := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{til1}theorem til1_wrong : til1 (Option.some 5) = 0 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `instance … where` with no field takes every field's default: `x` is `1`.
#[test]
fn an_empty_where_instance_takes_the_defaults() {
    let class = "class EW1 (α : Type) where\n  x : Nat := 1\ninstance : EW1 Nat where\n";
    check(&format!(
        "{class}theorem ew : (inferInstance : EW1 Nat).x = 1 := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{class}theorem ew_wrong : (inferInstance : EW1 Nat).x = 2 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// The ranges with an unbounded side are their `Std` structures' constructors (`macro_rules` in
/// `Init/Data/Range/Polymorphic/PRange.lean`): `*...b`/`*...<b` `Rio.mk b`, `*...=b` `Ric.mk b`,
/// `a...*` `Rci.mk a`, `a<...*` `Roi.mk a`, `*...*` `Rii.mk`; a prefix range's bound is a whole
/// term (`*...n + 1` has upper bound `n + 1`). The source seed has no ranges: the test declares
/// the structures.
#[test]
fn unbounded_ranges_are_their_structures() {
    let ranges = "namespace Std\n\
                  structure Rio (α : Type) where\n  upper : α\n\
                  structure Ric (α : Type) where\n  upper : α\n\
                  structure Rci (α : Type) where\n  lower : α\n\
                  structure Roi (α : Type) where\n  lower : α\n\
                  end Std\n";
    check(&format!(
        "{ranges}def below (n : Nat) : Std.Rio Nat := *...n + 1\n\
         theorem below_upper : (below 5).upper = 6 := rfl\n\
         def open_below (n : Nat) : Std.Rio Nat := *...<n\n\
         def at_most (n : Nat) : Std.Ric Nat := *...=n\n\
         theorem at_most_upper : (at_most 4).upper = 4 := rfl\n\
         def starting (n : Nat) : Std.Rci Nat := n...*\n\
         theorem starting_lower : (starting 3).lower = 3 := rfl\n\
         def above (n : Nat) : Std.Roi Nat := n<...*\n"
    ));
    let (engine, limits) = engine();
    for wrong in [
        "def wrong_kind (n : Nat) : Std.Rio Nat := *...=n\n",
        "def below (n : Nat) : Std.Rio Nat := *...n + 1\n\
         theorem below_wrong : (below 5).upper = 5 := rfl\n",
    ] {
        let source = format!("{ranges}{wrong}");
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A `where` declaration's termination hints are parsed with it (`letRecDecl`'s
/// `Termination.suffix`), and the elaborator, which reads no termination hint, refuses the
/// definition rather than dropping them; without hints the same definition is admitted.
#[test]
fn where_termination_hints_are_refused_not_dropped() {
    check("def plain (n : Nat) : Nat := go n where\n  go (i : Nat) : Nat := i\n");
    let (engine, limits) = engine();
    for source in [
        "def hinted (n : Nat) : Nat := go n where\n  go (i : Nat) : Nat := i\n  termination_by i\n",
        // A term `let rec`'s hints (`letRecDecl`'s suffix) likewise.
        "def hinted_let (n : Nat) : Nat :=\n  let rec go (i : Nat) : Nat := i\n  termination_by i\n  go n\n",
    ] {
        match engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        ) {
            Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
            Ok(_) => {}
            Err(error) => {
                assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}");
            }
        }
    }
}

/// `e matches p | q` is `match e with | p => true | q => true | _ => false`: `isSome` and
/// `small` compute the matching `Bool`, and a wrong value is refused.
#[test]
fn matches_is_the_boolean_match() {
    let defs = "def isSome (o : Option Nat) : Bool := o matches Option.some _\n\
                def small (n : Nat) : Bool := n matches 0 | 1\n";
    check(&format!(
        "{defs}theorem s1 : isSome (Option.some 3) = true := rfl\n\
         theorem s2 : isSome Option.none = false := rfl\n\
         theorem m1 : small 1 = true := rfl\ntheorem m2 : small 2 = false := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{defs}theorem wrong : small 2 = true := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `↑x` parses as the pin's `coeNotation`; the elaborator does not insert coercions, so it
/// refuses the file after parsing, never reading `↑x` as `x`.
#[test]
fn the_coercion_arrow_is_refused_after_parsing() {
    let (engine, limits) = engine();
    let source = "def up (n : Nat) : Nat := ↑n\n";
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits)) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}

/// `f $ x` is the application `f x` with `x` read at the lowest precedence: `dl Nat.succ 1` is
/// `Nat.succ (1 + 1)`, `3`, never `Nat.succ 1 + 1` read another way; a wrong value is refused.
#[test]
fn dollar_applies_its_function_to_the_rest() {
    let dl = "def dl (f : Nat → Nat) (x : Nat) : Nat := f $ x + 1\n";
    check(&format!("{dl}theorem dl_ok : dl Nat.succ 1 = 3 := rfl\n"));
    let (engine, limits) = engine();
    let source = format!("{dl}theorem dl_wrong : dl (fun n => n * 2) 1 = 3 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A definition's `deriving` clause is the pin's `optDefDeriving`; the checker derives no instance,
/// so it refuses the definition after parsing rather than admit it without them.
#[test]
fn definition_deriving_is_refused_after_parsing() {
    check("def Plain := Nat\n");
    let (engine, limits) = engine();
    let source = "def Derived := Nat\nderiving Inhabited\n";
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits)) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}

/// An `inductive` after `private`/`public`/attributes parses with the pin's `declModifiers`; the
/// elaborator reads only a doc comment there and refuses the rest after parsing.
#[test]
fn inductive_modifiers_are_refused_after_parsing() {
    check("/-- doc -/\ninductive Documented where\n  | a\n");
    let (engine, limits) = engine();
    let source = "private inductive Hidden where\n  | a\n";
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits)) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}

/// A tactic `have ⟨a, b⟩ := h` parses as the pin's `letPatDecl`; the tactic elaborator reads a
/// named declaration only, so it refuses the proof after parsing rather than drop the pattern.
#[test]
fn tactic_pattern_bindings_are_refused_after_parsing() {
    let (engine, limits) = engine();
    let source = "theorem tp (p q : Prop) (h : And p q) : p := by\n  have ⟨hp, hq⟩ := h\n  exact hp\n";
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits)) {
        Ok(fln::Outcome::Complete(_)) => panic!("{source}"),
        Ok(_) => {}
        Err(error) => assert!(format!("{error:?}").contains("Elaborate"), "{source}\n{error:?}"),
    }
}

/// Constructor docs: an `inductive` without `where` whose constructors carry doc comments is
/// admitted (a doc has no meaning to the kernel); a structure's named constructor after its doc or
/// `private` (`structCtor`) is refused, as a named constructor always is.
#[test]
fn constructor_docs_lead_their_constructors() {
    check(
        "inductive CD3\n  /-- One. -/\n  | one\n  /-- Two. -/\n  | two\n\
         def cd3 : CD3 := CD3.two\n",
    );
    let (engine, limits) = engine();
    for source in [
        "structure CD1 where\n  /-- The constructor. -/\n  mk ::\n  x : Nat\n",
        "structure CD2 where\n  private mk ::\n  x : Nat\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A structure's or class's modifiers (`private`, `@[ext]`, `public`) build the pin's
/// `declModifiers`; the checker models neither private names, nor the attribute, nor the module
/// system's visibility, so it refuses each file, all of which the pin accepts.
#[test]
fn structure_modifiers_are_refused_not_dropped() {
    let (engine, limits) = engine();
    for source in [
        "private structure SM1 where\n  x : Nat\n",
        "@[ext] structure SM2 where\n  x : Nat\n",
        "public class SM5 (α : Type) where\n  op : α → α\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A bare binder (`def bb1 α [Inhabited α]`, `let f x := …`) and a pattern ellipsis
/// (`.succ ..`) parse as the pin's trees; the checker reads neither, so it refuses each file,
/// all of which the pin accepts.
#[test]
fn bare_binders_and_pattern_ellipses_are_refused_not_misread() {
    let (engine, limits) = engine();
    for source in [
        "def bb1 α [Inhabited α] : α := default\n",
        "abbrev bb2 α β := α × β\n",
        "def bb3 (n : Nat) : Nat :=\n  match n with\n  | .succ .. => 1\n  | .zero => 0\n",
        "def bb4 (o : Option (Nat × Nat)) : Nat :=\n  match o with\n  | some (.mk ..) => 1\n  \
         | none => 0\n",
        "def bb5 (n : Nat) : Nat :=\n  let f x := x + 1\n  f n\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `a <|> b` (`HOrElse.hOrElse a fun _ => b`) and `exists e, …` (a macro for
/// `refine ⟨e, …, ?_⟩; try trivial`) parse as the pin's trees; the checker reads neither, so it
/// refuses both files, which the pin accepts.
#[test]
fn or_else_and_exists_are_refused_not_misread() {
    let (engine, limits) = engine();
    for source in [
        "def oe (a b : Option Nat) : Option Nat := a <|> b\n",
        "theorem ex2 : ∃ a b : Nat, a + b = 3 := by exists 1, 2\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// `|>` and `<|` share precedence `min`, and `|>`'s right operand is `term:min1`, so
/// `5 |> Nat.sub <| 3` is `(5 |> Nat.sub) <| 3`, `Nat.sub 5 3 = 2`; read as
/// `5 |> (Nat.sub <| 3)` it would be `Nat.sub 3 5 = 0`.
#[test]
fn a_forward_pipe_ends_before_a_backward_one() {
    check("theorem forward : (5 |> Nat.sub <| 3) = 2 := rfl\n");
    let (engine, limits) = engine();
    let source = "theorem nested : (5 |> Nat.sub <| 3) = 0 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `e |>.f args` is `(e).f args`: a field, a method with arguments, and a chain.
#[test]
fn a_pipeline_projection_is_its_field_application() {
    check(
        "structure Pair where\n  first : Nat\n  second : Nat\n\
         def p : Pair := { first := 1, second := 2 }\n\
         theorem field : (p |>.second) = 2 := rfl\n\
         theorem method : ([1, 2, 3] |>.length) = 3 := rfl\n\
         theorem chained : ([1, 2] |>.append [3] |>.length) = 3 := rfl\n",
    );
    let (engine, limits) = engine();
    let source = "theorem wrong : ([1, 2, 3] |>.length) = 4 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `fun ⟨x, _⟩ => x` destructures its argument as `fun | ⟨x, _⟩ => x` does, also next to an
/// ordinary binder.
#[test]
fn a_pattern_binder_destructures_the_lambdas_argument() {
    check(
        "structure Pair where\n  first : Nat\n  second : Nat\n\
         def left : Pair → Nat := fun ⟨x, _⟩ => x\n\
         def total : Nat → Pair → Nat := fun n ⟨a, b⟩ => n + a + b\n\
         theorem left_ok : left ⟨3, 4⟩ = 3 := rfl\n\
         theorem total_ok : total 1 ⟨2, 3⟩ = 6 := rfl\n",
    );
    let (engine, limits) = engine();
    let source = "structure Pair where\n  first : Nat\n  second : Nat\n\
                  def left : Pair → Nat := fun ⟨x, _⟩ => x\n\
                  theorem wrong : left ⟨3, 4⟩ = 4 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `no_index e` elaborates as `e` (it only affects simp's indexing).
#[test]
fn no_index_is_its_term() {
    check("theorem kept : no_index (1 + 1) = 2 := rfl\n");
    let (engine, limits) = engine();
    let source = "theorem wrong : no_index (1 + 1) = 3 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A `where` field defined by equations is that field as a pattern lambda; a theorem whose type
/// ends in a `match` reads every alternative as the match's.
#[test]
fn field_equations_and_matches_in_types_check() {
    check(
        "structure Flip where\n  flip : Bool → Bool\n\
         def f : Flip where\n  flip\n    | true => false\n    | false => true\n\
         theorem flipped : f.flip true = false := rfl\n\
         theorem typed (b : Bool) : b = match b with | true => true | false => false := by\n  \
         cases b <;> rfl\n",
    );
    let (engine, limits) = engine();
    let source = "structure Flip where\n  flip : Bool → Bool\n\
                  def f : Flip where\n  flip\n    | true => false\n    | false => true\n\
                  theorem wrong : f.flip true = true := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

const COND: &str = "def cond {α : Type} (c : Bool) (x y : α) : α :=\n  match c with\n  | true => x\n  | false => y\n";

/// `. tac` is the focus `· tac` in its ASCII spelling (`cdotTk := unicode("· ", ". ")`).
#[test]
fn the_ascii_focus_dot_solves_one_goal() {
    check(
        "theorem both (p q : Prop) (hp : p) (hq : q) : And p q := by\n  constructor\n  . exact hp\n  . exact hq\n",
    );
    let (engine, limits) = engine();
    let source = "theorem swapped (p q : Prop) (hp : p) (hq : q) : And p q := by\n  constructor\n  . exact hq\n  . exact hp\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `‹T›` is `(by assumption : T)`: a hypothesis of that type, which must be in scope.
#[test]
fn the_assumption_notation_finds_its_hypothesis() {
    check("theorem found (p q : Prop) (hq : q) (hp : p) : p := ‹p›\n");
    let (engine, limits) = engine();
    let source = "theorem missing (p q : Prop) (hq : q) : p := ‹p›\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `bif c then a else b` is `cond c a b`: it reduces to the branch its condition selects.
#[test]
fn a_boolean_conditional_selects_its_branch() {
    // The source seed has no `cond`: the test declares Init's (`Init/Prelude.lean`).
    check(&format!(
        "{COND}{AND}theorem yes : (bif true then 1 else 2) = 1 := rfl\n\
         theorem no : (bif false && true then 1 else 2) = 2 := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{COND}theorem wrong : (bif true then 1 else 2) = 2 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `grind_pattern` parses as the pin's `Command.grindPattern`; the checker does not read the
/// pattern, so it refuses the command rather than ignoring it.
#[test]
fn grind_patterns_are_refused_not_ignored() {
    check("theorem plain : True := True.intro\n");
    let (engine, limits) = engine();
    let source = "theorem plain : True := True.intro\ngrind_pattern plain => True\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A `section` with a header parses as the pin's `Command.section` with its `sectionHeader`, and
/// `export` as `Command.export`; the scope layer refuses an attribute command or an `open … in` it
/// does not model. The pin accepts each of these files; the checker models neither the module
/// system's `public`, nor `noncomputable` scopes, nor export aliases, nor the `inline` attribute,
/// nor `open` of selected names, nor syntax and notation declarations, nor conv mode, so it
/// refuses them rather than reading a plain scope or dropping what it does not read.
#[test]
fn headed_sections_and_exports_are_refused_not_read_as_plain_scopes() {
    check("section\ntheorem plain : True := True.intro\nend\n");
    let (engine, limits) = engine();
    for source in [
        "public section\ntheorem plain : True := True.intro\nend\n",
        "noncomputable section\ntheorem plain : True := True.intro\nend\n",
        "@[expose] public section\ntheorem plain : True := True.intro\nend\n",
        "theorem plain : True := True.intro\nexport Nat (succ)\n",
        "def d : Nat := 1\nattribute [inline] d\n",
        "open Nat (succ) in\ntheorem plain : True := True.intro\n",
        "syntax \"plain_tactic\" : tactic\ntheorem plain : True := True.intro\n",
        "infixl:65 \" +++ \" => Nat.add\ntheorem plain : True := True.intro\n",
        "theorem plain (a : Nat) : a = a := by\n  conv => lhs\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// While its body elaborates, `letI`'s value shows and `haveI`'s does not, as for `let` and
/// `have`: the pin accepts `shown` and refuses `hidden` with a type mismatch at `rfl`.
#[test]
fn an_inlined_let_shows_its_value_and_an_inlined_have_hides_it() {
    check("theorem shown : True := letI n : Nat := 7; have h : n = 7 := rfl; True.intro\n");
    let (engine, limits) = engine();
    let source = "theorem hidden : True := haveI n : Nat := 7; have h : n = 7 := rfl; True.intro\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `def d : T where fields` is `def d : T := { fields }` for any declaration, as for an instance
/// (`declVal`): each field holds its own value.
#[test]
fn a_declaration_where_body_is_its_structure_instance() {
    let pair = "structure Pair where\n  first : Nat\n  second : Nat\n\
                def paired : Pair where\n  first := 1\n  second := 2\n";
    check(&format!("{pair}theorem first : paired.first = 1 := rfl\n"));
    let (engine, limits) = engine();
    let source = format!("{pair}theorem swapped : paired.first = 2 := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `∀ n ≠ k, p` is `∀ n, n ≠ k → p`, the pin's `macro_rules` in `Init/BinderPredicates.lean`:
/// a hypothesis of the hand-written expansion proves the notation exactly, and its twin with
/// another bound is refused. (The seed has no `Exists`, and its `<` is the scalar `Nat.decLt`
/// rather than `LT.lt`, so `∃` and `<` are covered by their parse rows only.)
#[test]
fn a_binder_predicate_is_its_hypothesis() {
    check("theorem same (h : ∀ n, n ≠ (0 : Nat) → n = n) : ∀ n ≠ (0 : Nat), n = n := h\n");
    let (engine, limits) = engine();
    let source = "theorem other (h : ∀ n, n ≠ (0 : Nat) → n = n) : ∀ n ≠ (1 : Nat), n = n := h\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A declaration binder may be the hole `_` (`binderIdent`): it binds a name no source
/// identifier spells, and the rest of the signature is checked as usual.
#[test]
fn a_hole_binder_binds_an_unnamed_parameter() {
    check("theorem unnamed {_ : Nat} (_ _ : Nat) (n : Nat) : n = n := rfl\n");
    let (engine, limits) = engine();
    let source = "theorem unproved (_ : Nat) (n : Nat) : n = n + 1 := rfl\n";
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `{n : Nat // n = 3}` is `Subtype (fun (n : Nat) => n = 3)` (`Init/Notation.lean:579`): its
/// value carries the predicate's proof, and a value without one is refused. The seed has no
/// `Subtype`, so the root one the macro names is declared here.
#[test]
fn a_subtype_is_its_predicate_carrier() {
    let subtype =
        "structure Subtype {A : Type} (p : A → Prop) where\n  val : A\n  property : p val\n";
    check(&format!(
        "{subtype}def three : {{n : Nat // n = 3}} := ⟨3, rfl⟩\n\
         theorem value : three.val = 3 := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{subtype}def four : {{n : Nat // n = 3}} := ⟨4, rfl⟩\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `#[a, b]` is `List.toArray [a, b]` (`Init/Data/Array/Basic.lean`). The seed has no
/// `Array`, so the root `List.toArray` the macro names is declared here; over Init the pin
/// accepts `literal` and refuses `swapped` the same way.
#[test]
fn an_array_literal_is_its_list_converted() {
    let array = "structure Array (A : Type) where\n  toList : List A\n\
                 def List.toArray {A : Type} (l : List A) : Array A := Array.mk l\n";
    check(&format!(
        "{array}theorem literal : #[1, 2] = List.toArray [1, 2] := rfl\n"
    ));
    let (engine, limits) = engine();
    let source = format!("{array}theorem swapped : #[1, 2] = List.toArray [2, 1] := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `(a, b, c)` is `Prod.mk a (Prod.mk b c)`: the pin's `mkPairs` nests to the right
/// (`Lean/Elab/BuiltinNotation.lean:247`), so the left-nested reading is a type error.
#[test]
fn a_tuple_is_its_right_nested_pairs() {
    let prod = "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n";
    check(&format!(
        "{prod}theorem second (a b : Nat) : (a, b).2 = b := rfl\n\
         theorem nested (a b c : Nat) : (a, b, c) = Prod.mk a (Prod.mk b c) := rfl\n"
    ));
    let (engine, limits) = engine();
    let source =
        format!("{prod}theorem left (a b c : Nat) : (a, b, c) = Prod.mk (Prod.mk a b) c := rfl\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// `f[1]` is index notation (`syntax:max term noWs "[" … "]"`, `Init/GetElem.lean:81`), not `f`
/// applied to the list `[1]`: the pin finds no `GetElem` instance for a function and refuses
/// the theorem that the application reading proves.
#[test]
fn an_unspaced_bracket_indexes_rather_than_applies() {
    let preamble = "theorem applied (f : List Nat → Nat) (h : ∀ l, f l = 0) : ";
    check(&format!("{preamble}f [1] = 0 := h _\n"));
    let (engine, limits) = engine();
    let source = format!("{preamble}f[1] = 0 := h _\n");
    assert!(
        !matches!(
            engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            ),
            Ok(fln::Outcome::Complete(_))
        ),
        "{source}"
    );
}

/// A tactic this elaborator parses but cannot run (`omega`) is refused, never skipped: under
/// `try` the pin's `omega` closes the goal and the following `rfl` then fails, so the pin
/// rejects what skipping `omega` would accept. The tactic `if` (the pin's `tacDepIfThenElse`) is
/// refused too: the pin rejects `one_branch`, whose `else` branch fails, so running only the
/// `then` branch would accept it.
#[test]
fn a_parsed_tactic_without_an_elaborator_is_refused_even_under_try() {
    check("theorem skipped (a : Nat) : a + 0 = a := by\n  try skip\n  rfl\n");
    let (engine, limits) = engine();
    for source in [
        "theorem bare (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega\n",
        "theorem attempted (a : Nat) : a + 0 = a := by\n  try omega\n  rfl\n",
        "theorem one_branch (n : Nat) : n = 0 := by\n  if h : n = 0 then\n    exact h\n  else\n    rfl\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A simp rule that is a proof script is refused, never dropped. The pin parses each of these
/// and then refuses it (`rfl` meets a metavariable goal); without the rule each would close.
#[test]
fn a_proof_script_simp_rule_is_refused_rather_than_dropped() {
    for (tactic, goal) in [
        ("simp only", "(x : Nat) : x = x"),
        ("simp_all only", ": True"),
        ("simpa only", ": True"),
    ] {
        check(&format!("theorem dropped {goal} := by {tactic} []\n"));
        let (engine, limits) = engine();
        let source = format!("theorem kept {goal} := by {tactic} [by rfl]\n");
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}

/// A `by` inside a tactic's term argument is its own proof: it closes the goal it proves and
/// is refused on one it cannot.
#[test]
fn a_proof_nested_in_a_tactic_term_closes_only_what_it_proves() {
    check("theorem nested (h : 1 = 1) : 1 = 1 ∧ 2 = 2 := by exact ⟨h, by rfl⟩\n");
    let (engine, limits) = engine();
    // The pin parses each of these and refuses it in elaboration: a goal the nested proof does
    // not close, a nested proof as a `cases` target (not an inductive premise), and a `have`
    // whose nested `rfl` has no relation to close.
    for source in [
        "theorem unproved (h : 1 = 1) : 1 = 1 ∧ 2 = 3 := by exact ⟨h, by rfl⟩\n",
        "theorem target (b : Bool) : 0 = 0 := by cases (by cases b)\n",
        "theorem value : 0 = 0 := by\n  have h := (by rfl)\n",
    ] {
        assert!(
            !matches!(
                engine.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
                ),
                Ok(fln::Outcome::Complete(_))
            ),
            "{source}"
        );
    }
}
