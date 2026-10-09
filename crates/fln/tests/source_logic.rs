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
/// rejects what skipping `omega` would accept.
#[test]
fn a_parsed_tactic_without_an_elaborator_is_refused_even_under_try() {
    check("theorem skipped (a : Nat) : a + 0 = a := by\n  try skip\n  rfl\n");
    let (engine, limits) = engine();
    for source in [
        "theorem bare (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega\n",
        "theorem attempted (a : Nat) : a + 0 = a := by\n  try omega\n  rfl\n",
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
    let source = "theorem unproved (h : 1 = 1) : 1 = 1 ∧ 2 = 3 := by exact ⟨h, by rfl⟩\n";
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
