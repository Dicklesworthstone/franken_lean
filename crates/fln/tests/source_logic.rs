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
/// nor `open` of selected names, so it refuses them rather than reading a plain scope or dropping
/// what it does not read.
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
