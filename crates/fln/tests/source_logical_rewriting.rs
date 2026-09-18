//! Logical rewrite rules retain real proof terms and both admission vetoes.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(base: &Engine, source: &str) -> fln::SourceFileCheck {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .expect("checking must complete")
}
fn refuse(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(!matches!(result, Ok(Outcome::Complete(_))), "{source}");
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn iff_rules_rewrite_goals_hypotheses_and_type_valued_contexts() {
    let base = engine();
    let checked = check(
        &base,
        r#"
      theorem forward (P Q : Prop) (h : P ↔ Q) (q : Q) : P := by
        rw [h]
        exact q
      theorem backward (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
        rw [← h]
        exact p
      theorem localType (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
        simp only [h] at p
        exact p
      def dependent (P Q : Prop) (F : Prop -> Type) (h : P ↔ Q) (x : F P) : F Q := by
        rw [← h]
        exact x
      theorem nested (P Q : Prop) (F : Prop -> Prop) (h : P ↔ Q) (x : F Q) : F P := by
        simp only [h]
        exact x
    "#,
    );
    assert_eq!(checked.theorems, 4);
    assert_eq!(checked.commands, 5);
}

#[test]
fn quantified_and_conditional_equivalences_infer_parameters_but_not_premises() {
    let base = engine();
    check(
        &base,
        r#"
      theorem use (P Q : Nat -> Prop) (n : Nat)
          (h : ∀ x : Nat, P x ↔ Q x) (q : Q n) : P n := by
        simp only [h]
        exact q
      theorem conditional (P Q R : Prop) (h : R -> (P ↔ Q)) (r : R) (q : Q) : P := by
        simp only [h, r]
        exact q
    "#,
    );
    for source in [
        "theorem missing (P Q R : Prop) (h : R -> (P ↔ Q)) (q : Q) : P := by simp only [h]; exact q",
        "theorem invalid (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by rw [h]; exact p",
        "theorem falseProof : (0 : Nat) = 1 := by simp only []",
    ] {
        refuse(&base, source);
    }
}

#[test]
fn registered_iff_lemmas_are_persistent_and_explicit_exclusions_still_apply() {
    let base = engine();
    let registered = check(
        &base,
        r#"
      namespace Logic
      def wrap (p : Prop) : Prop := p
      @[simp] theorem unwrap (p : Prop) : wrap p ↔ p := by
        constructor
        · intro h; exact h
        · intro h; exact h
      end Logic
    "#,
    )
    .engine;
    check(
        &registered,
        "theorem normal (p : Prop) : Logic.wrap p = p := by simp",
    );
    refuse(
        &registered,
        "theorem excluded (p : Prop) : Logic.wrap p = p := by simp [-Logic.unwrap]",
    );
    check(
        &registered,
        "theorem retained (p : Prop) : Logic.wrap (Logic.wrap p) = p := by simp",
    );
    assert!(
        fln_elab::source::scope::simp::read(base.environment())
            .unwrap()
            .is_empty()
    );
}

#[test]
fn equivalence_transport_keeps_the_named_axiom_and_the_original_proof() {
    use fln::{ConstantInfo, Name};
    use fln_core::expr::ExprNode;
    let base = engine();
    let result = check(
        &base,
        "theorem transport (P Q : Prop) (h : P ↔ Q) : P = Q := by rw [h]",
    );
    let ConstantInfo::Thm(theorem) = result
        .engine
        .environment()
        .find(&Name::from_components(["transport"]))
        .unwrap()
    else {
        panic!("a theorem, not an axiom");
    };
    let mut work = vec![&theorem.value];
    let mut propext = false;
    let mut transport = false;
    while let Some(term) = work.pop() {
        match term.node() {
            ExprNode::Const { name, .. } => {
                propext |= name == &Name::from_components(["propext"]);
                transport |= name == &Name::from_components(["Eq", "rec"]);
            }
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => work.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => work.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    assert!(
        propext && transport,
        "the actual axiom and checked transport must survive"
    );
    assert!(!theorem.value.has_expr_mvar() && !theorem.value.has_fvar());
    assert!(matches!(
        base.environment().find(&Name::from_components(["propext"])),
        Some(ConstantInfo::Axiom(_))
    ));
    check(
        &base,
        "theorem direct (P Q : Prop) (h : P ↔ Q) : P = Q := propext h",
    );
    check(
        &base,
        "theorem shadow (P Q : Prop) (propext : Nat) (h : P ↔ Q) : P = Q := by rw [h]",
    );
}

#[test]
fn absent_extensionality_and_impostor_relations_cannot_create_a_conversion() {
    use fln::{Environment, Name};
    let mut base = Engine::from_environment(Environment::new());
    for declaration in fln_elab::seed::source_seed_declarations() {
        if declaration == fln_elab::seed::propext_seed_declaration() {
            continue;
        }
        base = base
            .admit_declaration(declaration, &KVMap::new(), limits())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    assert!(
        !base
            .environment()
            .contains(&Name::from_components(["propext"]))
    );
    refuse(
        &base,
        "theorem absent (P Q : Prop) (h : P ↔ Q) : P = Q := by rw [h]",
    );
    check(&base, "theorem oldPath (n : Nat) : n = n := by rfl");
    let base = engine();
    refuse(
        &base,
        "namespace Fake\ninductive Iff (P Q : Prop) : Prop where\n | intro : Iff P Q\nend Fake\ntheorem forged (P Q : Prop) (h : Fake.Iff P Q) : P = Q := by rw [h]",
    );
    refuse(
        &base,
        "@[simp] theorem forged (P Q : Prop) : P ↔ Q := by constructor; intro h; exact h",
    );
    check(&base, "theorem recover (n : Nat) : n = n := by rfl");
}

#[test]
fn conditional_equivalence_failure_restores_alternatives_and_retains_side_goals() {
    let base = engine();
    check(
        &base,
        r#"
      theorem fallback (P Q R : Prop) (h : R -> (P ↔ Q)) (p : P) : P := by
        first | simp only [h] | exact p
      theorem withSideGoal (P Q R : Prop) (h : R -> (P ↔ Q)) (q : Q) (r : R) : P := by
        rw [h]
        exact q
        exact r
    "#,
    );
    refuse(
        &base,
        "theorem missing (P Q R : Prop) (h : R -> (P ↔ Q)) (q : Q) : P := by rw [h]; exact q",
    );
}

#[test]
fn selected_propositions_and_refutations_rewrite_nested_contexts() {
    let base = engine();
    check(
        &base,
        r#"
      theorem truth (P : Prop) (h : P) : P = True := by simp only [h]
      theorem falsehood (P : Prop) (h : ¬ P) : P = False := by simp only [h]
      theorem falseArrow (P : Prop) (h : P -> False) : P = False := by simp only [h]
      theorem terminal (P : Prop) (h : P) : P := by simp only [h]
      theorem trivial : True := by simp only []
      theorem nested (P : Prop) (F : Prop -> Prop) (h : P) (q : F True) : F P := by
        simp only [h]
        exact q
      def typeTransport (P : Prop) (F : Prop -> Type) (h : ¬ P) (q : F False) : F P := by
        simp only [h]
        exact q
      theorem hypothesis (P : Prop) (F : Prop -> Prop) (h : P) (q : F P) : F True := by
        simp only [h] at q
        exact q
      theorem binder (P : Prop) (h : P) : (∀ n : Nat, P) = (∀ n : Nat, True) := by
        simp only [h]
    "#,
    );
}

#[test]
fn quantified_facts_infer_indices_and_keep_conditional_obligations() {
    let base = engine();
    check(
        &base,
        r#"
      theorem positive (P : Nat -> Prop) (h : ∀ n : Nat, P n) (n : Nat) : P n = True := by
        simp only [h]
      theorem negative (P : Nat -> Prop) (h : ∀ n : Nat, ¬ P n) (n : Nat) : P n = False := by
        simp only [h]
      theorem condition (P R : Prop) (h : R -> P) (r : R) : P = True := by
        simp only [h, r]
    "#,
    );
    for source in [
        "theorem missing (P R : Prop) (h : R -> P) (r : R) : P = True := by simp only [h]",
        "theorem cyclic (P : Prop) (h : P -> P) : P := by simp only [h]",
        "theorem data (n : Nat) : False := by simp only [n]",
        "theorem invalid (P : Prop) (h : ¬ P) : P := by simp only [h]",
        "theorem reversed (P : Prop) (h : P) : P = True := by simp only [← h]",
    ] {
        refuse(&base, source);
    }
    check(
        &base,
        "theorem recovery (P : Prop) (h : P) : P := by simp only [h]",
    );
}

#[test]
fn registered_proposition_rules_persist_without_leaking_to_old_snapshots() {
    let base = engine();
    let registered = check(
        &base,
        r#"
      inductive Known (n : Nat) : Prop where
        | intro : Known n
      @[simp] theorem known (n : Nat) : Known n := by constructor
    "#,
    )
    .engine;
    check(
        &registered,
        "theorem uses (n : Nat) : Known n = True := by simp",
    );
    refuse(
        &registered,
        "theorem omitted (n : Nat) : Known n = True := by simp only []",
    );
    refuse(
        &registered,
        "theorem erased (n : Nat) : Known n = True := by simp [-known]",
    );
    check(
        &registered,
        "theorem retained (n : Nat) : Known n = True := by simp",
    );
    assert!(
        fln_elab::source::scope::simp::read(base.environment())
            .unwrap()
            .is_empty()
    );
    for source in [
        "theorem old (P : Prop) (h : P) : P = True := by rw [h]",
        "theorem bad (P : Prop) (h : P) : False := by simp only [h]",
    ] {
        refuse(&base, source);
    }
    check(
        &base,
        r#"
      theorem restored (P Q : Prop) (h : P) (q : Q) : Q := by
        first
        | simp only [h]; fail
        | exact q
    "#,
    );
}
