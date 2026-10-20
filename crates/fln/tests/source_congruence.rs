//! Source congruence proofs go through ordinary elaboration and both checker seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
}

#[test]
fn congr_closes_unary_nested_and_polymorphic_applications() {
    check("theorem t (A B : Type) (f : A -> B) (a b : A) (h : a = b) : f a = f b := by congr");
    check("theorem t (f g : Nat -> Nat) (a b : Nat) (h : a = b) : f (g a) = f (g b) := by congr");
    check(
        "universe u v\ntheorem t (A : Sort u) (B : Sort v) (f : A -> B) (a b : A) (h : a = b) : f a = f b := by congr",
    );
}

#[test]
fn congr_depth_counts_application_spines_and_preserves_goal_order() {
    check(
        "theorem t (f : Nat -> Nat -> Nat) (a b c d : Nat) (ha : True -> a = c) (hb : True -> b = d) : f a b = f c d := by\n  congr 1\n  guard_target = a = c\n  exact ha True.intro\n  guard_target = b = d\n  exact hb True.intro",
    );
    check(
        "theorem t (f g : Nat -> Nat) (a b : Nat) (h : True -> a = b) : f (g a) = f (g b) := by\n  congr 1\n  guard_target = g a = g b\n  congr 1\n  guard_target = a = b\n  exact h True.intro",
    );
    check(
        "theorem t (f : Nat -> Nat) (a b : Nat) (h : True -> f a = f b) : f a = f b := by\n  congr 0\n  guard_target = f a = f b\n  exact h True.intro",
    );
}

#[test]
fn congr_retains_introductions_lets_and_sibling_proof_controls() {
    check(
        "theorem t (f : Nat -> Nat) : forall (a b : Nat), a = b -> f a = f b := by\n  intro a b h\n  congr",
    );
    check(
        "theorem t (f : Nat -> Nat) (a b : Nat) (h : a = b) : f a = f b := by\n  let c := a\n  have q : f c = f b := by congr\n  exact q",
    );
    check(
        "theorem t (f : Nat -> Nat) (a b : Nat) (h : a = b) : And (f a = f b) (f b = f a) := by\n  constructor\n  · congr\n  · symm\n    congr",
    );
}

#[test]
fn congr_handles_fixed_dependent_parameters_and_irrelevant_proofs() {
    check(
        "theorem t (f : (A : Type) -> A -> Nat) (a b : Nat) (h : a = b) : f Nat a = f Nat b := by congr",
    );
    check(
        "theorem t (P : Prop) (p q : P) (f : P -> Nat -> Nat) (a b : Nat) (h : a = b) : f p a = f q b := by congr",
    );
    check(
        "structure Item where\n value : Nat\n flag : Bool\ntheorem t (a b : Nat) (h : a = b) : Item.mk a true = Item.mk b true := by congr",
    );
}

#[test]
fn congr_keeps_unhandled_targets_and_rolls_back_alternatives() {
    check("theorem t (P : Prop) (h : True -> P) : P := by\n  congr\n  exact h True.intro");
    check(
        "theorem t (f : Nat -> Nat) (a b : Nat) (h : True -> a = b) : f a = f b := by\n  first | (congr 1; fail) | skip\n  guard_target = f a = f b\n  congr\n  exact h True.intro",
    );
}

#[test]
fn congr_never_proves_missing_equalities_or_drops_side_goals() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "theorem bad : 0 = 1 := by congr",
        "theorem bad (P : Prop) : P := by congr",
        "theorem bad (f : Nat -> Nat) (a b : Nat) : f a = f b := by congr",
        "theorem bad (f g : Nat -> Nat) (a : Nat) : f a = g a := by congr",
        "theorem bad (f : Nat -> Nat -> Nat) (a b c d : Nat) (h : a = c) : f a b = f c d := by congr",
    ] {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(limits),
        );
        assert!(!matches!(result, Ok(fln::Outcome::Complete(_))), "{source}");
        assert_eq!(engine.logical_root(&options), root);
    }
}

#[test]
fn congr_transports_dependent_telescope_arguments_and_results() {
    check(
        "theorem t (F : Nat -> Type) (f : (n : Nat) -> F n -> Nat) (n m : Nat) (a : F n) (b : F m) (hn : n = m) (hab : HEq a b) : f n a = f m b := by congr",
    );
    check(
        "theorem t (F : Nat -> Type) (f : (n : Nat) -> F n) (n m : Nat) (hn : n = m) : HEq (f n) (f m) := by congr",
    );
    check(
        "theorem t (F : Nat -> Type) (G : (n : Nat) -> F n -> Type) (f : (n : Nat) -> (a : F n) -> G n a -> Nat) (n m : Nat) (a : F n) (b : F m) (c : G n a) (d : G m b) (hn : n = m) (hab : HEq a b) (hcd : HEq c d) : f n a c = f m b d := by congr",
    );
}

#[test]
fn congr_transports_dependent_proof_arguments_without_extra_axioms() {
    check(
        "theorem t (P : Nat -> Prop) (f : (n : Nat) -> P n -> Nat) (n m : Nat) (a : P n) (b : P m) (h : n = m) : f n a = f m b := by congr",
    );
    check(
        "theorem t (P : Nat -> Prop) (f : (n : Nat) -> P n -> Nat -> Nat) (n m a b : Nat) (p : P n) (q : P m) (h : n = m) (hab : a = b) : f n p a = f m q b := by congr",
    );
}

#[test]
fn dependent_congruence_keeps_equalities_and_hequalities_in_telescope_order() {
    check(
        "theorem t (F : Nat -> Type) (f : (n : Nat) -> F n -> Nat) (n m : Nat) (a : F n) (b : F m) (hn : True -> n = m) (hab : True -> HEq a b) : f n a = f m b := by\n  congr 1\n  guard_target = n = m\n  exact hn True.intro\n  guard_target = HEq a b\n  exact hab True.intro",
    );
}

#[test]
fn congr_decomposes_implication_and_arrow_types_without_function_extensionality() {
    for source in [
        "theorem t (P Q R S : Prop) (h : P = R) (k : Q = S) : (P -> Q) = (R -> S) := by congr",
        "theorem t (A B C D : Type) (h : A = C) (k : B = D) : (A -> B) = (C -> D) := by congr",
        "universe u v\ntheorem t (A C : Sort u) (B D : Sort v) (h : A = C) (k : B = D) : (A -> B) = (C -> D) := by congr",
        "theorem t (P Q R S : Prop) (h : True -> P = R) (k : True -> Q = S) : (P -> Q) = (R -> S) := by\n  congr 1\n  guard_target = P = R\n  exact h True.intro\n  guard_target = Q = S\n  exact k True.intro",
        "theorem t (P Q R S T U : Prop) (h : P = R) (k : Q = S) (l : T = U) : ((P -> Q) -> T) = ((R -> S) -> U) := by congr",
    ] {
        check(source);
    }
}

#[test]
fn congr_dependent_motives_distinguish_repeated_argument_positions() {
    check(
        "theorem t (F : Nat -> Nat -> Type) (f : (n m : Nat) -> F n m -> Nat) (n m k : Nat) (a : F n n) (b : F m k) (h : n = m) (j : n = k) (hab : HEq a b) : f n n a = f m k b := by congr",
    );
    check(
        "universe u v w\ntheorem t (A : Sort u) (F : A -> Sort v) (G : (a : A) -> F a -> Sort w) (f : (a : A) -> (x : F a) -> G a x) (a b : A) (x : F a) (y : F b) (h : a = b) (j : HEq x y) : HEq (f a x) (f b y) := by congr",
    );
}

#[test]
fn congr_cannot_hide_missing_dependent_evidence_or_unsafe_axioms() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (F : Nat -> Type) (f : (n : Nat) -> F n -> Nat) (n m : Nat) (a : F n) (b : F m) (h : n = m) : f n a = f m b := by congr",
        "theorem bad (F : Nat -> Type) (f : (n : Nat) -> F n -> Nat) (n m : Nat) (a : F n) (b : F m) (h : HEq a b) : f n a = f m b := by congr",
        "theorem bad (P Q R S : Prop) (h : P = R) : (P -> Q) = (R -> S) := by congr",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits)
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let unsafe_source = "unsafe def forged (a b : Nat) : a = b := forged a b\ntheorem bad (f : Nat -> Nat) (a b : Nat) : f a = f b := by\n  have h : a = b := forged a b\n  congr";
    let problem = base
        .check_source_files(
            &[unsafe_source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_err();
    assert!(
        format!("{problem:?}").contains("SafetyViolation"),
        "{problem:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    check("theorem recovered (P Q : Prop) (h : P = Q) : (P -> P) = (Q -> Q) := by congr");
}

#[test]
fn arrow_congruence_retains_closed_elimination_terms_and_evidence_dependencies() {
    use fln::Name;
    use fln_core::expr::ExprNode;
    use fln_env::constants::ConstantInfo;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let result = base.check_source_files(
        &[b"axiom P : Prop\naxiom Q : Prop\naxiom h : P = Q\ntheorem retained : (P -> P) = (Q -> Q) := by\n  have evidence : P = Q := h\n  congr"],
        &KVMap::new(), SourceCheckLimits::new(limits),
    ).unwrap().into_complete().unwrap().engine;
    let Some(ConstantInfo::Thm(theorem)) = result
        .environment()
        .find(&Name::from_components(["retained"]))
    else {
        panic!("congruence must publish a theorem with a proof body");
    };
    assert!(!theorem.value.has_fvar());
    assert!(!theorem.value.has_expr_mvar());
    assert!(!theorem.value.has_level_mvar());
    assert!(!theorem.value.has_loose_bvars());
    let mut pending = vec![&theorem.value];
    let mut constants = std::collections::BTreeSet::new();
    while let Some(value) = pending.pop() {
        match value.node() {
            ExprNode::Const { name, .. } => {
                constants.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    assert!(constants.contains(&Name::from_components(["Eq", "rec"])));
    assert!(constants.contains(&Name::from_components(["h"])));
    assert!(!constants.contains(&Name::from_components(["sorryAx"])));
    assert!(!constants.contains(&Name::from_components(["propext"])));
}
