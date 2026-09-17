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
        "instDecidableImplies",
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
