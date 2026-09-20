//! Source -> native search -> ordinary admission through both kernel engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};

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
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
}

#[test]
fn local_search_chains_lemmas_and_solves_multiple_premises() {
    check(
        r#"
        theorem direct (p : Prop) (h : p) : p := by solve_by_elim
        theorem chain (p q r : Prop) (hp : p) (f : p -> q) (g : q -> r) : r := by solve_by_elim
        theorem combine (p q r : Prop) (hp : p) (hq : q) (f : p -> q -> r) : r := by solve_by_elim
        theorem repeat_argument (p q : Prop) (hp : p) (f : p -> p -> q) : q := by solve_by_elim
    "#,
    );
}

#[test]
fn local_search_backtracks_between_lemmas_and_around_cycles() {
    check(
        r#"
        theorem alternate (p q r : Prop) (hp : p) (good : p -> r) (bad : q -> r) : r := by solve_by_elim
        theorem cyclic (p q r : Prop) (hp : p) (f : p -> q) (g : q -> r) (loop : r -> r) : r := by solve_by_elim
        theorem mutual_cycle (p q r : Prop) (hp : p) (good : p -> r) (f : q -> r) (g : r -> q) : r := by solve_by_elim
    "#,
    );
}

#[test]
fn later_dependent_premises_backtrack_into_earlier_witness_choices() {
    check(
        r#"
        theorem witness (P : Nat -> Prop) (q : Prop) (x y : Nat) (hx : P x)
            (step : (n : Nat) -> P n -> q) : q := by solve_by_elim
        theorem implicit_witness (P : Nat -> Prop) (q : Prop) (x y : Nat) (hx : P x)
            (step : {n : Nat} -> P n -> q) : q := by solve_by_elim
    "#,
    );
}

#[test]
fn search_retains_polymorphic_local_telescopes() {
    check(
        r#"
        theorem polymorphic.{u} (A : Sort u) (P : A -> Prop) (q : Prop)
            (x y : A) (hx : P x) (step : {a : A} -> P a -> q) : q := by solve_by_elim
    "#,
    );
}

#[test]
fn search_composes_with_introduction_construction_and_tactic_alternatives() {
    check(
        r#"
        theorem introduced (p q : Prop) : (p -> q) -> p -> q := by
          intro f hp
          solve_by_elim
        theorem pair (p q : Prop) (hp : p) (f : p -> q) : And p q := by
          constructor <;> solve_by_elim
        theorem alternatives (p q : Prop) (hp : p) (f : p -> q) : q := by
          first | (solve_by_elim; fail) | solve_by_elim
        theorem recover (p : Prop) (hp : p) : Or p False := by
          first | solve_by_elim | (left; solve_by_elim)
        theorem local_lemma (p q : Prop) (hp : p) (f : p -> q) : q := by
          have available : p -> q := f
          solve_by_elim
    "#,
    );
}

#[test]
fn false_and_cyclic_goals_refuse_atomically_and_leave_the_engine_usable() {
    let (engine, limits) = engine();
    let root = engine.logical_root(&KVMap::new());
    for bad in [
        "theorem bad (p : Prop) : p := by solve_by_elim",
        "theorem bad (p : Prop) (loop : p -> p) : p := by solve_by_elim",
        "theorem bad (p q : Prop) (f : p -> q) (g : q -> p) : q := by solve_by_elim",
        "theorem bad (p : Prop) (hp : p) : False := by solve_by_elim",
        "def bad (f : Nat -> Nat) : Nat := by solve_by_elim",
        "theorem bad (p : Prop) (hp : p) : p := by solve_by_elim; assumption",
    ] {
        let source = format!("def earlier : Nat := 7\n{bad}\n");
        assert!(
            engine
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits),
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
                &[b"theorem recovered (p : Prop) (h : p) : p := by solve_by_elim"],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap();
    }
}
