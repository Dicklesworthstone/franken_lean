//! Equation theorems a source command names are generated before it and admitted through both
//! checkers (the pin's reserved-name action, vendored `Lean/Meta/Eqns.lean`); `rw [f]`
//! rewrites with them (`withRWRulesSeq`, vendored `Lean/Elab/Tactic/Rewrite.lean`).
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::ConstantInfo;

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
fn check(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn reject(base: &Engine, source: &str) -> String {
    let root = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .expect_err(source);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    format!("{} {:?}", error.disposition().0, error)
}
fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

#[test]
fn a_named_equation_is_generated_admitted_and_used() {
    let base = check(&engine(), "def wrapped (n : Nat) : Nat := n + 1");
    assert!(!base.environment().contains(&name("wrapped.eq_1")));
    let after = check(
        &base,
        "theorem result (n : Nat) : wrapped n = n + 1 := wrapped.eq_1 n",
    );
    let Some(ConstantInfo::Thm(theorem)) = after.environment().find(&name("wrapped.eq_1")) else {
        panic!("wrapped.eq_1 is not an admitted theorem");
    };
    assert!(theorem.base.level_params.is_empty());
    assert!(!after.environment().contains(&name("wrapped.eq_def")));
    let unfolded = check(
        &base,
        "theorem result : wrapped = fun n => n + 1 := wrapped.eq_unfold",
    );
    // `eq_unfold` is built from the unfolding theorem, which is generated first.
    for generated in ["wrapped.eq_def", "wrapped.eq_unfold"] {
        assert!(
            unfolded.environment().contains(&name(generated)),
            "{generated}"
        );
    }
}

#[test]
fn rewriting_with_a_definition_uses_its_equations_at_the_goal_and_hypotheses() {
    let base = check(&engine(), "def wrapped (n : Nat) : Nat := n + 1");
    check(
        &base,
        "theorem result (n : Nat) : wrapped (wrapped n) = n + 1 + 1 := by rw [wrapped, wrapped]",
    );
    check(
        &base,
        "theorem result (n : Nat) (h : wrapped n = 5) : n + 1 = 5 := by\n  rw [wrapped] at h\n  exact h",
    );
    check(
        &base,
        "theorem result (n : Nat) : n + 1 = wrapped n := by rw [← wrapped]",
    );
    let refused = reject(&base, "theorem bad (n : Nat) : n = n := by rw [wrapped]");
    assert!(refused.contains("RewriteEquations"), "{refused}");
    reject(
        &base,
        "theorem bad (n : Nat) : wrapped n = n := by rw [wrapped]",
    );
}

#[test]
fn an_equation_beyond_the_generated_ones_is_an_unknown_identifier() {
    let base = check(&engine(), "def wrapped (n : Nat) : Nat := n + 1");
    let refused = reject(
        &base,
        "theorem bad : True := (fun _ => True.intro) wrapped.eq_2",
    );
    assert!(refused.contains("UnknownConstant"), "{refused}");
    assert!(!refused.starts_with("capability"), "{refused}");
}

#[test]
fn a_definition_whose_equations_are_not_generated_is_refused_typed() {
    let base = check(&engine(), "def pred' : Nat → Nat\n  | 0 => 0\n  | n+1 => n");
    for source in [
        "theorem bad (n : Nat) : pred' (n + 1) = n := pred'.eq_2 n",
        "theorem bad (n : Nat) : pred' (n + 1) = n := by rw [pred']",
    ] {
        let refused = reject(&base, source);
        assert!(refused.starts_with("capability"), "{source}: {refused}");
        assert!(refused.contains("EquationTheorem"), "{source}: {refused}");
    }
    assert!(!base.environment().contains(&name("pred'.eq_1")));
}
