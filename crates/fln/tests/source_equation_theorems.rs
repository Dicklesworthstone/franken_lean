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

const MATCHING: &str = "def pred' : Nat → Nat\n  | 0 => 0\n  | n+1 => n
def fib : Nat → Nat\n  | 0 => 0\n  | 1 => 1\n  | n+2 => fib n + fib (n+1)
def pr : Nat → Nat → Nat\n  | 0, _ => 0\n  | k+1, m => pr k m + m
def bool2 : Bool → Bool → Bool\n  | true, true => true\n  | _, _ => false
def nested : Nat → Nat → Nat\n  | 0, m => match m with | 0 => 0 | m => m\n  | n+1, m => nested n m
section\nvariable (k : Nat)\ndef addk : Nat → Nat\n  | 0 => k\n  | n+1 => addk n + 1\nend
def k2 : Nat → Nat := fun n => match n with\n  | 0 => 1\n  | m+1 => m";

#[test]
fn the_equations_of_a_definition_by_matching_are_proved_and_admitted() {
    let base = check(&engine(), MATCHING);
    for (generated, source) in [
        (
            "pred'.eq_2",
            "theorem t (n : Nat) : pred' (n + 1) = n := pred'.eq_2 n",
        ),
        (
            "fib.eq_3",
            "theorem t (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := fib.eq_3 n",
        ),
        (
            "pr.eq_2",
            "theorem t (n m : Nat) : pr (n + 1) m = pr n m + m := pr.eq_2 m n",
        ),
        (
            "bool2.eq_2",
            "theorem t (a b : Bool) (h : a = true → b = true → False) : bool2 a b = false :=
  bool2.eq_2 a b h",
        ),
        (
            "fib.eq_2",
            "theorem t : fib 0 + fib 1 = 1 := by rw [fib, fib]",
        ),
        (
            "addk.eq_2",
            "theorem t (k n : Nat) : addk k (n + 1) = addk k n + 1 := addk.eq_2 k n",
        ),
        (
            "k2.eq_2",
            "theorem t (n : Nat) : k2 (n + 1) = n := k2.eq_2 n",
        ),
    ] {
        let after = check(&base, source);
        let Some(ConstantInfo::Thm(theorem)) = after.environment().find(&name(generated)) else {
            panic!("{generated} is not an admitted theorem");
        };
        assert!(theorem.base.level_params.is_empty(), "{generated}");
    }
    // A wrong statement is still refused by the kernel, and an equation past the alternatives
    // is no name the pin reserves.
    reject(
        &base,
        "theorem bad (n : Nat) : pred' (n + 1) = n + 1 := pred'.eq_2 n",
    );
    let refused = reject(
        &base,
        "theorem bad : True := (fun _ => True.intro) pred'.eq_3",
    );
    assert!(refused.contains("UnknownConstant"), "{refused}");
}

#[test]
fn previously_realized_pattern_equations_keep_source_simp_fallback() {
    use fln_elab::source::scope::simp;

    let base = engine();
    for proof in [
        "",
        "theorem first : pred' 0 = 0 := pred'.eq_1",
        "theorem first : pred' 0 = 0 := by rw [pred']",
    ] {
        // Keep the definition, first request and attribute in one source file:
        // source ownership permits default simple-equation preparation here.
        let after = check(
            &base,
            &format!(
                "def pred' : Nat → Nat\n  | 0 => 0\n  | n+1 => n\n\
                 {proof}\nattribute [simp] pred'\n\
                 theorem simplified : pred' 0 = 0 := by simp"
            ),
        );
        for equation in ["pred'.eq_1", "pred'.eq_2"] {
            assert!(
                matches!(
                    after.environment().find(&name(equation)),
                    Some(ConstantInfo::Thm(_))
                ),
                "{proof}: {equation} remains a checked pattern equation"
            );
        }
        assert!(matches!(
            simp::equations::prepare_owned(
                after.environment(),
                &name("pred'"),
                limits().admission.kernel
            )
            .unwrap(),
            simp::equations::Preparation::Unsupported
        ));
        // Preserving source unfolding must not grant simple-equation
        // provenance or claim portable metadata for the matched definition.
        assert!(matches!(
            simp::export::registrations(base.environment(), after.environment(), 1 << 20),
            Err(simp::SimpSetError::UnsupportedDeclaration(owner)) if owner == name("pred'")
        ));
    }
}

#[test]
fn pattern_simp_does_not_adopt_an_existing_theorem_with_an_unrelated_type() {
    use fln_elab::NatDefinitionElabError;
    use fln_elab::source::SourceInferenceError;
    use fln_elab::source::scope::simp;
    use fln_env::constants::{ConstantVal, TheoremVal};

    let base = check(&engine(), "def pred' : Nat → Nat\n  | 0 => 0\n  | n+1 => n");
    // This is a genuine kernel-checked theorem, but not pred's first equation.
    // Bypass only source reserved-name syntax to exercise the candidate reuse
    // boundary directly; its type must be re-derived from the recorded match.
    let after = base
        .admit_declaration(
            fln::Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: name("pred'.eq_1"),
                    level_params: Vec::new(),
                    type_: fln::Expr::const_(name("True"), Vec::new()),
                },
                value: fln::Expr::const_(name("True.intro"), Vec::new()),
                all: vec![name("pred'.eq_1")],
            }),
            &KVMap::new(),
            limits().admission,
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = after.logical_root(&KVMap::new());
    assert!(matches!(
        simp::equations::prepare_pattern_owned(
            after.environment(),
            &name("pred'"),
            limits().admission.kernel
        ),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::SimpSet(
            simp::SimpSetError::UnsupportedDeclaration(found)
        ))) if found == name("pred'.eq_1")
    ));
    assert_eq!(after.logical_root(&KVMap::new()), root);
}

#[test]
fn an_equation_the_pin_states_with_its_matcher_is_refused_typed() {
    let base = check(&engine(), MATCHING);
    for source in [
        "theorem bad : True := (fun _ => True.intro) fib.eq_def",
        "theorem bad : True := (fun _ => True.intro) fib.eq_unfold",
        "theorem bad : True := (fun _ => True.intro) nested.eq_1",
    ] {
        let refused = reject(&base, source);
        assert!(refused.starts_with("capability"), "{source}: {refused}");
        assert!(refused.contains("MatchInStatement"), "{source}: {refused}");
    }
}
