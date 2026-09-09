//! Quantified rewriting through the real source parser and dual-checker engine.
#![forbid(unsafe_code)]
use fln::{Engine, EngineAdmissionLimits};
use fln_core::{name::Name, options::KVMap};
use fln_kernel::verdict::Budget;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn admit(base: &Engine, source: &str) -> Engine {
    base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("the ordinary council must complete")
        .engine
}

#[test]
fn rewrite_infers_explicit_parameters_from_the_first_matching_occurrence() {
    let base = engine();
    let base = admit(&base, "def identity (x : Nat) : Nat := x");
    let base = admit(
        &base,
        "theorem identity_eq (x : Nat) : identity x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (x : Nat) : identity x = x := by rw [identity_eq]",
    );
    let base = admit(
        &base,
        "theorem congruent (f : Nat -> Nat) (x : Nat) : f x = f x := by rfl",
    );
    admit(
        &base,
        "theorem use (g : Nat -> Nat) (x : Nat) : g x = g x := by rw [congruent g]",
    );
}

#[test]
fn polymorphic_rewrite_infers_type_and_universe_parameters() {
    let base = engine();
    let base = admit(&base, "def identity {A : Type} (x : A) : A := x");
    let base = admit(
        &base,
        "theorem identity_eq {A : Type} (x : A) : identity x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (x : Nat) : identity x = x := by rw [identity_eq]",
    );
    admit(
        &base,
        "theorem use {A : Type} (x : A) : identity x = x := by rw [identity_eq]",
    );
}

#[test]
fn rewriting_quantified_theorems_retains_the_real_theorem_dependency() {
    let base = engine();
    let base = admit(
        &base,
        "theorem congruence (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [h]",
    );
    let result = admit(
        &base,
        "theorem use (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [congruence f]; exact h",
    );
    let fln_env::constants::ConstantInfo::Thm(theorem) = result
        .environment()
        .find(&Name::from_components(["use"]))
        .unwrap()
    else {
        panic!("the result must be a theorem");
    };
    let mut pending = vec![&theorem.value];
    let mut found = false;
    while let Some(expr) = pending.pop() {
        use fln_core::expr::ExprNode;
        match expr.node() {
            ExprNode::Const { name, .. } if name == &Name::from_components(["congruence"]) => {
                found = true
            }
            ExprNode::App { f, a } => {
                pending.push(f);
                pending.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(binder_type);
                pending.push(body);
            }
            _ => {}
        }
    }
    assert!(
        found,
        "non-definitional transport must retain the actual theorem proof"
    );
}

#[test]
fn reversed_and_partially_applied_rewrite_rules_infer_remaining_arguments() {
    let base = engine();
    let base = admit(&base, "def identity {A : Type} (x : A) : A := x");
    let base = admit(
        &base,
        "theorem compose_identity {A : Type} (f : A -> A) (x : A) : identity (f x) = f x := by rfl",
    );
    admit(
        &base,
        "theorem use (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [<- compose_identity f]",
    );
}

#[test]
fn rewriting_refuses_unresolved_metavariable_pattern_heads() {
    let base = admit(&engine(), "def identity {A : Type} (x : A) : A := x");
    let base = admit(&base, "theorem same (x : Nat) : x = x := by rfl");
    let base = admit(
        &base,
        "theorem congruent (f : Nat -> Nat) (x : Nat) : f x = f x := by rfl",
    );
    let base = admit(
        &base,
        "theorem identity_eq {A : Type} (x : A) : identity x = x := by rfl",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (x : Nat) : x = x := by rw [same]",
        "theorem bad (g : Nat -> Nat) (x : Nat) : g x = g x := by rw [congruent]",
        "theorem bad (x : Nat) : x = identity x := by rw [<- identity_eq]",
    ] {
        let error = base
            .admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
            .expect_err("an unresolved rewrite pattern must be refused");
        assert!(
            error
                .to_string()
                .contains("rewrite pattern has an unresolved metavariable head"),
            "{source}: {error}"
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn conditional_rewrites_leave_side_conditions_for_following_tactics() {
    let base = engine();
    let source = "theorem use (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : y = x := by rw [rule]; exact hp";
    admit(&base, source);
    admit(
        &base,
        "theorem use (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : y = x := by rw [rule hp]",
    );
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.admit_source_declaration(
            b"theorem bad (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : y = x := by rw [rule]",
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn failed_matches_do_not_leak_instantiations_to_later_candidates() {
    let base = engine();
    let base = admit(&base, "def identity {A : Type} (x : A) : A := x");
    let base = admit(
        &base,
        "theorem identity_eq {A : Type} (x : A) : identity x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (x : Nat) : identity x = x := by rw [identity_eq]",
    );
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.admit_source_declaration(
            b"theorem bad : 0 = 1 := by rw [identity_eq]",
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn simp_only_repeats_inside_out_until_nested_occurrences_are_gone() {
    admit(
        &engine(),
        "theorem use (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f (f x)) = x := by simp only [h]",
    );
}

#[test]
fn simp_only_instantiates_quantified_conditional_rules_repeatedly() {
    let base = admit(
        &engine(),
        "theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by exact h",
    );
    admit(
        &base,
        "theorem use (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [contract f, h]",
    );
    let error = base.admit_source_declaration(
        b"theorem bad (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by simp only [contract f]",
        &KVMap::new(), limits()).expect_err("unselected proof is not a simp premise");
    assert!(
        error.to_string().contains("simp only made no progress"),
        "{error}"
    );
}

#[test]
fn rewrite_side_goals_preserve_primary_and_telescope_order() {
    let base = engine();
    admit(
        &base,
        "theorem use (P Q : Prop) (x y z w : Nat) (rp : P -> x = y) (rq : Q -> y = z) (main : z = w) (hp : P) (hq : Q) : x = w := by rw [rp, rq]; exact main; exact hq; exact hp",
    );
    admit(
        &base,
        "theorem use (P Q : Prop) (x y z : Nat) (r : P -> Q -> x = y) (main : y = z) (hp : P) (hq : Q) : x = z := by rw [r]; exact main; exact hp; exact hq",
    );
    for source in [
        "theorem bad (P Q : Prop) (x y z w : Nat) (rp : P -> x = y) (rq : Q -> y = z) (main : z = w) (hp : P) (hq : Q) : x = w := by rw [rp, rq]; exact main; exact hp; exact hq",
        "theorem bad (P Q : Prop) (x y z : Nat) (r : P -> Q -> x = y) (main : y = z) (hp : P) (hq : Q) : x = z := by rw [r]; exact main; exact hq; exact hp",
    ] {
        assert!(
            base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
}

#[test]
fn rewrite_data_goals_can_be_solved_explicitly_or_by_the_primary_goal() {
    let base = admit(
        &engine(),
        "theorem rule (x y : Nat) (h : x = y) (n : Nat) : x = y := by exact h",
    );
    let base = admit(
        &base,
        "theorem conditional (P : Nat -> Prop) (x y : Nat) (h : x = y) (n : Nat) (hp : P n) : x = y := by exact h",
    );
    let base = admit(
        &base,
        "theorem choose (x n : Nat) (h : x = n) : x = n := by exact h",
    );
    admit(
        &base,
        "theorem use (x y : Nat) (h : x = y) : x = y := by rw [rule x y h]; exact 0",
    );
    admit(
        &base,
        "theorem use (P : Nat -> Prop) (x y : Nat) (h : x = y) (hp : P 0) : x = y := by rw [conditional P x y h]; exact 0; exact hp",
    );
    admit(
        &base,
        "theorem use (x y : Nat) (h : x = y) : x = y := by rw [choose x]; exact h",
    );
    let error = base
        .admit_source_declaration(
            b"theorem bad (x y : Nat) (h : x = y) : x = y := by rw [rule x y h]",
            &KVMap::new(),
            limits(),
        )
        .expect_err("unused data is still an obligation");
    assert!(error.to_string().contains("unsolved goals"), "{error}");
}

#[test]
fn rewrite_retains_implicit_arguments_after_new_premises() {
    let base = admit(
        &engine(),
        "theorem rule {A : Type} (f : Nat -> Nat) (x : Nat) : f x = f x := by rfl",
    );
    let error = base
        .admit_source_declaration(
            b"theorem bad (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [rule f]",
            &KVMap::new(),
            limits(),
        )
        .expect_err("unused implicit type remains a goal even if transport erases the rule");
    assert!(error.to_string().contains("unsolved goals"), "{error}");
    admit(
        &base,
        "theorem use (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [rule f]; exact Nat",
    );
    let base = admit(
        &base,
        "theorem conditional {A : Type} (P : Prop) (f : Nat -> Nat) (x : Nat) (h : P) : f x = f x := by rfl",
    );
    admit(
        &base,
        "theorem use (P : Prop) (hp : P) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [conditional P f]; exact hp; exact Nat",
    );
    assert!(
        base.admit_source_declaration(
            b"theorem bad (P : Prop) (hp : P) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [conditional P f]; exact Nat; exact hp",
            &KVMap::new(),
            limits(),
        )
        .is_err()
    );
}

#[test]
fn redundant_rewrites_retain_explicit_rule_arguments_for_checking() {
    let base = admit(
        &engine(),
        "theorem identity (P : Prop) (f : Nat -> Nat) (x : Nat) (h : P) : f x = f x := by rfl",
    );
    admit(
        &base,
        "theorem use (P : Prop) (hp : P) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [identity P f x hp]",
    );
    admit(
        &base,
        "theorem use (P : Prop) (hp : P) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [(fun h => identity P f x h) hp]",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (P : Prop) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [identity P f x Nat]",
        "theorem bad (P : Prop) (f : Nat -> Nat) (x : Nat) : f x = f x := by rw [(fun h => identity P f x h) Nat]",
    ] {
        assert!(
            base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn rewrite_does_not_discharge_even_reflexive_premises() {
    let base = engine();
    let error = base
        .admit_source_declaration(
            b"theorem bad (x y : Nat) (rule : (x = x) -> x = y) : x = y := by rw [rule]",
            &KVMap::new(),
            limits(),
        )
        .expect_err("rw must leave its reflexive premise");
    assert!(error.to_string().contains("unsolved goals"), "{error}");
    admit(
        &base,
        "theorem use (x y : Nat) (rule : (x = x) -> x = y) : x = y := by rw [rule]; rfl",
    );
    admit(
        &base,
        "theorem use (x y : Nat) (rule : (x = x) -> x = y) : x = y := by simp only [rule]",
    );
}

#[test]
fn simp_side_conditions_use_only_selected_proofs_and_definitions() {
    let base = admit(&engine(), "def SelfEq (x : Nat) : Prop := x = x");
    let base = admit(
        &base,
        "theorem conditional (P : Nat -> Prop) (x y : Nat) (h : x = y) (n : Nat) (hp : P n) : x = y := by exact h",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem use (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : x = y := by simp only [rule, hp]",
        "theorem use (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : x = y := by simp only [hp, rule]",
        "theorem use (P : Prop) (hp : P) : P := by simp only [hp]",
        "theorem use (x y : Nat) (rule : SelfEq x -> x = y) : x = y := by simp only [rule, SelfEq]",
    ] {
        admit(&base, source);
    }
    for source in [
        "theorem bad (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : x = y := by simp only [rule]",
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hp : P 0) : x = y := by simp only [conditional P x y h, hp]",
        "theorem bad (x y : Nat) (rule : SelfEq x -> x = y) : x = y := by simp only [rule]",
    ] {
        let error = base
            .admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
            .expect_err("unselected or unresolved premise must remain");
        assert!(
            error.to_string().contains("simp only made no progress"),
            "{source}: {error}"
        );
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn simp_only_empty_set_uses_kernel_conversion_and_never_proves_false() {
    let base = engine();
    admit(&base, "theorem arithmetic : 2 + 3 = 5 := by simp only []");
    admit(&base, "theorem reflexive (x : Nat) : x = x := by simp only");
    assert!(
        base.admit_source_declaration(
            b"theorem falsehood : 1 = 2 := by simp only []",
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
}

#[test]
fn simp_only_keeps_ordinary_definitions_closed_without_an_explicit_rule() {
    let base = admit(&engine(), "def identity (x : Nat) : Nat := x");
    let base = admit(
        &base,
        "theorem identity_eq (x : Nat) : identity x = x := by rfl",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : identity 5 = 5 := by simp only []",
        "theorem bad (x : Nat) : identity x = x := by simp only []",
    ] {
        let Err(error) = base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        else {
            panic!("automatic simplification unfolded an ordinary definition: {source}");
        };
        assert!(
            error.to_string().contains("simp only made no progress"),
            "{error}"
        );
    }
    admit(
        &base,
        "theorem explicit (x : Nat) : identity x = x := by simp only [identity_eq]",
    );
    admit(&base, "theorem explicit : identity 5 = 5 := by rfl");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn simp_only_arithmetic_resource_stop_remains_inconclusive() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let error = base
        .check_source_files(
            &[b"theorem bounded : (1 <<< 18446744073709551616) = 0 := by simp only []"],
            &options,
            fln::SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("inconclusive", false, 3));
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn automatic_reflexivity_preserves_beta_reduction() {
    let base = engine();
    for source in [
        "theorem beta (x : Nat) (h : x = 5) : (fun n => n) 5 = x := by rw [h]",
        "theorem beta : (fun n => n) 5 = 5 := by simp only []",
    ] {
        admit(&base, source);
    }
}

#[test]
fn automatic_reflexivity_respects_local_let_unfolding_policy() {
    let base = admit(
        &engine(),
        "theorem step (y x : Nat) (h : y = x) : x = x := by rfl",
    );
    let root = base.logical_root(&KVMap::new());
    admit(
        &base,
        "theorem use (x : Nat) : x = x := let y := x; by apply step y; rfl",
    );
    for source in [
        "theorem bad (x : Nat) : x = x := let y := x; by apply step y; simp only []",
        "theorem bad (f : Nat -> Nat) (x : Nat) : f x = f x := let y := x; by apply step (f y); simp only []",
    ] {
        let error = match base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        {
            Err(error) => error,
            Ok(outcome) => panic!(
                "expected a tactic error for {source}, got {:?}",
                outcome.into_complete().map(|_| ())
            ),
        };
        assert!(
            error.to_string().contains("simp only made no progress"),
            "{error}"
        );
    }
    for source in [
        "theorem use (x : Nat) : x = x := let y := x; by apply step y; simp only [y]",
        "theorem use (f : Nat -> Nat) (x : Nat) : f x = f x := let y := x; by apply step (f y); simp only [y]",
    ] {
        admit(&base, source);
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn automatic_reflexivity_keeps_ordinary_goal_aliases_closed() {
    let base = admit(&engine(), "def SelfEq (x : Nat) : Prop := x = x");
    let root = base.logical_root(&KVMap::new());
    for (source, diagnostic) in [
        (
            "theorem bad (x : Nat) (h : x = 5) : SelfEq x := by rw [h]",
            "unsolved goals",
        ),
        (
            "theorem bad (x : Nat) : SelfEq x := by simp only []",
            "simp only made no progress",
        ),
    ] {
        let Err(error) = base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
        else {
            panic!("automatic reflexivity unfolded an ordinary goal alias: {source}");
        };
        assert!(error.to_string().contains(diagnostic), "{error}");
    }
    admit(&base, "theorem explicit (x : Nat) : SelfEq x := by rfl");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn simp_only_preserves_introduced_context_and_leaves_real_remaining_goals() {
    let base = engine();
    admit(
        &base,
        "theorem use (x y : Nat) : (x = y) -> (y = x) := by intro h; simp only [h]",
    );
    admit(
        &base,
        "theorem use (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by simp only [h]; exact hy",
    );
}

#[test]
fn simp_only_skips_unused_rules_but_not_unknown_rules_or_missing_proofs() {
    let base = engine();
    admit(
        &base,
        "theorem use (x y z : Nat) (unused : y = z) (h : x = z) : x = z := by simp only [unused, h]",
    );
    for source in [
        "theorem bad (P : Prop) (x y : Nat) (h : P -> x = y) : x = y := by simp only [h]",
        "theorem bad (x : Nat) : x = x := by simp only [missing]",
        "theorem bad (x : Nat) : x = x := by simp",
    ] {
        assert!(
            base.admit_source_declaration(source.as_bytes(), &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
}

#[test]
fn simp_only_skips_reflexive_rules_and_refuses_nonterminating_rule_sets() {
    let base = engine();
    admit(
        &base,
        "theorem use (x : Nat) (h : x = x) : x = x := by simp only [h]",
    );
    let root = base.logical_root(&KVMap::new());
    let error = base.admit_source_declaration(b"theorem cycle (P : Nat -> Prop) (x y : Nat) (h : x = y) (k : y = x) : P x := by simp only [h, k]", &KVMap::new(), limits()).unwrap_err();
    assert!(
        format!("{error:?}").contains("SimplificationCycle"),
        "{error:?}"
    );
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn simp_only_reverses_rules_and_is_repeatable() {
    let base = engine();
    let source =
        "theorem use (f : Nat -> Nat) (x : Nat) (h : x = f x) : f (f x) = x := by simp only [<- h]";
    let a = admit(&base, source);
    let b = admit(&base, source);
    assert_eq!(a.logical_root(&KVMap::new()), b.logical_root(&KVMap::new()));
}

#[test]
fn simp_only_unfolds_selected_definitions_and_combines_them_with_proved_rules() {
    let base = admit(
        &engine(),
        "def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)",
    );
    admit(
        &base,
        "theorem use (f : Nat -> Nat) (x : Nat) (h : f x = x) : twice f (twice f x) = x := by simp only [twice, h]",
    );
    let base = admit(&base, "def identity {A : Type} (x : A) : A := x");
    admit(
        &base,
        "theorem use {A : Type} (x : A) : identity (identity x) = x := by simp only [identity]",
    );
    admit(
        &base,
        "theorem use (x : Nat) : x = x := by simp only [twice]",
    );
}

#[test]
fn simp_only_local_shadowing_never_unfolds_a_same_named_global() {
    let base = admit(&engine(), "def rule (x : Nat) : Nat := x");
    admit(
        &base,
        "theorem use (x y : Nat) (rule : x = y) : y = x := by simp only [rule]",
    );
    assert!(
        base.admit_source_declaration(
            b"theorem bad (x : Nat) : x = x := by simp only [<- rule]",
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
}

#[test]
fn simp_only_specializes_polymorphic_rules_at_distinct_types_in_one_goal() {
    let base = admit(&engine(), "def identity {A : Type} (x : A) : A := x");
    let base = admit(
        &base,
        "theorem identity_eq {A : Type} (x : A) : identity x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (f : Nat -> String -> Nat) (x : Nat) (s : String) : f (identity x) (identity s) = f x s := by simp only [identity_eq]",
    );
}

#[test]
fn independent_checker_converts_equal_terms_with_different_erased_arguments() {
    let base = admit(&engine(), "def erase (x : Nat) : Nat := 7");
    admit(&base, "theorem use : erase 1 = erase 2 := by rfl");
    admit(
        &base,
        "theorem use : erase 1 = erase 2 := by simp only [erase]",
    );
    assert!(
        base.admit_source_declaration(
            b"theorem bad : erase 1 = 8 := by rfl",
            &KVMap::new(),
            limits()
        )
        .is_err()
    );
}

#[test]
fn simp_only_unfolds_local_lets_in_tactic_generated_subgoals() {
    let base = admit(
        &engine(),
        "theorem step (y x : Nat) (h : y = x) : x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (x : Nat) : x = x := let y := x; by apply step y; simp only [y]",
    );
}
