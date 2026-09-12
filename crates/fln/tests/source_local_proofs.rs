//! Local proof declarations must produce checked terms, never assumptions.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let e = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    e.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    )
    .map_err(|e| format!("{e:?}"))?
    .into_complete()
    .map(|_| ())
    .map_err(|e| format!("{e:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|e| panic!("{source}\n{e}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted invalid source: {source}");
}
#[test]
fn named_and_anonymous_local_facts_use_real_values() {
    check("theorem identity (A : Type) (a : A) : a = a := by have h : a = a := rfl; exact h");
    check(
        "theorem identity (A : Type) (a : A) (h : a = a) : a = a := by have copy := h; exact copy",
    );
    check("theorem identity (n : Nat) : n = n := by have : n = n := rfl; exact this");
    check("theorem identity (n : Nat) (h : n = n) : n = n := by have := h; exact this");
}
#[test]
fn nested_by_proofs_are_scoped_and_may_use_earlier_facts() {
    check(
        "theorem identity (n : Nat) : n = n := by\n  have h : n = n := by\n    have k : n = n := by\n      rfl\n    exact k\n  exact h",
    );
    check(
        "theorem identity (n : Nat) : n = n := by\n  have h : n = n := by rfl\n  have k : n = n := by exact h\n  exact k",
    );
}
#[test]
fn a_local_quantified_lemma_is_available_to_application_and_rewriting() {
    check(
        "theorem reflexive (n : Nat) : n = n := by\n  have all : forall x : Nat, x = x := by\n    intro x\n    rfl\n  exact all n",
    );
    check(
        "theorem changed (n m : Nat) (h : n = m) : Nat.succ n = Nat.succ m := by\n  have same : n = m := by exact h\n  rw [same]",
    );
}
#[test]
fn tactic_lets_keep_values_and_dependent_types() {
    check("theorem seven : 7 = 7 := by let n : Nat := 7; have h : n = 7 := rfl; exact h");
    check("def recovered (A : Type) (a : A) : A := by let T := A; let b : T := a; exact b");
    check("def built : Nat := by\n  let n : Nat := by exact 7\n  exact n");
}
#[test]
fn original_obligations_survive_unused_bindings() {
    for binding in [
        "have h : String := 1",
        "let h : String := 1",
        "have h : 0 = 1 := rfl",
        "let h : 0 = 1 := rfl",
        "have h := (1 : String)",
    ] {
        reject(&format!("theorem bad : 0 = 0 := by {binding}; rfl"));
    }
    reject("theorem bad : 0 = 0 := by\n  have unused : 0 = 1 := by rfl\n  rfl");
}
#[test]
fn self_reference_and_sibling_leaks_are_rejected() {
    reject("theorem bad : 0 = 1 := by have h : 0 = 1 := h; exact h");
    reject("theorem bad : 0 = 1 := by\n  have h : 0 = 1 := by exact h\n  exact h");
    reject(
        "theorem bad : 0 = 0 := by\n  have h : 0 = 0 := by\n    have secret : 0 = 0 := rfl\n    exact secret\n  exact secret",
    );
    reject(
        "theorem bad (b : Bool) : 0 = 0 := by\n  cases b with\n  | false =>\n    have h : 0 = 0 := rfl\n    exact h\n  | true => exact h",
    );
}
#[test]
fn local_proofs_compose_with_case_analysis_and_induction() {
    check(
        "theorem split (b : Bool) : b = b := by\n  have h : b = b := by\n    cases b with\n    | false => rfl\n    | true => rfl\n  exact h",
    );
    check(
        "theorem count (n : Nat) : n = n := by\n  induction n with\n  | zero =>\n    have h : 0 = 0 := by rfl\n    exact h\n  | succ k ih =>\n    have h : k = k := by exact ih\n    rfl",
    );
}
#[test]
fn name_shadowing_uses_the_old_scope_for_the_new_value() {
    check("theorem shadow (n : Nat) (h : n = n) : n = n := by have h : n = n := h; exact h");
    check("def shadow : Nat := by let n := 3; let n := n + 4; exact n");
}
#[test]
fn dependencies_on_the_original_proof_are_preserved() {
    check(
        "theorem kept (n : Nat) (h : n = n) (P : n = n -> Prop) (ph : P h) : P h := by\n  have kept : P h := by exact ph\n  exact kept",
    );
    check(
        "theorem subst_kept (n m : Nat) (eq : n = m) (P : Nat -> Prop) (h : P n) : P m := by\n  have copy : P n := by exact h\n  subst eq\n  exact copy",
    );
}
#[test]
fn incomplete_or_overlong_nested_proofs_do_not_consume_outer_tactics() {
    reject("theorem bad : 0 = 0 := by\n  have h : 0 = 0 := by\n    intro\n  rfl");
    reject("theorem bad : 0 = 0 := by\n  have h : 0 = 0 := by\n    rfl\n    rfl\n  exact h");
    reject("theorem bad : 0 = 0 := by rfl; have h : 0 = 0 := rfl");
}

#[test]
fn local_fact_values_and_type_annotations_remain_in_the_final_kernel_term() {
    for body in [
        "have hidden : String := 1; rfl",
        "let hidden : String := 1; rfl",
        "have hidden : String := 1; cases n with | zero => rfl | succ k => rfl",
    ] {
        let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap();
        let root = engine.logical_root(&KVMap::new());
        let source = format!("theorem bad (n : Nat) : 0 = 0 := by {body}");
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap_err();
        assert!(
            error.disposition().1,
            "the original typed value must reach K1: {error:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn local_functions_and_record_values_can_be_used_in_later_proofs() {
    check(
        "theorem applied (n : Nat) : n = n := by\n  let identity : Nat -> Nat := fun x => x\n  have h : identity n = n := rfl\n  exact h",
    );
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ndef t : Nat := by\n  let p : Package := { value := 7, carrier := Nat }\n  exact p.value\ntheorem computed : t = 7 := by rfl",
    );
    check(
        "theorem higher (n : Nat) : n = n := by\n  have all : forall x : Nat, x = x := fun x => rfl\n  exact all n",
    );
}

#[test]
fn local_proofs_cannot_reveal_hidden_case_hypotheses_or_recurse_on_themselves() {
    reject(
        "def copy (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (copy k)\ntheorem bad (n : Nat) : copy n = n := by\n  cases n with\n  | zero => rfl\n  | succ k =>\n    have forged : copy k = k := by assumption\n    simp only [copy, forged]",
    );
    reject("theorem bad : 0 = 1 := by\n  let prove : 0 = 1 := by assumption\n  exact prove");
    reject("theorem bad : 0 = 0 := by\n  have h : Nat := by exact (1 : String)\n  rfl");
}

#[test]
fn deeply_nested_scoped_proofs_are_elaborated_by_the_term_worklist() {
    let depth = 48;
    let mut source = String::from("theorem nested : 0 = 0 := by\n");
    for i in 0..depth {
        source.push_str(&format!("{}have h{i} : 0 = 0 := by\n", "  ".repeat(i + 1)));
    }
    source.push_str(&format!("{}rfl\n", "  ".repeat(depth + 1)));
    for i in (0..depth).rev() {
        source.push_str(&format!("{}exact h{i}\n", "  ".repeat(i + 1)));
    }
    check(&source);
}

#[test]
fn argument_types_must_not_turn_into_unproved_local_facts() {
    reject("theorem bad : 0 = 1 := by have h : 0 = 1 := _; exact h");
    reject("theorem bad : 0 = 1 := by have h := rfl; exact h");
    reject("theorem bad : 0 = 0 := by have h : 7 := 7; rfl");
    reject("theorem bad : 0 = 0 := by let h : 7 := 7; rfl");
}

#[test]
fn resource_stops_in_local_proofs_leave_the_original_engine_reusable() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let source = "theorem t (n : Nat) : n = n := by\n  have h : n = n := by rfl\n  exact h";
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match engine.check_source_files(&[source.as_bytes()], &KVMap::new(), low) {
        Ok(fln::Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("expected a nonauthoritative resource stop: {other:?}"),
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
