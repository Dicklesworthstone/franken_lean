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
    let base = admit(&base, "theorem same (x : Nat) : x = x := by rfl");
    admit(&base, "theorem use (x : Nat) : x = x := by rw [same]");
    let base = admit(
        &base,
        "theorem congruent (f : Nat -> Nat) (x : Nat) : f x = f x := by rfl",
    );
    admit(
        &base,
        "theorem use (g : Nat -> Nat) (x : Nat) : g x = g x := by rw [congruent]",
    );
}

#[test]
fn polymorphic_rewrite_infers_type_and_universe_parameters() {
    let base = engine();
    let base = admit(&base, "theorem same {A : Type} (x : A) : x = x := by rfl");
    admit(&base, "theorem use (x : Nat) : x = x := by rw [same]");
    admit(
        &base,
        "theorem use {A : Type} (x : A) : x = x := by rw [same]",
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
        "theorem use (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by rw [congruence f]",
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
        "theorem identity_eq {A : Type} (x : A) : identity x = x := by rfl",
    );
    admit(
        &base,
        "theorem use (x : Nat) : x = identity x := by rw [<- identity_eq]",
    );
}

#[test]
fn conditional_rules_use_only_proved_local_side_conditions() {
    let base = engine();
    let source =
        "theorem use (P : Prop) (x y : Nat) (rule : P -> x = y) (hp : P) : y = x := by rw [rule]";
    admit(&base, source);
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.admit_source_declaration(
            b"theorem bad (P : Prop) (x y : Nat) (rule : P -> x = y) : y = x := by rw [rule]",
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
