//! Equality tactics must retain ordinary checked proofs and dependent contexts.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn subst_orients_equalities_and_finds_named_variables() {
    for tactic in ["subst h", "subst x", "subst y"] {
        check(&format!(
            "theorem transport (x y : Nat) (h : x = y) : y = x := by\n  {tactic}\n  rfl"
        ));
    }
    check("theorem transport (x : Nat) (h : x = 7) : x = 7 := by\n  subst h\n  rfl");
    check("theorem transport (x : Nat) (h : 7 = x) : x = 7 := by\n  subst h\n  rfl");
}
#[test]
fn subst_rebuilds_dependent_data_and_proof_telescopes() {
    check(
        "theorem transport (A : Type) (P : A -> Prop) (x y : A) (h : x = y) (hx : P x) : P y := by\n  subst h\n  exact hx",
    );
    check("def cast (A B : Type) (h : A = B) (a : A) : B := by\n  subst h\n  exact a");
    check(
        "theorem dependentProof (x y : Nat) (h : x = y) (P : (x = y) -> Prop) (hp : P h) : P h := by\n  subst h\n  exact hp",
    );
}
#[test]
fn substitution_preserves_introduced_scopes_and_nested_branches() {
    check("theorem introduced (x y : Nat) : x = y -> y = x := by\n  intro h\n  subst h\n  rfl");
    check(
        "theorem scoped (b : Bool) (x y : Nat) (h : x = y) : x = y := by\n  cases b with\n  | false =>\n    subst h\n    rfl\n  | true => exact h",
    );
}
#[test]
fn false_substitution_proofs_and_cycles_never_publish_a_successor() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for s in [
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by\n  subst h\n  rfl",
        "theorem bad (x : Nat) (h : x = Nat.succ x) : x = x := by\n  subst h\n  rfl",
        "theorem bad (x : Nat) : x = x := by\n  subst x\n  rfl",
        "theorem bad (x y : Nat) (h : x = y) : y = x := by\n  subst h\n  exact h",
    ] {
        assert!(
            base.check_source_files(
                &[s.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{s}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn substitution_reintroduces_local_let_values_and_their_dependents() {
    check(
        "theorem lets (x y : Nat) (h : x = y) : x = y := let saved := x; by\n  subst h\n  exact rfl",
    );
    check(
        "def localValue (x y : Nat) (h : x = y) : Nat := let saved := x; by\n  subst h\n  exact saved",
    );
}
#[test]
fn proof_dependent_substitution_does_not_need_symmetry_involution_conversion() {
    check(
        "theorem fixed (x : Nat) (h : x = 7) (P : (x = 7) -> Prop) (p : P h) : P h := by\n  subst h\n  exact p",
    );
    check(
        "theorem reversed (x : Nat) (h : 7 = x) (P : (7 = x) -> Prop) (p : P h) : P h := by\n  subst h\n  exact p",
    );
}
#[test]
fn substitution_follows_alias_dependencies_and_refuses_unused_ill_typed_terms() {
    let base = engine();
    for source in [
        "theorem cyclic (x : Nat) : x = x := let alias := x; by\n  intro h\n  subst x\n  rfl",
        "theorem bad (x y : Nat) (h : x = y) : y = x := by\n  subst h\n  exact (fun ignored => rfl) (1 : String)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
        );
    }
}

#[test]
fn heterogeneous_equality_seed_checks_through_both_engines() {
    check("theorem reflected (A : Type) (x : A) : HEq x x := HEq.refl x");
}

#[test]
fn heterogeneous_bridge_theorems_are_ordinary_checked_source_terms() {
    for source in [
        "theorem ordinary (A : Type) (a b : A) (h : HEq a b) : a = b := eq_of_heq h",
        "theorem heterogeneous (A : Type) (a b : A) (h : a = b) : HEq a b := heq_of_eq h",
        "theorem types (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := type_eq_of_heq h",
        "theorem symmetry (A B : Type) (a : A) (b : B) (h : HEq a b) : HEq b a := HEq.symm h",
        "theorem transitive (A B C : Type) (a : A) (b : B) (c : C) (h : HEq a b) (k : HEq b c) : HEq a c := HEq.trans h k",
        "theorem proofs (P : Prop) (p q : P) (h : HEq p q) : p = q := eq_of_heq h",
        "theorem typesAsValues (A B : Type) (h : HEq A B) : A = B := eq_of_heq h",
    ] {
        check(source);
    }
}

#[test]
fn subst_consumes_homogeneous_heq_without_assuming_proof_irrelevance() {
    for source in [
        "theorem endpoints (x y : Nat) (h : HEq x y) : y = x := by\n  subst h\n  rfl",
        "theorem dependent (A : Type) (P : A -> Prop) (x y : A) (h : HEq x y) (px : P x) : P y := by\n  subst h\n  exact px",
        "theorem proofDependent (A : Type) (x y : A) (h : HEq x y) (P : (HEq x y) -> Prop) (hp : P h) : P h := by\n  subst h\n  exact hp",
        "theorem introduced (x y : Nat) : HEq x y -> y = x := by\n  intro h\n  subst h\n  rfl",
    ] {
        check(source);
    }
}

#[test]
fn heterogeneous_substitution_transports_the_endpoint_types_before_values() {
    for source in [
        "def value (A B : Type) (a : A) (b : B) (h : HEq a b) : A := by\n  subst h\n  exact b",
        "theorem typeIdentity (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := by\n  subst h\n  rfl",
        "theorem proofDependent (A B : Type) (a : A) (b : B) (h : HEq a b) (P : (HEq a b) -> Prop) (hp : P h) : P h := by\n  subst h\n  exact hp",
        "def stored (A B : Type) (a : A) (b : B) (h : HEq a b) : A := let saved := b; by\n  subst h\n  exact saved",
        "theorem branchScopes (flag : Bool) (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := by\n  cases flag with\n  | false =>\n    subst h\n    rfl\n  | true => exact type_eq_of_heq h",
        "theorem introducedTypes (A B : Type) (a : A) (b : B) : HEq a b -> A = B := by\n  intro h\n  subst h\n  rfl",
    ] {
        check(source);
    }
}

#[test]
fn heterogeneous_substitution_has_no_false_proof_or_scope_escape() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad (x y : Nat) (h : HEq x y) : 0 = 1 := by\n  subst h\n  rfl",
        "theorem cyclic (x : Nat) (h : HEq x (Nat.succ x)) : x = x := by\n  subst h\n  rfl",
        "theorem consumed (x y : Nat) (h : HEq x y) : HEq x y := by\n  subst h\n  exact h",
        "theorem wrongBridge (x y : Nat) (h : HEq x y) : x = 7 := eq_of_heq h",
        "theorem bogus : HEq 0 1 := heq_of_eq rfl",
        "theorem unused (x y : Nat) (h : HEq x y) : y = x := by\n  subst h\n  exact (fun ignored => rfl) (1 : String)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn same_type_heq_can_drive_constructor_injection_and_contradiction() {
    for source in [
        "theorem injected (x y : Nat) (h : HEq (Nat.succ x) (Nat.succ y)) : x = y := by\n  injection h with predecessor\n  exact predecessor",
        "theorem impossible (n : Nat) (h : HEq (Nat.succ n) 0) : 0 = 1 := by contradiction",
        "theorem huge (h : HEq 340282366920938463463374607431768211456 340282366920938463463374607431768211457) : 0 = 1 := by contradiction",
        "theorem combined (x y : Nat) (h : HEq (Nat.succ x) (Nat.succ y)) (hy : y = 0) : x = 0 := by\n  injection h with same\n  subst same\n  exact hy",
    ] {
        check(source);
    }
}

#[test]
fn heterogeneous_reflexivity_is_checked_not_assumed() {
    check("theorem self (A : Type) (a : A) : HEq a a := by rfl");
    check("theorem computed : HEq (2 + 3) 5 := by rfl");
    let base = engine();
    for source in [
        "theorem wrong : HEq 0 1 := by rfl",
        "theorem wrong : HEq 1 true := by rfl",
        "theorem wrong (n m : Nat) (h : HEq (Nat.succ n) (Nat.succ m)) : 0 = 1 := by contradiction",
        "inductive ExistsNat : Prop where\n  | intro (value : Nat)\ntheorem wrong (h : HEq (ExistsNat.intro 0) (ExistsNat.intro 1)) : 0 = 1 := by contradiction",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn constructor_fallback_retains_dependent_proof_fields_in_data_records() {
    check(
        "structure Certificate where\n  carrier : Type\n  value : carrier\n  valid : value = value\ntheorem proofField (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (h : Certificate.mk A a pa = Certificate.mk B b pb) : HEq pa pb := by\n  injection h with types values proofs\n  exact proofs",
    );
    check(
        "structure Certificate where\n  carrier : Type\n  value : carrier\n  valid : value = value\n  serial : Nat\ntheorem serials (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (i j : Nat) (h : Certificate.mk A a pa i = Certificate.mk B b pb j) : i = j := by\n  injection h with types values proofs serials\n  exact serials",
    );
}

#[test]
fn injection_derives_successor_and_product_field_equalities() {
    check(
        "theorem succInj (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  injection h with hx\n  exact hx",
    );
    check(
        "structure Pair where\n  fst : Nat\n  snd : Nat\ntheorem sndInj (a b c d : Nat) (h : Pair.mk a b = Pair.mk c d) : b = d := by\n  injection h with first second\n  exact second",
    );
    check(
        "theorem reflected (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  injection h with same\n  subst same\n  rfl",
    );
}

#[test]
fn disjoint_constructors_produce_checked_contradictions() {
    check("theorem disjoint (h : true = false) : 0 = 1 := by\n  contradiction");
    check("def impossible (n : Nat) (h : 0 = Nat.succ n) : String := by\n  injection h");
    check(
        "inductive Choice (A : Type) where\n  | left (a : A)\n  | right (a : A)\ntheorem separate (A : Type) (a b : A) (h : Choice.left a = Choice.right b) : a = b := by\n  contradiction",
    );
}

#[test]
fn dependent_fields_produce_heterogeneous_not_forged_homogeneous_equalities() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ntheorem values (A B : Type) (a : A) (b : B) (h : Package.mk A a = Package.mk B b) : HEq a b := by\n  injection h with types values\n  subst types\n  exact heq_of_eq values",
    );
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ntheorem types (A B : Type) (a : A) (b : B) (h : Package.mk A a = Package.mk B b) : A = B := by\n  injection h with types values\n  exact types",
    );
}

#[test]
fn indexed_constructor_equalities_keep_their_dependent_payload_types() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (a : A) (tail : Vec A n) : Vec A (Nat.succ n)\ntheorem heads (A : Type) (n : Nat) (a b : A) (xs ys : Vec A n) (h : Vec.cons n a xs = Vec.cons n b ys) : a = b := by\n  injection h with lengths heads tails\n  exact heads",
    );
}

#[test]
fn contradiction_descends_through_constructor_fields_without_using_neutral_ones() {
    check(
        "inductive Chain where\n  | nil\n  | cons (value : Nat) (tail : Chain)\ntheorem nested (a b : Nat) (h : Chain.cons a (Chain.cons 7 Chain.nil) = Chain.cons b Chain.nil) : 0 = 1 := by\n  contradiction",
    );
    check(
        "theorem nested (n : Nat) (h : Nat.succ (Nat.succ n) = Nat.succ 0) : 0 = 1 := by\n  contradiction",
    );
}

#[test]
fn huge_literal_contradictions_do_not_expand_a_unary_prefix() {
    check(
        "theorem large (h : 340282366920938463463374607431768211456 = 340282366920938463463374607431768211457) : 0 = 1 := by\n  contradiction",
    );
    check(
        "theorem predecessor (n : Nat) (h : Nat.succ n = 340282366920938463463374607431768211456) : n = 340282366920938463463374607431768211455 := by\n  injection h with previous\n  exact previous",
    );
}

#[test]
fn proof_irrelevance_never_becomes_constructor_data_injectivity() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "inductive ExistsNat : Prop where\n  | intro (witness : Nat)\ntheorem bad (h : ExistsNat.intro 0 = ExistsNat.intro 1) : 0 = 1 := by\n  injection h with falseEquality\n  exact falseEquality",
        "inductive Disjunction (P Q : Prop) : Prop where\n  | left (p : P)\n  | right (q : Q)\ntheorem bad (P Q : Prop) (p : P) (q : Q) (h : Disjunction.left p = Disjunction.right q) : 0 = 1 := by\n  contradiction",
        "theorem falseRefl (n : Nat) (h : Nat.succ n = Nat.succ n) : 0 = 1 := by\n  injection h with same\n  exact same",
        "theorem noClash (n m : Nat) (h : Nat.succ n = Nat.succ m) : 0 = 1 := by\n  contradiction",
        "theorem falseHEq : HEq 0 1 := HEq.refl 0",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn constructor_tactics_preserve_source_obligations_and_branch_isolation() {
    check(
        "theorem scoped (b : Bool) (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  cases b with\n  | false =>\n    injection h with child\n    exact child\n  | true =>\n    injection h with other\n    exact other",
    );
    let base = engine();
    for source in [
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  injection h with a b\n  exact a",
        "structure Pair where\n  fst : Nat\n  snd : Nat\ntheorem bad (a b c d : Nat) (h : Pair.mk a b = Pair.mk c d) : a = c := by\n  injection h with same same\n  exact same",
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  injection h with same\n  exact (fun ignored => same) (1 : String)",
        "theorem bad (b : Bool) (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by\n  cases b with\n  | false =>\n    injection h with child\n    exact child\n  | true => exact child",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn injected_proofs_retain_the_actual_equality_and_admitted_recursors() {
    use fln_core::expr::ExprNode;
    use fln_env::constants::ConstantInfo;
    use std::collections::HashSet;
    let checked = engine().check_source_files(
        &[b"theorem derived (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by\n  injection h with field\n  exact field"],
        &KVMap::new(), SourceCheckLimits::new(limits()),
    ).unwrap().into_complete().unwrap();
    let Some(ConstantInfo::Thm(declaration)) = checked
        .engine
        .environment()
        .find(&fln::Name::from_components(["derived"]))
    else {
        panic!("the source theorem was not admitted");
    };
    assert!(!declaration.value.has_expr_mvar());
    assert!(!declaration.value.has_level_mvar());
    assert!(!declaration.value.has_fvar());
    assert!(!declaration.value.has_loose_bvars());
    let mut body = &declaration.value;
    for _ in 0..3 {
        let ExprNode::Lam { body: inner, .. } = body.node() else {
            panic!("expected three source parameters");
        };
        body = inner;
    }
    let mut pending = vec![(body, 0u32)];
    let mut seen = HashSet::new();
    let mut constants = HashSet::new();
    let mut uses_input_equality = false;
    while let Some((expr, depth)) = pending.pop() {
        if !seen.insert((expr.allocation_identity(), depth)) {
            continue;
        }
        match expr.node() {
            ExprNode::BVar { idx } if *idx == depth => uses_input_equality = true,
            ExprNode::Const { name, .. } => {
                constants.insert(name.to_display_string());
            }
            ExprNode::App { f, a } => {
                pending.push((f, depth));
                pending.push((a, depth));
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push((binder_type, depth));
                pending.push((body, depth + 1));
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push((type_, depth));
                pending.push((value, depth));
                pending.push((body, depth + 1));
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending.push((expr, depth))
            }
            _ => {}
        }
    }
    assert!(
        uses_input_equality,
        "the user-supplied equality cannot be discarded"
    );
    assert!(constants.contains("Eq.rec"), "{constants:?}");
    assert!(constants.contains("Nat.rec"), "{constants:?}");
    assert!(matches!(
        checked
            .engine
            .environment()
            .find(&fln::Name::from_components(["HEq"])),
        Some(ConstantInfo::Induct(_))
    ));
}

#[test]
fn heterogeneous_injection_preserves_the_entire_mixed_field_order() {
    check(
        "structure Mixed where\n  carrier : Type\n  value : carrier\n  count : Nat\ntheorem counters (A B : Type) (a : A) (b : B) (m n : Nat) (h : Mixed.mk A a m = Mixed.mk B b n) : m = n := by\n  injection h with types values counters\n  exact counters",
    );
    check(
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\ntheorem tails (A : Type) (n : Nat) (a b : A) (xs ys : Vec A n) (h : Vec.cons n a xs = Vec.cons n b ys) : HEq xs ys := by\n  injection h with _ _ tails\n  exact heq_of_eq tails",
    );
}

#[test]
fn heterogeneous_seed_and_conversion_bridges_cross_both_checkers() {
    for source in [
        "theorem reflected (A : Type) (a : A) : HEq a a := HEq.refl a",
        "theorem same (A : Type) (a b : A) (h : HEq a b) : a = b := eq_of_heq h",
        "theorem same (A : Type) (a b : A) (h : a = b) : HEq a b := heq_of_eq h",
        "theorem types (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := type_eq_of_heq h",
    ] {
        check(source);
    }
}

#[test]
fn heterogeneous_symmetry_and_transitivity_keep_distinct_endpoint_types() {
    check("theorem symmetric (A B : Type) (a : A) (b : B) (h : HEq a b) : HEq b a := HEq.symm h");
    check(
        "theorem transitive (A B C : Type) (a : A) (b : B) (c : C) (h : HEq a b) (k : HEq b c) : HEq a c := HEq.trans h k",
    );
    check(
        "theorem roundTrip (A : Type) (a b : A) (h : a = b) : b = a := eq_of_heq (HEq.symm (heq_of_eq h))",
    );
}

#[test]
fn heterogeneous_bridges_respect_sort_levels_and_proof_values() {
    check("theorem proofValues (P : Prop) (p q : P) (h : HEq p q) : p = q := eq_of_heq h");
    check("theorem typeValues (A B : Type) (h : HEq A B) : A = B := eq_of_heq h");
    check("theorem functionValues (A : Type) (f g : A -> A) (h : HEq f g) : f = g := eq_of_heq h");
}

#[test]
fn invalid_heterogeneous_evidence_never_becomes_homogeneous_equality() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : HEq 0 1 := HEq.refl 0",
        "theorem bad (h : HEq 0 0) : 0 = 1 := eq_of_heq h",
        "theorem bad (A B : Type) (a : A) (b : B) (h : HEq a b) : HEq a 0 := HEq.symm h",
        "theorem bad (A : Type) (a b : A) (h : HEq a b) : a = b := eq_of_heq ((fun ignored => h) (1 : String))",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn heterogeneous_bridges_are_theorems_over_inductives_not_axioms() {
    use fln_env::constants::ConstantInfo;
    let base = engine();
    for name in ["HEq", "HEq.refl", "HEq.rec"] {
        assert!(matches!(
            base.environment()
                .find(&fln::Name::from_components(name.split('.'))),
            Some(ConstantInfo::Induct(_) | ConstantInfo::Ctor(_) | ConstantInfo::Rec(_))
        ));
    }
    for name in [
        "eq_of_heq",
        "heq_of_eq",
        "type_eq_of_heq",
        "HEq.symm",
        "HEq.trans",
    ] {
        let Some(ConstantInfo::Thm(decl)) = base
            .environment()
            .find(&fln::Name::from_components(name.split('.')))
        else {
            panic!("{name} must be a checked theorem");
        };
        assert!(!decl.value.has_fvar());
        assert!(!decl.value.has_expr_mvar());
        assert!(!decl.value.has_level_mvar());
        assert!(!decl.value.has_loose_bvars());
    }
}
