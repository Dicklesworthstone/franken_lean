//! Equality tactics must retain ordinary checked proofs and dependent contexts.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};
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
fn refuse(source: &str) {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
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
        "theorem scopedCase (b : Bool) (x y : Nat) (h : x = y) : x = y := by\n  cases b with\n  | false =>\n    subst h\n    rfl\n  | true => exact h",
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
fn substitution_preserves_computed_replacements_in_runtime_let_values() {
    // The pin reduces the selected endpoint to a variable, but keeps the
    // opposite endpoint in the reconstructed local. Expanding `x + 20` here
    // would leak Nat.add's dependent history recursor into a scalar program.
    for equation in [
        "(fun value : Nat => value) y = x + 20",
        "x + 20 = (fun value : Nat => value) y",
    ] {
        let source = format!(
            "def keep (x y : Nat) (h : {equation}) : Nat :=\n  let saved := y\n  by\n    subst h\n    exact saved + 20\n#eval keep 2 22 (Eq.refl 22)"
        );
        let result = engine()
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("checked substitution must return a value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
    }
}

#[test]
fn substitution_keeps_generated_casts_and_local_aliases_in_scope() {
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ntheorem castAlias (A B : Type) (a : A) (b : B) (h : Package.mk A a = Package.mk B b) : HEq b a :=\n  let saved := a\n  by\n    injection h with types values\n    subst types\n    subst values\n    exact HEq.symm (HEq.refl saved)",
    );
}

#[test]
fn substitution_does_not_normalize_away_syntactic_occurrences() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    // All three are refused by the pin. Although beta reduction can remove
    // `x`, substitution checks the original replacement and its local aliases.
    for source in [
        "theorem forward (x : Nat) (h : x = (fun ignored : Nat => 42) x) : x = 42 := by\n  subst h\n  rfl",
        "theorem reverse (x : Nat) (h : (fun ignored : Nat => 42) x = x) : x = 42 := by\n  subst h\n  rfl",
        "theorem aliasCycle (x : Nat) (h : x = 42) : x = 42 :=\n  let saved := x\n  by\n    have same : x = (fun ignored : Nat => 42) saved := h\n    subst same\n    rfl",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        assert!(
            format!("{error:?}").contains("SubstitutionLocal"),
            "{error:?}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    check("theorem usable (x : Nat) (h : x = 42) : x = 42 := by\n  subst h\n  rfl");
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

/// `subst h` on `h : HEq a b` whose types differ is refused, in the pin's words: the pin
/// substitutes an `HEq` only when its two types are definitionally equal (`heqToEq`, vendored
/// src/Lean/Meta/Tactic/Subst.lean), and otherwise finds no equation that eliminates `h`.
/// Each program was run at the pin (lean v4.32.0, 2026-10-06); each is refused with exactly
/// this first error. This test used to accept all six by transporting the endpoint types.
#[test]
fn heterogeneous_substitution_is_refused_when_the_types_differ() {
    for source in [
        "def value (A B : Type) (a : A) (b : B) (h : HEq a b) : A := by\n  subst h\n  exact b",
        "theorem typeIdentity (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := by\n  subst h\n  rfl",
        "theorem proofDependent (A B : Type) (a : A) (b : B) (h : HEq a b) (P : (HEq a b) -> Prop) (hp : P h) : P h := by\n  subst h\n  exact hp",
        "def stored (A B : Type) (a : A) (b : B) (h : HEq a b) : A := let saved := b; by\n  subst h\n  exact saved",
        "theorem branchScopes (flag : Bool) (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B := by\n  cases flag with\n  | false =>\n    subst h\n    rfl\n  | true => exact type_eq_of_heq h",
        "theorem introducedTypes (A B : Type) (a : A) (b : B) : HEq a b -> A = B := by\n  intro h\n  subst h\n  rfl",
    ] {
        let error = engine()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source)
            .to_string();
        assert!(
            error.contains("Tactic `subst` failed: did not find equation for eliminating 'h'"),
            "{source}\nmust be refused as the pin refuses it: {error}"
        );
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
        "theorem injected (x y : Nat) (h : HEq (Nat.succ x) (Nat.succ y)) : y = x := by\n  injection h with predecessor\n  exact eq_of_heq (HEq.symm (heq_of_eq predecessor))",
        "theorem impossible (n : Nat) (h : HEq (Nat.succ n) 0) : 0 = 1 := by contradiction",
        "theorem combined (x y : Nat) (h : HEq (Nat.succ x) (Nat.succ y)) (hy : y = 0) : x = 0 := by\n  injection h with same\n  subst same\n  exact hy",
    ] {
        check(source);
    }
    // Two distinct nonzero numerals share the head `Nat.succ`, and an `HEq` never reaches
    // the pin's `decide`: "Tactic `contradiction` failed" (lean v4.32.0, 2026-10-06). The
    // same equation as an `Eq` is decided and accepted.
    refuse(
        "theorem huge (h : HEq 340282366920938463463374607431768211456 340282366920938463463374607431768211457) : 0 = 1 := by contradiction",
    );
    check(
        "theorem huge (h : HEq 340282366920938463463374607431768211456 340282366920938463463374607431768211457) : 0 = 1 := by\n  have e := eq_of_heq h\n  contradiction",
    );
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

/// The pin's `noConfusion` makes no equation for a proof field (proofs are irrelevant), so
/// `injection` names only the other fields' equations, and its closing `tryAssumption` never
/// sees a proof-field one. Every program was run at the pin (lean v4.32.0, 2026-10-06); each
/// refusal is its first error, verbatim. These programs used to be accepted by naming the
/// proof field's equation.
#[test]
fn proof_fields_take_no_injection_name_as_at_the_pin() {
    let certificate = "structure Certificate where\n  carrier : Type\n  value : carrier\n  valid : value = value\n";
    let serial = "structure Certificate where\n  carrier : Type\n  value : carrier\n  valid : value = value\n  serial : Nat\n";
    check(&format!(
        "{certificate}theorem proofField (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (h : Certificate.mk A a pa = Certificate.mk B b pb) : HEq pa pb := by\n  injection h with types values\n  subst types\n  subst values\n  rfl"
    ));
    check(&format!(
        "{serial}theorem serials (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (i j : Nat) (h : Certificate.mk A a pa i = Certificate.mk B b pb j) : j = i := by\n  injection h with types values serials\n  exact eq_of_heq (HEq.symm (heq_of_eq serials))"
    ));
    for (source, unused) in [
        (
            format!(
                "{certificate}theorem proofField (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (h : Certificate.mk A a pa = Certificate.mk B b pb) : HEq pa pb := by\n  injection h with types values proofs\n  exact proofs"
            ),
            "[proofs]",
        ),
        (
            format!(
                "{serial}theorem serials (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b) (i j : Nat) (h : Certificate.mk A a pa i = Certificate.mk B b pb j) : i = j := by\n  injection h with types values proofs serials\n  exact serials"
            ),
            "[serials]",
        ),
        (
            "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  injection h with a b\n  exact eq_of_heq (HEq.symm (heq_of_eq a))".to_string(),
            "[b]",
        ),
    ] {
        let error = engine()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(&source)
            .to_string();
        let wording =
            format!("Tactic `injection` failed: too many identifiers provided, unused: {unused}");
        assert!(
            error.contains(&wording),
            "{source}\nmust be refused as the pin refuses it, with {wording}: {error}"
        );
    }
}

#[test]
fn injection_derives_successor_and_product_field_equalities() {
    check(
        "theorem succInj (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  injection h with hx\n  exact eq_of_heq (HEq.symm (heq_of_eq hx))",
    );
    check(
        "structure Pair where\n  fst : Nat\n  snd : Nat\ntheorem sndInj (a b c d : Nat) (h : Pair.mk a b = Pair.mk c d) : d = b := by\n  injection h with first second\n  exact eq_of_heq (HEq.symm (heq_of_eq second))",
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
        // Accepted at the pin (lean v4.32.0, 2026-10-06). The pin's `values` is `HEq a b`;
        // this injection's is a transported `Eq`, so the proof avoids naming its type.
        "structure Package where\n  carrier : Type\n  value : carrier\ntheorem values (A B : Type) (a : A) (b : B) (h : Package.mk A a = Package.mk B b) : HEq b a := by\n  injection h with types values\n  subst types\n  subst values\n  rfl",
    );
    check(
        "structure Package where\n  carrier : Type\n  value : carrier\ntheorem types (A B : Type) (a : A) (b : B) (h : Package.mk A a = Package.mk B b) : B = A := by\n  injection h with types values\n  exact eq_of_heq (HEq.symm (heq_of_eq types))",
    );
}

#[test]
fn indexed_constructor_equalities_keep_their_dependent_payload_types() {
    check(
        "inductive Vec (A : Type) : Nat -> Type where\n  | nil : Vec A 0\n  | cons (n : Nat) (a : A) (tail : Vec A n) : Vec A (Nat.succ n)\ntheorem heads (A : Type) (n : Nat) (a b : A) (xs ys : Vec A n) (h : Vec.cons n a xs = Vec.cons n b ys) : b = a := by\n  injection h with lengths heads tails\n  exact eq_of_heq (HEq.symm (heq_of_eq heads))",
    );
}

#[test]
fn contradiction_compares_head_constructors_only_for_open_equations() {
    // Both are open with the same head constructor on each side, so the pin's
    // `contradiction` neither injects nor decides them: "Tactic `contradiction` failed"
    // (lean v4.32.0, 2026-10-06). These are the old forms of the
    // examples/native_constructor_equalit{y,ies}.lean theorems, which now inject first.
    for source in [
        "inductive Chain where\n  | nil\n  | cons (value : Nat) (tail : Chain)\ntheorem nested (a b : Nat) (h : Chain.cons a (Chain.cons 7 Chain.nil) = Chain.cons b Chain.nil) : 0 = 1 := by\n  contradiction",
        "theorem nested (n : Nat) (h : Nat.succ (Nat.succ n) = Nat.succ 0) : 0 = 1 := by\n  contradiction",
    ] {
        refuse(source);
    }
}

#[test]
fn huge_literal_contradictions_do_not_expand_a_unary_prefix() {
    check(
        "theorem large (h : 340282366920938463463374607431768211456 = 340282366920938463463374607431768211457) : 0 = 1 := by\n  contradiction",
    );
    check(
        "theorem predecessor (n : Nat) (h : Nat.succ n = 340282366920938463463374607431768211456) : 340282366920938463463374607431768211455 = n := by\n  injection h with previous\n  exact eq_of_heq (HEq.symm (heq_of_eq previous))",
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
        "theorem scopedCase (b : Bool) (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  cases b with\n  | false =>\n    injection h with child\n    exact eq_of_heq (HEq.symm (heq_of_eq child))\n  | true =>\n    injection h with other\n    exact eq_of_heq (HEq.symm (heq_of_eq other))",
    );
    let base = engine();
    for source in [
        // Each goal is stated the other way round, so the pin's closing `tryAssumption`
        // does not end the script before the defect each case is about.
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  injection h with a b\n  exact eq_of_heq (HEq.symm (heq_of_eq a))",
        "structure Pair where\n  fst : Nat\n  snd : Nat\ntheorem bad (a b c d : Nat) (h : Pair.mk a b = Pair.mk c d) : c = a := by\n  injection h with same same\n  exact eq_of_heq (HEq.symm (heq_of_eq same))",
        "theorem bad (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  injection h with same\n  exact (fun ignored => eq_of_heq (HEq.symm (heq_of_eq same))) (1 : String)",
        "theorem bad (b : Bool) (x y : Nat) (h : Nat.succ x = Nat.succ y) : y = x := by\n  cases b with\n  | false =>\n    injection h with child\n    exact eq_of_heq (HEq.symm (heq_of_eq child))\n  | true => exact eq_of_heq (HEq.symm (heq_of_eq child))",
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
        // `injection` closes the goal with `field` itself (the pin's `tryAssumption`).
        &[b"theorem derived (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by\n  injection h with field"],
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
        "structure Mixed where\n  carrier : Type\n  value : carrier\n  count : Nat\ntheorem counters (A B : Type) (a : A) (b : B) (m n : Nat) (h : Mixed.mk A a m = Mixed.mk B b n) : n = m := by\n  injection h with types values counters\n  exact eq_of_heq (HEq.symm (heq_of_eq counters))",
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
