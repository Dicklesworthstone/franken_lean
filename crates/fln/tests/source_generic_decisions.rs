//! Universe-polymorphic decision dictionaries elaborate through the native engine.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("generic decision checking must complete");
}
#[test]
fn generic_equality_uses_inferred_nat_and_bool_dictionaries() {
    check(
        r#"
        def generic {A : Type} [DecidableEq A] (a b : A) : Bool := decide (a = b)
        theorem nat_equal : generic 3 3 = true := by rfl
        theorem nat_unequal : generic 3 4 = false := by rfl
        theorem bool_equal : generic true true = true := by rfl
        theorem bool_unequal : generic false true = false := by rfl
        def nat_dictionary : DecidableEq Nat := inferInstance
        def bool_dictionary : DecidableEq Bool := inferInstance
        def explicit_nat : DecidableEq Nat := Nat.decEq
        def explicit_bool : DecidableEq Bool := Bool.decEq
        def via_dec_eq (a b : Nat) : Decidable (a = b) := decEq a b
        theorem true_field : via_dec_eq 2 2 = Decidable.isTrue (Eq.refl 2) := by rfl
    "#,
    );
}
#[test]
fn generic_equality_preserves_local_function_dictionary_evidence() {
    check(
        r#"
        def chosen {A : Sort u} [d : DecidableEq A] (a b : A) : Decidable (a = b) := decEq a b
        theorem preserved {A : Sort u} [d : DecidableEq A] (a b : A) : chosen a b = d a b := by rfl
        def proof_choice {A : Prop} [d : DecidableEq A] (a b : A) : Decidable (a = b) := decEq a b
        theorem proposition {A : Prop} [d : DecidableEq A] (a b : A) : proof_choice a b = d a b := by rfl
    "#,
    );
}
#[test]
fn equality_decisions_enable_checked_surface_conditionals_and_case_splits() {
    check(
        r#"
        def classify (a b : Nat) : Nat := if a = b then 7 else 9
        theorem yes : classify 3 3 = 7 := by rfl
        theorem no : classify 3 4 = 9 := by rfl
        theorem named (a b : Nat) (fallback : a = b) : a = b := if h : a = b then h else fallback
        def split (a b : Bool) : Nat := by
          by_cases h : a = b
          · exact 11
          · exact 13
        theorem same : split true true = 11 := by rfl
        theorem different : split false true = 13 := by rfl
    "#,
    );
}
#[test]
fn generic_decisions_never_invent_instances_or_evidence() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def missing : DecidableEq String := inferInstance",
        "def missing {A : Type} (a b : A) : Decidable (a = b) := decEq a b",
        "def forged : DecidableEq Nat := fun a => fun b => Decidable.isTrue (Eq.refl a)",
        "def forged : Decidable (true = false) := decEq true true",
        "def forged : Decidable (2 = 3) := decEq 2 2",
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
        assert_eq!(base.logical_root(&KVMap::new()), root, "{source}");
    }
}
#[test]
fn an_exhausted_equality_check_is_a_nonanswer_and_leaves_no_declaration() {
    use fln_core::outcome::Outcome;
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let base = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&KVMap::new());
    let mut low = SourceCheckLimits::new(limits);
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let source = b"theorem stopped : 3 = 3 := by decide";
    match base.check_source_files(&[source], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(error) => assert!(
            matches!(error.disposition(), ("resource" | "inconclusive", false, 3)),
            "{error:?}"
        ),
        other => panic!("resource exhaustion became a verdict: {other:?}"),
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(
        !base
            .environment()
            .contains(&fln::Name::from_components(["stopped"]))
    );
    base.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits))
        .unwrap()
        .into_complete()
        .unwrap();
}
