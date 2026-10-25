//! Source-inferred inductive universes must pass both native checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::expr::ExprNode;
use fln_core::level::Level;
use fln_core::name::Name;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn check(source: &str) {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("source and both judges complete");
}

#[test]
fn inferred_polymorphic_sum_eliminates_and_retains_independent_carrier_universes() {
    check(include_str!(
        "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
    ));
}

fn stored_result_levels(source: &str, expected: &[(&str, Level)]) {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("source and both judges complete")
        .engine;
    for (name, expected) in expected {
        let info = engine
            .environment()
            .find(&Name::from_components(name.split('.')))
            .unwrap_or_else(|| panic!("missing {name}"));
        let mut type_ = &info.constant_val().type_;
        while let ExprNode::ForallE { body, .. } = type_.node() {
            type_ = body;
        }
        let ExprNode::Sort { level } = type_.node() else {
            panic!("{name} does not end in a sort: {type_:?}");
        };
        assert_eq!(level, expected, "stored result universe of {name}");
    }
}

// Oracle: pinned Lean 4.32.0, `repr (getConstInfo name).type`, rather than
// pretty printing or universe equivalence (both can hide redundant maxima).
#[test]
fn inferred_result_levels_store_the_pins_normalized_terms() {
    let u = Level::param(Name::from_components(["u"]));
    let v = Level::param(Name::from_components(["v"]));
    stored_result_levels(
        "universe u v\n\
         inductive SortNat where | mk (n m : Nat)\n\
         inductive SortPoly (A : Type u) where | mk (x : A)\n\
         inductive SortMixed (A : Sort u) (B : Type v) where | mk (x : A) (y : B)\n\
         mutual\n\
           inductive SortTree (A : Type u) where | leaf (x : A) | node (f : SortForest A)\n\
           inductive SortForest (A : Type u) where | nil | cons (x : SortTree A) (xs : SortForest A)\n\
         end\n",
        &[
            ("SortNat", Level::one()),
            ("SortPoly", Level::succ(u.clone()).unwrap()),
            (
                "SortMixed",
                Level::max(u.clone(), Level::succ(v).unwrap()).unwrap(),
            ),
            ("SortTree", Level::succ(u.clone()).unwrap()),
            ("SortForest", Level::succ(u).unwrap()),
        ],
    );
}

#[test]
fn inferred_prop_candidates_keep_empty_enumeration_and_recursive_controls_in_type() {
    stored_result_levels(
        "inductive SortProof where | mk (h : True)\n\
         inductive SortProp : Prop where | mk (h : True)\n\
         inductive SortEmpty\n\
         inductive SortUnit where | mk\n\
         inductive SortEnum where | left (h : True) | right (h : True)\n\
         inductive SortRecursive where | mk (child : SortRecursive)\n\
         mutual\n\
           inductive SortProofLeft where | mk (h : True)\n\
           inductive SortProofRight where | mk (h : True)\n\
         end\n",
        &[
            ("SortProof", Level::zero()),
            ("SortProp", Level::zero()),
            ("SortEmpty", Level::one()),
            ("SortUnit", Level::one()),
            ("SortEnum", Level::one()),
            ("SortRecursive", Level::one()),
            ("SortProofLeft", Level::zero()),
            ("SortProofRight", Level::zero()),
        ],
    );
}

#[test]
fn inferred_record_results_share_the_pins_normalized_terms() {
    let u = Level::param(Name::from_components(["u"]));
    let v = Level::param(Name::from_components(["v"]));
    stored_result_levels(
        "universe u v\n\
         structure SortRecord where\n  first : Nat\n  second : Nat\n\
         structure SortRecordPoly (A : Type u) where\n  value : A\n\
         structure SortRecordMixed (A : Sort u) (B : Type v) where\n  first : A\n  second : B\n\
         structure SortRecordProof where\n  proof : True\n",
        &[
            ("SortRecord", Level::one()),
            ("SortRecordPoly", Level::succ(u.clone()).unwrap()),
            (
                "SortRecordMixed",
                Level::max(u, Level::succ(v).unwrap()).unwrap(),
            ),
            ("SortRecordProof", Level::zero()),
        ],
    );
}

#[test]
fn inferred_polymorphic_product_and_exception_families_keep_their_fields() {
    check(
        "structure Prod (α : Type u) (β : Type v) where\n  fst : α\n  snd : β\n\
           def pair : Prod Nat Bool := Prod.mk 4 true\n\
           theorem first : pair.fst = 4 := by rfl\n\
           theorem second : pair.snd = true := by rfl",
    );
    check(
        "inductive Except (ε : Type u) (α : Type v) where | error (value : ε) | ok (value : α)\n\
           def result (e : Except Bool Nat) : Nat := match e with | Except.error b => if b then 1 else 2 | Except.ok n => n\n\
           theorem success : result (Except.ok 4) = 4 := by rfl\n\
           theorem failure : result (Except.error true) = 1 := by rfl",
    );
}

#[test]
fn explicit_reordered_maxima_and_redundant_result_bounds_are_convertible() {
    for level in ["max v u", "max 0 (max u v)", "max (max u v) u"] {
        check(&format!(
            "inductive Sum (α : Type u) (β : Type v) : Type ({level}) where | inl (a : α) | inr (b : β)\n\
          def take (x : Sum Nat Bool) : Nat := match x with | Sum.inl n => n | Sum.inr b => if b then 1 else 0\n\
          theorem value : take (Sum.inl 4) = 4 := by rfl"
        ));
    }
}

#[test]
fn reconstructed_coproducts_execute_through_the_native_vm() {
    use fln::{EngineExecutionLimits, VmExit};
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = seed
        .check_source_files(
            &[include_bytes!(
                "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
            )],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let source = "#eval observe (Sum.inl 4)\n#eval observe (Sum.inr false)\n#eval observe (mapSum (fun n => n + 2) (fun b => b) (Sum.inl 4))";
    let run = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), 3);
    for (execution, expected) in run.executions.iter().zip(["5", "3", "7"]) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{:?}", execution.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn universe_equality_cannot_hide_wrong_carriers_false_proofs_or_small_results() {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = seed
        .check_source_files(
            &[include_bytes!(
                "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
            )],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    for source in [
        "def bad : Sum Nat Bool := Sum.inl true",
        "def bad : Sum Nat Bool := Sum.inr 1",
        "theorem bad : observe (Sum.inl 4) = 6 := by rfl",
        "def bad : Sum Nat Bool := higherLeft Nat",
        "inductive TooSmall (α : Type (u+1)) : Type u where | mk (a : α)",
    ] {
        let result = engine.check_source_files(&[source.as_bytes()], &options, limits());
        assert!(result.is_err(), "invalid source admitted: {source}");
        assert_eq!(engine.logical_root(&options), before);
    }
    engine
        .check_source_files(
            &[b"theorem recovered : observe (Sum.inr false) = 3 := by rfl"],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
