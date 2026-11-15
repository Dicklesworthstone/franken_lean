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

#[test]
fn prelude_punit_bootstraps_from_an_empty_environment_with_the_pins_option() {
    // Init/Prelude.lean uses precisely this option for its first inductive.
    // Start without the source seed so PUnit cannot come from an imported world.
    let base = Engine::from_environment(fln::Environment::new());
    let root = base.logical_root(&KVMap::new());
    let source = "universe u\n\
        set_option bootstrap.inductiveCheckResultingUniverse false in\n\
        inductive PUnit : Sort u where\n  | unit : PUnit\n\
        def propUnit : PUnit.{0} := PUnit.unit\n\
        def typeUnit : PUnit.{1} := PUnit.unit\n";
    let checked = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("Prelude PUnit bootstrap: {error:?}"))
        .into_complete()
        .expect("PUnit and both instantiations pass both checkers");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    let environment = checked.engine.environment();
    let family = environment.find(&Name::from_components(["PUnit"])).unwrap();
    assert_eq!(
        family.constant_val().level_params,
        [Name::from_components(["u"])]
    );
    assert_eq!(
        family.constant_val().type_,
        fln_core::expr::Expr::sort(Level::param(Name::from_components(["u"])))
    );
    let fln_env::constants::ConstantInfo::Rec(rec) = environment
        .find(&Name::from_components(["PUnit", "rec"]))
        .unwrap()
    else {
        panic!("PUnit.rec must be a checked recursor");
    };
    assert_eq!(rec.base.level_params.len(), 2, "singleton eliminates large");
    assert!(!rec.k, "Sort u is not syntactically Prop");
}

#[test]
fn sort_polymorphic_inductives_keep_the_pins_elimination_restrictions() {
    let source = "universe u\n\
        set_option bootstrap.inductiveCheckResultingUniverse false\n\
        inductive SortEmpty : Sort u\n\
        inductive SortUnit : Sort u where | unit\n\
        inductive SortChoice : Sort u where | left | right\n\
        inductive SortBox (A : Sort u) : Sort u where | mk (value : A)\n";
    let checked = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("Sort-polymorphic families: {error:?}"))
        .into_complete()
        .expect("generated recursors pass both checking engines");
    for (name, large) in [
        ("SortEmpty", true),
        ("SortUnit", true),
        ("SortChoice", false),
        ("SortBox", false),
    ] {
        let fln_env::constants::ConstantInfo::Rec(rec) = checked
            .engine
            .environment()
            .find(&Name::from_components([name, "rec"]))
            .unwrap()
        else {
            panic!("missing checked recursor for {name}");
        };
        assert_eq!(
            rec.base.level_params.len(),
            if large { 2 } else { 1 },
            "{name}"
        );
        assert!(!rec.k, "Sort-polymorphic {name} cannot enable K reduction");
        let mut telescope = &rec.base.type_;
        for _ in 0..rec.num_params {
            let ExprNode::ForallE { body, .. } = telescope.node() else {
                panic!("{name} is missing a parameter");
            };
            telescope = body;
        }
        let ExprNode::ForallE { binder_type, .. } = telescope.node() else {
            panic!("{name} is missing its motive");
        };
        let mut motive = binder_type;
        while let ExprNode::ForallE { body, .. } = motive.node() {
            motive = body;
        }
        let ExprNode::Sort { level } = motive.node() else {
            panic!("{name}'s motive must end in a sort");
        };
        assert_eq!(
            level,
            &if large {
                Level::param(rec.base.level_params[0].clone())
            } else {
                Level::zero()
            },
            "{name} elimination universe"
        );
    }
    // A Type instantiation does not retroactively grant a polymorphic
    // recursor large elimination: its motive was fixed when it was declared.
    for source in [
        "noncomputable def bad (x : SortChoice.{1}) : Nat := @SortChoice.rec (fun _ => Nat) 0 1 x",
        "noncomputable def bad (x : SortBox.{1} Nat) : Nat := @SortBox.rec Nat (fun _ => Nat) (fun n => n) x",
    ] {
        let error = checked
            .engine
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err("the universe-polymorphic recursor cannot eliminate into Type");
        assert_eq!(error.disposition().2, 1, "{source}\n{error:?}");
    }
}

#[test]
fn bootstrap_option_is_scoped_and_never_disables_structural_or_universe_checks() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "universe u\ninductive Bad : Sort u where | unit",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse true\ninductive Bad : Sort u where | unit",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse false in\ninductive Allowed : Sort u where | unit\ninductive Bad : Sort u where | unit",
        "universe u\nsection\nset_option bootstrap.inductiveCheckResultingUniverse false\ninductive Allowed : Sort u where | unit\nend\ninductive Bad : Sort u where | unit",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse false\nset_option bootstrap.inductiveCheckResultingUniverse true\ninductive Bad : Sort u where | unit",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse false\nstructure Bad (A : Sort u) : Sort u where\n  value : A",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse false\ninductive Bad : Sort u where | mk (large : Type u)",
        "universe u\nset_option bootstrap.inductiveCheckResultingUniverse false\ninductive Bad : Sort u where | mk (negative : Bad -> Nat)",
        "set_option bootstrap.inductiveCheckResultingUniverse 0\ninductive Bad where | unit",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err("invalid bootstrap source must be rejected");
        assert_eq!(error.disposition().2, 1, "{source}\n{error:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root, "{source}");
        assert!(!base.environment().contains(&Name::from_components(["Bad"])));
    }
    // Recovery uses the unchanged base and the option changes no ordinary data rules.
    check("inductive Recovered : Type where | unit");
}
