//! Plan §8.3c council verification policies (`fln-9908`):
//! - `standard`: K1 on every declaration, `fln-checker` on a deterministic
//!   content-seeded 1/16 sample plus every high-risk form (inductives,
//!   recursors, quotients, mutuals, unsafe/partial, eagerReduce/decide,
//!   non-trivial literal arithmetic, deep universes, and anything K1 took
//!   > `high_risk_k1_steps` steps on).
//! - `release`: full closure (`fln-checker` on 100% of declarations).
//! - `paranoid`: requires an independent second kernel lane (K2) or external
//!   witness; when unavailable, returns typed `Inconclusive` (never silent
//!   fallback to `release` or `standard`).
//! - `compat-bench`: sampled observation only; `attestable == false` everywhere
//!   and never eligible for G1 or import reuse.
#![forbid(unsafe_code)]

use std::num::NonZeroUsize;

use fln::{
    AxiomVal, BinderInfo, Budget, CheckerHighRiskForm, CheckerPolicySummary,
    CheckerSelectionReason, ConstantInfo, ConstantVal, ConstructorVal, Declaration,
    DefinitionSafety, DefinitionVal, Engine, EngineAdmissionError, Environment, Expr, InductiveVal,
    KVMap, Level, Literal, Name, NatLit, OLEAN_ACCEPTED_VERSIONS, OLEAN_PIN_COMMIT, OLEAN_PIN_TAG,
    OLEAN_REGION_ALIGN, OleanCheckError, OleanCheckLimits, OleanFrontierJobs, OleanModuleImport,
    OleanModuleInput, OleanModuleVerdict, OleanModuleWriteInput, OleanWriteBudget,
    OleanWriteHeader, Outcome, RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
    VerificationPolicy, encode_olean_module,
};

const STACK_BYTES: usize = 16 * 1024 * 1024;

fn n(parts: &[&str]) -> Name {
    Name::from_components(parts.iter().copied())
}

fn bv(idx: u32) -> Expr {
    Expr::bvar(idx).expect("small bvar")
}

fn encode_fixture(imports: &[OleanModuleImport], constants: &[ConstantInfo]) -> Vec<u8> {
    encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.trim_start_matches('v'),
            githash: OLEAN_PIN_COMMIT,
            base_addr: OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("encode test olean fixture")
    .bytes
}

fn simple_prop_axiom(name: Name) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: false,
    })
}

fn simple_identity_thm(name: Name, prop: &Name, binder_info: BinderInfo) -> ConstantInfo {
    let p = Expr::const_(prop.clone(), Vec::new());
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: Expr::forall_e(n(&["h"]), p.clone(), p.clone(), binder_info),
        },
        value: Expr::lam(n(&["h"]), p, bv(0), binder_info),
        all: Vec::new(),
    })
}

fn simple_unsafe_def(name: Name, prop: &Name, binder_info: BinderInfo) -> ConstantInfo {
    let p = Expr::const_(prop.clone(), Vec::new());
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::forall_e(n(&["h"]), p.clone(), p.clone(), binder_info),
        },
        value: Expr::lam(n(&["h"]), p, bv(0), binder_info),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Unsafe,
        all: vec![name],
    })
}

fn nullary_inductive_family(prefix: &str) -> Vec<ConstantInfo> {
    let ind_name = n(&[prefix, "Flag"]);
    let ctor_a = n(&[prefix, "Flag", "on"]);
    let ctor_b = n(&[prefix, "Flag", "off"]);
    let rec_name = n(&[prefix, "Flag", "rec"]);
    let u = Level::param(n(&["u"]));
    let flag = Expr::const_(ind_name.clone(), Vec::new());
    let motive = Expr::forall_e(
        n(&["t"]),
        flag.clone(),
        Expr::sort(u.clone()),
        BinderInfo::Default,
    );
    let minor_a = Expr::app(bv(0), Expr::const_(ctor_a.clone(), Vec::new()));
    let minor_b = Expr::app(bv(1), Expr::const_(ctor_b.clone(), Vec::new()));
    let rec_ty = Expr::forall_e(
        n(&["motive"]),
        motive.clone(),
        Expr::forall_e(
            n(&["on"]),
            minor_a.clone(),
            Expr::forall_e(
                n(&["off"]),
                minor_b.clone(),
                Expr::forall_e(
                    n(&["t"]),
                    flag.clone(),
                    Expr::app(bv(3), bv(0)),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let rhs_a = Expr::lam(
        n(&["motive"]),
        motive.clone(),
        Expr::lam(
            n(&["on"]),
            minor_a.clone(),
            Expr::lam(n(&["off"]), minor_b.clone(), bv(1), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let rhs_b = Expr::lam(
        n(&["motive"]),
        motive,
        Expr::lam(
            n(&["on"]),
            minor_a,
            Expr::lam(n(&["off"]), minor_b, bv(0), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    vec![
        ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: ind_name.clone(),
                level_params: Vec::new(),
                type_: Expr::sort(Level::succ(Level::zero()).expect("level 1")),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![ind_name.clone()],
            ctors: vec![ctor_a.clone(), ctor_b.clone()],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: ctor_a.clone(),
                level_params: Vec::new(),
                type_: flag.clone(),
            },
            induct: ind_name.clone(),
            cidx: 0,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: ctor_b.clone(),
                level_params: Vec::new(),
                type_: flag,
            },
            induct: ind_name.clone(),
            cidx: 1,
            num_params: 0,
            num_fields: 0,
            is_unsafe: false,
        }),
        ConstantInfo::Rec(RecursorVal {
            base: ConstantVal {
                name: rec_name,
                level_params: vec![n(&["u"])],
                type_: rec_ty,
            },
            all: vec![ind_name],
            num_params: 0,
            num_indices: 0,
            num_motives: 1,
            num_minors: 2,
            rules: vec![
                RecursorRule {
                    ctor: ctor_a,
                    nfields: 0,
                    rhs: rhs_a,
                },
                RecursorRule {
                    ctor: ctor_b,
                    nfields: 0,
                    rhs: rhs_b,
                },
            ],
            k: false,
            is_unsafe: false,
        }),
    ]
}

fn large_mixed_constants() -> Vec<ConstantInfo> {
    let prop = n(&["PolicyFix", "P"]);
    let mut rows = vec![simple_prop_axiom(prop.clone())];
    // 64 ordinary theorems so the 1/16 content-seeded bucket both selects some
    // and skips most deterministically.
    for idx in 0..64 {
        rows.push(simple_identity_thm(
            n(&["PolicyFix", &format!("thm_{idx:02}")]),
            &prop,
            BinderInfo::Default,
        ));
    }
    // High-risk unsafe definition.
    rows.push(simple_unsafe_def(
        n(&["PolicyFix", "unsafeId"]),
        &prop,
        BinderInfo::Default,
    ));
    // High-risk inductive family (Flag + 2 ctors + recursor).
    rows.extend(nullary_inductive_family("PolicyFix"));
    rows
}

#[test]
fn policy_risk_classifier_catches_every_high_risk_class() {
    let prop = n(&["Risk", "P"]);
    // Ordinary safe theorem: no static high-risk forms.
    let ConstantInfo::Thm(plain_thm) =
        simple_identity_thm(n(&["Risk", "plain"]), &prop, BinderInfo::Default)
    else {
        unreachable!()
    };
    assert!(fln::classify_declaration_risks(&Declaration::Thm(plain_thm)).is_empty());

    // Unsafe / partial definitions -> NativeReduction floor.
    let ConstantInfo::Defn(unsafe_def) =
        simple_unsafe_def(n(&["Risk", "unsafeDef"]), &prop, BinderInfo::Default)
    else {
        unreachable!()
    };
    let unsafe_risks = fln::classify_declaration_risks(&Declaration::Defn(unsafe_def));
    assert!(unsafe_risks.contains(CheckerHighRiskForm::NativeReduction));

    // eagerReduce / Decidable.decide / Lean.ofReduceBool references -> NativeReduction floor.
    for sym in [
        n(&["eagerReduce"]),
        n(&["Decidable", "decide"]),
        n(&["Lean", "ofReduceBool"]),
        n(&["Lean", "ofReduceNat"]),
        n(&["Lean", "trustCompiler"]),
    ] {
        let ax = AxiomVal {
            base: ConstantVal {
                name: n(&["Risk", "refNative"]),
                level_params: Vec::new(),
                type_: Expr::const_(sym.clone(), Vec::new()),
            },
            is_unsafe: false,
        };
        let risks = fln::classify_declaration_risks(&Declaration::Axiom(ax));
        assert!(
            risks.contains(CheckerHighRiskForm::NativeReduction),
            "symbol {} must trigger NativeReduction floor",
            sym.to_display_string()
        );
    }

    // Literal arithmetic (Nat > 1) -> LiteralArithmetic floor.
    let lit_ax = AxiomVal {
        base: ConstantVal {
            name: n(&["Risk", "litArith"]),
            level_params: Vec::new(),
            type_: Expr::lit(Literal::Nat(NatLit::from_u64(42))),
        },
        is_unsafe: false,
    };
    assert!(
        fln::classify_declaration_risks(&Declaration::Axiom(lit_ax))
            .contains(CheckerHighRiskForm::LiteralArithmetic)
    );

    // Deep universe (depth > 8) -> DeepUniverse floor.
    let mut deep = Level::zero();
    for _ in 0..10 {
        deep = Level::succ(deep).expect("level depth 10");
    }
    let deep_ax = AxiomVal {
        base: ConstantVal {
            name: n(&["Risk", "deepUniv"]),
            level_params: Vec::new(),
            type_: Expr::sort(deep),
        },
        is_unsafe: false,
    };
    assert!(
        fln::classify_declaration_risks(&Declaration::Axiom(deep_ax))
            .contains(CheckerHighRiskForm::DeepUniverse)
    );
}

#[test]
fn standard_release_compat_bench_and_paranoid_policies_behave_per_spec() {
    let constants = large_mixed_constants();
    let bytes = encode_fixture(&[], &constants);
    let base_limits = OleanCheckLimits::new(bytes.len(), Budget::for_stack_bytes(STACK_BYTES));
    let engine = Engine::from_environment(Environment::new());

    // 1. Release: 100% checked by fln-checker, attestable, G1-eligible.
    let release = engine
        .check_olean_artifact(
            &bytes,
            &KVMap::new(),
            base_limits.with_policy(VerificationPolicy::Release),
        )
        .expect("release check")
        .into_complete()
        .expect("release completes");
    let rel_summary = release.policy_summary(VerificationPolicy::Release);
    assert_eq!(rel_summary.policy, VerificationPolicy::Release);
    assert!(rel_summary.attestable);
    assert_eq!(rel_summary.k1_checked, constants.len() as u64);
    assert_eq!(rel_summary.checker_selected, constants.len() as u64);
    assert_eq!(rel_summary.checker_full_policy, constants.len() as u64);
    assert_eq!(rel_summary.checker_skipped, 0);
    assert!(release.declarations.iter().all(|d| d.is_checker_reviewed()));

    // 2. Standard: K1 on 100%, fln-checker on high-risk floor + deterministic 1/16 bucket.
    let standard = engine
        .check_olean_artifact(
            &bytes,
            &KVMap::new(),
            base_limits.with_policy(VerificationPolicy::Standard),
        )
        .expect("standard check")
        .into_complete()
        .expect("standard completes");
    let std_summary = standard.policy_summary(VerificationPolicy::Standard);
    assert_eq!(std_summary.policy, VerificationPolicy::Standard);
    assert!(std_summary.attestable);
    assert_eq!(std_summary.k1_checked, constants.len() as u64);
    assert!(
        std_summary.checker_skipped > 0 && std_summary.checker_selected < std_summary.k1_checked,
        "standard policy must skip ordinary declarations outside the 1/16 bucket: {std_summary:?}"
    );
    assert!(
        std_summary.checker_high_risk >= 5,
        "unsafeId + 4 Flag inductive rows must hit high-risk floor: {std_summary:?}"
    );
    assert_eq!(
        std_summary.checker_selected + std_summary.checker_skipped,
        std_summary.k1_checked
    );
    assert_eq!(
        std_summary.checker_full_policy
            + std_summary.checker_high_risk
            + std_summary.checker_sampled,
        std_summary.checker_selected
    );
    // High-risk declarations MUST have been reviewed by fln-checker.
    for must_check in [
        "PolicyFix.unsafeId",
        "PolicyFix.Flag",
        "PolicyFix.Flag.on",
        "PolicyFix.Flag.off",
        "PolicyFix.Flag.rec",
    ] {
        let row = standard
            .declarations
            .iter()
            .find(|d| d.name.to_display_string() == must_check)
            .expect("high-risk declaration present");
        assert!(
            row.is_checker_reviewed(),
            "{must_check} must be reviewed by fln-checker under standard policy"
        );
        assert_eq!(
            row.policy_decision.expect("policy decision").reason,
            CheckerSelectionReason::HighRiskFloor
        );
    }
    // Resulting K1 environment logical root is bit-identical between release and standard!
    assert_eq!(release.result_logical_root, standard.result_logical_root);

    // 3. K1 step floor: setting high_risk_k1_steps = 0 forces EVERY declaration
    //    that consumes >= 1 K1 step across fln-checker under standard policy!
    let k1_floor = engine
        .check_olean_artifact(
            &bytes,
            &KVMap::new(),
            base_limits
                .with_policy(VerificationPolicy::Standard)
                .with_high_risk_k1_steps(0),
        )
        .expect("k1 step floor check")
        .into_complete()
        .expect("k1 step floor completes");
    let k1_floor_summary = k1_floor.policy_summary(VerificationPolicy::Standard);
    assert!(
        k1_floor_summary.checker_high_risk_k1_steps > 0,
        "lowering high_risk_k1_steps must trigger the K1-step high-risk floor: {k1_floor_summary:?}"
    );
    assert!(
        k1_floor_summary.checker_selected > std_summary.checker_selected,
        "K1-step floor must strictly increase checker selection over default standard"
    );

    // 4. CompatBench: identical selection counts to Standard, NEVER attestable!
    let bench = engine
        .check_olean_artifact(
            &bytes,
            &KVMap::new(),
            base_limits.with_policy(VerificationPolicy::CompatBench),
        )
        .expect("compat-bench check")
        .into_complete()
        .expect("compat-bench completes");
    let bench_summary = bench.policy_summary(VerificationPolicy::CompatBench);
    assert_eq!(bench_summary.policy, VerificationPolicy::CompatBench);
    assert!(
        !bench_summary.attestable,
        "compat-bench must NEVER be attestable"
    );
    assert_eq!(bench_summary.k1_checked, std_summary.k1_checked);
    assert_eq!(bench_summary.checker_selected, std_summary.checker_selected);
    assert_eq!(bench_summary.checker_skipped, std_summary.checker_skipped);

    // 5. Paranoid: unavailable K2 / external witness MUST return non-answer, NEVER fallback!
    let paranoid = engine.check_olean_artifact(
        &bytes,
        &KVMap::new(),
        base_limits.with_policy(VerificationPolicy::Paranoid),
    );
    assert!(
        matches!(
            paranoid,
            Err(OleanCheckError::Admission(
                EngineAdmissionError::BatchDeclaration { ref error, .. }
            )) if matches!(error.as_ref(), EngineAdmissionError::CouncilNoAnswer { summary } if summary.contains("paranoid-second-witness"))
        ),
        "paranoid must halt as CouncilNoAnswer when K2/external witness is unavailable, got: {paranoid:?}"
    );

    // Even an empty module MUST return Inconclusive under Paranoid (no silent success).
    let empty_bytes = encode_fixture(&[], &[]);
    let empty_paranoid = engine
        .check_olean_artifact(
            &empty_bytes,
            &KVMap::new(),
            OleanCheckLimits::new(empty_bytes.len(), Budget::for_stack_bytes(STACK_BYTES))
                .with_policy(VerificationPolicy::Paranoid),
        )
        .expect("empty paranoid returns typed Outcome::Inconclusive");
    assert!(
        matches!(empty_paranoid, Outcome::Inconclusive(_)),
        "empty module under paranoid must be Inconclusive, got: {empty_paranoid:?}"
    );
}

#[test]
fn planted_checker_only_defect_in_high_risk_declaration_is_caught_under_standard() {
    // Plant a defect that K1 accepts (binder info does not change typing) while
    // fln-checker's independent reading of the artifact bytes catches the mismatch.
    // Because `unsafeId` is a high-risk declaration (`DefinitionSafety::Unsafe`),
    // `--policy standard` MUST route it to fln-checker even if its content hash
    // falls outside the 1/16 sampling bucket.
    let prop = n(&["HighRiskDefect", "P"]);
    let primary_rows = vec![
        simple_prop_axiom(prop.clone()),
        simple_unsafe_def(
            n(&["HighRiskDefect", "unsafeId"]),
            &prop,
            BinderInfo::Default,
        ),
    ];
    let flipped_rows = vec![
        simple_prop_axiom(prop.clone()),
        simple_unsafe_def(
            n(&["HighRiskDefect", "unsafeId"]),
            &prop,
            BinderInfo::Implicit,
        ),
    ];
    let primary_bytes = encode_fixture(&[], &primary_rows);
    let flipped_bytes = encode_fixture(&[], &flipped_rows);
    let limits = OleanCheckLimits::new(
        primary_bytes.len().max(flipped_bytes.len()),
        Budget::for_stack_bytes(STACK_BYTES),
    )
    .with_policy(VerificationPolicy::Standard);

    let mut decoded =
        fln::decode_olean_artifact(&primary_bytes, limits.decode).expect("decode primary");
    // Replace the independent checker's own reading with the flipped artifact's
    // reading: K1 accepts `primary_rows` cleanly, so ONLY fln-checker can catch it.
    decoded.independent = fln::independent_reading(&[&flipped_bytes], limits.decode);

    let engine = Engine::from_environment(Environment::new());
    let err = engine
        .check_decoded_olean(decoded, &KVMap::new(), limits)
        .expect_err("standard policy MUST catch checker-only defect on high-risk unsafeId");
    assert!(
        matches!(
            err,
            OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration { ref error, .. })
                if matches!(error.as_ref(), EngineAdmissionError::CouncilHalted { summary } if summary.contains("HighRiskDefect.unsafeId"))
        ),
        "expected CouncilHalted naming HighRiskDefect.unsafeId, got: {err:?}"
    );
}

#[test]
fn standard_policy_selection_is_identical_across_thread_counts() {
    // Build a 4-module diamond: Base -> Left, Base -> Right, {Left, Right} -> Top.
    let base_name = n(&["DetPol", "Base"]);
    let left_name = n(&["DetPol", "Left"]);
    let right_name = n(&["DetPol", "Right"]);
    let top_name = n(&["DetPol", "Top"]);
    let prop = n(&["DetPol", "P"]);

    let base_bytes = encode_fixture(&[], &[simple_prop_axiom(prop.clone())]);
    let imp = |module: &Name| OleanModuleImport {
        module: module.clone(),
        import_all: false,
        is_exported: false,
        is_meta: false,
    };
    let left_rows: Vec<ConstantInfo> = (0..24)
        .map(|i| {
            simple_identity_thm(
                n(&["DetPol", &format!("L{i:02}")]),
                &prop,
                BinderInfo::Default,
            )
        })
        .collect();
    let right_rows: Vec<ConstantInfo> = (0..24)
        .map(|i| {
            simple_identity_thm(
                n(&["DetPol", &format!("R{i:02}")]),
                &prop,
                BinderInfo::Default,
            )
        })
        .collect();
    let mut top_rows: Vec<ConstantInfo> = (0..16)
        .map(|i| {
            simple_identity_thm(
                n(&["DetPol", &format!("T{i:02}")]),
                &prop,
                BinderInfo::Default,
            )
        })
        .collect();
    top_rows.push(simple_unsafe_def(
        n(&["DetPol", "topUnsafe"]),
        &prop,
        BinderInfo::Default,
    ));

    let left_bytes = encode_fixture(&[imp(&base_name)], &left_rows);
    let right_bytes = encode_fixture(&[imp(&base_name)], &right_rows);
    let top_bytes = encode_fixture(&[imp(&left_name), imp(&right_name)], &top_rows);
    let total_bytes = base_bytes.len() + left_bytes.len() + right_bytes.len() + top_bytes.len();
    let inputs = [
        OleanModuleInput {
            name: &top_name,
            artifact: &top_bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &right_name,
            artifact: &right_bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &left_name,
            artifact: &left_bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &base_name,
            artifact: &base_bytes,
            server_artifact: None,
            private_artifact: None,
        },
    ];
    let limits = OleanCheckLimits::new(total_bytes, Budget::for_stack_bytes(STACK_BYTES))
        .with_policy(VerificationPolicy::Standard);
    let engine = Engine::from_environment(Environment::new());

    let run = |threads: usize| -> (CheckerPolicySummary, Vec<CheckerPolicySummary>) {
        let frontier = engine
            .check_olean_frontier_scheduled(
                &inputs,
                &KVMap::new(),
                limits,
                OleanFrontierJobs {
                    threads: NonZeroUsize::new(threads).unwrap(),
                    worker_stack_bytes: STACK_BYTES,
                },
                &mut |_| {},
            )
            .expect("scheduled frontier");
        assert!(
            frontier
                .rows
                .iter()
                .all(|row| matches!(row.verdict, OleanModuleVerdict::Accepted { .. }))
        );
        let per_row = frontier.rows.iter().map(|r| r.policy_summary).collect();
        (frontier.policy_summary, per_row)
    };

    let (serial_agg, serial_rows) = run(1);
    let (parallel_4_agg, parallel_4_rows) = run(4);
    let (parallel_8_agg, parallel_8_rows) = run(8);

    assert_eq!(serial_agg, parallel_4_agg);
    assert_eq!(serial_agg, parallel_8_agg);
    assert_eq!(serial_rows, parallel_4_rows);
    assert_eq!(serial_rows, parallel_8_rows);
    assert!(serial_agg.checker_skipped > 0);
    assert!(serial_agg.checker_high_risk >= 1);
}
