//! Pin-free companion unit & negative-control tests for the file-scale T2/T3
//! declaration-identity comparator (bead `fln-file-scale-t2-differential-5f1b`).
//!
//! Runs on every `cargo test -p fln-conformance` without requiring the pinned
//! Reference toolchain, exercising:
//! * planted implicit-binder, type, and universe mutations -> T2 mismatch;
//! * proof-body-only mutation -> T2 preserved, T3 flipped;
//! * alpha-renaming & `MData` normalization preserves ONLY declared equivalences;
//! * auxiliary declaration addition/removal -> name-set T2 mismatch;
//! * attribute mismatch detection (`protected`, `reducibility`, `instance`);
//! * missing & corrupted `.olean` artifact typed refusal + pristine recovery;
//! * crash/resume JSONL checkpoint recovery from truncated/corrupted tail and
//!   digest-invalidation on changed source;
//! * ratchet ledger enforcement of nonzero floors, zero false accepts, zero T2
//!   regressions, and mandatory residual ownership.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;

use fln::OleanDecodeLimits;
use fln_conformance::t2_differential::{
    AuxClass, CheckpointJournal, DeclarationRole, ModuleSnapshot, ObservedFileRow, SideVerdict,
    SnapshotError, T2NormalizerId, T2RatchetLedger, TierStatus, classify_declaration_name,
    compare_modules, fixture_digest_hex, normalize_expr, scratch_root,
};
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints, TheoremVal,
};

fn n(path: &str) -> Name {
    Name::from_components(path.split('.'))
}

fn identity_type(u_name: &str, alpha_name: &str, x_name: &str, alpha_bi: BinderInfo) -> Expr {
    let sort_u = Expr::sort(Level::param(n(u_name)));
    let b0 = Expr::bvar(0).unwrap();
    let b1 = Expr::bvar(1).unwrap();
    let inner = Expr::forall_e(n(x_name), b0, b1, BinderInfo::Default);
    Expr::forall_e(n(alpha_name), sort_u, inner, alpha_bi)
}

fn identity_value(u_name: &str, alpha_name: &str, x_name: &str, alpha_bi: BinderInfo) -> Expr {
    let sort_u = Expr::sort(Level::param(n(u_name)));
    let b0 = Expr::bvar(0).unwrap();
    let inner = Expr::lam(n(x_name), b0.clone(), b0, BinderInfo::Default);
    Expr::lam(n(alpha_name), sort_u, inner, alpha_bi)
}

fn mk_defn(
    name: &str,
    u_name: &str,
    alpha_name: &str,
    x_name: &str,
    alpha_bi: BinderInfo,
) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![n(u_name)],
            type_: identity_type(u_name, alpha_name, x_name, alpha_bi),
        },
        value: identity_value(u_name, alpha_name, x_name, alpha_bi),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn mk_snapshot(constants: Vec<ConstantInfo>) -> ModuleSnapshot {
    ModuleSnapshot {
        module: n("Main"),
        constants: constants
            .into_iter()
            .map(|c| (c.name().clone(), c))
            .collect(),
        attributes: BTreeMap::new(),
    }
}

#[test]
fn planted_implicit_binder_and_type_mutations_fail_t2() {
    let pin = mk_snapshot(vec![mk_defn("id", "u", "α", "x", BinderInfo::Implicit)]);
    let exact = mk_snapshot(vec![mk_defn("id", "u", "α", "x", BinderInfo::Implicit)]);
    let cmp_ok = compare_modules(&exact, &pin, T2NormalizerId::V1).unwrap();
    assert!(cmp_ok.full_t2_identical);
    assert!(cmp_ok.t3_identical);

    // Planted implicit -> explicit binder mutation must fail T2 and report exact binder_info path.
    let explicit_binder = mk_snapshot(vec![mk_defn("id", "u", "α", "x", BinderInfo::Default)]);
    let cmp_binder = compare_modules(&explicit_binder, &pin, T2NormalizerId::V1).unwrap();
    assert!(!cmp_binder.primary_t2_identical);
    assert!(!cmp_binder.full_t2_identical);
    assert_eq!(cmp_binder.diff_class(), "primary_t2_interface");
    assert!(
        cmp_binder.t2_diffs.iter().any(|d| d
            .reasons
            .iter()
            .any(|r| r.contains("binder_info: Default vs Implicit"))),
        "expected binder_info diff, got {:?}",
        cmp_binder.t2_diffs
    );

    // Planted type change (`Sort (u+1)` vs `Sort u`) must fail T2.
    let mut bad_level = mk_defn("id", "u", "α", "x", BinderInfo::Implicit);
    if let ConstantInfo::Defn(ref mut def) = bad_level {
        let sort_u1 = Expr::sort(Level::param(n("u")).succ().unwrap());
        let b0 = Expr::bvar(0).unwrap();
        let b1 = Expr::bvar(1).unwrap();
        def.base.type_ = Expr::forall_e(
            n("α"),
            sort_u1,
            Expr::forall_e(n("x"), b0, b1, BinderInfo::Default),
            BinderInfo::Implicit,
        );
    }
    let cmp_level =
        compare_modules(&mk_snapshot(vec![bad_level]), &pin, T2NormalizerId::V1).unwrap();
    assert!(!cmp_level.primary_t2_identical);
    assert!(
        cmp_level
            .t2_diffs
            .iter()
            .any(|d| d.reasons.iter().any(|r| r.contains("sort level"))),
        "expected sort level diff, got {:?}",
        cmp_level.t2_diffs
    );
}

#[test]
fn proof_body_change_preserves_t2_and_flips_t3() {
    let prop_type = Expr::const_(n("True"), Vec::new());
    let proof_a = Expr::const_(n("True.intro"), Vec::new());
    let proof_b = Expr::app(
        Expr::lam(
            n("h"),
            prop_type.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        Expr::const_(n("True.intro"), Vec::new()),
    );
    let pin = mk_snapshot(vec![ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n("myThm"),
            level_params: Vec::new(),
            type_: prop_type.clone(),
        },
        value: proof_a,
        all: vec![n("myThm")],
    })]);
    let native = mk_snapshot(vec![ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n("myThm"),
            level_params: Vec::new(),
            type_: prop_type,
        },
        value: proof_b,
        all: vec![n("myThm")],
    })]);

    let cmp = compare_modules(&native, &pin, T2NormalizerId::V1).unwrap();
    assert!(
        cmp.primary_t2_identical,
        "proof body change must keep primary T2"
    );
    assert!(cmp.full_t2_identical, "proof body change must keep full T2");
    assert!(!cmp.t3_identical, "proof body change must flip T3");
    assert_eq!(cmp.t3_diffs.len(), 1);
    assert!(cmp.t3_diffs[0].detail.starts_with("thm.proof:"));
}

#[test]
fn alpha_and_mdata_normalizer_preserves_only_declared_equivalences() {
    // Alpha renaming of binder names + universe param name + MData wrapper -> identical under V1.
    let pin_defn = mk_defn("id", "u", "α", "x", BinderInfo::Implicit);
    let mut native_defn = mk_defn(
        "id",
        "v_renamed",
        "T_renamed",
        "arg_renamed",
        BinderInfo::Implicit,
    );
    let mut mdata = KVMap::new();
    mdata.insert(n("pp.explicit"), DataValue::OfBool(true));
    if let ConstantInfo::Defn(ref mut def) = native_defn {
        def.base.type_ = Expr::mdata(mdata.clone(), def.base.type_.clone());
        def.value = Expr::mdata(mdata.clone(), def.value.clone());
    }
    let cmp = compare_modules(
        &mk_snapshot(vec![native_defn]),
        &mk_snapshot(vec![pin_defn.clone()]),
        T2NormalizerId::V1,
    )
    .unwrap();
    assert!(
        cmp.full_t2_identical,
        "alpha + MData must normalize equal: {:?}",
        cmp.t2_diffs
    );
    assert!(
        cmp.t3_identical,
        "alpha + MData values must normalize equal: {:?}",
        cmp.t3_diffs
    );

    // Stripping MData must NEVER hide a semantic change (e.g. StrictImplicit vs Implicit inside MData).
    let mut disguised = mk_defn("id", "u", "α", "x", BinderInfo::StrictImplicit);
    if let ConstantInfo::Defn(ref mut def) = disguised {
        def.base.type_ = Expr::mdata(mdata, def.base.type_.clone());
    }
    let cmp_bad = compare_modules(
        &mk_snapshot(vec![disguised]),
        &mk_snapshot(vec![pin_defn]),
        T2NormalizerId::V1,
    )
    .unwrap();
    assert!(!cmp_bad.full_t2_identical);
    assert!(
        cmp_bad.t2_diffs[0]
            .reasons
            .iter()
            .any(|r| r.contains("StrictImplicit vs Implicit"))
    );

    // Algebraic Level normalization: `max u 0` == `u`, while `max u 1` != `u`.
    let u = Level::param(n("u"));
    let max_u_0 = Expr::sort(Level::max(u.clone(), Level::zero()).unwrap());
    let plain_u = Expr::sort(u.clone());
    let max_u_1 = Expr::sort(Level::max(u, Level::one()).unwrap());
    assert_eq!(
        normalize_expr(&max_u_0, &[n("u")], T2NormalizerId::V1).unwrap(),
        normalize_expr(&plain_u, &[n("u")], T2NormalizerId::V1).unwrap(),
    );
    assert_ne!(
        normalize_expr(&max_u_1, &[n("u")], T2NormalizerId::V1).unwrap(),
        normalize_expr(&plain_u, &[n("u")], T2NormalizerId::V1).unwrap(),
    );
}

#[test]
fn auxiliary_name_set_and_attribute_mismatches_fail_t2() {
    let base_fn = mk_defn("foo", "u", "α", "x", BinderInfo::Implicit);
    let aux_eq = ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n("foo.eq_1"),
            level_params: Vec::new(),
            type_: Expr::const_(n("True"), Vec::new()),
        },
        value: Expr::const_(n("True.intro"), Vec::new()),
        all: vec![n("foo.eq_1")],
    });

    let pin = mk_snapshot(vec![base_fn.clone(), aux_eq.clone()]);
    let missing_aux = mk_snapshot(vec![base_fn.clone()]);
    let cmp_missing = compare_modules(&missing_aux, &pin, T2NormalizerId::V1).unwrap();
    assert!(cmp_missing.primary_t2_identical);
    assert!(!cmp_missing.full_t2_identical);
    assert_eq!(cmp_missing.diff_class(), "auxiliary_name_set");
    assert_eq!(
        cmp_missing.pin_only_auxiliary,
        vec![(n("foo.eq_1"), AuxClass::Equation)]
    );

    let extra_aux = mk_snapshot(vec![
        base_fn.clone(),
        aux_eq,
        mk_defn("foo._sunfold", "u", "α", "x", BinderInfo::Implicit),
    ]);
    let cmp_extra = compare_modules(&extra_aux, &pin, T2NormalizerId::V1).unwrap();
    assert!(!cmp_extra.full_t2_identical);
    assert_eq!(
        cmp_extra.native_only_auxiliary,
        vec![(n("foo._sunfold"), AuxClass::Sunfold)]
    );

    // Attribute mismatch (`protected` missing in native) must fail T2.
    let mut pin_attr = mk_snapshot(vec![base_fn.clone()]);
    pin_attr
        .attributes
        .entry(n("foo"))
        .or_default()
        .insert("protected".to_owned());
    let native_no_attr = mk_snapshot(vec![base_fn]);
    let cmp_attr = compare_modules(&native_no_attr, &pin_attr, T2NormalizerId::V1).unwrap();
    assert!(!cmp_attr.primary_t2_identical);
    assert!(!cmp_attr.full_t2_identical);
    assert!(
        cmp_attr.t2_diffs[0]
            .reasons
            .iter()
            .any(|r| r.contains("missing_in_native=[\"protected\"]"))
    );
}

#[test]
fn missing_and_corrupted_olean_artifacts_refuse_typed_and_pristine_recovers() {
    let dir = scratch_root("artifact-recovery").unwrap();
    let limits = OleanDecodeLimits::new(16 * 1024 * 1024);

    // 1. Missing artifact -> typed MissingArtifact refusal.
    let absent = dir.join("absent.olean");
    assert!(matches!(
        ModuleSnapshot::from_olean_file(n("Absent"), &absent, limits),
        Err(SnapshotError::MissingArtifact { .. })
    ));

    // 2. Corrupted/truncated bytes -> typed Decode refusal (never panics).
    let corrupt = dir.join("corrupt.olean");
    fs::write(&corrupt, b"not-an-olean-header").unwrap();
    assert!(matches!(
        ModuleSnapshot::from_olean_file(n("Corrupt"), &corrupt, limits),
        Err(SnapshotError::Decode { .. })
    ));

    // 3. Pristine native-emitted `.olean` recovers cleanly into the exact constants.
    let initial = fln::Engine::builder().build_empty();
    let source = b"prelude\ndef pristine.{u} {A : Sort u} (x : A) : A := x\n";
    let built = initial
        .compile_source_modules(
            &[fln::SourceModuleInput {
                name: &n("Pristine"),
                source,
            }],
            &n("Pristine"),
            &fln::KVMap::new(),
            fln::source_check::modules::SourceModuleCheckLimits::new(fln::SourceCheckLimits::new(
                fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024)),
            )),
            fln::OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let pristine_path = dir.join("Pristine.olean");
    fs::write(&pristine_path, &built.artifacts[0].bytes).unwrap();
    let recovered = ModuleSnapshot::from_olean_file(n("Pristine"), &pristine_path, limits).unwrap();
    assert!(recovered.constants.contains_key(&n("pristine")));
}

#[test]
fn crash_resume_checkpoint_recovers_truncated_tail_and_invalidates_changed_source() {
    let dir = scratch_root("checkpoint-resume").unwrap();
    let ckpt_path = dir.join("run.jsonl");

    let row_a = ObservedFileRow {
        family: "source_ladder".to_owned(),
        file: "examples/a.lean".to_owned(),
        source_digest: fixture_digest_hex(b"def a := 1"),
        pin_tag: "v4.32.0".to_owned(),
        pin_commit: "8c9756b2".to_owned(),
        binary_digest: fixture_digest_hex(b"bin-v1"),
        normalizer: T2NormalizerId::V1.as_str().to_owned(),
        pin_verdict: SideVerdict::Accept,
        native_verdict: SideVerdict::Accept,
        primary_t2: TierStatus::Identical,
        full_t2: TierStatus::Identical,
        t3: TierStatus::Identical,
        diff_class: "identical".to_owned(),
        first_difference: String::new(),
        native_decls: 1,
        pin_decls: 1,
    };

    let mut journal = CheckpointJournal::load(&ckpt_path).unwrap();
    journal.record(row_a.clone()).unwrap();

    // Simulate a crash leaving a half-written JSONL line at the tail.
    let mut raw = fs::read_to_string(&ckpt_path).unwrap();
    raw.push_str("{\"schema\":\"fln.t2-differential-checkpoint/1\",\"file\":\"examples/b.lean\"");
    fs::write(&ckpt_path, raw).unwrap();

    let resumed = CheckpointJournal::load(&ckpt_path).unwrap();
    assert_eq!(resumed.corrupted_lines(), 1);
    // Exact identity hit reuses row_a.
    let hit = resumed
        .reusable(
            "examples/a.lean",
            &row_a.source_digest,
            "v4.32.0",
            "8c9756b2",
            &row_a.binary_digest,
            T2NormalizerId::V1.as_str(),
        )
        .expect("matching checkpoint must be reused");
    assert_eq!(hit, &row_a);
    // Changed source digest invalidates cached entry.
    assert!(
        resumed
            .reusable(
                "examples/a.lean",
                &fixture_digest_hex(b"def a := 2"),
                "v4.32.0",
                "8c9756b2",
                &row_a.binary_digest,
                T2NormalizerId::V1.as_str(),
            )
            .is_none()
    );
    // Truncated entry b.lean is not reused.
    assert!(
        resumed
            .reusable(
                "examples/b.lean",
                &fixture_digest_hex(b"def b := 1"),
                "v4.32.0",
                "8c9756b2",
                &row_a.binary_digest,
                T2NormalizerId::V1.as_str(),
            )
            .is_none()
    );
}

#[test]
fn ratchet_ledger_enforces_floors_forbids_false_accepts_and_catches_t2_regression() {
    let ledger_text = "\
# schema=fln.t2-differential-ledger/1
# pin_tag=v4.32.0
# normalizer=fln.t2-decl-normalizer/1
# floor source_ladder 1
# floor ordinary_probe 1
source_ladder\texamples/id.lean\taccept\taccept\tidentical\tidentical\tidentical\tidentical\tverified
ordinary_probe\tprobe/bad.lean\treject\treject\tn/a\tn/a\tn/a\tboth_reject\tnegative_control
";
    let ledger = T2RatchetLedger::parse(ledger_text).unwrap();

    let ok_rows = vec![
        ObservedFileRow {
            family: "source_ladder".to_owned(),
            file: "examples/id.lean".to_owned(),
            source_digest: "aaa".to_owned(),
            pin_tag: "v4.32.0".to_owned(),
            pin_commit: "8c9756b2".to_owned(),
            binary_digest: "bbb".to_owned(),
            normalizer: T2NormalizerId::V1.as_str().to_owned(),
            pin_verdict: SideVerdict::Accept,
            native_verdict: SideVerdict::Accept,
            primary_t2: TierStatus::Identical,
            full_t2: TierStatus::Identical,
            t3: TierStatus::Identical,
            diff_class: "identical".to_owned(),
            first_difference: String::new(),
            native_decls: 1,
            pin_decls: 1,
        },
        ObservedFileRow {
            family: "ordinary_probe".to_owned(),
            file: "probe/bad.lean".to_owned(),
            source_digest: "ccc".to_owned(),
            pin_tag: "v4.32.0".to_owned(),
            pin_commit: "8c9756b2".to_owned(),
            binary_digest: "bbb".to_owned(),
            normalizer: T2NormalizerId::V1.as_str().to_owned(),
            pin_verdict: SideVerdict::Reject,
            native_verdict: SideVerdict::Reject,
            primary_t2: TierStatus::NotApplicable,
            full_t2: TierStatus::NotApplicable,
            t3: TierStatus::NotApplicable,
            diff_class: "both_reject".to_owned(),
            first_difference: String::new(),
            native_decls: 0,
            pin_decls: 0,
        },
    ];
    assert!(ledger.verify(&ok_rows).is_clean());

    // 1. T2 regression fails the ratchet.
    let mut regressed = ok_rows.clone();
    regressed[0].full_t2 = TierStatus::Diff;
    regressed[0].first_difference = "pin_only_aux(equation): id.eq_1".to_owned();
    let v_reg = ledger.verify(&regressed);
    assert!(!v_reg.is_clean());
    assert!(
        v_reg
            .problems
            .iter()
            .any(|p| p.contains("REGRESSION (full T2)"))
    );

    // 2. False accept fails loudly.
    let mut false_accept = ok_rows.clone();
    false_accept[1].native_verdict = SideVerdict::Accept;
    let v_fa = ledger.verify(&false_accept);
    assert!(!v_fa.is_clean());
    assert!(v_fa.problems.iter().any(|p| p.contains("FALSE ACCEPT")));

    // 3. Dropped family below floor fails loudly.
    let dropped = vec![ok_rows[0].clone()];
    let v_drop = ledger.verify(&dropped);
    assert!(!v_drop.is_clean());
    assert!(
        v_drop
            .problems
            .iter()
            .any(|p| p.contains("below declared nonzero floor"))
    );

    // 4. Zero floor in ledger header is refused at parse time.
    let zero_floor = ledger_text.replace("# floor source_ladder 1", "# floor source_ladder 0");
    assert!(T2RatchetLedger::parse(&zero_floor).is_err());
}

#[test]
fn declaration_role_classifier_separates_pin_auxiliaries_from_primary_names() {
    // Pin-generated inductive and matcher auxiliaries must classify as Auxiliary
    // (while still participating strictly in `full_t2_identical`).
    assert_eq!(
        classify_declaration_name(&n("Tree.brecOn.eq")),
        DeclarationRole::Auxiliary(AuxClass::InductiveConstruction)
    );
    assert_eq!(
        classify_declaration_name(&n("Below.below.rec")),
        DeclarationRole::Auxiliary(AuxClass::InductiveConstruction)
    );
    assert_eq!(
        classify_declaration_name(&n("T.below.fn")),
        DeclarationRole::Auxiliary(AuxClass::InductiveConstruction)
    );
    assert_eq!(
        classify_declaration_name(&n("Certified.proof._autoParam")),
        DeclarationRole::Auxiliary(AuxClass::InductiveConstruction)
    );
    assert_eq!(
        classify_declaration_name(&n("priority._sparseCasesOn_1")),
        DeclarationRole::Auxiliary(AuxClass::Matcher)
    );
    assert_eq!(
        classify_declaration_name(&n("classify.match_1")),
        DeclarationRole::Auxiliary(AuxClass::Matcher)
    );
    assert_eq!(
        classify_declaration_name(&n("huge_clash._proof_1")),
        DeclarationRole::Auxiliary(AuxClass::ProofAux)
    );

    // Primary user declarations and top-level parser descriptors stay Primary.
    assert_eq!(
        classify_declaration_name(&n("Tree")),
        DeclarationRole::Primary
    );
    assert_eq!(
        classify_declaration_name(&n("NatBox.mk")),
        DeclarationRole::Primary
    );
    assert_eq!(
        classify_declaration_name(&n("termDbl_")),
        DeclarationRole::Primary
    );
}
