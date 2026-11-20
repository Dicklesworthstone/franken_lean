//! Real sealed `.flnpack` capsule verification tests for `fln-wasm`.
//!
//! Every fixture is a genuine pinned-format `.olean` module sealed into a real
//! `fln.capsule.olean-replay/1` archive (`CartridgeArchiveV1`) — no mocks.
#![forbid(unsafe_code)]

use fln::capsule::{CapsuleLimits, PINNED_EPOCH, SCHEMA_OLEAN_CAPSULE, seal_olean_capsule};
use fln::{
    AxiomVal, BinderInfo, Budget, ConstantInfo, ConstantVal, ContentRoot, DefinitionSafety,
    DefinitionVal, Expr, KVMap, Level, Mode, Name, OLEAN_ACCEPTED_VERSIONS, OLEAN_PIN_COMMIT,
    OLEAN_PIN_TAG, OLEAN_REGION_ALIGN, OleanModuleImport, OleanModuleInput, OleanModuleWriteInput,
    OleanWriteBudget, OleanWriteHeader, Outcome, ReducibilityHints, ReproducibilityProfile,
    TheoremVal, encode_olean_module,
};
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::cartridge::{
    CartridgeBuilderV1, CartridgeObjectKindV1, ObjectPortabilityV1, ObjectRequirementV1,
};
use fln_hash::domain::Digest;
use fln_wasm::{
    CapsuleError, Verdict, VerificationBudget, verify_flnpack_capsule, verify_olean_parts,
};

fn zero_root() -> ContentRoot {
    ContentRoot::new([0u8; 32])
}

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn generic_theorem(name: &str, forged: bool) -> ConstantInfo {
    let binders = [
        (
            n("A"),
            Expr::sort(Level::param(n("u"))),
            BinderInfo::Implicit,
        ),
        (
            n("P"),
            Expr::forall_e(n("x"), b(0), Expr::sort(Level::zero()), BinderInfo::Default),
            BinderInfo::Default,
        ),
        (n("a"), b(1), BinderInfo::Default),
        (n("h"), Expr::app(b(1), b(0)), BinderInfo::Default),
    ];
    let mut type_ = Expr::app(b(2), b(1));
    let mut value = b(u32::from(forged));
    for (binder_name, domain, style) in binders.into_iter().rev() {
        type_ = Expr::forall_e(binder_name.clone(), domain.clone(), type_, style);
        value = Expr::lam(binder_name, domain, value, style);
    }
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![n("u")],
            type_,
        },
        value,
        all: vec![n(name)],
    })
}

fn simple_axiom(name: &str) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: false,
    })
}

/// Concrete ill-typed definition (`def bad : Prop := Prop`, i.e. inferred `Type` vs expected `Prop`)
/// whose head mismatch is decided directly by `fln-checker` as `Rejected`.
fn ill_typed_def(name: &str) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn encode_module(constants: &[ConstantInfo], imports: &[&str], region: u64) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.trim_start_matches('v'),
            githash: OLEAN_PIN_COMMIT,
            base_addr: region * OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("encode olean")
    .bytes
}

fn seal_two_module_capsule() -> Vec<u8> {
    let base_bytes = encode_module(
        &[simple_axiom("Base.P"), generic_theorem("Base.ok", false)],
        &[],
        2,
    );
    let top_bytes = encode_module(&[generic_theorem("Top.ok", false)], &["Base"], 2);
    let base_name = n("Base");
    let top_name = n("Top");
    let inputs = [
        OleanModuleInput {
            name: &base_name,
            artifact: &base_bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &top_name,
            artifact: &top_bytes,
            server_artifact: None,
            private_artifact: None,
        },
    ];
    let limits = CapsuleLimits::new(16 * 1024 * 1024, Budget::for_stack_bytes(2 * 1024 * 1024));
    match seal_olean_capsule(&inputs, &KVMap::new(), PINNED_EPOCH, limits).expect("seal capsule") {
        Outcome::Complete(sealed) => sealed.bytes,
        other => panic!("expected Complete sealed capsule, got {other:?}"),
    }
}

#[test]
fn valid_sealed_multi_module_capsule_is_accepted() {
    let bytes = seal_two_module_capsule();
    let verdict = verify_flnpack_capsule(&bytes, VerificationBudget::default());
    assert_eq!(verdict, Verdict::Accepted { declarations: 3 });
}

#[test]
fn standalone_olean_parts_accept_valid_and_reject_forged() {
    let valid_bytes = encode_module(&[generic_theorem("Solo.ok", false)], &[], 2);
    assert_eq!(
        verify_olean_parts(&[&valid_bytes], VerificationBudget::default()),
        Verdict::Accepted { declarations: 1 }
    );

    let forged_bytes = encode_module(&[ill_typed_def("Solo.forged")], &[], 2);
    assert_eq!(
        verify_olean_parts(&[&forged_bytes], VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Solo.forged"),
            rejection_count: 1,
        }
    );

    // When the checker defers a Bound-vs-Apply conversion mismatch, FL-INV-07
    // requires Inconclusive — never Accepted.
    let deferred_bytes = encode_module(&[generic_theorem("Solo.deferred", true)], &[], 2);
    assert!(matches!(
        verify_olean_parts(&[&deferred_bytes], VerificationBudget::default()),
        Verdict::Inconclusive { .. }
    ));
}

#[test]
fn forged_proof_resealed_into_valid_archive_is_rejected() {
    let forged_bytes = encode_module(&[ill_typed_def("Evil.forged")], &[], 2);
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let decl_id = builder.add_object(
        CartridgeObjectKindV1::Declaration,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        forged_bytes,
    );

    // Craft a syntactically valid semantic profile pointing at the forged module.
    let mut profile = CanonWriter::new();
    profile.schema(SCHEMA_OLEAN_CAPSULE);
    profile.u64(PINNED_EPOCH.get() as u64);
    profile.u64((PINNED_EPOCH.get() >> 64) as u64);
    profile.u8(Mode::Sound.tag());
    profile.u8(ReproducibilityProfile::Standard.tag());
    profile.str(OLEAN_PIN_TAG);
    profile.str(OLEAN_PIN_COMMIT);
    KVMap::new().write_body(&mut profile);
    profile.digest(&Digest([0u8; 32]));
    profile.digest(&Digest([0u8; 32]));
    profile.u64(1);
    n("Evil").write_body(&mut profile);
    profile.digest(&decl_id.digest());
    profile.bool(false);
    profile.digest(&Digest([0u8; 32]));
    profile.digest(&Digest([0u8; 32]));
    profile.u64(1);
    let profile_bytes = profile.into_bytes();

    let receipt_id = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile_bytes,
    );
    builder.add_root_receipt(receipt_id);
    let archive_bytes = builder
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");

    assert_eq!(
        verify_flnpack_capsule(&archive_bytes, VerificationBudget::default()),
        Verdict::Rejected {
            first_rejection: n("Evil.forged"),
            rejection_count: 1,
        }
    );
}

#[test]
fn corrupted_archive_and_legacy_capsule_return_malformed() {
    let mut bytes = seal_two_module_capsule();
    let mid = bytes.len() / 2;
    bytes[mid] ^= 0xFF;
    assert!(matches!(
        verify_flnpack_capsule(&bytes, VerificationBudget::default()),
        Verdict::Malformed(_)
    ));

    // Legacy archive with no semantic receipt must be refused, not accepted.
    let mut legacy = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let obj = legacy.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"legacy-opaque-receipt".to_vec(),
    );
    legacy.add_root_receipt(obj);
    let legacy_bytes = legacy
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");
    assert_eq!(
        verify_flnpack_capsule(&legacy_bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::Truncated)
    );
}

#[test]
fn unsupported_profile_version_returns_unsupported_version() {
    let mut builder = CartridgeBuilderV1::new(PINNED_EPOCH, zero_root());
    let mut profile = CanonWriter::new();
    profile.str(SCHEMA_OLEAN_CAPSULE.name);
    profile.u16(99);
    let receipt_id = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile.into_bytes(),
    );
    builder.add_root_receipt(receipt_id);
    let archive_bytes = builder
        .build()
        .expect("build")
        .to_canonical_bytes()
        .expect("encode");

    assert_eq!(
        verify_flnpack_capsule(&archive_bytes, VerificationBudget::default()),
        Verdict::Malformed(CapsuleError::UnsupportedVersion(99))
    );
}

#[test]
fn tight_budgets_yield_inconclusive_never_accepted_or_rejected() {
    let bytes = seal_two_module_capsule();

    let decl_limited = verify_flnpack_capsule(
        &bytes,
        VerificationBudget {
            max_declarations: 1,
            ..VerificationBudget::default()
        },
    );
    assert!(
        matches!(decl_limited, Verdict::Inconclusive { .. }),
        "expected Inconclusive on declaration limit, got {decl_limited:?}"
    );

    let step_limited = verify_flnpack_capsule(
        &bytes,
        VerificationBudget {
            max_steps: 1,
            ..VerificationBudget::default()
        },
    );
    assert!(
        matches!(step_limited, Verdict::Inconclusive { .. }),
        "expected Inconclusive on step limit, got {step_limited:?}"
    );
}
