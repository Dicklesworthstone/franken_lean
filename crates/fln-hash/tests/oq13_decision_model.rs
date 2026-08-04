//! OQ-13 warm defeq-cache format and attachment-policy decision model.

#![forbid(unsafe_code)]

use fln_core::mode::{ContentRoot, EpochId, Mode};
use fln_core::outcome::Outcome;
use fln_hash::canon::DecodeBudget;
use fln_hash::cartridge::{
    AttachmentRoleV1, CartridgeBuilderV1, CartridgeExtensionV1, CartridgeObjectIdV1,
    CartridgeObjectKindV1, CartridgeRefusalV1, CartridgeRuleV1, DefeqTransparencyV1,
    ObjectPortabilityV1, ObjectRequirementV1, Oq13AttachmentPolicyV1, Oq13FieldV1,
    Oq13ProjectionV1, WarmCacheActionV1, WarmCacheStateV1, WarmDefeqBindingV1, WarmDefeqCacheV1,
    WarmDefeqContextV1, WarmDefeqEntryV1, WarmDefeqQueryV1, oq13_attachment_policy,
    oq13_projection, warm_cache_action,
};
use fln_hash::domain::Digest;

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn binding(receipt: CartridgeObjectIdV1, certificate: CartridgeObjectIdV1) -> WarmDefeqBindingV1 {
    WarmDefeqBindingV1 {
        receipt_object: receipt,
        certificate_object: certificate,
        epoch: EpochId::new(4_032_000),
        mode: Mode::Sound,
        environment_root: root(1),
        kernel_build_root: root(2),
        checker_build_root: root(3),
        policy_root: root(4),
        fuel_profile_root: root(5),
    }
}

fn context() -> WarmDefeqContextV1 {
    WarmDefeqContextV1 {
        epoch: EpochId::new(4_032_000),
        mode: Mode::Sound,
        environment_root: root(1),
        kernel_build_root: root(2),
        checker_build_root: root(3),
        policy_root: root(4),
        fuel_profile_root: root(5),
    }
}

fn entries() -> Vec<WarmDefeqEntryV1> {
    DefeqTransparencyV1::ALL
        .into_iter()
        .enumerate()
        .map(|(index, transparency)| {
            let left = root(10 + index as u8 * 3);
            let right = root(11 + index as u8 * 3);
            let normal = root(12 + index as u8 * 3);
            WarmDefeqEntryV1 {
                query: WarmDefeqQueryV1 {
                    left_term_root: left,
                    right_term_root: right,
                    expected_type_root: Some(root(30 + index as u8)),
                    transparency,
                },
                normal_form_root: normal,
                left_trace: vec![left, normal],
                right_trace: vec![right, normal],
            }
        })
        .collect()
}

#[test]
fn every_oq13_field_has_an_explicit_nondropping_projection() {
    assert_eq!(Oq13FieldV1::ALL.len(), 12);
    for field in Oq13FieldV1::ALL {
        assert!(matches!(
            oq13_projection(field),
            Oq13ProjectionV1::ReceiptAttachedAdvisory
                | Oq13ProjectionV1::ReplayCheckedSemanticField
                | Oq13ProjectionV1::RefuseWithoutRegisteredMapping
        ));
    }
}

#[test]
fn receipt_attachment_policy_is_optional_and_never_authority() {
    assert_eq!(
        oq13_attachment_policy(),
        Oq13AttachmentPolicyV1::OptionalAdvisoryReceiptAttachment
    );
    for state in WarmCacheStateV1::ALL {
        let action = warm_cache_action(state);
        match state {
            WarmCacheStateV1::CurrentAndBound => {
                assert_eq!(action, WarmCacheActionV1::ReplayHints);
            }
            WarmCacheStateV1::InternalFault => {
                assert_eq!(action, WarmCacheActionV1::QuarantineAndVerifyIndependently);
            }
            _ => assert_eq!(action, WarmCacheActionV1::VerifyWithoutCache),
        }
    }
}

#[test]
fn all_transparency_rows_round_trip_with_every_binding_coordinate() {
    let receipt = CartridgeObjectIdV1::new(Digest([40; 32]));
    let certificate = CartridgeObjectIdV1::new(Digest([41; 32]));
    let expected = binding(receipt, certificate);
    let cache = WarmDefeqCacheV1::new(expected.clone(), entries(), Vec::new()).unwrap();
    let bytes = cache.to_canonical_bytes().unwrap();
    let decoded = match WarmDefeqCacheV1::from_canonical_bytes(&bytes) {
        Outcome::Complete(Ok(cache)) => cache,
        other => panic!("decode failed: {other:?}"),
    };
    assert_eq!(decoded, cache);
    assert_eq!(decoded.to_canonical_bytes().unwrap(), bytes);
    assert_eq!(decoded.entries.len(), DefeqTransparencyV1::ALL.len());
    assert_eq!(
        decoded.binding.classify_against(&expected),
        WarmCacheStateV1::CurrentAndBound
    );

    let mut mismatches = Vec::new();
    let mut changed = expected.clone();
    changed.receipt_object = CartridgeObjectIdV1::new(Digest([42; 32]));
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.certificate_object = CartridgeObjectIdV1::new(Digest([43; 32]));
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.epoch = EpochId::new(4_032_001);
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.mode = Mode::Faithful;
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.environment_root = root(6);
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.kernel_build_root = root(7);
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.checker_build_root = root(8);
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.policy_root = root(9);
    mismatches.push(changed);
    let mut changed = expected.clone();
    changed.fuel_profile_root = root(10);
    mismatches.push(changed);
    assert_eq!(mismatches.len(), 9);
    for mismatch in mismatches {
        let state = expected.classify_against(&mismatch);
        assert_eq!(state, WarmCacheStateV1::BindingMismatch);
        assert_eq!(
            warm_cache_action(state),
            WarmCacheActionV1::VerifyWithoutCache
        );
    }
}

#[test]
fn unknown_critical_extension_and_trace_damage_are_refused() {
    let receipt = CartridgeObjectIdV1::new(Digest([40; 32]));
    let certificate = CartridgeObjectIdV1::new(Digest([41; 32]));
    let critical = WarmDefeqCacheV1::new(
        binding(receipt, certificate),
        entries(),
        vec![CartridgeExtensionV1 {
            id: 9,
            critical: true,
            payload: vec![1],
        }],
    );
    assert!(matches!(
        critical,
        Err(CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::UnknownCriticalExtension,
            ..
        })
    ));

    let mut damaged = entries();
    damaged[0].left_trace[0] = root(99);
    assert!(matches!(
        WarmDefeqCacheV1::new(binding(receipt, certificate), damaged, Vec::new()),
        Err(CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::WarmTraceWrongStart,
            ..
        })
    ));
}

#[test]
fn cache_binding_mismatch_refuses_hints_but_not_the_cartridge_transport() {
    let epoch = EpochId::new(4_032_000);
    let environment = root(1);
    let mut builder = CartridgeBuilderV1::new(epoch, environment)
        .with_chunk_size(4)
        .unwrap();
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt".to_vec(),
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"certificate".to_vec(),
    );
    let wrong_receipt = CartridgeObjectIdV1::new(Digest([88; 32]));
    let cache =
        WarmDefeqCacheV1::new(binding(wrong_receipt, certificate), entries(), Vec::new()).unwrap();
    let cache = builder.add_object(
        CartridgeObjectKindV1::WarmDefeqCache,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::EpochBound,
        cache.to_canonical_bytes().unwrap(),
    );
    builder.add_root_receipt(receipt);
    builder.attach(receipt, AttachmentRoleV1::Certificate, certificate);
    builder.attach(receipt, AttachmentRoleV1::WarmDefeqCache, cache);
    let archive = builder
        .build()
        .expect("transport remains structurally valid");
    assert_eq!(
        archive.transport_state(),
        fln_hash::cartridge::CartridgeTransportStateV1::Complete
    );
    let report = archive
        .classify_present_warm_caches(&context(), DecodeBudget::unlimited(), u64::MAX)
        .expect("a stale optional cache does not reject its transport");
    assert_eq!(report.replayable(), 0);
    assert_eq!(report.bypassed(), 1);
    assert_eq!(report.quarantined(), 0);
    assert_eq!(report.decisions[0].state, WarmCacheStateV1::BindingMismatch);
    assert_eq!(
        report.decisions[0].action,
        WarmCacheActionV1::VerifyWithoutCache
    );
}

#[test]
fn warm_cache_can_never_enter_the_required_verification_closure() {
    let mut builder = CartridgeBuilderV1::new(EpochId::new(1), root(1))
        .with_chunk_size(4)
        .unwrap();
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt".to_vec(),
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"certificate".to_vec(),
    );
    let cache =
        WarmDefeqCacheV1::new(binding(receipt, certificate), entries(), Vec::new()).unwrap();
    let cache = builder.add_object(
        CartridgeObjectKindV1::WarmDefeqCache,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        cache.to_canonical_bytes().unwrap(),
    );
    builder.add_root_receipt(receipt);
    builder.attach(receipt, AttachmentRoleV1::Certificate, certificate);
    builder.attach(receipt, AttachmentRoleV1::WarmDefeqCache, cache);
    assert!(matches!(
        builder.build(),
        Err(CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::OptionalOnlyKindDeclaredRequired
                | CartridgeRuleV1::WarmCacheAttachmentRequired,
            ..
        })
    ));
}

#[test]
fn cartridge_module_has_no_kernel_admission_or_verdict_surface() {
    let source = include_str!("../src/cartridge.rs");
    assert!(!source.contains("fln_kernel"));
    assert!(!source.contains("fln_checker"));
    assert!(!source.contains(" Verdict"));
    assert!(
        source.contains("WarmCacheActionV1::VerifyWithoutCache"),
        "the fallback policy must be executable code, not only prose"
    );
}
