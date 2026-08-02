//! Cartridge manifest, staging, random-access, and portability model.

#![forbid(unsafe_code)]

use fln_core::mode::{ContentRoot, EpochId, Mode};
use fln_core::outcome::Outcome;
use fln_hash::canon::DecodeBudget;
use fln_hash::cartridge::{
    AttachmentRoleV1, CartridgeArchiveV1, CartridgeBuilderV1, CartridgeDecodeBudgetsV1,
    CartridgeFrameV1, CartridgeIndexV1, CartridgeObjectKindV1, CartridgeRefusalV1, CartridgeRuleV1,
    CartridgeStagerV1, CartridgeTransportStateV1, DefeqTransparencyV1, ObjectPortabilityV1,
    ObjectRequirementV1, WarmDefeqBindingV1, WarmDefeqCacheV1, WarmDefeqEntryV1, WarmDefeqQueryV1,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn full_archive() -> CartridgeArchiveV1 {
    let epoch = EpochId::new(4_032_000);
    let environment_root = root(1);
    let mut builder = CartridgeBuilderV1::new(epoch, environment_root)
        .with_chunk_size(5)
        .expect("nonzero chunk size");

    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt-v1".to_vec(),
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"certificate-v1".to_vec(),
    );
    let dependency = builder.add_object(
        CartridgeObjectKindV1::Dependency,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"dependency-v1".to_vec(),
    );
    let fixture = builder.add_object(
        CartridgeObjectKindV1::Fixture,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::Portable,
        b"fixture-v1".to_vec(),
    );
    let schema = builder.add_object(
        CartridgeObjectKindV1::Schema,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::Portable,
        b"schema-v1".to_vec(),
    );
    let resource_contract = builder.add_object(
        CartridgeObjectKindV1::ResourceContract,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::Portable,
        b"resource-contract-v1".to_vec(),
    );
    let witness = builder.add_object(
        CartridgeObjectKindV1::Witness,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::Portable,
        b"witness-v1".to_vec(),
    );
    let cache = WarmDefeqCacheV1::new(
        WarmDefeqBindingV1 {
            receipt_object: receipt,
            certificate_object: certificate,
            epoch,
            mode: Mode::Sound,
            environment_root,
            kernel_build_root: root(2),
            checker_build_root: root(3),
            policy_root: root(4),
            fuel_profile_root: root(5),
        },
        vec![WarmDefeqEntryV1 {
            query: WarmDefeqQueryV1 {
                left_term_root: root(10),
                right_term_root: root(11),
                expected_type_root: Some(root(12)),
                transparency: DefeqTransparencyV1::Semireducible,
            },
            normal_form_root: root(13),
            left_trace: vec![root(10), root(13)],
            right_trace: vec![root(11), root(13)],
        }],
        Vec::new(),
    )
    .expect("warm cache");
    let cache = builder.add_object(
        CartridgeObjectKindV1::WarmDefeqCache,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::EpochBound,
        cache.to_canonical_bytes().expect("warm bytes"),
    );

    builder.add_root_receipt(receipt);
    for (role, object) in [
        (AttachmentRoleV1::Certificate, certificate),
        (AttachmentRoleV1::Dependency, dependency),
        (AttachmentRoleV1::Fixture, fixture),
        (AttachmentRoleV1::Schema, schema),
        (AttachmentRoleV1::ResourceContract, resource_contract),
        (AttachmentRoleV1::Witness, witness),
        (AttachmentRoleV1::WarmDefeqCache, cache),
    ] {
        builder.attach(receipt, role, object);
    }
    builder.build().expect("complete archive")
}

fn complete<T: std::fmt::Debug>(outcome: Outcome<Result<T, CartridgeRefusalV1>>) -> T {
    match outcome {
        Outcome::Complete(Ok(value)) => value,
        other => panic!("expected completed cartridge value, got {other:?}"),
    }
}

#[test]
fn thin_partial_sealed_and_complete_share_one_manifest_identity() {
    let complete_archive = full_archive();
    assert_eq!(
        complete_archive.transport_state(),
        CartridgeTransportStateV1::Complete
    );
    let root = complete_archive.manifest_root().expect("manifest root");

    let thin = CartridgeArchiveV1::thin(complete_archive.manifest.clone()).expect("thin");
    assert_eq!(thin.transport_state(), CartridgeTransportStateV1::Thin);
    assert_eq!(thin.manifest_root().expect("thin root"), root);

    let required = complete_archive.manifest.required_chunk_ids();
    let mut partial_frames = Vec::new();
    let mut optional_frames = Vec::new();
    for frame in &complete_archive.frames {
        if required.contains(&frame.id) {
            partial_frames.push(frame.clone());
        } else {
            optional_frames.push(frame.clone());
        }
    }
    partial_frames.pop();
    let partial =
        CartridgeArchiveV1::new(complete_archive.manifest.clone(), partial_frames.clone())
            .expect("valid partial archive");
    assert!(matches!(
        partial.transport_state(),
        CartridgeTransportStateV1::Partial { .. }
    ));
    assert_eq!(partial.manifest_root().expect("partial root"), root);

    for frame in &complete_archive.frames {
        if required.contains(&frame.id) && !partial_frames.iter().any(|item| item.id == frame.id) {
            partial_frames.push(frame.clone());
        }
    }
    partial_frames.sort_by_key(|frame| frame.id);
    let sealed =
        CartridgeArchiveV1::new(complete_archive.manifest.clone(), partial_frames).expect("sealed");
    if optional_frames.is_empty() {
        assert_eq!(
            sealed.transport_state(),
            CartridgeTransportStateV1::Complete
        );
    } else {
        assert!(matches!(
            sealed.transport_state(),
            CartridgeTransportStateV1::Sealed { .. }
        ));
    }
    assert_eq!(sealed.manifest_root().expect("sealed root"), root);
    assert_eq!(complete_archive.manifest_root().expect("full root"), root);
}

#[test]
fn canonical_archive_round_trip_and_derived_random_access_are_exact() {
    let archive = full_archive();
    let bytes = archive.to_canonical_bytes().expect("archive bytes");
    let decoded = complete(CartridgeArchiveV1::from_canonical_bytes(&bytes));
    assert_eq!(decoded, archive);
    assert_eq!(
        decoded.to_canonical_bytes().expect("re-encode"),
        bytes,
        "canonical re-encoding must be byte exact"
    );

    let index = complete(CartridgeIndexV1::from_canonical_bytes(
        &bytes,
        CartridgeDecodeBudgetsV1::unlimited(),
    ));
    assert_eq!(index.manifest_root, archive.manifest_root().unwrap());
    assert_eq!(index.chunks.len(), archive.frames.len());
    for frame in &archive.frames {
        assert_eq!(
            index.read_chunk(&bytes, frame.id).expect("indexed chunk"),
            frame.bytes
        );
    }
}

#[test]
fn staging_is_failure_atomic_and_recovers_exactly() {
    let archive = full_archive();
    let mut stager = CartridgeStagerV1::new(archive.manifest.clone()).expect("stager");
    let first = archive.frames.first().expect("frames").clone();
    let mut corrupt = first.clone();
    corrupt.bytes.push(0xff);
    let refusal = stager.stage(corrupt).expect_err("wrong frame bytes");
    assert!(matches!(
        refusal,
        CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::FrameLengthMismatch | CartridgeRuleV1::FrameDigestMismatch,
            ..
        }
    ));
    assert_eq!(
        stager.staged_frames(),
        0,
        "a rejected frame cannot mutate staging state"
    );

    stager.stage(first.clone()).expect("pristine frame");
    assert!(matches!(
        stager.stage(first),
        Err(CartridgeRefusalV1::DuplicateFrame { .. })
    ));
    assert_eq!(stager.staged_frames(), 1);
    for frame in archive.frames.iter().skip(1) {
        stager.stage(frame.clone()).expect("remaining frame");
    }
    let recovered = stager.finalize_sealed().expect("sealed recovery");
    assert_eq!(
        recovered.to_canonical_bytes().unwrap(),
        archive.to_canonical_bytes().unwrap()
    );
}

#[test]
fn nested_warm_cache_binding_is_validated_without_becoming_required() {
    let archive = full_archive();
    let report =
        complete(archive.validate_present_warm_caches(DecodeBudget::new(u64::MAX, u64::MAX)));
    assert_eq!(report.validated, 1);
    assert_eq!(report.missing, 0);

    let required = archive.manifest.required_chunk_ids();
    let sealed_frames: Vec<_> = archive
        .frames
        .iter()
        .filter(|frame| required.contains(&frame.id))
        .cloned()
        .collect();
    let sealed =
        CartridgeArchiveV1::new(archive.manifest.clone(), sealed_frames).expect("sealed archive");
    let report =
        complete(sealed.validate_present_warm_caches(DecodeBudget::new(u64::MAX, u64::MAX)));
    assert_eq!(report.validated, 0);
    assert_eq!(report.missing, 1);
}

#[test]
fn portability_is_explicit_and_epoch_or_target_mismatch_refuses() {
    let archive = full_archive();
    archive
        .manifest
        .portable_to(EpochId::new(4_032_000), "x86_64-unknown-linux-gnu")
        .expect("epoch-bound but platform-neutral archive");
    assert!(matches!(
        archive
            .manifest
            .portable_to(EpochId::new(4_033_000), "x86_64-unknown-linux-gnu"),
        Err(CartridgeRefusalV1::PortabilityMismatch { .. })
    ));

    let mut manifest = archive.manifest.clone();
    let fixture = manifest
        .objects
        .iter_mut()
        .find(|object| object.kind == CartridgeObjectKindV1::Fixture)
        .expect("fixture row");
    fixture.portability = ObjectPortabilityV1::PlatformBound {
        target: "x86_64-unknown-linux-gnu".to_string(),
    };
    manifest
        .portable_to(EpochId::new(4_032_000), "x86_64-unknown-linux-gnu")
        .expect("matching platform");
    assert!(matches!(
        manifest.portable_to(EpochId::new(4_032_000), "aarch64-apple-darwin"),
        Err(CartridgeRefusalV1::PortabilityMismatch { .. })
    ));
}

#[test]
fn reordered_frames_and_undeclared_frames_are_refused() {
    let archive = full_archive();
    let mut reversed = archive.frames.clone();
    reversed.reverse();
    assert!(matches!(
        CartridgeArchiveV1::new(archive.manifest.clone(), reversed),
        Err(CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::FramesNotStrictlySorted,
            ..
        })
    ));

    let foreign = CartridgeFrameV1::new(b"undeclared".to_vec());
    assert!(matches!(
        CartridgeArchiveV1::new(archive.manifest, vec![foreign]),
        Err(CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::FrameUndeclared,
            ..
        })
    ));
}
