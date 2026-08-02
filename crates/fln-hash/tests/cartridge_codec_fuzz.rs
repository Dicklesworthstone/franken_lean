//! Totality, mutation, and budget properties for hostile cartridge bytes.

#![forbid(unsafe_code)]

use fln_core::mode::{ContentRoot, EpochId};
use fln_core::outcome::Outcome;
use fln_hash::canon::{
    DecodeBudget, SCHEMA_CARTRIDGE_ARCHIVE, SCHEMA_CARTRIDGE_MANIFEST, SCHEMA_WARM_DEFEQ_CACHE,
};
use fln_hash::cartridge::{
    AttachmentRoleV1, CartridgeArchiveV1, CartridgeBuilderV1, CartridgeDecodeBudgetsV1,
    CartridgeManifestV1, CartridgeObjectKindV1, CartridgeRefusalV1, ObjectPortabilityV1,
    ObjectRequirementV1, WarmDefeqCacheV1,
};

fn archive() -> CartridgeArchiveV1 {
    let mut builder = CartridgeBuilderV1::new(EpochId::new(4_032_000), ContentRoot::new([1; 32]))
        .with_chunk_size(11)
        .unwrap();
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt-fuzz".to_vec(),
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        (0..83u8).collect::<Vec<_>>(),
    );
    builder.add_root_receipt(receipt);
    builder.attach(receipt, AttachmentRoleV1::Certificate, certificate);
    builder.build().unwrap()
}

fn schema_version_offset(name: &str) -> usize {
    8 + name.len()
}

fn assert_archive_total(bytes: &[u8]) {
    let outcome = CartridgeArchiveV1::from_canonical_bytes_budgeted(
        bytes,
        CartridgeDecodeBudgetsV1 {
            archive: DecodeBudget::new(4096, 4096),
            manifest: DecodeBudget::new(4096, 4096),
        },
    );
    if let Outcome::Complete(Ok(value)) = outcome {
        assert_eq!(
            value
                .to_canonical_bytes()
                .expect("accepted value re-encodes"),
            bytes,
            "acceptance is allowed only for canonical bytes"
        );
    }
}

#[test]
fn every_truncation_and_single_bit_change_is_total_and_canonical_if_accepted() {
    let bytes = archive().to_canonical_bytes().unwrap();
    for end in 0..bytes.len() {
        assert_archive_total(&bytes[..end]);
    }
    for index in 0..bytes.len() {
        for bit in 0..8 {
            let mut changed = bytes.clone();
            changed[index] ^= 1 << bit;
            assert_archive_total(&changed);
        }
    }
}

#[test]
fn deterministic_arbitrary_bytes_are_total_under_independent_budgets() {
    let mut state = 0x7f4a_7c15_d3e2_91b5u64;
    for case in 0..10_000usize {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        let len = (state as usize) % 257;
        let mut bytes = Vec::with_capacity(len);
        for index in 0..len {
            state = state
                .rotate_left(9)
                .wrapping_add(0x9e37_79b9_7f4a_7c15u64 ^ index as u64);
            bytes.push((state >> 24) as u8);
        }
        let budget = DecodeBudget::new(
            1 + ((case * 31) % 512) as u64,
            1 + ((case * 17) % 256) as u64,
        );
        let _ = CartridgeArchiveV1::from_canonical_bytes_budgeted(
            &bytes,
            CartridgeDecodeBudgetsV1 {
                archive: budget,
                manifest: budget,
            },
        );
        let _ = CartridgeManifestV1::from_canonical_bytes_budgeted(&bytes, budget);
        let _ = WarmDefeqCacheV1::from_canonical_bytes_budgeted(&bytes, budget);
    }
}

#[test]
fn every_archive_schema_version_is_classified() {
    let canonical = archive().to_canonical_bytes().unwrap();
    let offset = schema_version_offset(SCHEMA_CARTRIDGE_ARCHIVE.name);
    assert_eq!(
        u16::from_le_bytes([canonical[offset], canonical[offset + 1]]),
        SCHEMA_CARTRIDGE_ARCHIVE.version
    );
    for version in 0..=u16::MAX {
        let mut bytes = canonical.clone();
        bytes[offset..offset + 2].copy_from_slice(&version.to_le_bytes());
        match CartridgeArchiveV1::from_canonical_bytes(&bytes) {
            Outcome::Complete(Ok(_)) => {
                assert_eq!(version, SCHEMA_CARTRIDGE_ARCHIVE.version);
            }
            Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion { schema, seen })) => {
                assert_ne!(version, SCHEMA_CARTRIDGE_ARCHIVE.version);
                assert_eq!(schema, SCHEMA_CARTRIDGE_ARCHIVE.name);
                assert_eq!(seen, version);
            }
            other => panic!("version {version} was not classified exactly: {other:?}"),
        }
    }
}

#[test]
fn nested_manifest_and_warm_cache_unknown_versions_are_typed_refusals() {
    let archive = archive();
    let mut manifest = archive.manifest.to_canonical_bytes().unwrap();
    let manifest_offset = schema_version_offset(SCHEMA_CARTRIDGE_MANIFEST.name);
    manifest[manifest_offset..manifest_offset + 2].copy_from_slice(&2u16.to_le_bytes());
    assert!(matches!(
        CartridgeManifestV1::from_canonical_bytes(&manifest),
        Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion {
            schema,
            seen: 2,
        })) if schema == SCHEMA_CARTRIDGE_MANIFEST.name
    ));

    let mut warm_header = Vec::new();
    warm_header.extend_from_slice(&(SCHEMA_WARM_DEFEQ_CACHE.name.len() as u64).to_le_bytes());
    warm_header.extend_from_slice(SCHEMA_WARM_DEFEQ_CACHE.name.as_bytes());
    warm_header.extend_from_slice(&2u16.to_le_bytes());
    assert!(matches!(
        WarmDefeqCacheV1::from_canonical_bytes(&warm_header),
        Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion {
            schema,
            seen: 2,
        })) if schema == SCHEMA_WARM_DEFEQ_CACHE.name
    ));
}

#[test]
fn input_and_produced_node_stops_are_inconclusive_not_malformed() {
    let archive = archive();
    let bytes = archive.to_canonical_bytes().unwrap();
    let input_stop = CartridgeArchiveV1::from_canonical_bytes_budgeted(
        &bytes,
        CartridgeDecodeBudgetsV1 {
            archive: DecodeBudget::new((bytes.len() - 1) as u64, u64::MAX),
            manifest: DecodeBudget::unlimited(),
        },
    );
    assert!(matches!(input_stop, Outcome::Inconclusive(_)));

    let manifest = archive.manifest.to_canonical_bytes().unwrap();
    let node_stop = CartridgeManifestV1::from_canonical_bytes_budgeted(
        &manifest,
        DecodeBudget::new(u64::MAX, 1),
    );
    assert!(matches!(node_stop, Outcome::Inconclusive(_)));
}

#[test]
fn malformed_prefix_before_a_budget_boundary_is_a_completed_refusal() {
    let mut bytes = archive().to_canonical_bytes().unwrap();
    bytes[..8].copy_from_slice(&0_u64.to_le_bytes());
    assert!(matches!(
        CartridgeArchiveV1::from_canonical_bytes_budgeted(
            &bytes,
            CartridgeDecodeBudgetsV1 {
                archive: DecodeBudget::new(8, 0),
                manifest: DecodeBudget::new(0, 0),
            },
        ),
        Outcome::Complete(Err(_))
    ));
}
