//! Streaming-boundary and productive schedule-equivalence properties.

#![forbid(unsafe_code)]

use std::thread;

use fln_core::mode::{ContentRoot, EpochId};
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_hash::cartridge::{
    AttachmentRoleV1, CartridgeArchiveV1, CartridgeBuilderV1, CartridgeDecodeBudgetsV1,
    CartridgeObjectKindV1, CartridgeStreamDecoderV1, ObjectPortabilityV1, ObjectRequirementV1,
};

fn archive() -> CartridgeArchiveV1 {
    let mut builder = CartridgeBuilderV1::new(EpochId::new(4_032_000), ContentRoot::new([1; 32]))
        .with_chunk_size(7)
        .expect("chunk size");
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        b"receipt-stream".to_vec(),
    );
    let certificate = builder.add_object(
        CartridgeObjectKindV1::Certificate,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        (0..97u8).collect::<Vec<_>>(),
    );
    let witness = builder.add_object(
        CartridgeObjectKindV1::Witness,
        ObjectRequirementV1::Optional,
        ObjectPortabilityV1::Portable,
        b"optional witness".to_vec(),
    );
    builder.add_root_receipt(receipt);
    builder.attach(receipt, AttachmentRoleV1::Certificate, certificate);
    builder.attach(receipt, AttachmentRoleV1::Witness, witness);
    builder.build().expect("archive")
}

fn finish(decoder: CartridgeStreamDecoderV1) -> CartridgeArchiveV1 {
    match decoder.finish(CartridgeDecodeBudgetsV1::unlimited()) {
        Outcome::Complete(Ok(value)) => value,
        other => panic!("stream did not complete: {other:?}"),
    }
}

#[test]
fn every_two_piece_boundary_decodes_to_the_same_archive() {
    let expected = archive();
    let bytes = expected.to_canonical_bytes().expect("bytes");
    for split in 0..=bytes.len() {
        let mut decoder = CartridgeStreamDecoderV1::new(bytes.len() as u64);
        assert!(matches!(
            decoder.push(&bytes[..split]),
            Outcome::Complete(Ok(()))
        ));
        assert!(matches!(
            decoder.push(&bytes[split..]),
            Outcome::Complete(Ok(()))
        ));
        assert_eq!(finish(decoder), expected, "split at byte {split}");
    }
}

#[test]
fn one_byte_streaming_and_empty_chunks_are_total() {
    let expected = archive();
    let bytes = expected.to_canonical_bytes().expect("bytes");
    let mut decoder = CartridgeStreamDecoderV1::new(bytes.len() as u64);
    for byte in &bytes {
        assert!(matches!(
            decoder.push(std::slice::from_ref(byte)),
            Outcome::Complete(Ok(()))
        ));
    }
    assert_eq!(finish(decoder), expected);

    let mut empty = CartridgeStreamDecoderV1::new(bytes.len() as u64);
    assert!(matches!(empty.push(&[]), Outcome::Complete(Ok(()))));
    assert!(matches!(empty.push(&bytes), Outcome::Complete(Ok(()))));
    assert_eq!(finish(empty), expected);
}

#[test]
fn memory_stop_and_cancellation_publish_no_partial_archive() {
    let bytes = archive().to_canonical_bytes().expect("bytes");
    let mut limited = CartridgeStreamDecoderV1::new((bytes.len() - 1) as u64);
    let before = limited.buffered_bytes();
    let outcome = limited.push(&bytes);
    assert!(matches!(
        outcome,
        Outcome::Inconclusive(ref stop)
            if matches!(
                stop.cause,
                InconclusiveCause::ResourceExhausted { .. }
            )
    ));
    assert_eq!(
        limited.buffered_bytes(),
        before,
        "a resource refusal must be failure-atomic"
    );

    let mut cancelled = CartridgeStreamDecoderV1::new(bytes.len() as u64);
    cancelled.cancel();
    assert!(matches!(
        cancelled.push(&bytes),
        Outcome::Inconclusive(ref stop)
            if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
    ));
    assert!(matches!(
        cancelled.finish(CartridgeDecodeBudgetsV1::unlimited()),
        Outcome::Inconclusive(ref stop)
            if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
    ));
}

#[test]
fn productive_1_8_32_stream_schedules_are_byte_and_semantic_identical() {
    let expected = archive();
    let bytes = expected.to_canonical_bytes().expect("bytes");
    for width in [1usize, 8, 32] {
        let mut workers = Vec::new();
        for worker in 0..width {
            let bytes = bytes.clone();
            workers.push(thread::spawn(move || {
                let stride = 1 + ((worker * 17 + width) % 31);
                let mut decoder = CartridgeStreamDecoderV1::new(bytes.len() as u64);
                for chunk in bytes.chunks(stride) {
                    assert!(matches!(decoder.push(chunk), Outcome::Complete(Ok(()))));
                }
                let archive = finish(decoder);
                (
                    archive.manifest_root().expect("root"),
                    archive.to_canonical_bytes().expect("bytes"),
                    archive.frames.len(),
                )
            }));
        }
        let rows: Vec<_> = workers
            .into_iter()
            .map(|worker| worker.join().expect("worker"))
            .collect();
        assert_eq!(rows.len(), width, "productive worker count");
        for row in rows {
            assert_eq!(row.0, expected.manifest_root().unwrap());
            assert_eq!(row.1, bytes);
            assert!(row.2 > 0, "productive frame count");
        }
    }
}
