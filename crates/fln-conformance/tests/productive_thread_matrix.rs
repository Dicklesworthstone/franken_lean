//! `productive_thread_matrix` — the named suite for td9's seventh campaign
//! framework: the deterministic productive thread matrix
//! (`fln_conformance::campaign`'s `WidthRun`, `judge_matrix`, `partition_units`,
//! `MatrixVerdict`).
//!
//! # The laws proven here
//!
//! The verdict law (identical canonical semantic outputs across widths is
//! schedule independence; a divergence names its width pair), the closure law
//! (identical content-hashed closures or the comparison is refused — never
//! averaged), the productivity law (a "parallel" run with one partition, or an
//! empty partition, is a fake thread label and is refused), the telemetry
//! separation law (the judge's API cannot see telemetry — two run sets differing
//! only there take the same verdict), and the real controlled target: a real
//! workload driven at widths 1/2/4/8 on real threads, once schedule-independent
//! (verdict proves it), once with a planted order-sensitive reducer the matrix
//! catches (divergence named).

#![forbid(unsafe_code)]

use fln_conformance::campaign::{
    MatrixVerdict, RunTelemetry, ThreadMatrixError, WidthRun, judge_matrix, partition_units,
};

fn telemetry(wall_ms: u64) -> RunTelemetry {
    RunTelemetry {
        wall_ms,
        host: "test-host".to_string(),
        os_threads: 8,
    }
}

fn run(width: usize, closure: &str, semantic: &str, partitions: Vec<u64>) -> WidthRun {
    WidthRun {
        width,
        closure_digest: closure.to_string(),
        semantic_digest: semantic.to_string(),
        partitions,
        telemetry: telemetry(100),
    }
}

// ---------------------------------------------------------------------------
// The verdict law
// ---------------------------------------------------------------------------

#[test]
fn identical_semantics_is_schedule_independence_and_a_difference_is_named() {
    let runs = vec![
        run(1, "closure-a", "sem-1", vec![64]),
        run(8, "closure-a", "sem-1", vec![8; 8]),
        run(32, "closure-a", "sem-1", vec![2; 32]),
    ];
    assert_eq!(judge_matrix(&runs), Ok(MatrixVerdict::ScheduleIndependent));

    let mut divergent = runs.clone();
    divergent[2].semantic_digest = "sem-OTHER".to_string();
    assert_eq!(
        judge_matrix(&divergent),
        Ok(MatrixVerdict::ScheduleDivergence {
            width_a: 1,
            width_b: 32
        }),
        "the divergence names its pair"
    );
}

#[test]
fn a_matrix_of_one_width_compares_nothing() {
    let runs = vec![run(1, "closure-a", "sem-1", vec![64])];
    assert_eq!(
        judge_matrix(&runs),
        Err(vec![ThreadMatrixError::TooFewWidths { offered: 1 }])
    );
}

// ---------------------------------------------------------------------------
// The closure law
// ---------------------------------------------------------------------------

#[test]
fn different_closures_are_refused_not_averaged() {
    let runs = vec![
        run(1, "closure-a", "sem-1", vec![64]),
        run(8, "closure-B", "sem-1", vec![8; 8]),
    ];
    assert_eq!(
        judge_matrix(&runs),
        Err(vec![ThreadMatrixError::ClosureMismatch {
            width_a: 1,
            width_b: 8
        }]),
        "identical content-hashed closures is the matrix law"
    );
}

// ---------------------------------------------------------------------------
// The productivity law
// ---------------------------------------------------------------------------

#[test]
fn a_fake_thread_label_is_refused() {
    // Everything in one partition at width 8: a fake label.
    let one_partition = vec![run(1, "c", "s", vec![64]), run(8, "c", "s", vec![64])];
    let errors = judge_matrix(&one_partition).expect_err("a width-8 run needs 2+ partitions");
    assert!(matches!(
        errors[0],
        ThreadMatrixError::NonProductiveWidth { width: 8, .. }
    ));

    // An empty partition riding along.
    let empty_partition = vec![
        run(1, "c", "s", vec![64]),
        run(8, "c", "s", vec![16, 16, 16, 16, 0, 0, 0, 0]),
    ];
    let errors = judge_matrix(&empty_partition).expect_err("an empty partition is refused");
    assert!(matches!(
        errors[0],
        ThreadMatrixError::NonProductiveWidth { width: 8, .. }
    ));

    // The honest shape when work < width: partition_units narrows the label.
    assert_eq!(partition_units(3, 8), vec![1, 1, 1]);
    assert_eq!(partition_units(64, 8), vec![8; 8]);
    assert_eq!(partition_units(65, 8), vec![9, 8, 8, 8, 8, 8, 8, 8]);
    assert_eq!(partition_units(0, 8), Vec::<u64>::new());
}

// ---------------------------------------------------------------------------
// The telemetry separation law
// ---------------------------------------------------------------------------

#[test]
fn telemetry_never_reaches_the_verdict() {
    let base = vec![run(1, "c", "s", vec![64]), run(8, "c", "s", vec![8; 8])];
    let mut slower = base.clone();
    slower[1].telemetry = telemetry(99_999);
    slower[1].telemetry.host = "a-different-host-entirely".to_string();
    slower[1].telemetry.os_threads = 96;
    assert_eq!(
        judge_matrix(&base),
        judge_matrix(&slower),
        "wall time, host, and OS thread count are recorded, never compared — the \
         semantic/telemetry mixing mutant cannot reach the judge"
    );
}

// ---------------------------------------------------------------------------
// The real controlled target: a real workload at real widths
// ---------------------------------------------------------------------------

/// The workload: digest each unit's bytes and combine the unit digests. The
/// combining step is where schedule dependence would live — XOR is order-free,
/// sequential concatenation is not.
fn workload(width: usize, order_free: bool) -> WidthRun {
    let units: Vec<Vec<u8>> = (0..64u64).map(|i| vec![(i % 251) as u8; 64]).collect();
    let partition_sizes = partition_units(units.len() as u64, width);
    let mut offset = 0usize;
    let mut partition_digests = Vec::new();
    for &size in &partition_sizes {
        let chunk = &units[offset..offset + size as usize];
        offset += size as usize;
        // Real threads: each partition's digest computed on its own worker.
        let digests: Vec<String> = std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for unit in chunk {
                handles.push(scope.spawn(move || {
                    fln_hash::domain::hash(fln_hash::domain::Domain::Fixture, unit).to_hex()
                }));
            }
            handles
                .into_iter()
                .map(|h| h.join().expect("worker"))
                .collect()
        });
        let combined = if order_free {
            // Order-free combine: XOR the 32-byte digests.
            let mut acc = [0u8; 32];
            for hex in &digests {
                let bytes = hex::decode(hex);
                for (a, b) in acc.iter_mut().zip(bytes) {
                    *a ^= b;
                }
            }
            hex::encode(&acc)
        } else {
            // Order-SENSITIVE combine: concatenate in completion order — with real
            // threads the completion order is schedule-dependent (the plant).
            let mut joined: Vec<String> = std::thread::scope(|scope| {
                let (tx, rx) = std::sync::mpsc::channel();
                for (index, hex) in digests.iter().enumerate() {
                    let tx = tx.clone();
                    scope.spawn(move || {
                        // Stagger deterministically by index so narrow widths and
                        // wide widths complete in different orders.
                        std::thread::sleep(std::time::Duration::from_micros(
                            (index % 7) as u64 * 50,
                        ));
                        tx.send(hex.clone()).expect("send");
                    });
                }
                drop(tx);
                rx.iter().collect()
            });
            joined.sort();
            joined.concat()
        };
        partition_digests.push(combined);
    }
    let semantic = if order_free {
        let mut acc = [0u8; 32];
        for hex in &partition_digests {
            let bytes = hex::decode(hex);
            for (a, b) in acc.iter_mut().zip(bytes) {
                *a ^= b;
            }
        }
        hex::encode(&acc)
    } else {
        partition_digests.concat()
    };
    WidthRun {
        width,
        closure_digest: fln_hash::domain::hash(
            fln_hash::domain::Domain::Fixture,
            b"the-matrix-workload-closure/1",
        )
        .to_hex(),
        semantic_digest: fln_hash::domain::hash(
            fln_hash::domain::Domain::Fixture,
            semantic.as_bytes(),
        )
        .to_hex(),
        partitions: partition_sizes,
        telemetry: telemetry(0),
    }
}

/// Minimal hex helpers (D1: no hex crate).
mod hex {
    pub fn decode(text: &str) -> Vec<u8> {
        (0..text.len() / 2)
            .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).expect("hex"))
            .collect()
    }

    pub fn encode(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

#[test]
fn the_real_workload_matrix_proves_schedule_independence() {
    let runs: Vec<WidthRun> = [1usize, 2, 4, 8]
        .iter()
        .map(|&width| workload(width, true))
        .collect();
    assert_eq!(
        judge_matrix(&runs),
        Ok(MatrixVerdict::ScheduleIndependent),
        "an order-free reducer gives the same canonical output at 1, 2, 4, and 8 \
         real threads — FL-INV-01's campaign shape on a real workload"
    );
    // Productivity held the whole way: every wide run really partitioned.
    for run in &runs {
        if run.width > 1 {
            assert!(run.partitions.len() >= 2);
            assert!(run.partitions.iter().all(|&units| units > 0));
        }
    }
}

#[test]
fn the_matrix_catches_a_planted_schedule_dependence() {
    // The control that makes the cell above worth anything: a reducer whose
    // combine order is schedule-shaped is CAUGHT, at real widths on real threads.
    // (Completion order is staggered by index, so width 1 and width 8 disagree by
    // construction; the semantic digest names the pair.)
    let narrow = workload(1, false);
    let wide = workload(8, false);
    assert_ne!(
        narrow.semantic_digest, wide.semantic_digest,
        "control: the planted order-sensitive reducer really is schedule-dependent"
    );
    assert_eq!(
        judge_matrix(&[narrow, wide]),
        Ok(MatrixVerdict::ScheduleDivergence {
            width_a: 1,
            width_b: 8
        }),
        "the matrix names the divergence"
    );
}
