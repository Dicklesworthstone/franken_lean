//! Semantic/telemetry separation — the epic's ninth suite, as a structural rule
//! (bead `fln-euo`; plan §18, §19.2's bundle-facts discipline one layer down).
//!
//! # The law this module exists for
//!
//! **Canonical semantic evidence excludes timestamps, durations, process ids,
//! absolute paths, scheduler facts, allocator facts and performance facts.
//! Those live in bounded telemetry, LINKED to the semantic root and never
//! inside it.** Two runs of the same comparison on different hosts, at
//! different times, under different load, must produce byte-identical semantic
//! roots — or determinism claims (FL-INV-01) become unfalsifiable, because
//! every root difference might be a timestamp and every root agreement might
//! be luck. A leaked host fact does not make evidence wrong; it makes it
//! UNCOMPARABLE, which is worse, because nothing fails.
//!
//! The rule is structural where structure can carry it, in the house style of
//! [`crate::oracle`]:
//!
//! - [`Telemetry::attach`] is the only constructor and takes the
//!   [`SemanticEvidence`] it annotates, so unlinked telemetry is
//!   unrepresentable rather than forbidden.
//! - [`SemanticEvidence::semantic_root`] reads nothing but admitted facts, and
//!   admission is the only way in, so a telemetry-shaped value cannot reach
//!   the root without [`admit`](SemanticEvidence::admit) having named its
//!   class and refused it first.
//! - A parallel execution claim carries its partitions, and
//!   [`validate_execution`] refuses a width the partitions do not productively
//!   fill — a FAKE THREAD LABEL — while an intrinsically serial step presented
//!   as parallel is refused outright, whatever its partitions look like.
//!
//! # Where structure cannot carry it: the detectors, and their declared bounds
//!
//! Whether a STRING smuggles a host fact is not decidable structurally, so
//! admission uses shape detectors, and each one is deliberately conservative
//! and documented at its definition. The failure directions are priced, not
//! assumed away: an under-detection leaks a fact into the root (the defect
//! this module exists for), an over-detection refuses a legitimate semantic
//! value (a wall against correct practice). Every detector therefore has a
//! refusal cell AND an admission cell for its nearest legitimate neighbour in
//! `semantic_telemetry_separation`, and the detector set is extendable —
//! a new class arrives with both cells or it is not a detector, it is a guess.
//!
//! # What this module does NOT do
//!
//! It does not measure anything, schedule anything, or read the tree. It is
//! the vocabulary the rigs above it must speak — the same claim class as its
//! sibling model slices: `bounded_model`, refusing what it is shown.

use fln_hash::domain::{Domain, DomainHasher};
use std::collections::BTreeMap;

/// Domain tag for every digest this module produces.
const TELEMETRY_TAG: &[u8] = b"fln.telemetry/1";

/// The seven telemetry fact classes — a closed vocabulary.
///
/// Closed on purpose: "miscellaneous host fact" is not a class, because a
/// bucket with no membership rule is where the eighth kind of leak would hide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TelemetryClass {
    Timestamp,
    Duration,
    ProcessId,
    AbsolutePath,
    Scheduler,
    Allocator,
    Performance,
}

impl TelemetryClass {
    pub fn as_str(self) -> &'static str {
        match self {
            TelemetryClass::Timestamp => "timestamp",
            TelemetryClass::Duration => "duration",
            TelemetryClass::ProcessId => "process-id",
            TelemetryClass::AbsolutePath => "absolute-path",
            TelemetryClass::Scheduler => "scheduler",
            TelemetryClass::Allocator => "allocator",
            TelemetryClass::Performance => "performance",
        }
    }
}

/// Why an admission or a claim was refused. Every arm names what a caller
/// needs to repair it; none can be built from a success path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeparationError {
    /// A semantic KEY announces a telemetry class by name.
    TelemetryKeyInSemantic { key: String, class: TelemetryClass },
    /// A semantic VALUE carries a telemetry-shaped fragment.
    TelemetryValueInSemantic {
        key: String,
        class: TelemetryClass,
        fragment: String,
    },
    /// Facts must exist: an empty semantic record digests to a constant, and a
    /// constant root reads as agreement between runs that compared nothing.
    EmptySemanticEvidence,
    /// Telemetry is bounded; an envelope over budget is refused, never
    /// truncated — a silently truncated envelope reads as complete.
    TelemetryOverBudget {
        entries: usize,
        bytes: usize,
        max_entries: usize,
        max_bytes: usize,
    },
    /// A parallel claim whose declared width its partitions do not
    /// productively fill: wrong partition count, or an empty partition.
    FakeThreadLabel {
        width: u32,
        partitions: usize,
        empty_partitions: usize,
    },
    /// Partitions must be a partition: exactly the declared inputs, each
    /// exactly once.
    PartitionMismatch { missing: usize, duplicated: usize },
    /// An intrinsically serial step presented as parallel. Order IS its
    /// semantics; relabeling it parallel does not make it safe, it makes the
    /// order claim silently vacuous.
    SerialStepRelabeled { step: String },
}

impl SeparationError {
    pub fn reason(&self) -> &'static str {
        match self {
            SeparationError::TelemetryKeyInSemantic { .. } => "telemetry-key-in-semantic",
            SeparationError::TelemetryValueInSemantic { .. } => "telemetry-value-in-semantic",
            SeparationError::EmptySemanticEvidence => "empty-semantic-evidence",
            SeparationError::TelemetryOverBudget { .. } => "telemetry-over-budget",
            SeparationError::FakeThreadLabel { .. } => "fake-thread-label",
            SeparationError::PartitionMismatch { .. } => "partition-mismatch",
            SeparationError::SerialStepRelabeled { .. } => "serial-step-relabeled",
        }
    }
}

impl std::fmt::Display for SeparationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SeparationError::TelemetryKeyInSemantic { key, class } => {
                write!(
                    f,
                    "semantic key {key:?} names telemetry class {}",
                    class.as_str()
                )
            }
            SeparationError::TelemetryValueInSemantic {
                key,
                class,
                fragment,
            } => write!(
                f,
                "semantic value under {key:?} carries {} fragment {fragment:?}",
                class.as_str()
            ),
            SeparationError::EmptySemanticEvidence => {
                write!(
                    f,
                    "semantic evidence is empty; a constant root is not agreement"
                )
            }
            SeparationError::TelemetryOverBudget {
                entries,
                bytes,
                max_entries,
                max_bytes,
            } => {
                write!(
                    f,
                    "telemetry over budget: {entries} entries / {bytes} bytes \
                     against {max_entries} / {max_bytes}"
                )
            }
            SeparationError::FakeThreadLabel {
                width,
                partitions,
                empty_partitions,
            } => write!(
                f,
                "claimed width {width} with {partitions} partitions of which \
                 {empty_partitions} are empty — a fake thread label"
            ),
            SeparationError::PartitionMismatch {
                missing,
                duplicated,
            } => write!(
                f,
                "partitions are not a partition: {missing} inputs missing, \
                 {duplicated} duplicated"
            ),
            SeparationError::SerialStepRelabeled { step } => {
                write!(f, "intrinsically serial step {step:?} relabeled parallel")
            }
        }
    }
}

impl std::error::Error for SeparationError {}

/// Key-name fragments that announce a telemetry class. Lowercased comparison;
/// each entry earns its place with a refusal cell in the suite.
const KEY_CLASSES: &[(&str, TelemetryClass)] = &[
    ("timestamp", TelemetryClass::Timestamp),
    ("started_at", TelemetryClass::Timestamp),
    ("finished_at", TelemetryClass::Timestamp),
    ("duration", TelemetryClass::Duration),
    ("elapsed", TelemetryClass::Duration),
    ("wall_ms", TelemetryClass::Duration),
    ("pid", TelemetryClass::ProcessId),
    ("tid", TelemetryClass::ProcessId),
    ("thread_id", TelemetryClass::ProcessId),
    ("scheduler", TelemetryClass::Scheduler),
    ("cpu_affinity", TelemetryClass::Scheduler),
    ("nice_level", TelemetryClass::Scheduler),
    ("alloc", TelemetryClass::Allocator),
    ("heap_bytes", TelemetryClass::Allocator),
    ("rss", TelemetryClass::Allocator),
    ("latency", TelemetryClass::Performance),
    ("throughput", TelemetryClass::Performance),
    ("ops_per_sec", TelemetryClass::Performance),
];

/// Classify a semantic KEY. `None` means the key announces no telemetry class.
fn key_class(key: &str) -> Option<TelemetryClass> {
    let lowered = key.to_ascii_lowercase();
    KEY_CLASSES
        .iter()
        .find(|(needle, _)| {
            lowered.split(['.', '_', '-']).any(|part| part == *needle) || lowered == *needle
        })
        .map(|(_, class)| *class)
}

/// Classify a semantic VALUE by shape. Returns the class and the offending
/// fragment, or `None` for a value with no detected host-fact shape.
///
/// The detectors, each with its declared bound:
///
/// - **Absolute path**: a whitespace-delimited token starting `/` with a
///   second `/` in it. Repo-relative paths (`crates/...`) pass, which is the
///   doctrine's own host-independence rule; a bare `/` (division, a lone
///   slash) passes because it carries no host information.
/// - **Timestamp**: an RFC3339-shaped token (`dddd-dd-ddT`), or a FULL value
///   that is one integer of 10+ digits — epoch seconds through nanos. The
///   bound: a genuine semantic count of ten-plus digits is refused too; a rig
///   with a real 10-digit semantic count states it as a named field split
///   from any unit, or this detector is deliberately in its way until a
///   reviewed carve-out exists. Embedded long integers (inside hex digests,
///   ids) do NOT trip it — only a value that IS the integer.
/// - **Duration**: a token that is digits (with optional `.` fraction)
///   followed exactly by `ns`, `us`, `ms`, `s`, `m` or `h`. `sha256s` does
///   not trip it (non-digit prefix); `300ms` does.
fn value_class(value: &str) -> Option<(TelemetryClass, String)> {
    let trimmed = value.trim();
    if !trimmed.is_empty() && trimmed.len() >= 10 && trimmed.bytes().all(|b| b.is_ascii_digit()) {
        return Some((TelemetryClass::Timestamp, trimmed.to_string()));
    }
    for token in value.split_whitespace() {
        if token.len() >= 3 && token.starts_with('/') && token[1..].contains('/') {
            return Some((TelemetryClass::AbsolutePath, token.to_string()));
        }
        let bytes = token.as_bytes();
        if bytes.len() >= 11
            && bytes[..4].iter().all(u8::is_ascii_digit)
            && bytes[4] == b'-'
            && bytes[5..7].iter().all(u8::is_ascii_digit)
            && bytes[7] == b'-'
            && bytes[8..10].iter().all(u8::is_ascii_digit)
            && bytes[10] == b'T'
        {
            return Some((TelemetryClass::Timestamp, token.to_string()));
        }
        for suffix in ["ns", "us", "ms", "s", "m", "h"] {
            if let Some(head) = token.strip_suffix(suffix)
                && !head.is_empty()
                && head.bytes().all(|b| b.is_ascii_digit() || b == b'.')
                && head.bytes().any(|b| b.is_ascii_digit())
            {
                return Some((TelemetryClass::Duration, token.to_string()));
            }
        }
    }
    None
}

/// Canonical semantic evidence: ordered facts, admitted one at a time, with
/// admission as the only path in.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SemanticEvidence {
    facts: BTreeMap<String, String>,
}

impl SemanticEvidence {
    pub fn new() -> SemanticEvidence {
        SemanticEvidence::default()
    }

    /// Admit one fact, or refuse it naming the telemetry class it carries.
    pub fn admit(&mut self, key: &str, value: &str) -> Result<(), SeparationError> {
        if let Some(class) = key_class(key) {
            return Err(SeparationError::TelemetryKeyInSemantic {
                key: key.to_string(),
                class,
            });
        }
        if let Some((class, fragment)) = value_class(value) {
            return Err(SeparationError::TelemetryValueInSemantic {
                key: key.to_string(),
                class,
                fragment,
            });
        }
        self.facts.insert(key.to_string(), value.to_string());
        Ok(())
    }

    pub fn len(&self) -> usize {
        self.facts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// The canonical root: a digest over the sorted admitted facts and nothing
    /// else. Telemetry cannot reach it because telemetry was never admitted.
    pub fn semantic_root(&self) -> Result<String, SeparationError> {
        if self.facts.is_empty() {
            return Err(SeparationError::EmptySemanticEvidence);
        }
        let mut h = DomainHasher::new(Domain::Fixture);
        h.update(TELEMETRY_TAG);
        h.update(&[0]);
        h.update(&(self.facts.len() as u64).to_le_bytes());
        for (k, v) in &self.facts {
            h.update(&(k.len() as u64).to_le_bytes());
            h.update(k.as_bytes());
            h.update(&(v.len() as u64).to_le_bytes());
            h.update(v.as_bytes());
        }
        Ok(h.finalize().to_hex())
    }
}

/// Telemetry budget: bounded is part of the law, not a tuning knob. An
/// envelope big enough to hide arbitrary data in is a side channel.
pub const MAX_TELEMETRY_ENTRIES: usize = 256;
pub const MAX_TELEMETRY_BYTES: usize = 65_536;

/// Host facts, linked to the semantic root they annotate.
///
/// The linkage is by construction: [`Telemetry::attach`] is the only
/// constructor and takes the evidence itself, so there is no way to hold a
/// telemetry envelope that annotates nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Telemetry {
    semantic_root: String,
    entries: Vec<(TelemetryClass, String, String)>,
}

impl Telemetry {
    /// Attach an envelope of host facts to the evidence they describe.
    pub fn attach(
        evidence: &SemanticEvidence,
        entries: Vec<(TelemetryClass, String, String)>,
    ) -> Result<Telemetry, SeparationError> {
        let semantic_root = evidence.semantic_root()?;
        let bytes: usize = entries.iter().map(|(_, k, v)| k.len() + v.len()).sum();
        if entries.len() > MAX_TELEMETRY_ENTRIES || bytes > MAX_TELEMETRY_BYTES {
            return Err(SeparationError::TelemetryOverBudget {
                entries: entries.len(),
                bytes,
                max_entries: MAX_TELEMETRY_ENTRIES,
                max_bytes: MAX_TELEMETRY_BYTES,
            });
        }
        Ok(Telemetry {
            semantic_root,
            entries,
        })
    }

    /// The root this envelope annotates — the link, readable but never
    /// writable.
    pub fn semantic_root(&self) -> &str {
        &self.semantic_root
    }

    pub fn entries(&self) -> &[(TelemetryClass, String, String)] {
        &self.entries
    }
}

/// Whether a step is intrinsically serial, declared by its owner. This is the
/// half validation cannot derive: order-dependence is a semantic property of
/// the step, so it must be stated — and once stated, it cannot be relabeled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepKind {
    IntrinsicallySerial,
    SafelyParallel,
}

/// An execution claim over a fixed semantic input set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecutionClaim {
    /// Ordered, and the ORDER is bound into the root.
    Serial { steps: Vec<String> },
    /// Partitioned across `width` workers; reduction must be a function of
    /// the SET, so the reduction root is order-independent by construction.
    Parallel {
        width: u32,
        partitions: Vec<Vec<String>>,
    },
}

/// Validate an execution claim against the step's declared kind and the fixed
/// input set it must cover.
pub fn validate_execution(
    step: &str,
    kind: StepKind,
    claim: &ExecutionClaim,
    inputs: &[String],
) -> Result<(), SeparationError> {
    match claim {
        ExecutionClaim::Serial { steps } => {
            let mut sorted: Vec<&String> = steps.iter().collect();
            sorted.sort();
            let mut expected: Vec<&String> = inputs.iter().collect();
            expected.sort();
            if sorted != expected {
                let missing = expected.iter().filter(|i| !sorted.contains(i)).count();
                return Err(SeparationError::PartitionMismatch {
                    missing,
                    duplicated: steps.len().saturating_sub(inputs.len()),
                });
            }
            Ok(())
        }
        ExecutionClaim::Parallel { width, partitions } => {
            if kind == StepKind::IntrinsicallySerial {
                return Err(SeparationError::SerialStepRelabeled {
                    step: step.to_string(),
                });
            }
            let empty = partitions.iter().filter(|p| p.is_empty()).count();
            if partitions.len() != *width as usize || empty > 0 {
                return Err(SeparationError::FakeThreadLabel {
                    width: *width,
                    partitions: partitions.len(),
                    empty_partitions: empty,
                });
            }
            let mut all: Vec<&String> = partitions.iter().flatten().collect();
            all.sort();
            let mut expected: Vec<&String> = inputs.iter().collect();
            expected.sort();
            if all != expected {
                let missing = expected.iter().filter(|i| !all.contains(i)).count();
                let duplicated = {
                    let mut d = 0;
                    let mut prev: Option<&&String> = None;
                    for x in &all {
                        if prev == Some(x) {
                            d += 1;
                        }
                        prev = Some(x);
                    }
                    d
                };
                return Err(SeparationError::PartitionMismatch {
                    missing,
                    duplicated,
                });
            }
            Ok(())
        }
    }
}

/// The reduction root of an execution claim.
///
/// Serial binds the ORDER (length-prefixed list digest); parallel binds the
/// SET (sorted union), so any partitioning of the same inputs at any width
/// reduces to the same root — deterministic reduction as a property of the
/// digest rather than a promise of the scheduler.
pub fn reduction_root(claim: &ExecutionClaim) -> String {
    let mut h = DomainHasher::new(Domain::Fixture);
    h.update(TELEMETRY_TAG);
    h.update(&[1]);
    match claim {
        ExecutionClaim::Serial { steps } => {
            h.update(b"serial");
            h.update(&(steps.len() as u64).to_le_bytes());
            for s in steps {
                h.update(&(s.len() as u64).to_le_bytes());
                h.update(s.as_bytes());
            }
        }
        ExecutionClaim::Parallel { partitions, .. } => {
            h.update(b"parallel");
            let mut all: Vec<&str> = partitions.iter().flatten().map(String::as_str).collect();
            all.sort_unstable();
            h.update(&(all.len() as u64).to_le_bytes());
            for s in all {
                h.update(&(s.len() as u64).to_le_bytes());
                h.update(s.as_bytes());
            }
        }
    }
    h.finalize().to_hex()
}
