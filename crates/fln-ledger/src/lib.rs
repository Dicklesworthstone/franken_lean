//! **fln-ledger** — the Ledger — the build fabric: content-addressed
//! declaration records over frankensqlite, the true-cone invalidation law,
//! epochs, and cache federation over atp (plan §13).
//!
//! The environment is a Merkle DAG of content-addressed declarations; builds
//! are memoized queries over it; a one-line leaf edit re-elaborates its true
//! dependency cone (seconds), not its file cone (hours); the cloud cache is
//! native CAS sync over atp (bet B1).
//!
//! # Subsystems
//!
//! * **record store** — content-addressed declaration records with typed
//!   metadata: hash, deps, epoch, mode, options (§13.1).
//! * **demand graph** — generalized build records with read/effect tracking
//!   and determinism classification D0–D4 (§13.1).
//! * **invalidation** — true-dependency-cone invalidation, not file-cone;
//!   published rules per change class (§13.2).
//! * **hermeticity** — H0–H4 hermeticity ladder (§13.3).
//! * **cache federation** — ATP/HHTTPS CAS sync with signature/epoch
//!   validation (§13.4).
//! * **epoch bridging** — conservative record bridging across toolchain
//!   epoch bumps (§13.6).

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::mode::Mode;
use fln_core::name::Name;
use fln_hash::domain::Digest;

// ---------------------------------------------------------------------------
// §13.1 — content-addressed declaration records
// ---------------------------------------------------------------------------

/// A content-addressed declaration record in the Ledger.
///
/// `H(name, statement, body_class, dep_hashes, options, epoch, mode)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LedgerRecord {
    /// Content hash of this record (the CAS key).
    pub hash: Digest,
    /// Fully qualified declaration name.
    pub name: Name,
    /// Hash of the declaration's statement (type).
    pub statement_hash: Digest,
    /// Classification of the body (definition, theorem, opaque, etc.).
    pub body_class: BodyClass,
    /// Content hashes of all declarations this one depends on.
    pub dep_hashes: Vec<Digest>,
    /// Epoch at which this record was created.
    pub epoch: Epoch,
    /// Mode under which this record was produced.
    pub mode: Mode,
}

/// Classification of a declaration body for Ledger retention.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BodyClass {
    /// A definition with a reducible body.
    Definition,
    /// An opaque definition (body not unfolded).
    Opaque,
    /// A theorem (proof-irrelevant body).
    Theorem,
    /// An axiom (no body).
    Axiom,
    /// An inductive type family.
    Inductive,
    /// A constructor of an inductive type.
    Constructor,
    /// A recursor/eliminator.
    Recursor,
    /// A quotient-initialization declaration.
    Quotient,
}

/// A toolchain epoch: a monotonically increasing version tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Epoch(pub u64);

// ---------------------------------------------------------------------------
// §13.1 — demand graph (generalized build records)
// ---------------------------------------------------------------------------

/// A generalized build record in the demand graph.
#[derive(Debug, Clone)]
pub struct DemandNode {
    /// Unique hash of this demand node.
    pub hash: Digest,
    /// What kind of build demand this is.
    pub kind: DemandKind,
    /// Epoch at which this demand was recorded.
    pub epoch: Epoch,
    /// Content hashes of input records.
    pub inputs: Vec<Digest>,
    /// Declared read effects (files, environment queries).
    pub declared_reads: Vec<String>,
    /// Declared write effects (artifacts produced).
    pub declared_effects: Vec<String>,
    /// Determinism classification of this build step.
    pub determinism: DeterminismClass,
}

/// The kind of build demand.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DemandKind {
    /// Elaborate a declaration from source.
    Elaborate,
    /// Check a declaration through the kernel.
    KernelCheck,
    /// Compile a declaration to FLBC.
    Compile,
    /// Generate documentation.
    Document,
    /// Run a user `#eval`.
    Eval,
    /// Build an external library.
    ExternalBuild,
}

/// Determinism classification D0–D4 for build records.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DeterminismClass {
    /// D0: bit-exact determinism.
    BitExact,
    /// D1: semantic determinism (may differ in serialization order).
    Semantic,
    /// D2: deterministic given a fixed schedule.
    ScheduleFixed,
    /// D3: deterministic given a fixed environment.
    EnvironmentFixed,
    /// D4: best-effort (may vary across runs).
    BestEffort,
}

// ---------------------------------------------------------------------------
// §13.2 — invalidation
// ---------------------------------------------------------------------------

/// An invalidation cone: the set of records transitively affected by a change.
#[derive(Debug, Clone)]
pub struct InvalidationCone {
    /// The root record whose change triggered this cone.
    pub root: Digest,
    /// Records in the true dependency cone, in topological order.
    pub affected: Vec<Digest>,
    /// How many records were bypassed (not in the file cone).
    pub bypassed: u64,
}

/// The class of change that triggered invalidation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ChangeClass {
    /// The declaration's type (interface) changed.
    Interface,
    /// The declaration's body changed but its type did not.
    Body,
    /// Only the proof term changed (theorem bodies are proof-irrelevant).
    Proof,
    /// Build options changed.
    Options,
    /// The toolchain epoch changed.
    EpochBump,
}

// ---------------------------------------------------------------------------
// §13.3 — hermeticity ladder
// ---------------------------------------------------------------------------

/// Hermeticity level H0–H4 for builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HermeticityLevel {
    /// H0: no hermeticity guarantee.
    None,
    /// H1: inputs are content-addressed.
    ContentAddressed,
    /// H2: build environment is declared.
    EnvironmentDeclared,
    /// H3: all effects are tracked.
    EffectTracked,
    /// H4: full deterministic reproducibility.
    Reproducible,
}

// ---------------------------------------------------------------------------
// §13.4 — cache federation
// ---------------------------------------------------------------------------

/// A validated CAS cache entry.
#[derive(Debug, Clone)]
pub struct CacheEntry {
    /// Content hash (the CAS key).
    pub hash: Digest,
    /// Epoch at which this entry was produced.
    pub epoch: Epoch,
    /// Whether this entry has been locally verified.
    pub verified: bool,
    /// Size in bytes of the cached artifact.
    pub size_bytes: u64,
}

/// Outcome of a cache sync operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CacheSyncOutcome {
    /// All requested entries are available.
    Complete { fetched: u64, cached: u64 },
    /// Some entries were not available.
    Partial {
        fetched: u64,
        cached: u64,
        missing: u64,
    },
    /// Cache federation is unavailable.
    Unavailable { reason: String },
}

// ---------------------------------------------------------------------------
// §13.6 — epoch bridging
// ---------------------------------------------------------------------------

/// A bridge between records across toolchain epoch bumps.
#[derive(Debug, Clone)]
pub struct EpochBridge {
    /// Source epoch.
    pub from: Epoch,
    /// Target epoch.
    pub to: Epoch,
    /// Records that bridge conservatively (unchanged semantics).
    pub bridged: Vec<Digest>,
    /// Records that require re-elaboration.
    pub invalidated: Vec<Digest>,
}

// ---------------------------------------------------------------------------
// §13 — build explanation
// ---------------------------------------------------------------------------

/// "Why did this rebuild?" explanation.
#[derive(Debug, Clone)]
pub struct BuildExplain {
    /// The target that was rebuilt.
    pub target: Name,
    /// The change class that triggered the rebuild.
    pub cause: ChangeClass,
    /// Records in the causal chain from root change to target.
    pub chain: Vec<Digest>,
    /// Cache outcome for this target.
    pub cache: CacheOutcome,
}

/// Cache outcome for a single build target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CacheOutcome {
    /// Cache hit: no rebuild needed.
    Hit,
    /// Cache miss: rebuild required.
    Miss,
    /// Cache entry exists but is invalid (epoch mismatch, etc.).
    Invalid,
    /// Cache federation unavailable.
    Unavailable,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for Epoch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "epoch:{}", self.0)
    }
}

impl fmt::Display for BodyClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Definition => write!(f, "definition"),
            Self::Opaque => write!(f, "opaque"),
            Self::Theorem => write!(f, "theorem"),
            Self::Axiom => write!(f, "axiom"),
            Self::Inductive => write!(f, "inductive"),
            Self::Constructor => write!(f, "constructor"),
            Self::Recursor => write!(f, "recursor"),
            Self::Quotient => write!(f, "quotient"),
        }
    }
}

impl fmt::Display for DeterminismClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BitExact => write!(f, "D0:bit-exact"),
            Self::Semantic => write!(f, "D1:semantic"),
            Self::ScheduleFixed => write!(f, "D2:schedule-fixed"),
            Self::EnvironmentFixed => write!(f, "D3:environment-fixed"),
            Self::BestEffort => write!(f, "D4:best-effort"),
        }
    }
}

impl fmt::Display for HermeticityLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => write!(f, "H0:none"),
            Self::ContentAddressed => write!(f, "H1:content-addressed"),
            Self::EnvironmentDeclared => write!(f, "H2:environment-declared"),
            Self::EffectTracked => write!(f, "H3:effect-tracked"),
            Self::Reproducible => write!(f, "H4:reproducible"),
        }
    }
}

impl fmt::Display for ChangeClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interface => write!(f, "interface"),
            Self::Body => write!(f, "body"),
            Self::Proof => write!(f, "proof"),
            Self::Options => write!(f, "options"),
            Self::EpochBump => write!(f, "epoch-bump"),
        }
    }
}

impl fmt::Display for CacheOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Hit => write!(f, "hit"),
            Self::Miss => write!(f, "miss"),
            Self::Invalid => write!(f, "invalid"),
            Self::Unavailable => write!(f, "unavailable"),
        }
    }
}

impl fmt::Display for CacheSyncOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Complete { fetched, cached } => {
                write!(f, "complete: {fetched} fetched, {cached} cached")
            }
            Self::Partial {
                fetched,
                cached,
                missing,
            } => write!(f, "partial: {fetched} fetched, {cached} cached, {missing} missing"),
            Self::Unavailable { reason } => write!(f, "unavailable: {reason}"),
        }
    }
}
