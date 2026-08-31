//! **fln-trace** — Palimpsest — always-on structured provenance and the causal
//! proof graph; an observer with read access everywhere and authority nowhere
//! (plan §15).
//!
//! Every declaration, instance selection, simp firing, macro expansion, and
//! kernel verdict is a node in a typed provenance graph with completeness
//! classes. Impact cones, semantic blame, semantic diff, and conflict-aware
//! semantic merge become queries over this graph.
//!
//! Palimpsest never grants environment authority: it records, explains, and
//! advises. The subsystem it observes (Crucible, Athanor, Synod, Anvil,
//! Ledger) owns the decision; Palimpsest owns the evidence.
//!
//! # Subsystems
//!
//! * **ring buffer** — cheap per-declaration event journal, always on (§15.1).
//! * **archive** — opt-in deep trace in frankensqlite (§15.1).
//! * **causal proof graph** — typed provenance DAG (bet B7, §15.1).
//! * **impact cones** — interface, definitional, instance/search, syntax
//!   cones from a single edit (§15.1).
//! * **blame slices** — minimal causal subgraph explaining a failure (§15.3).
//! * **semantic diff** — multi-level diff: source through evidence (§15.3b).
//! * **semantic merge** — graph-based merge with conflict detection (§15.3b).
//! * **fragility signals** — advisory evidence-backed fragility (§15.3c).
//! * **trust cones** — `fln why-trusts` provenance walk (§15.3c).
//! * **replay bundles** — deterministic time-travel and repro packs (§15.4).

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::name::Name;
use fln_core::pos::Position;

// ---------------------------------------------------------------------------
// §15.1 — causal proof graph: node and edge vocabulary
// ---------------------------------------------------------------------------

/// Opaque identifier for a node in the causal proof graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TraceId(pub u64);

/// The kind of a proof-graph node, determining what event it represents.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofGraphNodeKind {
    /// A source range in a file.
    SourceRange {
        file: String,
        start: Position,
        end: Position,
    },
    /// A top-level command (definition, theorem, instance, etc.).
    Command { name: Name },
    /// A syntax/macro expansion event.
    MacroExpansion { macro_name: Name },
    /// A declaration admitted to the environment.
    Declaration { name: Name },
    /// An instance selection event.
    InstanceSelection {
        class: Name,
        instance: Name,
        selected: bool,
    },
    /// A search step (premise retrieval, lemma lookup).
    SearchStep { query: String },
    /// A tactic step in proof construction.
    TacticStep { tactic: Name },
    /// A kernel or checker verdict.
    KernelVerdict { declaration: Name, accepted: bool },
    /// A `simp` rule firing.
    SimpFiring { rule: Name },
    /// A build facet event (from Ledger).
    BuildFacet { target: Name },
    /// A capability session boundary.
    CapabilitySession { session_id: u64 },
}

/// A node in the causal proof graph.
#[derive(Debug, Clone)]
pub struct ProofGraphNode {
    /// Unique identifier.
    pub id: TraceId,
    /// What this node represents.
    pub kind: ProofGraphNodeKind,
    /// Completeness class of this observation.
    pub completeness: CompletenessClass,
    /// Wall-clock timestamp (nanoseconds since epoch).
    pub timestamp_ns: u64,
}

/// How complete the observation behind a proof-graph edge is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompletenessClass {
    /// Every causal input is recorded.
    Complete,
    /// A sound over-approximation of the true dependencies.
    Conservative,
    /// Observed at runtime but not verified against a spec.
    Observed,
    /// An external component whose internals are not visible.
    Opaque,
    /// Inferred from structure rather than direct observation.
    Inferred,
}

// ---------------------------------------------------------------------------
// §15.1 — edge families
// ---------------------------------------------------------------------------

/// The family of a causal edge, determining the semantic relationship.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeFamily {
    // declaration/type dependencies
    Imports,
    ReadsType,
    ReadsValue,
    Unfolds,
    // instance/search
    SelectsInstance,
    RejectsInstance,
    UsesSimpRule,
    UsesCoercion,
    // syntax/macro
    ExpandsFrom,
    GeneratedBy,
    ReadsGrammar,
    WritesGrammar,
    // kernel/checker
    Proves,
    CheckedBy,
    CrossCheckedBy,
    // compiler/runtime
    CompilesTo,
    ExportsSymbol,
    InitializesBefore,
    // build/file
    ReadsFile,
    SpawnsTool,
    LoadsLibrary,
    // invalidation/cache
    Invalidates,
    Reuses,
    // agent/suggestion
    SuggestedBy,
    AcceptedFromSuggestion,
    // migration/repair
    MigratesTo,
    Repairs,
}

/// A directed edge in the causal proof graph.
#[derive(Debug, Clone)]
pub struct ProofGraphEdge {
    /// Source node.
    pub from: TraceId,
    /// Target node.
    pub to: TraceId,
    /// Semantic family of this edge.
    pub family: EdgeFamily,
    /// Completeness class inherited from the producing subsystem.
    pub completeness: CompletenessClass,
}

// ---------------------------------------------------------------------------
// §15.1 — impact cones
// ---------------------------------------------------------------------------

/// The kind of impact cone to compute from an edit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ImpactConeKind {
    /// Only declarations whose interface (type) changes.
    Interface,
    /// Declarations whose definition (body) changes.
    Definitional,
    /// Instance and search results that change.
    InstanceSearch,
    /// Syntax/grammar/macro changes.
    Syntax,
}

/// An impact cone: the set of declarations transitively affected by an edit.
#[derive(Debug, Clone)]
pub struct ImpactCone {
    /// What kind of cone this is.
    pub kind: ImpactConeKind,
    /// The root edit that caused this cone.
    pub root: TraceId,
    /// Affected declaration names, in topological order.
    pub affected: Vec<Name>,
}

// ---------------------------------------------------------------------------
// §15.2 — unification diagnostics
// ---------------------------------------------------------------------------

/// A minimal unification disagreement explaining why two terms do not unify.
#[derive(Debug, Clone)]
pub struct UnificationDisagreement {
    /// Path to the disagreeing subterm in the left-hand side.
    pub lhs_path: Vec<u32>,
    /// Path to the disagreeing subterm in the right-hand side.
    pub rhs_path: Vec<u32>,
    /// Human-readable summary of the transparency/approximation context.
    pub context: String,
}

// ---------------------------------------------------------------------------
// §15.3 — blame slices, why-not trees, fragility
// ---------------------------------------------------------------------------

/// A minimal causal subgraph explaining a failure, instance choice, slow
/// build, or invalidation.
#[derive(Debug, Clone)]
pub struct SemanticBlameSlice {
    /// The node whose behavior is being explained.
    pub target: TraceId,
    /// Nodes in the blame slice, in causal order.
    pub nodes: Vec<ProofGraphNode>,
    /// Edges in the blame slice.
    pub edges: Vec<ProofGraphEdge>,
}

/// A node in a "why not" tree for instance forensics.
#[derive(Debug, Clone)]
pub struct WhyNotNode {
    /// The candidate instance.
    pub instance: Name,
    /// Why it was rejected (or accepted).
    pub reason: String,
    /// Children: sub-candidates explored.
    pub children: Vec<WhyNotNode>,
}

/// Advisory evidence-backed fragility signal per declaration.
#[derive(Debug, Clone)]
pub struct FragilitySignal {
    /// Declaration this signal applies to.
    pub declaration: Name,
    /// Human-readable fragility description.
    pub description: String,
    /// Estimated impact if this declaration changes (number of affected decls).
    pub estimated_impact: u64,
}

// ---------------------------------------------------------------------------
// §15.3b — semantic diff levels
// ---------------------------------------------------------------------------

/// The level at which a semantic diff operates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DiffLevel {
    Source,
    Syntax,
    Interface,
    Proof,
    Reduction,
    Extension,
    Executable,
    Evidence,
}

// ---------------------------------------------------------------------------
// §15.3c — trust cones
// ---------------------------------------------------------------------------

/// A trust cone: the walk of `CHECKED_BY` / `LOADS_LIBRARY` edges for
/// `fln why-trusts`.
#[derive(Debug, Clone)]
pub struct TrustCone {
    /// The declaration being explained.
    pub root: Name,
    /// Nodes in the trust path, from declaration to axioms/imports.
    pub path: Vec<TrustConeEntry>,
}

/// An entry in a trust cone path.
#[derive(Debug, Clone)]
pub struct TrustConeEntry {
    /// The declaration at this point in the chain.
    pub name: Name,
    /// How this declaration was verified.
    pub edge: EdgeFamily,
    /// Completeness of the verification evidence.
    pub completeness: CompletenessClass,
}

// ---------------------------------------------------------------------------
// §15.4 — replay bundles
// ---------------------------------------------------------------------------

/// A deterministic replay / bug-report bundle.
#[derive(Debug, Clone)]
pub struct ReplayBundle {
    /// Content hash of the bundle.
    pub hash: [u8; 32],
    /// The declarations included in this replay.
    pub declarations: Vec<Name>,
    /// Serialized trace events for deterministic replay.
    pub trace_bytes: Vec<u8>,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for TraceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "trace:{}", self.0)
    }
}

impl fmt::Display for CompletenessClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Complete => write!(f, "complete"),
            Self::Conservative => write!(f, "conservative"),
            Self::Observed => write!(f, "observed"),
            Self::Opaque => write!(f, "opaque"),
            Self::Inferred => write!(f, "inferred"),
        }
    }
}

impl fmt::Display for EdgeFamily {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Imports => "IMPORTS",
            Self::ReadsType => "READS_TYPE",
            Self::ReadsValue => "READS_VALUE",
            Self::Unfolds => "UNFOLDS",
            Self::SelectsInstance => "SELECTS_INSTANCE",
            Self::RejectsInstance => "REJECTS_INSTANCE",
            Self::UsesSimpRule => "USES_SIMP_RULE",
            Self::UsesCoercion => "USES_COERCION",
            Self::ExpandsFrom => "EXPANDS_FROM",
            Self::GeneratedBy => "GENERATED_BY",
            Self::ReadsGrammar => "READS_GRAMMAR",
            Self::WritesGrammar => "WRITES_GRAMMAR",
            Self::Proves => "PROVES",
            Self::CheckedBy => "CHECKED_BY",
            Self::CrossCheckedBy => "CROSS_CHECKED_BY",
            Self::CompilesTo => "COMPILES_TO",
            Self::ExportsSymbol => "EXPORTS_SYMBOL",
            Self::InitializesBefore => "INITIALIZES_BEFORE",
            Self::ReadsFile => "READS_FILE",
            Self::SpawnsTool => "SPAWNS_TOOL",
            Self::LoadsLibrary => "LOADS_LIBRARY",
            Self::Invalidates => "INVALIDATES",
            Self::Reuses => "REUSES",
            Self::SuggestedBy => "SUGGESTED_BY",
            Self::AcceptedFromSuggestion => "ACCEPTED_FROM_SUGGESTION",
            Self::MigratesTo => "MIGRATES_TO",
            Self::Repairs => "REPAIRS",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for DiffLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Source => write!(f, "source"),
            Self::Syntax => write!(f, "syntax"),
            Self::Interface => write!(f, "interface"),
            Self::Proof => write!(f, "proof"),
            Self::Reduction => write!(f, "reduction"),
            Self::Extension => write!(f, "extension"),
            Self::Executable => write!(f, "executable"),
            Self::Evidence => write!(f, "evidence"),
        }
    }
}

impl fmt::Display for ImpactConeKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interface => write!(f, "interface"),
            Self::Definitional => write!(f, "definitional"),
            Self::InstanceSearch => write!(f, "instance-search"),
            Self::Syntax => write!(f, "syntax"),
        }
    }
}
