//! **fln-mcp** — Envoy — the MCP server surface: goal inspection, tactic
//! application against O(1)-forked snapshots, premise search, budgeted `#eval`,
//! certificate retrieval, and Ledger/trace queries (plan §16.3).
//!
//! Envoy is the **agent door**: MCP tools over Lantern's session API, scoped
//! by macaroon-based capability tokens from asupersync. Read tools are `sound`;
//! write-to-file tools are explicit and default-off. Every tool result carries
//! provenance. The server framework is `fastmcp_rust`.
//!
//! Multi-agent orchestration forks branches per agent, assigns disjoint impact
//! regions, accepts patch proposals, re-elaborates + kernel-checks, and emits
//! a mission receipt with a rollback root on deterministic merge.

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::expr::Expr;
use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §16.3 — MCP tool definitions
// ---------------------------------------------------------------------------

/// An MCP tool identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum McpTool {
    /// Inspect the current goal state.
    GoalState,
    /// Apply a tactic to a proof state (against a forked snapshot).
    ApplyTactic,
    /// Search for lemmas via Bloodhound.
    SearchLemmas,
    /// Type-check a term in the current context.
    CheckTerm,
    /// Evaluate an expression on Golem (capability-scoped, budgeted).
    Eval,
    /// Retrieve a kernel certificate for a declaration.
    GetCertificate,
    /// Query the Ledger (build records, invalidation cones).
    LedgerQuery,
    /// Query Palimpsest traces (provenance, blame, impact cones).
    TraceQuery,
}

// ---------------------------------------------------------------------------
// §16.3 — proof state snapshots
// ---------------------------------------------------------------------------

/// A versioned proof-state snapshot for MCP tool interactions.
///
/// Schema-registered and canonically serialized; O(1) fork from a Lantern
/// session handle.
#[derive(Debug, Clone)]
pub struct ProofStateSnapshot {
    /// Unique snapshot identifier.
    pub snapshot_id: u64,
    /// Goals in the current proof state.
    pub goals: Vec<Goal>,
    /// Environment logical root at snapshot time.
    pub env_root: [u8; 32],
    /// Journal position for deterministic replay.
    pub journal_position: u64,
}

/// A single goal in a proof state.
#[derive(Debug, Clone)]
pub struct Goal {
    /// Goal index (0-based).
    pub index: u32,
    /// The goal type (what needs to be proved).
    pub target: Expr,
    /// Local context: hypotheses available.
    pub hypotheses: Vec<Hypothesis>,
    /// User-facing name for this goal (if named).
    pub tag: Option<String>,
}

/// A hypothesis in a goal's local context.
#[derive(Debug, Clone)]
pub struct Hypothesis {
    /// Hypothesis name.
    pub name: Name,
    /// Hypothesis type.
    pub ty: Expr,
    /// Hypothesis value (if a `let` binding).
    pub value: Option<Expr>,
}

// ---------------------------------------------------------------------------
// §16.3 — tool requests and responses
// ---------------------------------------------------------------------------

/// Budget parameters for tool execution.
#[derive(Debug, Clone, Copy)]
pub struct ToolBudget {
    /// Maximum wall-clock time in milliseconds.
    pub wall_ms: u64,
    /// Maximum memory in bytes.
    pub memory_bytes: u64,
    /// Maximum number of heartbeats (reduction steps).
    pub heartbeats: u64,
}

impl Default for ToolBudget {
    fn default() -> Self {
        Self {
            wall_ms: 30_000,
            memory_bytes: 512 * 1024 * 1024,
            heartbeats: 10_000_000,
        }
    }
}

/// A tool request envelope.
#[derive(Debug, Clone)]
pub struct ToolRequest {
    /// Which tool to invoke.
    pub tool: McpTool,
    /// Idempotency key for mutating operations.
    pub idempotency_key: Option<String>,
    /// Budget for this invocation.
    pub budget: ToolBudget,
    /// Snapshot to operate on (if applicable).
    pub snapshot_id: Option<u64>,
}

/// Data grade of a tool response.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DataGrade {
    /// Result is provisional (may change with further elaboration).
    Provisional,
    /// Result is kernel-verified.
    Verified,
}

/// A tool response envelope.
#[derive(Debug, Clone)]
pub struct ToolResponse {
    /// Which tool produced this response.
    pub tool: McpTool,
    /// Data grade of the result.
    pub grade: DataGrade,
    /// Request snapshot ID (if applicable).
    pub snapshot_id: Option<u64>,
    /// Resources consumed.
    pub resources: ResourceFacts,
}

/// Resource consumption facts for a tool invocation.
#[derive(Debug, Clone, Copy)]
pub struct ResourceFacts {
    /// Wall-clock time used (milliseconds).
    pub wall_ms: u64,
    /// Memory high-water mark (bytes).
    pub memory_bytes: u64,
    /// Heartbeats consumed.
    pub heartbeats: u64,
}

// ---------------------------------------------------------------------------
// §16.3 — multi-agent orchestration
// ---------------------------------------------------------------------------

/// A mission receipt from multi-agent orchestration.
#[derive(Debug, Clone)]
pub struct MissionReceipt {
    /// Mission identifier.
    pub mission_id: String,
    /// Agents that participated.
    pub agents: Vec<AgentRecord>,
    /// Merge outcome.
    pub merge: MergeOutcome,
    /// Rollback root (content hash of the pre-mission state).
    pub rollback_root: [u8; 32],
}

/// Record of a single agent's contribution.
#[derive(Debug, Clone)]
pub struct AgentRecord {
    /// Agent identifier.
    pub agent_id: String,
    /// Impact region assigned to this agent.
    pub impact_region: Vec<Name>,
    /// Number of declarations modified.
    pub declarations_modified: u64,
    /// Whether all modifications were kernel-accepted.
    pub all_accepted: bool,
}

/// Outcome of a deterministic merge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MergeOutcome {
    /// Merge succeeded cleanly.
    Success,
    /// Merge has conflicts requiring resolution.
    Conflict { conflicts: Vec<String> },
    /// Merge was rolled back.
    RolledBack { reason: String },
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for McpTool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::GoalState => "goal_state",
            Self::ApplyTactic => "apply_tactic",
            Self::SearchLemmas => "search_lemmas",
            Self::CheckTerm => "check_term",
            Self::Eval => "eval",
            Self::GetCertificate => "get_certificate",
            Self::LedgerQuery => "ledger_query",
            Self::TraceQuery => "trace_query",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for DataGrade {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Provisional => write!(f, "provisional"),
            Self::Verified => write!(f, "verified"),
        }
    }
}

impl fmt::Display for MergeOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Success => write!(f, "success"),
            Self::Conflict { conflicts } => {
                write!(f, "conflict ({} conflicts)", conflicts.len())
            }
            Self::RolledBack { reason } => write!(f, "rolled-back: {reason}"),
        }
    }
}
