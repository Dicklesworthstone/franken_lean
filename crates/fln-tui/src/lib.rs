//! **fln-tui** — the terminal InfoView (`fln goals`) and Tribunal dashboards
//! over frankentui (plan §16.4).
//!
//! This crate owns the interactive terminal surfaces:
//!
//! - **`fln goals`** — the live proof panel over SSH/tmux, displaying the
//!   current goal state, hypotheses, and tactic suggestions as a TUI.
//! - **Build progress** — incremental build status and resource usage.
//! - **Tribunal dashboards** — differential evidence, conformance matrices,
//!   and census-drift summaries in a navigable terminal view.
//!
//! The TUI framework is `frankentui` from the FrankenSuite. All rendering
//! is bounded: panels have maximum-line budgets and gracefully degrade on
//! small terminals.

#![forbid(unsafe_code)]

use std::fmt;

use fln_core::expr::Expr;
use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §16.4 — goal panel model
// ---------------------------------------------------------------------------

/// A single hypothesis in the local context display.
#[derive(Debug, Clone)]
pub struct HypothesisView {
    /// Hypothesis name.
    pub name: Name,
    /// Pretty-printed type.
    pub ty_text: String,
    /// Pretty-printed value (for `let` bindings).
    pub value_text: Option<String>,
    /// Whether this hypothesis is inaccessible (generated name).
    pub inaccessible: bool,
}

/// A single goal for display in the InfoView panel.
#[derive(Debug, Clone)]
pub struct GoalView {
    /// Goal index (0-based).
    pub index: u32,
    /// User-facing tag (e.g. `case succ`).
    pub tag: Option<String>,
    /// Pretty-printed target type.
    pub target_text: String,
    /// The raw target expression (for hover/inspect).
    pub target: Expr,
    /// Local context hypotheses, in declaration order.
    pub hypotheses: Vec<HypothesisView>,
}

/// The full goals panel state.
#[derive(Debug, Clone)]
pub struct GoalsPanel {
    /// Current declaration or tactic cursor position.
    pub cursor_name: Option<Name>,
    /// Goals at the current position.
    pub goals: Vec<GoalView>,
    /// Whether the goals are provisional (elaboration still running).
    pub provisional: bool,
    /// Number of goals remaining after the displayed set.
    pub remaining: u32,
}

// ---------------------------------------------------------------------------
// §16.4 — build progress model
// ---------------------------------------------------------------------------

/// Build phase for progress display.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuildPhase {
    /// Parsing source files.
    Parse,
    /// Elaborating declarations.
    Elaborate,
    /// Type-checking / kernel verification.
    Check,
    /// Compiling to FLBC.
    Compile,
    /// Executing on Golem.
    Execute,
    /// Writing output artifacts.
    Emit,
}

impl fmt::Display for BuildPhase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let label = match self {
            Self::Parse => "parse",
            Self::Elaborate => "elaborate",
            Self::Check => "check",
            Self::Compile => "compile",
            Self::Execute => "execute",
            Self::Emit => "emit",
        };
        write!(f, "{label}")
    }
}

/// Progress state for a single module in the build.
#[derive(Debug, Clone)]
pub struct ModuleProgress {
    /// Module name.
    pub name: Name,
    /// Current phase.
    pub phase: BuildPhase,
    /// Fraction complete within the current phase (0.0..=1.0).
    pub fraction: f64,
    /// Number of declarations processed so far.
    pub declarations_done: u32,
    /// Total declarations expected (if known).
    pub declarations_total: Option<u32>,
}

/// The overall build progress panel state.
#[derive(Debug, Clone)]
pub struct BuildProgressPanel {
    /// Per-module progress entries.
    pub modules: Vec<ModuleProgress>,
    /// Total elapsed time in milliseconds.
    pub elapsed_ms: u64,
    /// Whether the build is still running.
    pub in_progress: bool,
}

// ---------------------------------------------------------------------------
// §16.4 — Tribunal dashboard model
// ---------------------------------------------------------------------------

/// A single row in the conformance matrix display.
#[derive(Debug, Clone)]
pub struct ConformanceRow {
    /// Surface or subsystem name.
    pub surface: String,
    /// Evidence level (L0-L4).
    pub evidence_level: u8,
    /// Release readiness level (R0-R5).
    pub release_level: u8,
    /// Number of passing conformance tests.
    pub passing: u32,
    /// Number of failing conformance tests.
    pub failing: u32,
    /// Number of tests not yet implemented.
    pub pending: u32,
}

/// Tribunal dashboard state.
#[derive(Debug, Clone)]
pub struct TribunalPanel {
    /// Conformance matrix rows.
    pub rows: Vec<ConformanceRow>,
    /// Last census extraction timestamp (epoch seconds).
    pub census_timestamp: u64,
    /// Whether any surface has a drift alert.
    pub has_drift: bool,
}

// ---------------------------------------------------------------------------
// §16.4 — terminal layout
// ---------------------------------------------------------------------------

/// Terminal dimensions.
#[derive(Debug, Clone, Copy)]
pub struct TerminalSize {
    /// Columns (width).
    pub cols: u16,
    /// Rows (height).
    pub rows: u16,
}

/// Maximum line budget for a panel before it degrades.
#[derive(Debug, Clone, Copy)]
pub struct PanelBudget {
    /// Maximum lines for the goals panel.
    pub goals_lines: u16,
    /// Maximum lines for the build progress panel.
    pub progress_lines: u16,
    /// Maximum lines for the tribunal dashboard.
    pub tribunal_lines: u16,
}

impl Default for PanelBudget {
    fn default() -> Self {
        Self {
            goals_lines: 40,
            progress_lines: 20,
            tribunal_lines: 30,
        }
    }
}
