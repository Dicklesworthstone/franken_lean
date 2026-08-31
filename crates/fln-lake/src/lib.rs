//! **fln-lake** — the Lake-compatible build surface over the Ledger —
//! `lakefile.lean` on Golem, the `lakefile.toml` fast path, `lean-toolchain`
//! and elan layout compatibility, and `fln build explain` diagnostics
//! (plan §13.3).
//!
//! Lake is a **facade over the Ledger**: targets and facets map onto Ledger
//! queries, `require` fetches via the D2 `git` subprocess protocol,
//! dependency resolution produces transactional resolution receipts, and
//! `lake build --watch` delegates to asupersync's watch infrastructure.
//!
//! The Lake surface must match the Reference pin's exit codes, `--json`
//! output, manifest format, and `lean-toolchain` layout so that `elan`
//! can name a FrankenLean toolchain with zero configuration changes.

#![forbid(unsafe_code)]

use std::fmt;
use std::path::PathBuf;

use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §13.3 — lakefile configuration
// ---------------------------------------------------------------------------

/// A parsed `lakefile.lean` or `lakefile.toml` configuration.
#[derive(Debug, Clone)]
pub struct LakeConfig {
    /// Project name.
    pub name: String,
    /// Default build targets.
    pub default_targets: Vec<String>,
    /// Lean toolchain version constraint from `lean-toolchain`.
    pub lean_toolchain: Option<String>,
    /// Source directory root.
    pub src_dir: PathBuf,
    /// Build output directory.
    pub build_dir: PathBuf,
    /// Package dependencies declared via `require`.
    pub requires: Vec<LakeRequire>,
    /// Configuration format that was parsed.
    pub format: LakeConfigFormat,
}

/// Which configuration format was used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LakeConfigFormat {
    /// `lakefile.lean` — executed on Golem.
    Lean,
    /// `lakefile.toml` — fast declarative path.
    Toml,
}

/// A `require` dependency declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeRequire {
    /// Package name.
    pub name: String,
    /// Git URL (fetched via the D2 `git` subprocess protocol).
    pub url: Option<String>,
    /// Git revision or tag.
    pub rev: Option<String>,
    /// Subdirectory within the repository.
    pub subdir: Option<String>,
}

// ---------------------------------------------------------------------------
// §13.3 — build targets and facets
// ---------------------------------------------------------------------------

/// A build target that maps to a Ledger query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildTarget {
    /// Target name (e.g., library name, executable name).
    pub name: String,
    /// What kind of artifact this target produces.
    pub kind: TargetKind,
    /// Root module for this target.
    pub root: Name,
    /// Source glob patterns.
    pub globs: Vec<String>,
}

/// The kind of build target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetKind {
    /// A Lean library (`.olean` / olean-next artifacts).
    Library,
    /// A Lean executable (`main` entry point compiled to native).
    Executable,
    /// A Lean script (interpreted on Golem).
    Script,
    /// An external library (C/C++ FFI).
    ExternalLibrary,
}

/// A build facet: a secondary product of a build target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuildFacet {
    /// Compiled `.olean` files.
    Olean,
    /// Olean-next format (frontier).
    OleanNext,
    /// Documentation (Folio).
    Doc,
    /// C backend object files (Iron).
    CObject,
    /// Compiled native shared library.
    SharedLib,
}

// ---------------------------------------------------------------------------
// §13.3 — resolution receipts
// ---------------------------------------------------------------------------

/// A transactional dependency resolution receipt.
#[derive(Debug, Clone)]
pub struct ResolutionReceipt {
    /// Resolved packages in dependency order.
    pub packages: Vec<ResolvedPackage>,
    /// Whether the resolution is fully reproducible.
    pub reproducible: bool,
}

/// A resolved package in the dependency graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPackage {
    /// Package name.
    pub name: String,
    /// Resolved version or revision.
    pub version: String,
    /// Local path after fetch.
    pub path: PathBuf,
    /// Git URL that was fetched.
    pub url: Option<String>,
    /// Exact commit hash.
    pub rev: Option<String>,
}

// ---------------------------------------------------------------------------
// §13.3 — build outcomes
// ---------------------------------------------------------------------------

/// Outcome of a `lake build` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildOutcome {
    /// Build succeeded.
    Success {
        /// Number of targets built.
        targets_built: u64,
        /// Number of targets from cache.
        targets_cached: u64,
    },
    /// Build failed.
    Failure {
        /// Name of the first failing target.
        failed_target: String,
        /// Error description.
        error: String,
    },
    /// Build was cancelled.
    Cancelled,
}

/// A build explain entry for `fln build explain <target>`.
#[derive(Debug, Clone)]
pub struct BuildExplainEntry {
    /// Target being explained.
    pub target: String,
    /// What the Reference toolchain would rebuild.
    pub reference_decision: RebuildDecision,
    /// What FrankenLean's Ledger actually rebuilds.
    pub native_decision: RebuildDecision,
    /// Changed input identities (content hashes that differ).
    pub changed_inputs: Vec<String>,
    /// Whether cache was consulted and the outcome.
    pub cache_outcome: String,
}

/// A rebuild decision for build-explain comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RebuildDecision {
    /// Rebuild required (inputs changed).
    Rebuild,
    /// Cached (no inputs changed).
    Cached,
    /// Skipped (not in the dependency cone).
    Skipped,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for LakeConfigFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lean => write!(f, "lakefile.lean"),
            Self::Toml => write!(f, "lakefile.toml"),
        }
    }
}

impl fmt::Display for TargetKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Library => write!(f, "library"),
            Self::Executable => write!(f, "executable"),
            Self::Script => write!(f, "script"),
            Self::ExternalLibrary => write!(f, "external-library"),
        }
    }
}

impl fmt::Display for BuildFacet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Olean => write!(f, "olean"),
            Self::OleanNext => write!(f, "olean-next"),
            Self::Doc => write!(f, "doc"),
            Self::CObject => write!(f, "c-object"),
            Self::SharedLib => write!(f, "shared-lib"),
        }
    }
}

impl fmt::Display for RebuildDecision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rebuild => write!(f, "rebuild"),
            Self::Cached => write!(f, "cached"),
            Self::Skipped => write!(f, "skipped"),
        }
    }
}

impl fmt::Display for BuildOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Success {
                targets_built,
                targets_cached,
            } => write!(f, "success: {targets_built} built, {targets_cached} cached"),
            Self::Failure {
                failed_target,
                error,
            } => write!(f, "failure: {failed_target}: {error}"),
            Self::Cancelled => write!(f, "cancelled"),
        }
    }
}
