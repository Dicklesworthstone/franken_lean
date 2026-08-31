//! **fln-doc** — Folio — `doc-gen4`-surface-compatible documentation as a
//! Ledger build facet: native HTML/PDF, `fmd-math` for `$...$`,
//! `Vellum`-fed syntax highlighting, `franken_networkx` dependency and
//! instance graphs, incremental rendering (plan §16.2).
//!
//! Documents are **receipt-bound**: a rendered page embeds the logical root
//! and receipt links for every checked excerpt; a source change marks the
//! artifact `stale` rather than silently serving outdated content.
//!
//! The document plane uses `franken_markdown` (+ `fmd-font`, `fmd-math`)
//! for native typography and TeX-math layout, and `franken_networkx` for
//! dependency and instance visualization graphs.

#![forbid(unsafe_code)]

use std::fmt;
use std::path::PathBuf;

use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §16.2 — document structure
// ---------------------------------------------------------------------------

/// A documentation page for a single declaration or module.
#[derive(Debug, Clone)]
pub struct DocPage {
    /// Fully qualified name of the documented declaration or module.
    pub name: Name,
    /// What kind of documentation page this is.
    pub kind: DocPageKind,
    /// Logical root hash at the time this page was rendered.
    pub logical_root: [u8; 32],
    /// Whether this page is stale (source changed since render).
    pub stale: bool,
    /// Sections in this page.
    pub sections: Vec<DocSection>,
}

/// The kind of documentation page.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DocPageKind {
    /// Module overview page.
    Module,
    /// Declaration page (definition, theorem, class, etc.).
    Declaration,
    /// Instance listing page.
    InstanceIndex,
    /// Top-level project/package page.
    Package,
}

/// A section within a documentation page.
#[derive(Debug, Clone)]
pub struct DocSection {
    /// Section heading.
    pub heading: String,
    /// Content blocks in this section.
    pub blocks: Vec<DocBlock>,
}

/// A content block in a documentation section.
#[derive(Debug, Clone)]
pub enum DocBlock {
    /// Rendered markdown prose (from docstrings).
    Prose(String),
    /// A syntax-highlighted Lean source excerpt.
    SourceExcerpt {
        /// The source code.
        code: String,
        /// Receipt hash proving this excerpt was kernel-checked.
        receipt: Option<[u8; 32]>,
    },
    /// An inline or display math expression (rendered via `fmd-math`).
    Math {
        /// TeX source.
        tex: String,
        /// Whether this is display math (`$$...$$`) or inline (`$...$`).
        display: bool,
    },
    /// A dependency or instance graph (rendered via `franken_networkx`).
    Graph {
        /// Graph kind.
        kind: DocGraphKind,
        /// Nodes in the graph.
        nodes: Vec<Name>,
    },
    /// A cross-reference link to another declaration.
    CrossRef {
        /// Target declaration.
        target: Name,
        /// Display text.
        label: String,
    },
}

/// The kind of graph embedded in documentation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DocGraphKind {
    /// Import/dependency graph.
    Dependency,
    /// Instance hierarchy graph.
    Instance,
    /// Type class hierarchy graph.
    TypeClass,
}

// ---------------------------------------------------------------------------
// §16.2 — rendering configuration and output
// ---------------------------------------------------------------------------

/// Configuration for document rendering.
#[derive(Debug, Clone)]
pub struct RenderConfig {
    /// Output format.
    pub format: OutputFormat,
    /// Output directory.
    pub output_dir: PathBuf,
    /// Whether to include dependency graphs.
    pub include_graphs: bool,
    /// Whether to include source excerpts.
    pub include_source: bool,
    /// Whether to render only stale pages (incremental mode).
    pub incremental: bool,
}

/// Documentation output format.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OutputFormat {
    /// Native HTML with embedded CSS.
    Html,
    /// Native PDF via `franken_markdown`.
    Pdf,
    /// Both HTML and PDF.
    Both,
}

/// Outcome of a documentation render pass.
#[derive(Debug, Clone)]
pub struct RenderOutcome {
    /// Number of pages rendered.
    pub pages_rendered: u64,
    /// Number of pages skipped (already up-to-date).
    pub pages_skipped: u64,
    /// Number of pages with stale receipts (source changed).
    pub pages_stale: u64,
    /// Output directory.
    pub output_dir: PathBuf,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for DocPageKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Module => write!(f, "module"),
            Self::Declaration => write!(f, "declaration"),
            Self::InstanceIndex => write!(f, "instance-index"),
            Self::Package => write!(f, "package"),
        }
    }
}

impl fmt::Display for OutputFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Html => write!(f, "html"),
            Self::Pdf => write!(f, "pdf"),
            Self::Both => write!(f, "html+pdf"),
        }
    }
}

impl fmt::Display for DocGraphKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Dependency => write!(f, "dependency"),
            Self::Instance => write!(f, "instance"),
            Self::TypeClass => write!(f, "type-class"),
        }
    }
}
