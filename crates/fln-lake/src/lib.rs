//! **fln-lake** — the Lake-compatible build surface over the Ledger —
//! `lakefile.lean` on Golem, the `lakefile.toml` fast path, `lean-toolchain`
//! and elan layout compatibility, and `fln build explain` diagnostics
//! (plan §13.3).
//!
//! Configuration and package operations are implemented here. Artifact
//! compilation and provenance-backed build decisions are not yet connected;
//! their entry points return explicit errors rather than synthetic products
//! or cache hits. Executable Lean configuration is likewise unavailable.
//!
//! The Lake surface must match the Reference pin's exit codes, `--json`
//! output, manifest format, and `lean-toolchain` layout so that `elan`
//! can name a FrankenLean toolchain with zero configuration changes.

#![forbid(unsafe_code)]

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §13.3 — lakefile configuration
// ---------------------------------------------------------------------------

/// A parsed `lakefile.lean` or `lakefile.toml` configuration.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Declared `lean_lib` and `lean_exe` targets, in declaration order.
    pub targets: Vec<LakeTarget>,
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
    /// Local package directory, relative to the declaring package.
    pub path: Option<PathBuf>,
    /// Git URL (fetched via the D2 `git` subprocess protocol).
    pub url: Option<String>,
    /// Git revision or tag.
    pub rev: Option<String>,
    /// Subdirectory within the repository.
    pub subdir: Option<String>,
}

/// One `lean_lib` / `lean_exe` target declared in `lakefile.toml`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeTarget {
    /// Target name as written in the configuration.
    pub name: String,
    /// `Library` for `lean_lib`, `Executable` for `lean_exe`.
    pub kind: TargetKind,
    /// Dotted root module names. A `lean_exe` has exactly one.
    pub roots: Vec<String>,
    /// Per-target source directory, relative to the package source directory.
    pub src_dir: Option<PathBuf>,
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

// ---------------------------------------------------------------------------
// §13.3 — errors and operations
// ---------------------------------------------------------------------------

/// Pinned default Lean toolchain string.
pub const DEFAULT_PIN_TAG: &str = "v4.32.0";

/// An error encountered while parsing a `lakefile.toml`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LakeParseError {
    /// A required field is missing.
    MissingField(&'static str),
    /// A syntax error occurred on a specific line.
    InvalidSyntax(String),
    /// A build-affecting setting has no native implementation yet.
    UnsupportedBuildSetting(String),
}

impl fmt::Display for LakeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingField(field) => {
                write!(f, "missing required field '{field}' in lakefile.toml")
            }
            Self::InvalidSyntax(msg) => write!(f, "syntax error in lakefile.toml: {msg}"),
            Self::UnsupportedBuildSetting(setting) => {
                write!(f, "native Lake build setting is unavailable: {setting}")
            }
        }
    }
}

impl std::error::Error for LakeParseError {}

/// An error encountered while discovering Lake configuration in a directory.
#[derive(Debug)]
pub enum LakeDiscoveryError {
    /// No configuration file (`lakefile.toml` or `lakefile.lean`) was found.
    NotFound(PathBuf),
    /// An I/O error occurred reading the configuration file.
    Io(io::Error),
    /// A parsing error occurred.
    Parse(LakeParseError),
    /// Only `lakefile.lean` exists. Evaluating it requires running Lean code on
    /// Golem, which is not implemented, so its targets are unknown.
    LeanConfigUnsupported(PathBuf),
}

impl fmt::Display for LakeDiscoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(p) => write!(f, "no Lake configuration found in '{}'", p.display()),
            Self::Io(e) => write!(f, "I/O error discovering Lake configuration: {e}"),
            Self::Parse(e) => write!(f, "error parsing Lake configuration: {e}"),
            Self::LeanConfigUnsupported(p) => write!(
                f,
                "executable Lake configuration is unavailable: {} requires evaluating Lean code, \
                 which is not implemented; use the supported lakefile.toml subset",
                p.display()
            ),
        }
    }
}

impl std::error::Error for LakeDiscoveryError {}

/// An error encountered while cleaning Lake build outputs.
#[derive(Debug)]
pub enum LakeCleanError {
    /// Neither `lakefile.toml` nor `lakefile.lean` was found in the package root.
    NoConfigFile(PathBuf),
    /// An I/O error occurred during removal of build outputs.
    Io(String),
    /// The configuration is a `lakefile.lean`, which is not evaluated, so the
    /// package's build directory is not known. Nothing was removed.
    BuildDirUnknown(PathBuf),
    /// The configured `buildDir` is absolute, empty, or leaves the package.
    /// Nothing was removed.
    BuildDirOutsidePackage(PathBuf),
    /// The configuration could not be read.
    Config(String),
}

impl LakeCleanError {
    /// The request was well formed and this implementation cannot serve it.
    pub fn is_unavailable(&self) -> bool {
        matches!(self, Self::BuildDirUnknown(_))
    }
}

impl fmt::Display for LakeCleanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoConfigFile(p) => write!(
                f,
                "error: no such file or directory (error code: 2)\n  file: {}",
                p.join("lakefile.lean").display()
            ),
            Self::Io(msg) => write!(f, "error cleaning Lake build outputs: {msg}"),
            Self::BuildDirUnknown(path) => write!(
                f,
                "{} is not evaluated, so the package's build directory is not known; nothing was removed",
                path.display()
            ),
            Self::BuildDirOutsidePackage(path) => write!(
                f,
                "error: buildDir {:?} is not a directory inside the package; nothing was removed",
                path.display().to_string()
            ),
            Self::Config(detail) => write!(f, "error: {detail}"),
        }
    }
}

impl std::error::Error for LakeCleanError {}

/// Result of a clean operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeCleanReport {
    /// Whether the package's build directory was found and removed.
    pub build_dir_removed: bool,
    /// The package root cleaned.
    pub dir: PathBuf,
}

/// An error encountered while initializing or creating a Lake package.
#[derive(Debug)]
pub enum LakeInitError {
    /// The package name is invalid.
    IllegalName(String),
    /// The package name is a reserved identifier.
    ReservedName(String),
    /// The destination directory already exists.
    AlreadyExists(PathBuf),
    /// An I/O error occurred creating the package files.
    Io(String),
    /// The template is not one of the pin's.
    UnknownTemplate(String),
    /// The configuration language is not one of the pin's.
    UnknownConfigLanguage(String),
    /// The pin has this template and language; this implementation writes
    /// only `std` in TOML. Nothing was created.
    TemplateUnavailable { template: String, language: String },
    /// The directory already holds a package configuration.
    AlreadyInitialized,
}

impl LakeInitError {
    /// The request was well formed and this implementation cannot serve it.
    pub fn is_unavailable(&self) -> bool {
        matches!(self, Self::TemplateUnavailable { .. })
    }
}

impl fmt::Display for LakeInitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IllegalName(msg) => write!(f, "error: {msg}"),
            Self::ReservedName(name) => write!(f, "error: reserved package name '{name}'"),
            Self::AlreadyExists(p) => {
                write!(
                    f,
                    "error: package directory '{}' already exists",
                    p.display()
                )
            }
            Self::Io(msg) => write!(f, "error initializing Lake package: {msg}"),
            Self::UnknownTemplate(template) => {
                write!(f, "error: unknown package template `{template}`")
            }
            Self::UnknownConfigLanguage(language) => {
                write!(f, "error: unknown configuration language `{language}`")
            }
            Self::TemplateUnavailable { template, language } => write!(
                f,
                "the `{template}` template with a `{language}` configuration is not written here, only `std` with `toml`; nothing was created"
            ),
            Self::AlreadyInitialized => write!(f, "error: package already initialized"),
        }
    }
}

impl std::error::Error for LakeInitError {}

fn strip_comment(line: &str) -> &str {
    let mut in_quote = false;
    let mut quote_char = '"';
    let mut chars = line.char_indices();
    while let Some((idx, ch)) = chars.next() {
        if in_quote {
            if ch == '\\' {
                let _ = chars.next();
            } else if ch == quote_char {
                in_quote = false;
            }
        } else if ch == '"' || ch == '\'' {
            in_quote = true;
            quote_char = ch;
        } else if ch == '#' {
            return &line[..idx];
        }
    }
    line
}

fn parse_string_val(s: &str) -> Option<String> {
    let s = s.trim();
    if s.len() < 2 {
        return None;
    }
    let quote = s.as_bytes()[0];
    if !matches!(quote, b'\'' | b'"') || s.as_bytes().last().copied() != Some(quote) {
        return None;
    }
    let inner = &s[1..s.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == char::from(quote) || (c.is_control() && c != '\t') {
            return None;
        }
        if c != '\\' || quote == b'\'' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            'b' => out.push('\u{8}'),
            'f' => out.push('\u{c}'),
            '\\' => out.push('\\'),
            '"' => out.push('"'),
            escape @ ('u' | 'U') => {
                let width = if escape == 'u' { 4 } else { 8 };
                let digits: String = chars.by_ref().take(width).collect();
                if digits.len() != width || !digits.bytes().all(|b| b.is_ascii_hexdigit()) {
                    return None;
                }
                out.push(char::from_u32(u32::from_str_radix(&digits, 16).ok()?)?);
            }
            _ => return None,
        }
    }
    Some(out)
}

fn parse_string_array(s: &str) -> Option<Vec<String>> {
    let s = s.trim();
    if !s.starts_with('[') || !s.ends_with(']') {
        return None;
    }
    let inner = s[1..s.len() - 1].trim();
    if inner.is_empty() {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    let mut quote_char = '"';
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if in_quote {
            if ch == '\\' && quote_char == '"' {
                current.push(ch);
                if let Some(next) = chars.next() {
                    current.push(next);
                }
            } else if ch == quote_char {
                in_quote = false;
                current.push(ch);
            } else {
                current.push(ch);
            }
        } else if ch == '"' || ch == '\'' {
            in_quote = true;
            quote_char = ch;
            current.push(ch);
        } else if ch == ',' {
            result.push(parse_string_val(&current)?);
            current.clear();
        } else {
            current.push(ch);
        }
    }
    if in_quote {
        return None;
    }
    if !current.trim().is_empty() {
        result.push(parse_string_val(&current)?);
    }
    Some(result)
}

impl LakeConfig {
    /// The artifact-producing path must not silently ignore compiler options,
    /// custom globs, dependency jobs or native facets. Other configuration-only
    /// commands retain their existing permissive discovery surface.
    pub fn parse_toml_for_build(content: &str) -> Result<Self, LakeParseError> {
        Self::parse_toml_strict(content)
    }

    /// Checked executables and artifact builds resolve the same bounded local
    /// path requirements without silently accepting remote or custom settings.
    pub fn parse_toml_for_execution(content: &str) -> Result<Self, LakeParseError> {
        Self::parse_toml_strict(content)
    }

    fn parse_toml_strict(content: &str) -> Result<Self, LakeParseError> {
        let mut section = "package";
        let mut keys = std::collections::BTreeSet::new();
        for (index, raw) in content.lines().enumerate() {
            let line = strip_comment(raw).trim();
            if line.is_empty() {
                continue;
            }
            if line.starts_with('[') {
                section = match line {
                    "[package]" => "package",
                    "[[lean_lib]]" => "lean_lib",
                    "[[lean_exe]]" => "lean_exe",
                    "[[require]]" => "require",
                    _ => {
                        return Err(LakeParseError::UnsupportedBuildSetting(format!(
                            "line {}: {line}",
                            index + 1
                        )));
                    }
                };
                keys.clear();
                continue;
            }
            let invalid = || LakeParseError::InvalidSyntax(format!("line {}: {line}", index + 1));
            let Some((key, value)) = line.split_once('=') else {
                return Err(invalid());
            };
            let key = key.trim();
            if !keys.insert(key) {
                return Err(LakeParseError::InvalidSyntax(format!(
                    "line {}: duplicate {key}",
                    index + 1
                )));
            }
            let array = match (section, key) {
                ("package", "defaultTargets" | "keywords") | ("lean_lib", "roots") => true,
                (
                    "package",
                    "name" | "version" | "description" | "homepage" | "license" | "srcDir"
                    | "buildDir",
                )
                | ("lean_lib" | "lean_exe", "name" | "srcDir")
                | ("lean_exe", "root")
                | ("require", "name" | "path") => false,
                _ => {
                    return Err(LakeParseError::UnsupportedBuildSetting(format!(
                        "line {}: {section}.{key}",
                        index + 1
                    )));
                }
            };
            if if array {
                parse_string_array(value).is_none()
            } else {
                parse_string_val(value).is_none()
            } {
                return Err(invalid());
            }
            if key == "roots" && parse_string_array(value).is_some_and(|roots| roots.is_empty()) {
                return Err(LakeParseError::UnsupportedBuildSetting(format!(
                    "line {}: an empty library roots array",
                    index + 1
                )));
            }
        }
        let config = Self::parse_toml(content)?;
        for requirement in &config.requires {
            if requirement.name.is_empty() {
                return Err(LakeParseError::MissingField("require name"));
            }
            if requirement.path.is_none() {
                return Err(LakeParseError::UnsupportedBuildSetting(format!(
                    "require {} has no local path",
                    requirement.name
                )));
            }
        }
        let mut names = std::collections::BTreeSet::new();
        for target in &config.targets {
            if !names.insert(&target.name) {
                return Err(LakeParseError::InvalidSyntax(format!(
                    "duplicate target {}",
                    target.name
                )));
            }
        }
        Ok(config)
    }

    /// Parse a `lakefile.toml` configuration string.
    pub fn parse_toml(content: &str) -> Result<Self, LakeParseError> {
        let mut name: Option<String> = None;
        let mut default_targets: Vec<String> = Vec::new();
        let mut src_dir = PathBuf::from(".");
        let mut build_dir = PathBuf::from(".lake/build");
        let mut requires: Vec<LakeRequire> = Vec::new();
        let mut targets: Vec<LakeTarget> = Vec::new();

        #[derive(PartialEq)]
        enum Section {
            Top,
            Package,
            Require,
            Target,
            Other,
        }

        let mut current_section = Section::Top;

        for (line_idx, raw_line) in content.lines().enumerate() {
            let line = strip_comment(raw_line).trim();
            if line.is_empty() {
                continue;
            }

            if line.starts_with("[[") && line.ends_with("]]") {
                let section_name = line[2..line.len() - 2].trim();
                if section_name == "require" {
                    current_section = Section::Require;
                    requires.push(LakeRequire {
                        name: String::new(),
                        path: None,
                        url: None,
                        rev: None,
                        subdir: None,
                    });
                } else if section_name == "lean_lib" || section_name == "lean_exe" {
                    current_section = Section::Target;
                    targets.push(LakeTarget {
                        name: String::new(),
                        kind: if section_name == "lean_lib" {
                            TargetKind::Library
                        } else {
                            TargetKind::Executable
                        },
                        roots: Vec::new(),
                        src_dir: None,
                    });
                } else {
                    current_section = Section::Other;
                }
                continue;
            }

            if line.starts_with('[') && line.ends_with(']') {
                let section_name = line[1..line.len() - 1].trim();
                if section_name == "package" {
                    current_section = Section::Package;
                } else {
                    current_section = Section::Other;
                }
                continue;
            }

            if let Some((key_part, val_part)) = line.split_once('=') {
                let key = key_part.trim();
                let val = val_part.trim();

                match current_section {
                    Section::Top | Section::Package => match key {
                        "name" => {
                            if let Some(s) = parse_string_val(val) {
                                name = Some(s);
                            } else {
                                return Err(LakeParseError::InvalidSyntax(format!(
                                    "line {}: invalid string value for name: {}",
                                    line_idx + 1,
                                    val
                                )));
                            }
                        }
                        "defaultTargets" | "default_targets" => {
                            if let Some(arr) = parse_string_array(val) {
                                default_targets = arr;
                            } else {
                                return Err(LakeParseError::InvalidSyntax(format!(
                                    "line {}: invalid string array for defaultTargets: {}",
                                    line_idx + 1,
                                    val
                                )));
                            }
                        }
                        "srcDir" | "src_dir" => {
                            if let Some(s) = parse_string_val(val) {
                                src_dir = PathBuf::from(s);
                            }
                        }
                        "buildDir" | "build_dir" => {
                            if let Some(s) = parse_string_val(val) {
                                build_dir = PathBuf::from(s);
                            }
                        }
                        _ => {}
                    },
                    Section::Require => {
                        if let Some(req) = requires.last_mut() {
                            match key {
                                "name" => {
                                    if let Some(s) = parse_string_val(val) {
                                        req.name = s;
                                    }
                                }
                                "path" => {
                                    req.path = parse_string_val(val).map(PathBuf::from);
                                }
                                "url" | "git" => {
                                    req.url = parse_string_val(val);
                                }
                                "rev" => {
                                    req.rev = parse_string_val(val);
                                }
                                "subdir" | "subDir" => {
                                    req.subdir = parse_string_val(val);
                                }
                                _ => {}
                            }
                        }
                    }
                    Section::Target => {
                        if let Some(target) = targets.last_mut() {
                            let invalid = |what: &str| {
                                LakeParseError::InvalidSyntax(format!(
                                    "line {}: invalid {what}: {val}",
                                    line_idx + 1
                                ))
                            };
                            match key {
                                "name" => {
                                    target.name = parse_string_val(val)
                                        .ok_or_else(|| invalid("target name"))?;
                                }
                                "root" if target.kind == TargetKind::Executable => {
                                    target.roots =
                                        vec![parse_string_val(val).ok_or_else(|| invalid("root"))?];
                                }
                                "roots" if target.kind == TargetKind::Library => {
                                    target.roots =
                                        parse_string_array(val).ok_or_else(|| invalid("roots"))?;
                                }
                                "srcDir" | "src_dir" => {
                                    target.src_dir = Some(PathBuf::from(
                                        parse_string_val(val).ok_or_else(|| invalid("srcDir"))?,
                                    ));
                                }
                                _ => {}
                            }
                        }
                    }
                    Section::Other => {}
                }
            }
        }

        let name = name.ok_or(LakeParseError::MissingField("name"))?;
        for target in &mut targets {
            if target.name.is_empty() {
                return Err(LakeParseError::MissingField("lean_lib/lean_exe name"));
            }
            // Lake's defaults: a library's roots and an executable's root are its name.
            if target.roots.is_empty() {
                target.roots.push(target.name.clone());
            }
        }

        Ok(LakeConfig {
            name,
            default_targets,
            lean_toolchain: None,
            src_dir,
            build_dir,
            requires,
            targets,
            format: LakeConfigFormat::Toml,
        })
    }

    /// Discover and parse Lake configuration in `dir`.
    pub fn discover(dir: &Path) -> Result<Self, LakeDiscoveryError> {
        let toml_path = dir.join("lakefile.toml");
        let lean_path = dir.join("lakefile.lean");
        let toolchain_path = dir.join("lean-toolchain");

        let lean_toolchain = if toolchain_path.exists() {
            fs::read_to_string(&toolchain_path)
                .ok()
                .map(|s| s.trim().to_owned())
                .filter(|s| !s.is_empty())
        } else {
            None
        };

        if toml_path.exists() {
            let content = fs::read_to_string(&toml_path).map_err(LakeDiscoveryError::Io)?;
            let mut cfg = Self::parse_toml(&content).map_err(LakeDiscoveryError::Parse)?;
            cfg.lean_toolchain = lean_toolchain;
            Ok(cfg)
        } else if lean_path.exists() {
            Err(LakeDiscoveryError::LeanConfigUnsupported(lean_path))
        } else {
            Err(LakeDiscoveryError::NotFound(dir.to_path_buf()))
        }
    }
}

/// Clean build outputs in the package directory `dir`.
///
/// What is removed is the package's own build directory: `buildDir` from its
/// configuration, `.lake/build` when the configuration does not set one. A
/// `lakefile.lean` cannot be evaluated here, so its build directory is not
/// known and nothing is removed.
///
/// A `buildDir` that is absolute, empty, or leaves the package through `..` is
/// refused. The pin removes whatever the configuration names; this does not
/// delete outside the package on a configuration's say-so.
pub fn clean(dir: &Path) -> Result<LakeCleanReport, LakeCleanError> {
    let configured = match LakeConfig::discover(dir) {
        Ok(config) => config.build_dir,
        Err(LakeDiscoveryError::NotFound(_)) => {
            return Err(LakeCleanError::NoConfigFile(dir.to_path_buf()));
        }
        Err(LakeDiscoveryError::LeanConfigUnsupported(path)) => {
            return Err(LakeCleanError::BuildDirUnknown(path));
        }
        Err(other) => return Err(LakeCleanError::Config(other.to_string())),
    };
    let inside = configured.components().next().is_some()
        && configured
            .components()
            .all(|component| matches!(component, std::path::Component::Normal(_)));
    if !inside {
        return Err(LakeCleanError::BuildDirOutsidePackage(configured));
    }
    let build_dir = dir.join(&configured);
    let mut build_dir_removed = false;
    if build_dir.exists() {
        fs::remove_dir_all(&build_dir).map_err(|e| LakeCleanError::Io(e.to_string()))?;
        build_dir_removed = true;
    }
    Ok(LakeCleanReport {
        build_dir_removed,
        dir: dir.to_path_buf(),
    })
}

/// Validate a Lake package name according to Lake rules.
pub fn validate_package_name(name: &str) -> Result<(), LakeInitError> {
    if name.is_empty() {
        return Err(LakeInitError::IllegalName(
            "package name cannot be empty".to_owned(),
        ));
    }
    if name.chars().all(|c| c == '.') {
        return Err(LakeInitError::IllegalName(format!(
            "illegal package name '{name}'"
        )));
    }
    if name.contains('/') || name.contains('\\') {
        return Err(LakeInitError::IllegalName(format!(
            "illegal package name '{name}'"
        )));
    }
    let lower = name.to_ascii_lowercase();
    if lower == "init" || lower == "lean" || lower == "lake" || lower == "main" {
        return Err(LakeInitError::ReservedName(name.to_owned()));
    }
    Ok(())
}

fn capitalize_ident(s: &str) -> String {
    let mut res = String::new();
    let mut cap_next = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            cap_next = true;
        } else if cap_next {
            res.extend(c.to_uppercase());
            cap_next = false;
        } else {
            res.push(c);
        }
    }
    if res.is_empty() {
        "Package".to_owned()
    } else {
        res
    }
}

/// The pin's package templates (`Lake.InitTemplate.ofString?`) and
/// configuration languages (`Lake.ConfigLang.ofString?`).
const INIT_TEMPLATES: [&str; 5] = ["std", "exe", "lib", "math-lax", "math"];
const INIT_LANGUAGES: [&str; 2] = ["lean", "toml"];

/// Read a `[template][.language]` argument the way the pin's
/// `parseTemplateLangSpec` does: one or two dot-separated parts, an empty part
/// meaning its default, any other shape meaning both defaults. A part the pin
/// does not know is the pin's own error, template first.
fn init_template_spec(
    spec: Option<&str>,
    format: LakeConfigFormat,
) -> Result<(String, String), LakeInitError> {
    let parts: Vec<&str> = spec.unwrap_or("").split('.').collect();
    let (template, language) = match parts.as_slice() {
        [template, language] => (*template, *language),
        [template] => (*template, ""),
        _ => ("", ""),
    };
    let template = if template.is_empty() {
        "std".to_owned()
    } else {
        let lower = template.to_lowercase();
        if !INIT_TEMPLATES.contains(&lower.as_str()) {
            return Err(LakeInitError::UnknownTemplate(template.to_owned()));
        }
        lower
    };
    let language = if language.is_empty() {
        match format {
            LakeConfigFormat::Toml => "toml".to_owned(),
            LakeConfigFormat::Lean => "lean".to_owned(),
        }
    } else {
        let lower = language.to_lowercase();
        if !INIT_LANGUAGES.contains(&lower.as_str()) {
            return Err(LakeInitError::UnknownConfigLanguage(language.to_owned()));
        }
        lower
    };
    Ok((template, language))
}

fn write_new(path: &Path, contents: &str) -> Result<(), LakeInitError> {
    if path.exists() {
        return Ok(());
    }
    fs::write(path, contents).map_err(|e| LakeInitError::Io(e.to_string()))
}

/// Initialize a Lake package in `dir` from the pin's `std` template with a
/// TOML configuration: the files `Lake.initPkg` writes, with the same bytes.
///
/// `template` is the pin's `[template][.language]` argument. Only `std` in
/// TOML is written; another known template or language is refused before
/// anything is created, and an unknown one is the pin's own error.
///
/// Two things the pin does here are not done: no git repository is
/// initialized (D2: git is spawned only to fetch dependencies), and an
/// existing `lean-toolchain` is left as it is.
pub fn init_package(
    dir: &Path,
    name: &str,
    template: Option<&str>,
    format: LakeConfigFormat,
) -> Result<(), LakeInitError> {
    validate_package_name(name)?;
    let (template, language) = init_template_spec(template, format)?;
    if template != "std" || language != "toml" {
        return Err(LakeInitError::TemplateUnavailable { template, language });
    }
    let config_file = dir.join("lakefile.toml");
    if config_file.exists() {
        return Err(LakeInitError::AlreadyInitialized);
    }
    let io = |e: std::io::Error| LakeInitError::Io(e.to_string());
    fs::create_dir_all(dir).map_err(io)?;

    let lib_name = capitalize_ident(name);
    let exe_name = name.to_ascii_lowercase();

    let workflows = dir.join(".github").join("workflows");
    fs::create_dir_all(&workflows).map_err(io)?;
    write_new(
        &workflows.join("lean_action_ci.yml"),
        "name: Lean Action CI\n\
         \n\
         on:\n\
         \x20 push:\n\
         \x20 pull_request:\n\
         \x20 workflow_dispatch:\n\
         \n\
         jobs:\n\
         \x20 build:\n\
         \x20   runs-on: ubuntu-latest\n\
         \n\
         \x20   steps:\n\
         \x20     - uses: actions/checkout@v5\n\
         \x20     - uses: leanprover/lean-action@v1\n",
    )?;

    fs::write(
        &config_file,
        format!(
            "name = \"{name}\"\n\
             version = \"0.1.0\"\n\
             defaultTargets = [\"{exe_name}\"]\n\
             \n\
             [[lean_lib]]\n\
             name = \"{lib_name}\"\n\
             \n\
             [[lean_exe]]\n\
             name = \"{exe_name}\"\n\
             root = \"Main\"\n"
        ),
    )
    .map_err(io)?;

    // The library root and its first module, unless the root is already there.
    let root_file = dir.join(format!("{lib_name}.lean"));
    if !root_file.exists() {
        let lib_dir = dir.join(&lib_name);
        fs::create_dir_all(&lib_dir).map_err(io)?;
        write_new(&lib_dir.join("Basic.lean"), "def hello := \"world\"\n")?;
        fs::write(
            &root_file,
            format!(
                "-- This module serves as the root of the `{lib_name}` library.\n\
                 -- Import modules here that should be built as part of the library.\n\
                 import {lib_name}.Basic\n"
            ),
        )
        .map_err(io)?;
    }

    write_new(
        &dir.join("Main.lean"),
        &format!(
            "import {lib_name}\n\
             \n\
             def main : IO Unit :=\n\
             \x20 IO.println s!\"Hello, {{hello}}!\"\n"
        ),
    )?;

    // The pin's README has no final newline, and a dotted name is written with dashes.
    write_new(
        &dir.join("README.md"),
        &format!("# {}", name.replace('.', "-")),
    )?;

    // The pin appends its entry whether or not the file is there.
    let gitignore = dir.join(".gitignore");
    let mut ignored = fs::read_to_string(&gitignore).unwrap_or_default();
    ignored.push_str("/.lake\n");
    fs::write(&gitignore, ignored).map_err(io)?;

    write_new(
        &dir.join("lean-toolchain"),
        &format!("leanprover/lean4:{DEFAULT_PIN_TAG}\n"),
    )?;

    Ok(())
}

/// Create a new Lake package in `parent_dir / name`.
pub fn new_package(
    parent_dir: &Path,
    name: &str,
    template: Option<&str>,
    format: LakeConfigFormat,
) -> Result<PathBuf, LakeInitError> {
    validate_package_name(name)?;
    let target_dir = parent_dir.join(name);
    if target_dir.exists() {
        return Err(LakeInitError::AlreadyExists(target_dir));
    }
    init_package(&target_dir, name, template, format)?;
    Ok(target_dir)
}

// ---------------------------------------------------------------------------
// §13.3 — Lake manifest (lake-manifest.json)
// ---------------------------------------------------------------------------

/// A package entry within `lake-manifest.json`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestPackageEntry {
    pub name: String,
    pub scope: String,
    pub entry_type: String,
    /// Local package directory relative to the workspace containing the manifest.
    pub dir: Option<PathBuf>,
    pub url: Option<String>,
    pub rev: Option<String>,
    pub input_rev: Option<String>,
    pub subdir: Option<String>,
    pub inherited: bool,
    pub config_file: String,
    pub manifest_file: Option<PathBuf>,
}

/// The serialized Lake package manifest (`lake-manifest.json`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub name: String,
    pub lake_dir: PathBuf,
    pub fixed_toolchain: bool,
    pub packages_dir: Option<PathBuf>,
    pub version: String,
    pub packages: Vec<ManifestPackageEntry>,
}

#[derive(Debug)]
pub enum LakeUpdateError {
    Resource(String),
    Unsupported(String),
    Discovery(LakeDiscoveryError),
    Io(String),
    Parse(String),
    /// A selected remote requirement needs materialization and a resolved
    /// commit. Fetching is not implemented (the D2 subprocess protocol, bead
    /// `fln-7k0`), so no manifest is written. Local path requirements resolve
    /// without fetching; a requested remote revision is never copied into a
    /// resolved `rev` as a substitute for materialization.
    DependencyResolutionUnavailable {
        requirements: Vec<String>,
    },
}

impl fmt::Display for LakeUpdateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Resource(resource) => write!(f, "Lake update resource limit: {resource}"),
            Self::Unsupported(detail) => write!(f, "unsupported Lake update: {detail}"),
            Self::Discovery(e) => write!(f, "error discovering Lake configuration: {e}"),
            Self::Io(msg) => write!(f, "I/O error updating Lake manifest: {msg}"),
            Self::Parse(msg) => write!(f, "error parsing Lake manifest: {msg}"),
            Self::DependencyResolutionUnavailable { requirements } => write!(
                f,
                "dependency resolution is unavailable, so {} requirement(s) cannot be \
                 resolved ({}); no manifest was written",
                requirements.len(),
                requirements.join(", ")
            ),
        }
    }
}

impl std::error::Error for LakeUpdateError {}

/// A malformed manifest is distinct from an exhausted decoding budget.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManifestParseError {
    Invalid(String),
    Resource(&'static str),
}

impl fmt::Display for ManifestParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Invalid(detail) => f.write_str(detail),
            Self::Resource(resource) => write!(f, "manifest resource limit: {resource}"),
        }
    }
}

impl std::error::Error for ManifestParseError {}

impl From<String> for ManifestParseError {
    fn from(detail: String) -> Self {
        Self::Invalid(detail)
    }
}

const MAX_MANIFEST_BYTES: usize = 1024 * 1024;
const MAX_MANIFEST_VALUES: usize = 100_000;
const MAX_MANIFEST_DEPTH: usize = 64;

#[derive(Debug)]
enum ManifestJson {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<ManifestJson>),
    Object(std::collections::BTreeMap<String, ManifestJson>),
}

type ManifestFields = std::collections::BTreeMap<String, ManifestJson>;

/// JSON is parsed structurally before any field is used for package resolution.
/// The limits also cover ignored extension fields. Like the pin's TreeMap JSON
/// parser, later occurrences of the same decoded object key replace earlier ones.
struct ManifestParser<'a> {
    input: &'a str,
    offset: usize,
    values: usize,
}

impl<'a> ManifestParser<'a> {
    fn error(&self, reason: &str) -> ManifestParseError {
        ManifestParseError::Invalid(format!(
            "manifest JSON at byte {}: {reason}",
            self.offset,
        ))
    }

    fn peek(&self) -> Option<u8> {
        self.input.as_bytes().get(self.offset).copied()
    }

    fn whitespace(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.offset += 1;
        }
    }

    fn take(&mut self, byte: u8) -> bool {
        if self.peek() == Some(byte) {
            self.offset += 1;
            true
        } else {
            false
        }
    }

    fn hex4(&mut self) -> Result<u32, ManifestParseError> {
        let mut value = 0;
        for _ in 0..4 {
            let digit = match self.peek() {
                Some(byte @ b'0'..=b'9') => u32::from(byte - b'0'),
                Some(byte @ b'a'..=b'f') => u32::from(byte - b'a') + 10,
                Some(byte @ b'A'..=b'F') => u32::from(byte - b'A') + 10,
                _ => return Err(self.error("invalid Unicode escape")),
            };
            self.offset += 1;
            value = value * 16 + digit;
        }
        Ok(value)
    }

    fn string(&mut self) -> Result<String, ManifestParseError> {
        if !self.take(b'"') {
            return Err(self.error("expected a string"));
        }
        let mut output = String::new();
        let mut start = self.offset;
        loop {
            match self.peek() {
                Some(b'"') => {
                    output.push_str(&self.input[start..self.offset]);
                    self.offset += 1;
                    return Ok(output);
                }
                Some(b'\\') => {
                    output.push_str(&self.input[start..self.offset]);
                    self.offset += 1;
                    let escaped = self
                        .peek()
                        .ok_or_else(|| self.error("unfinished string escape"))?;
                    self.offset += 1;
                    match escaped {
                        b'"' => output.push('"'),
                        b'\\' => output.push('\\'),
                        b'/' => output.push('/'),
                        b'b' => output.push('\u{0008}'),
                        b'f' => output.push('\u{000c}'),
                        b'n' => output.push('\n'),
                        b'r' => output.push('\r'),
                        b't' => output.push('\t'),
                        b'u' => {
                            let first = self.hex4()?;
                            let scalar = if (0xd800..=0xdbff).contains(&first) {
                                if !self.take(b'\\') || !self.take(b'u') {
                                    return Err(self.error("missing low Unicode surrogate"));
                                }
                                let second = self.hex4()?;
                                if !(0xdc00..=0xdfff).contains(&second) {
                                    return Err(self.error("invalid low Unicode surrogate"));
                                }
                                0x10000 + ((first - 0xd800) << 10) + second - 0xdc00
                            } else {
                                first
                            };
                            let character = char::from_u32(scalar)
                                .ok_or_else(|| self.error("invalid Unicode scalar"))?;
                            output.push(character);
                        }
                        _ => return Err(self.error("invalid string escape")),
                    }
                    start = self.offset;
                }
                Some(0..=31) => return Err(self.error("unescaped string control character")),
                Some(_) => self.offset += 1,
                None => return Err(self.error("unterminated string")),
            }
        }
    }

    fn number(&mut self) -> Result<ManifestJson, ManifestParseError> {
        let start = self.offset;
        self.take(b'-');
        if !self.take(b'0') {
            if !matches!(self.peek(), Some(b'1'..=b'9')) {
                return Err(self.error("invalid number"));
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
        }
        if self.take(b'.') {
            let digits = self.offset;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
            if self.offset == digits {
                return Err(self.error("number lacks fractional digits"));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.offset += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.offset += 1;
            }
            let digits = self.offset;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.offset += 1;
            }
            if self.offset == digits {
                return Err(self.error("number lacks exponent digits"));
            }
        }
        Ok(ManifestJson::Number(
            self.input[start..self.offset].to_owned(),
        ))
    }

    fn value(&mut self, depth: usize) -> Result<ManifestJson, ManifestParseError> {
        if depth > MAX_MANIFEST_DEPTH {
            return Err(ManifestParseError::Resource("JSON depth exceeds 64"));
        }
        if self.values >= MAX_MANIFEST_VALUES {
            return Err(ManifestParseError::Resource("JSON values exceed 100000"));
        }
        self.values += 1;
        self.whitespace();
        match self.peek() {
            Some(b'"') => self.string().map(ManifestJson::String),
            Some(b'-' | b'0'..=b'9') => self.number(),
            Some(b'{') => {
                self.offset += 1;
                let mut fields = ManifestFields::new();
                self.whitespace();
                if self.take(b'}') {
                    return Ok(ManifestJson::Object(fields));
                }
                loop {
                    self.whitespace();
                    let key = self.string()?;
                    self.whitespace();
                    if !self.take(b':') {
                        return Err(self.error("expected ':' after object key"));
                    }
                    let value = self.value(depth + 1)?;
                    fields.insert(key, value);
                    self.whitespace();
                    if self.take(b'}') {
                        return Ok(ManifestJson::Object(fields));
                    }
                    if !self.take(b',') {
                        return Err(self.error("expected ',' or '}'"));
                    }
                }
            }
            Some(b'[') => {
                self.offset += 1;
                let mut values = Vec::new();
                self.whitespace();
                if self.take(b']') {
                    return Ok(ManifestJson::Array(values));
                }
                loop {
                    values.push(self.value(depth + 1)?);
                    self.whitespace();
                    if self.take(b']') {
                        return Ok(ManifestJson::Array(values));
                    }
                    if !self.take(b',') {
                        return Err(self.error("expected ',' or ']'"));
                    }
                }
            }
            Some(b'n') if self.input[self.offset..].starts_with("null") => {
                self.offset += 4;
                Ok(ManifestJson::Null)
            }
            Some(b't') if self.input[self.offset..].starts_with("true") => {
                self.offset += 4;
                Ok(ManifestJson::Bool(true))
            }
            Some(b'f') if self.input[self.offset..].starts_with("false") => {
                self.offset += 5;
                Ok(ManifestJson::Bool(false))
            }
            _ => Err(self.error("expected a JSON value")),
        }
    }

    fn parse(input: &'a str) -> Result<ManifestFields, ManifestParseError> {
        if input.len() > MAX_MANIFEST_BYTES {
            return Err(ManifestParseError::Resource("input exceeds 1 MiB"));
        }
        let mut parser = Self {
            input,
            offset: 0,
            values: 0,
        };
        let value = parser.value(0)?;
        parser.whitespace();
        if parser.offset != input.len() {
            return Err(parser.error("trailing bytes"));
        }
        match value {
            ManifestJson::Object(fields) => Ok(fields),
            _ => Err(ManifestParseError::Invalid(
                "manifest must be a JSON object".to_owned(),
            )),
        }
    }
}

fn manifest_string(
    fields: &ManifestFields,
    key: &str,
    default: Option<&str>,
) -> Result<String, String> {
    match fields.get(key) {
        Some(ManifestJson::String(value)) => Ok(value.clone()),
        None | Some(ManifestJson::Null) if default.is_some() => {
            Ok(default.unwrap().to_owned())
        }
        None => Err(format!("missing '{key}' field")),
        _ => Err(format!("'{key}' must be a string")),
    }
}

fn manifest_optional_string(fields: &ManifestFields, key: &str) -> Result<Option<String>, String> {
    match fields.get(key) {
        None | Some(ManifestJson::Null) => Ok(None),
        Some(ManifestJson::String(value)) => Ok(Some(value.clone())),
        _ => Err(format!("'{key}' must be a string or null")),
    }
}

/// Name-valued JSON fields follow String.toName at the pin. Quoted dots
/// belong to a component; numeric components and redundant quoting normalize.
fn manifest_name(
    fields: &ManifestFields,
    key: &str,
    default: Option<&str>,
) -> Result<String, String> {
    let text = manifest_string(fields, key, default)?;
    parse_manifest_name(&text).map_err(|()| format!("'{key}' is not a valid Lean name"))
}

fn parse_manifest_name(text: &str) -> Result<String, ()> {
    use fln_core::name::identifier::{is_id_first, is_id_rest};
    if text == "[anonymous]" {
        return Ok(text.to_owned());
    }
    let mut rest = text;
    let mut result = String::new();
    loop {
        let first = rest.chars().next().ok_or(())?;
        let (component, after) = if let Some(quoted) = rest.strip_prefix('«') {
            let end = quoted.find('»').ok_or(())?;
            let component = &quoted[..end];
            let mut chars = component.chars();
            let plain = chars.next().is_some_and(is_id_first) && chars.all(is_id_rest);
            let rendered = if plain {
                component.to_owned()
            } else {
                format!("«{component}»")
            };
            (rendered, &quoted[end + '»'.len_utf8()..])
        } else if first.is_ascii_digit() {
            let end = rest.bytes().take_while(u8::is_ascii_digit).count();
            let digits = rest[..end].trim_start_matches('0');
            (
                if digits.is_empty() { "0" } else { digits }.to_owned(),
                &rest[end..],
            )
        } else if is_id_first(first) {
            let end = rest
                .char_indices()
                .find(|(_, character)| !is_id_rest(*character))
                .map_or(rest.len(), |(index, _)| index);
            (rest[..end].to_owned(), &rest[end..])
        } else {
            return Err(());
        };
        if !result.is_empty() {
            result.push('.');
        }
        result.push_str(&component);
        if after.is_empty() {
            return Ok(result);
        }
        rest = after.strip_prefix('.').ok_or(())?;
    }
}

/// JSON spelling of Lake TOML's legal-or-simple package identity. Unlike a
/// JSON Name, a TOML name that is not a legal hierarchical spelling becomes one
/// string component. This distinction matters for ordinary hyphenated names.
pub fn canonical_package_name(name: &str) -> String {
    if name != "[anonymous]"
        && let Ok(parsed) = parse_manifest_name(name)
    {
        return parsed;
    }
    // Name.toString cannot escape a component containing the closing quote.
    // Preserve the pin's spelling; a subsequent manifest parse refuses an
    // unrepresentable name instead of silently selecting a different package.
    if name.contains('»') {
        name.to_owned()
    } else {
        format!("«{name}»")
    }
}

fn manifest_bool(fields: &ManifestFields, key: &str, default: Option<bool>) -> Result<bool, String> {
    match fields.get(key) {
        Some(ManifestJson::Bool(value)) => Ok(*value),
        None | Some(ManifestJson::Null) if default.is_some() => Ok(default.unwrap()),
        None => Err(format!("missing '{key}' field")),
        _ => Err(format!("'{key}' must be a boolean")),
    }
}

fn manifest_version(fields: &ManifestFields) -> Result<String, String> {
    let value = fields
        .get("version")
        .or_else(|| fields.get("schemaVersion"))
        .ok_or_else(|| "missing 'version' field in manifest".to_owned())?;
    let (text, major, minor) = match value {
        ManifestJson::Number(text) if text.bytes().all(|byte| byte.is_ascii_digit()) => {
            let minor = text
                .parse::<u64>()
                .map_err(|_| "manifest version exceeds the supported range")?;
            (text, 0, minor)
        }
        ManifestJson::String(text) => {
            let core = if let Some((core, suffix)) = text.split_once('-') {
                if suffix.is_empty() || suffix.chars().any(char::is_whitespace) {
                    return Err("invalid manifest version suffix".to_owned());
                }
                core
            } else {
                text.as_str()
            };
            let parts: Vec<_> = core.split('.').collect();
            if parts.len() != 3
                || parts.iter().any(|part| {
                    part.is_empty() || !part.bytes().all(|byte| byte.is_ascii_digit())
                })
            {
                return Err("manifest version must have three numeric components".to_owned());
            }
            let parts = parts
                .iter()
                .map(|part| part.parse::<u64>())
                .collect::<Result<Vec<_>, _>>()
                .map_err(|_| "manifest version exceeds the supported range")?;
            (text, parts[0], parts[1])
        }
        _ => return Err("manifest version must be an integer or a semantic version".to_owned()),
    };
    if major > 1 {
        return Err(format!("unsupported manifest major version: {text}"));
    }
    if major == 0 && minor < 7 {
        return Err(format!(
            "legacy manifest version {text} requires an unsupported pre-v7 package schema"
        ));
    }
    Ok(text.clone())
}

fn manifest_package(value: &ManifestJson) -> Result<ManifestPackageEntry, String> {
    let ManifestJson::Object(fields) = value else {
        return Err("manifest package entry must be an object".to_owned());
    };
    let name = manifest_name(fields, "name", None)?;
    let entry_type = manifest_string(fields, "type", None)?;
    let (dir, url, rev, input_rev, subdir) = match entry_type.as_str() {
        "path" => (
            Some(PathBuf::from(manifest_string(fields, "dir", None)?)),
            None,
            None,
            None,
            None,
        ),
        "git" => (
            None,
            Some(manifest_string(fields, "url", None)?),
            Some(manifest_string(fields, "rev", None)?),
            manifest_optional_string(fields, "inputRev")?,
            manifest_optional_string(fields, "subDir")?,
        ),
        _ => return Err(format!("unknown package entry type '{entry_type}'")),
    };
    Ok(ManifestPackageEntry {
        name,
        scope: manifest_string(fields, "scope", Some(""))?,
        entry_type,
        dir,
        url,
        rev,
        input_rev,
        subdir,
        inherited: manifest_bool(fields, "inherited", None)?,
        config_file: manifest_string(fields, "configFile", Some("lakefile"))?,
        // At the pin getD treats an explicit null as the same default as an
        // absent field, even though the in-memory writer can emit null.
        manifest_file: Some(PathBuf::from(manifest_string(
            fields,
            "manifestFile",
            Some("lake-manifest.json"),
        )?)),
    })
}

fn manifest_quote(value: &str) -> String {
    let mut output = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            '\u{0008}' => output.push_str("\\b"),
            '\u{000c}' => output.push_str("\\f"),
            character if character < ' ' => {
                output.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

fn manifest_optional_json(value: Option<&str>) -> String {
    value.map_or_else(|| "null".to_owned(), manifest_quote)
}

impl Manifest {
    pub fn new(name: impl Into<String>) -> Self {
        let name = name.into();
        Self {
            name: canonical_package_name(&name),
            lake_dir: PathBuf::from(".lake"),
            fixed_toolchain: false,
            packages_dir: Some(PathBuf::from(".lake/packages")),
            version: "1.2.0".to_owned(),
            packages: Vec::new(),
        }
    }

    pub fn to_json(&self) -> String {
        let version = if !self.version.is_empty()
            && self.version.bytes().all(|byte| byte.is_ascii_digit())
        {
            self.version.clone()
        } else {
            manifest_quote(&self.version)
        };
        let mut out = format!(
            "{{\n  \"name\": {},\n  \"version\": {version},\n  \"lakeDir\": {},\n  \"fixedToolchain\": {},\n  \"packagesDir\": {},\n  \"packages\": [\n",
            manifest_quote(&self.name),
            manifest_quote(&self.lake_dir.to_string_lossy()),
            self.fixed_toolchain,
            manifest_optional_json(self.packages_dir.as_ref().map(|p| p.to_string_lossy()).as_deref()),
        );
        for (index, package) in self.packages.iter().enumerate() {
            out.push_str(&format!(
                "    {{\n      \"name\": {},\n      \"scope\": {},\n      \"type\": {},\n      \"inherited\": {},\n      \"configFile\": {},\n      \"manifestFile\": {}",
                manifest_quote(&package.name),
                manifest_quote(&package.scope),
                manifest_quote(&package.entry_type),
                package.inherited,
                manifest_quote(&package.config_file),
                manifest_optional_json(package.manifest_file.as_ref().map(|p| p.to_string_lossy()).as_deref()),
            ));
            if package.entry_type == "path" {
                out.push_str(&format!(
                    ",\n      \"dir\": {}",
                    manifest_optional_json(package.dir.as_ref().map(|p| p.to_string_lossy()).as_deref()),
                ));
            } else {
                for (key, value) in [
                    ("url", package.url.as_deref()),
                    ("rev", package.rev.as_deref()),
                    ("inputRev", package.input_rev.as_deref()),
                    ("subDir", package.subdir.as_deref()),
                ] {
                    out.push_str(&format!(
                        ",\n      \"{key}\": {}",
                        manifest_optional_json(value),
                    ));
                }
            }
            out.push_str("\n    }");
            if index + 1 < self.packages.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str("  ]\n}\n");
        out
    }

    /// Decode the pin's v7 / 1.x package-entry schema without treating nested
    /// fields, malformed JSON, or incomplete dependency entries as a lockfile.
    /// Older tagged-sum schemas are explicitly unsupported.
    pub fn parse_json(content: &str) -> Result<Self, ManifestParseError> {
        let fields = ManifestParser::parse(content)?;
        let version = manifest_version(&fields)?;
        let packages = match fields.get("packages") {
            None | Some(ManifestJson::Null) => Vec::new(),
            Some(ManifestJson::Array(entries)) => entries
                .iter()
                .map(manifest_package)
                .collect::<Result<_, _>>()?,
            _ => {
                return Err(ManifestParseError::Invalid(
                    "'packages' must be an array".to_owned(),
                ));
            }
        };
        Ok(Self {
            name: manifest_name(&fields, "name", Some("[anonymous]"))?,
            lake_dir: PathBuf::from(manifest_string(&fields, "lakeDir", Some(".lake"))?),
            fixed_toolchain: manifest_bool(&fields, "fixedToolchain", Some(false))?,
            packages_dir: manifest_optional_string(&fields, "packagesDir")?.map(PathBuf::from),
            version,
            packages,
        })
    }

    pub fn load_from_dir(dir: &Path) -> Result<Option<Self>, LakeUpdateError> {
        use std::io::Read;
        let manifest_path = dir.join("lake-manifest.json");
        let file = match fs::File::open(&manifest_path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(LakeUpdateError::Io(error.to_string())),
        };
        let mut content = String::new();
        file.take((MAX_MANIFEST_BYTES + 1) as u64)
            .read_to_string(&mut content)
            .map_err(|error| LakeUpdateError::Io(error.to_string()))?;
        Self::parse_json(&content)
            .map(Some)
            .map_err(|error| match error {
                ManifestParseError::Invalid(detail) => LakeUpdateError::Parse(detail),
                ManifestParseError::Resource(resource) => {
                    LakeUpdateError::Resource(resource.to_owned())
                }
            })
    }

    pub fn save_to_dir(&self, dir: &Path) -> Result<(), io::Error> {
        use std::io::Write;
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT_WRITE: AtomicU64 = AtomicU64::new(0);

        let content = self.to_json();
        Self::parse_json(&content)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))?;
        let destination = dir.join("lake-manifest.json");
        match fs::symlink_metadata(&destination) {
            Ok(metadata) if !metadata.is_file() => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "manifest destination is not a regular file",
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        // Never truncate the fixed temporary pathname used by older releases:
        // another writer, or a symlink planted there, must remain untouched.
        for _ in 0..64 {
            let sequence = NEXT_WRITE.fetch_add(1, Ordering::Relaxed);
            let temporary = dir.join(format!(
                ".lake-manifest.json.{}.{sequence}.tmp",
                std::process::id(),
            ));
            let mut file = match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)
            {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            };
            let written = file
                .write_all(content.as_bytes())
                .and_then(|()| file.sync_all());
            drop(file);
            let result = written.and_then(|()| fs::rename(&temporary, &destination));
            if result.is_err() {
                let _ = fs::remove_file(&temporary);
            }
            return result;
        }
        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "could not reserve a manifest publication file",
        ))
    }
}

/// Resolve the bounded local TOML dependency graph and publish its manifest.
///
/// This is a bare update: the root's previous selection is replaced from its
/// current requirements. Direct requirements win before dependency manifests
/// are inherited, and the remaining graph follows the pin's reverse
/// breadth-first order (Lake/Load/Resolve.lean). No dependency is modified.
/// Git fetching, executable configuration, custom selectors and toolchain
/// changes remain explicit unavailable outcomes. Every input is rechecked
/// before the one atomic root-manifest publication.
pub fn update_manifest(dir: &Path) -> Result<Manifest, LakeUpdateError> {
    use std::collections::BTreeMap;

    let root = fs::canonicalize(dir).map_err(|error| LakeUpdateError::Io(error.to_string()))?;
    let mut inputs = Vec::new();
    let mut input_bytes = 0usize;
    let (config, toolchain) =
        update_package_configuration(&root, false, &mut inputs, &mut input_bytes)?;
    let previous = capture_update_input(
        &root,
        Path::new("lake-manifest.json"),
        1024 * 1024,
        &mut inputs,
        &mut input_bytes,
    )?;
    if let Some(bytes) = &previous {
        match parse_update_manifest(bytes) {
            Ok(manifest) => {
                if manifest.packages_dir.as_ref().is_some_and(|path| {
                    path.components()
                        .filter(|component| !matches!(component, std::path::Component::CurDir))
                        .ne(Path::new(".lake/packages").components())
                }) {
                    return Err(LakeUpdateError::Unsupported(
                        "updating a manifest with a custom packagesDir requires package-directory relocation"
                            .to_owned(),
                    ));
                }
            }
            // The pin's bare update deliberately rebuilds a malformed root
            // manifest. A resource stop is not a malformed-input judgment.
            Err(LakeUpdateError::Parse(_)) => {}
            Err(error) => return Err(error),
        }
    }
    if config.requires.len() > LOCAL_UPDATE_MAX_REQUIREMENTS {
        return Err(LakeUpdateError::Resource(
            "local requirement count exceeds 4096".to_owned(),
        ));
    }
    let mut manifest = Manifest::new(&config.name);
    let mut locked = BTreeMap::new();
    // Reserve ALL direct names before importing any child's manifest. Without
    // this phase a child's lock could override a later direct requirement.
    for requirement in config.requires.iter().rev() {
        let path = requirement.path.as_ref().ok_or_else(|| {
            LakeUpdateError::DependencyResolutionUnavailable {
                requirements: vec![requirement.name.clone()],
            }
        })?;
        locked.entry(requirement.name.clone()).or_insert_with(|| {
            local_update_entry(requirement.name.clone(), path.clone(), false)
        });
    }
    let mut selected = BTreeMap::from([(config.name.clone(), 0usize)]);
    let mut packages = vec![LocalUpdatePackage {
        relative: PathBuf::from("."),
        config,
        entry: None,
    }];
    let mut edges = vec![Vec::new()];
    let mut requirements = 0usize;
    let mut next = 0usize;
    while next < packages.len() {
        let declared = packages[next].config.requires.clone();
        requirements = requirements
            .checked_add(declared.len())
            .filter(|count| *count <= LOCAL_UPDATE_MAX_REQUIREMENTS)
            .ok_or_else(|| {
                LakeUpdateError::Resource("local requirement count exceeds 4096".to_owned())
            })?;
        for requirement in declared.iter().rev() {
            if let Some(&index) = selected.get(&requirement.name) {
                edges[next].push(index);
                continue;
            }
            if packages.len() >= LOCAL_UPDATE_MAX_PACKAGES {
                return Err(LakeUpdateError::Resource(
                    "local package count exceeds 64".to_owned(),
                ));
            }
            let mut entry = if let Some(entry) = locked.get(&requirement.name) {
                entry.clone()
            } else {
                let path = requirement.path.as_ref().ok_or_else(|| {
                    LakeUpdateError::DependencyResolutionUnavailable {
                        requirements: vec![requirement.name.clone()],
                    }
                })?;
                local_update_entry(
                    requirement.name.clone(),
                    packages[next].relative.join(path),
                    true,
                )
            };
            if entry.entry_type != "path" {
                return Err(LakeUpdateError::DependencyResolutionUnavailable {
                    requirements: vec![entry.name.clone()],
                });
            }
            if !matches!(entry.config_file.as_str(), "lakefile" | "lakefile.toml")
                || entry
                    .manifest_file
                    .as_deref()
                    .is_some_and(|path| path != Path::new("lake-manifest.json"))
            {
                return Err(LakeUpdateError::Unsupported(format!(
                    "dependency {} has a custom configuration or manifest selector",
                    entry.name,
                )));
            }
            let path = entry.dir.as_deref().ok_or_else(|| {
                LakeUpdateError::Parse(format!("path dependency {} has no directory", entry.name))
            })?;
            let directory = update_dependency_directory(&root, path)?;
            let relative = relative_update_directory(&root, &directory)?;
            let (config, dependency_toolchain) = update_package_configuration(
                &directory,
                entry.config_file == "lakefile.toml",
                &mut inputs,
                &mut input_bytes,
            )?;
            if next == 0 && dependency_toolchain.is_some() && dependency_toolchain != toolchain {
                return Err(LakeUpdateError::Unsupported(format!(
                    "dependency {} requires toolchain selection; local manifest updates do not change lean-toolchain",
                    entry.name,
                )));
            }
            entry.dir = Some(relative.clone());
            entry.config_file = "lakefile.toml".to_owned();
            entry.manifest_file = Some(PathBuf::from("lake-manifest.json"));
            locked.insert(entry.name.clone(), entry.clone());
            if let Some(bytes) = capture_update_input(
                &directory,
                Path::new("lake-manifest.json"),
                1024 * 1024,
                &mut inputs,
                &mut input_bytes,
            )? {
                let inherited = parse_update_manifest(&bytes)?;
                for mut inherited_entry in inherited.packages {
                    if locked.contains_key(&inherited_entry.name) {
                        continue;
                    }
                    if locked.len() >= LOCAL_UPDATE_MAX_REQUIREMENTS {
                        return Err(LakeUpdateError::Resource(
                            "local manifest entry count exceeds 4096".to_owned(),
                        ));
                    }
                    inherited_entry.inherited = true;
                    if let Some(path) = inherited_entry.dir.take() {
                        inherited_entry.dir = Some(relative.join(path));
                    }
                    locked.insert(inherited_entry.name.clone(), inherited_entry);
                }
            }
            let index = packages.len();
            selected.insert(requirement.name.clone(), index);
            packages.push(LocalUpdatePackage {
                relative,
                config,
                entry: Some(entry),
            });
            edges.push(Vec::new());
            edges[next].push(index);
        }
        next += 1;
    }
    fn cyclic(index: usize, edges: &[Vec<usize>], states: &mut [u8]) -> bool {
        if states[index] != 0 {
            return states[index] == 1;
        }
        states[index] = 1;
        if edges[index].iter().any(|&next| cyclic(next, edges, states)) {
            return true;
        }
        states[index] = 2;
        false
    }
    if cyclic(0, &edges, &mut vec![0; packages.len()]) {
        return Err(LakeUpdateError::Parse(
            "local package dependency cycle".to_owned(),
        ));
    }
    for input in inputs {
        if read_update_input(&input.root, &input.relative, input.max_bytes)? != input.bytes {
            return Err(LakeUpdateError::Parse(format!(
                "Lake configuration or manifest changed during dependency resolution: {}",
                input.root.join(&input.relative).display(),
            )));
        }
    }
    manifest.packages = packages
        .into_iter()
        .filter_map(|package| package.entry)
        .collect();
    manifest
        .save_to_dir(&root)
        .map_err(|error| LakeUpdateError::Io(error.to_string()))?;
    Ok(manifest)
}

const LOCAL_UPDATE_MAX_PACKAGES: usize = 64;
const LOCAL_UPDATE_MAX_REQUIREMENTS: usize = 4096;
const LOCAL_UPDATE_MAX_INPUT_BYTES: usize = 4 * 1024 * 1024;

struct LocalUpdatePackage {
    relative: PathBuf,
    config: LakeConfig,
    entry: Option<ManifestPackageEntry>,
}

struct LocalUpdateInput {
    root: PathBuf,
    relative: PathBuf,
    max_bytes: usize,
    bytes: Option<Vec<u8>>,
}

fn local_update_entry(name: String, dir: PathBuf, inherited: bool) -> ManifestPackageEntry {
    ManifestPackageEntry {
        name,
        scope: String::new(),
        entry_type: "path".to_owned(),
        dir: Some(dir),
        url: None,
        rev: None,
        input_rev: None,
        subdir: None,
        inherited,
        config_file: "lakefile".to_owned(),
        manifest_file: Some(PathBuf::from("lake-manifest.json")),
    }
}

fn parse_update_manifest(bytes: &[u8]) -> Result<Manifest, LakeUpdateError> {
    let text = std::str::from_utf8(bytes)
        .map_err(|_| LakeUpdateError::Parse("lake-manifest.json is not UTF-8".to_owned()))?;
    Manifest::parse_json(text).map_err(|error| match error {
        ManifestParseError::Invalid(detail) => LakeUpdateError::Parse(detail),
        ManifestParseError::Resource(detail) => LakeUpdateError::Resource(detail.to_owned()),
    })
}

fn capture_update_input(
    root: &Path,
    relative: &Path,
    max_bytes: usize,
    inputs: &mut Vec<LocalUpdateInput>,
    input_bytes: &mut usize,
) -> Result<Option<Vec<u8>>, LakeUpdateError> {
    let bytes = read_update_input(root, relative, max_bytes)?;
    *input_bytes = input_bytes
        .checked_add(bytes.as_ref().map_or(0, Vec::len))
        .filter(|count| *count <= LOCAL_UPDATE_MAX_INPUT_BYTES)
        .ok_or_else(|| LakeUpdateError::Resource("local update inputs exceed 4 MiB".to_owned()))?;
    inputs.push(LocalUpdateInput {
        root: root.to_path_buf(),
        relative: relative.to_path_buf(),
        max_bytes,
        bytes: bytes.clone(),
    });
    Ok(bytes)
}

fn read_update_input(
    root: &Path,
    relative: &Path,
    max_bytes: usize,
) -> Result<Option<Vec<u8>>, LakeUpdateError> {
    use std::io::Read;

    let mut path = root.to_path_buf();
    let mut components = relative.components().peekable();
    while let Some(component) = components.next() {
        if !matches!(component, std::path::Component::Normal(_)) {
            return Err(LakeUpdateError::Unsupported(
                "custom update input paths are unavailable".to_owned(),
            ));
        }
        path.push(component.as_os_str());
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(LakeUpdateError::Io(format!("{}: {error}", path.display()))),
        };
        if metadata.file_type().is_symlink() {
            return Err(LakeUpdateError::Parse(format!(
                "refusing symlink {}",
                path.display(),
            )));
        }
        if components.peek().is_some() {
            if !metadata.is_dir() {
                return Err(LakeUpdateError::Parse(format!(
                    "update input parent is not a directory: {}",
                    path.display(),
                )));
            }
        } else if !metadata.is_file() {
            return Err(LakeUpdateError::Parse(format!(
                "update input is not a regular file: {}",
                path.display(),
            )));
        } else if metadata.len() > max_bytes as u64 {
            return Err(LakeUpdateError::Resource(format!(
                "update input exceeds {max_bytes} bytes: {}",
                path.display(),
            )));
        }
    }
    let file = fs::File::open(&path)
        .map_err(|error| LakeUpdateError::Io(format!("{}: {error}", path.display())))?;
    let mut bytes = Vec::new();
    file.take(max_bytes as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|error| LakeUpdateError::Io(format!("{}: {error}", path.display())))?;
    if bytes.len() > max_bytes {
        return Err(LakeUpdateError::Resource(format!(
            "update input exceeds {max_bytes} bytes: {}",
            path.display(),
        )));
    }
    Ok(Some(bytes))
}

fn update_package_configuration(
    root: &Path,
    explicit_toml: bool,
    inputs: &mut Vec<LocalUpdateInput>,
    input_bytes: &mut usize,
) -> Result<(LakeConfig, Option<String>), LakeUpdateError> {
    for relative in ["lakefile.lean", ".lake/package-overrides.json"] {
        if relative == "lakefile.lean" && explicit_toml {
            continue;
        }
        if capture_update_input(root, Path::new(relative), 64 * 1024, inputs, input_bytes)?
            .is_some()
        {
            return Err(LakeUpdateError::Unsupported(format!(
                "local manifest updates do not support {}",
                root.join(relative).display(),
            )));
        }
    }
    let bytes =
        capture_update_input(root, Path::new("lakefile.toml"), 64 * 1024, inputs, input_bytes)?
            .ok_or_else(|| {
                LakeUpdateError::Discovery(LakeDiscoveryError::NotFound(root.to_path_buf()))
            })?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|_| LakeUpdateError::Parse("lakefile.toml is not UTF-8".to_owned()))?;
    let unchecked = LakeConfig::parse_toml(text)
        .map_err(|error| LakeUpdateError::Discovery(LakeDiscoveryError::Parse(error)))?;
    let unavailable: Vec<_> = unchecked
        .requires
        .iter()
        .filter(|requirement| {
            requirement.path.is_none()
                || requirement.url.is_some()
                || requirement.rev.is_some()
                || requirement.subdir.is_some()
        })
        .map(|requirement| requirement.name.clone())
        .collect();
    if !unavailable.is_empty() {
        return Err(LakeUpdateError::DependencyResolutionUnavailable {
            requirements: unavailable,
        });
    }
    let mut config = LakeConfig::parse_toml_for_execution(text).map_err(|error| match error {
        LakeParseError::UnsupportedBuildSetting(detail) => LakeUpdateError::Unsupported(detail),
        error => LakeUpdateError::Discovery(LakeDiscoveryError::Parse(error)),
    })?;
    config.name = canonical_package_name(&config.name);
    for requirement in &mut config.requires {
        requirement.name = canonical_package_name(&requirement.name);
    }
    let toolchain =
        capture_update_input(root, Path::new("lean-toolchain"), 4096, inputs, input_bytes)?
            .map(|bytes| {
                String::from_utf8(bytes)
                    .map(|text| text.trim().to_owned())
                    .map_err(|_| LakeUpdateError::Parse("lean-toolchain is not UTF-8".to_owned()))
            })
            .transpose()?
            .filter(|text| !text.is_empty());
    Ok((config, toolchain))
}

/// Inspect every component BEFORE normalizing away parent components.
fn update_dependency_directory(root: &Path, path: &Path) -> Result<PathBuf, LakeUpdateError> {
    use std::path::Component;

    if path.components().count() > 128 {
        return Err(LakeUpdateError::Resource(
            "local dependency path exceeds 128 components".to_owned(),
        ));
    }
    let mut cursor = root.to_path_buf();
    for component in path.components() {
        match component {
            Component::Prefix(_) => {
                return Err(LakeUpdateError::Unsupported(
                    "local dependency path has an unsupported platform prefix".to_owned(),
                ));
            }
            Component::RootDir => cursor = PathBuf::from(component.as_os_str()),
            Component::CurDir => continue,
            Component::ParentDir => {
                cursor.pop();
            }
            Component::Normal(part) => cursor.push(part),
        }
        let metadata = fs::symlink_metadata(&cursor)
            .map_err(|error| LakeUpdateError::Io(format!("{}: {error}", cursor.display())))?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(LakeUpdateError::Parse(format!(
                "local dependency is not a real directory (refusing symlink): {}",
                cursor.display(),
            )));
        }
    }
    fs::canonicalize(&cursor)
        .map_err(|error| LakeUpdateError::Io(format!("{}: {error}", cursor.display())))
}

fn relative_update_directory(root: &Path, directory: &Path) -> Result<PathBuf, LakeUpdateError> {
    let root_components: Vec<_> = root.components().collect();
    let components: Vec<_> = directory.components().collect();
    let common = root_components
        .iter()
        .zip(&components)
        .take_while(|(left, right)| left == right)
        .count();
    let path = if common == 0 {
        directory.to_path_buf()
    } else {
        let mut relative = PathBuf::new();
        for _ in &root_components[common..] {
            relative.push("..");
        }
        for component in &components[common..] {
            relative.push(component.as_os_str());
        }
        if relative.as_os_str().is_empty() {
            relative.push(".");
        }
        relative
    };
    if path.to_str().is_none() {
        return Err(LakeUpdateError::Unsupported(
            "manifest dependency paths must be UTF-8".to_owned(),
        ));
    }
    Ok(path)
}

// ---------------------------------------------------------------------------
// §13.3 — Lake build and dual rebuild decision model
// ---------------------------------------------------------------------------

/// Outcome report of a `lake build` or `lake check-build` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeBuildReport {
    /// Package name.
    pub package: String,
    /// Targets considered in the build.
    pub targets: Vec<String>,
    /// Number of targets that were compiled or refreshed.
    pub targets_built: u64,
    /// Number of targets satisfied from cache.
    pub targets_cached: u64,
}

/// An error encountered while building a Lake package.
#[derive(Debug)]
pub enum LakeBuildError {
    /// Configuration discovery failed.
    Discovery(LakeDiscoveryError),
    /// Target was not found in package.
    TargetNotFound(String),
    /// I/O error occurred during build.
    Io(String),
    /// No artifact-producing compilation path is connected to this command.
    Unavailable,
}

impl fmt::Display for LakeBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Discovery(e) => write!(f, "{e}"),
            Self::TargetNotFound(t) => write!(f, "error: target '{t}' not found in package"),
            Self::Io(msg) => write!(f, "error during Lake build: {msg}"),
            Self::Unavailable => write!(
                f,
                "native Lake artifact compilation is unavailable; no build or cache validation was performed"
            ),
        }
    }
}

impl std::error::Error for LakeBuildError {}

/// A full build explain report for `fln build explain`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildExplainReport {
    /// Package name.
    pub package: String,
    /// Target being explained.
    pub target: String,
    /// What the Reference toolchain would rebuild (file cone invalidation).
    pub reference_decision: RebuildDecision,
    /// What FrankenLean's Ledger actually rebuilds (demand-node early cutoff).
    pub native_decision: RebuildDecision,
    /// Difference/rationale between reference and native decisions.
    pub delta: String,
    /// Changed input files/identities that triggered rebuild.
    pub changed_inputs: Vec<String>,
    /// Opaque barriers preventing memoization (e.g. IO effects, unclassified macros).
    pub opaque_barriers: Vec<String>,
    /// Cache outcome (e.g. "hit", "miss", "bypassed").
    pub cache_outcome: String,
}

/// An error encountered while explaining a Lake build.
#[derive(Debug)]
pub enum LakeExplainError {
    /// Configuration discovery failed.
    Discovery(LakeDiscoveryError),
    /// Target was not found in package.
    TargetNotFound(String),
    /// I/O error occurred.
    Io(String),
    /// No recorded, content-bound build provenance supports a decision.
    Unavailable,
}

impl fmt::Display for LakeExplainError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Discovery(e) => write!(f, "{e}"),
            Self::TargetNotFound(t) => write!(f, "error: target '{t}' not found in package"),
            Self::Io(msg) => write!(f, "error explaining Lake build: {msg}"),
            Self::Unavailable => write!(
                f,
                "build provenance is unavailable; cannot establish changed inputs, rebuild decisions or cache outcomes"
            ),
        }
    }
}

impl std::error::Error for LakeExplainError {}

/// Refuse artifact builds until a real compiler and module publisher are wired.
///
/// Configuration presence, source timestamps and existing output files cannot
/// authorize a successful build. In particular, do not create output directories
/// or replace old artifacts on this unsupported path.
pub fn build_package(dir: &Path, _targets: &[String]) -> Result<LakeBuildReport, LakeBuildError> {
    LakeConfig::discover(dir).map_err(LakeBuildError::Discovery)?;
    Err(LakeBuildError::Unavailable)
}

/// Refuse build explanations without content-bound, recorded build provenance.
///
/// Neither a timestamp nor a source comment establishes semantic early cutoff.
/// This applies equally to native and faithful-invalidation requests. This crate
/// has no source graph or build snapshot; `fln build explain` is implemented in
/// `fln-cli` over the snapshot `lake build` writes (bead `franken_lean-z8j.1.2`).
pub fn explain_build(
    dir: &Path,
    _target: Option<&str>,
    _faithful_invalidation: bool,
) -> Result<BuildExplainReport, LakeExplainError> {
    LakeConfig::discover(dir).map_err(LakeExplainError::Discovery)?;
    Err(LakeExplainError::Unavailable)
}

// ---------------------------------------------------------------------------
// §13.3 — D2 git dependency fetching capsule
// ---------------------------------------------------------------------------

/// An error encountered while fetching dependencies via git.
#[derive(Debug)]
pub enum LakeFetchError {
    /// Git is not available on the host.
    CapabilityDenied(String),
    /// I/O error during fetch.
    Io(String),
    /// Git command failed.
    GitFailed { command: String, stderr: String },
    /// Discovery error.
    Discovery(LakeDiscoveryError),
}

impl fmt::Display for LakeFetchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapabilityDenied(msg) => write!(f, "error: {msg}"),
            Self::Io(msg) => write!(f, "error during dependency fetch: {msg}"),
            Self::GitFailed { command, stderr } => {
                write!(f, "error: git command '{command}' failed:\n{stderr}")
            }
            Self::Discovery(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for LakeFetchError {}

/// Check if the system `git` tool is available under Rule D2.
pub fn is_git_available() -> bool {
    std::process::Command::new("git")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Fetch a git dependency into `.lake/packages/<name>` using the D2 subprocess protocol.
pub fn fetch_git_dependency(
    packages_dir: &Path,
    name: &str,
    url: &str,
    rev: Option<&str>,
) -> Result<PathBuf, LakeFetchError> {
    if !is_git_available() {
        return Err(LakeFetchError::CapabilityDenied(format!(
            "external tool 'git' is not available for dependency fetching. \
             Alternative: configure ATP CAS cache synchronization or download \
             package '{name}' into {} manually (Rule D2)",
            packages_dir.join(name).display()
        )));
    }

    fs::create_dir_all(packages_dir).map_err(|e| LakeFetchError::Io(e.to_string()))?;
    let pkg_dest = packages_dir.join(name);

    if !pkg_dest.exists() {
        // Clone with argv-only invocation, no shell
        let mut clone_cmd = std::process::Command::new("git");
        clone_cmd.args(["clone", "--quiet", url, pkg_dest.to_str().unwrap_or(name)]);
        let output = clone_cmd
            .output()
            .map_err(|e| LakeFetchError::Io(e.to_string()))?;
        if !output.status.success() {
            return Err(LakeFetchError::GitFailed {
                command: format!("git clone {url} {}", pkg_dest.display()),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
    }

    if let Some(revision) = rev {
        let mut checkout_cmd = std::process::Command::new("git");
        checkout_cmd.current_dir(&pkg_dest);
        checkout_cmd.args(["checkout", "--quiet", revision]);
        let output = checkout_cmd
            .output()
            .map_err(|e| LakeFetchError::Io(e.to_string()))?;
        if !output.status.success() {
            return Err(LakeFetchError::GitFailed {
                command: format!("git checkout {revision}"),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
    }

    Ok(pkg_dest)
}
