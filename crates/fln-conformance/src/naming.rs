//! The suite-wide subsystem-name registry and current-vocabulary scanner (bead
//! fln-7gr6): `ci/SUBSYSTEM_REGISTRY.txt` reserves load-bearing codenames across the
//! FrankenSuite (Quill belongs to the Frankensearch lexical engine; the FrankenLean
//! parser/macro subsystem is Vellum), and the scanner proves the governed current
//! vocabulary — docs, source, ci artifacts, contracts, scripts, and mutable bead
//! fields — never uses a reserved name outside an explicit owner citation.
//!
//! File format (`ci/SUBSYSTEM_REGISTRY.txt`, line-oriented, '#' comments):
//!
//! ```text
//! schema fln-subsystem-registry/1
//! row <name> | <owner> | <scope> | <crates|-> | <aliases|-> | <status> | <reason>
//! ```
//!
//! Laws enforced here:
//! * names and aliases are unique case-insensitively across the whole file, and a
//!   crate is claimed by at most one row — verdicts are independent of row order,
//!   witnesses are canonically ordered;
//! * unknown schema versions and unknown statuses fail typed, never default;
//! * a `<registry>.candidate` sibling is an interrupted publication and fails typed
//!   (`stale-candidate`) until explicitly resolved;
//! * a reserved name may appear in current vocabulary only on a line (or bead
//!   field) that also names its owning project — immutable history (bead comments,
//!   `.br_history/`, published receipts) is exempt by construction, and the files
//!   that *define* this contract ([`CONTRACT_DEFINITION_PATHS`]) are exempt by
//!   visible, validated enumeration, never silently.

use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};

/// Repo-relative path of the registry.
pub const REGISTRY_PATH: &str = "ci/SUBSYSTEM_REGISTRY.txt";
/// The one supported schema version.
pub const REGISTRY_SCHEMA: &str = "fln-subsystem-registry/1";
/// Canonical scan-report schema tag.
pub const REPORT_SCHEMA: &str = "fln-naming-inventory/1";

/// Files that define the naming contract itself and therefore legitimately spell
/// reserved names (mutant fixtures, sed seeds, rule prose). This list is public and
/// validated: every entry must exist, and nothing else is exempt.
pub const CONTRACT_DEFINITION_PATHS: &[&str] = &[
    "ci/SUBSYSTEM_REGISTRY.txt",
    "crates/fln-conformance/src/naming.rs",
    "crates/fln-conformance/tests/subsystem_name_registry.rs",
    "crates/fln-conformance/tests/reserved_name_collision_model.rs",
    "crates/fln-conformance/tests/vellum_surface_inventory.rs",
    "crates/fln-conformance/tests/generated_name_drift_guard.rs",
    "scripts/e2e/vellum_naming_no_mock_e2e.sh",
];

/// Mutable bead fields that carry *current* vocabulary. Comments are immutable
/// historical records and are deliberately absent.
pub const BEAD_CURRENT_FIELDS: &[&str] = &[
    "title",
    "description",
    "acceptance_criteria",
    "design",
    "notes",
];

/// Row status. Closed set; unknown statuses fail typed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    Active,
    Reserved,
    Historical,
}

impl Status {
    fn parse(s: &str) -> Option<Status> {
        Some(match s {
            "active" => Status::Active,
            "reserved" => Status::Reserved,
            "historical" => Status::Historical,
            _ => return None,
        })
    }
}

/// One registered subsystem codename.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SubsystemRow {
    pub name: String,
    pub owner: String,
    pub scope: String,
    pub crates: Vec<String>,
    pub aliases: Vec<String>,
    pub status: Status,
    pub reason: String,
    pub line: usize,
}

/// The parsed registry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registry {
    pub rows: Vec<SubsystemRow>,
}

impl Registry {
    /// Rows whose names are reserved for a project other than this workspace:
    /// their spelling is what the scanner hunts for.
    pub fn reserved_rows(&self) -> Vec<&SubsystemRow> {
        self.rows
            .iter()
            .filter(|row| row.status == Status::Reserved)
            .collect()
    }

    pub fn find(&self, name: &str) -> Option<&SubsystemRow> {
        let needle = name.to_ascii_lowercase();
        self.rows
            .iter()
            .find(|row| row.name.to_ascii_lowercase() == needle)
    }
}

/// Typed registry failures. `Display` renders the stable reason token first so
/// harnesses can assert the *intended* reason, not merely "some failure".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegistryError {
    MissingSchema,
    UnsupportedSchema { found: String },
    MalformedRow { line: usize, detail: String },
    EmptyField { line: usize, field: &'static str },
    UnknownStatus { line: usize, status: String },
    NameCollision { witnesses: Vec<String> },
    CrateCollision { witnesses: Vec<String> },
    StaleCandidate { candidate: String },
    Unreadable { path: String, detail: String },
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::MissingSchema => write!(f, "missing-schema"),
            RegistryError::UnsupportedSchema { found } => {
                write!(f, "unsupported-schema: {found}")
            }
            RegistryError::MalformedRow { line, detail } => {
                write!(f, "malformed-row: line {line}: {detail}")
            }
            RegistryError::EmptyField { line, field } => {
                write!(f, "empty-field: line {line}: {field}")
            }
            RegistryError::UnknownStatus { line, status } => {
                write!(f, "unknown-status: line {line}: {status}")
            }
            RegistryError::NameCollision { witnesses } => {
                write!(f, "name-collision: {}", witnesses.join("; "))
            }
            RegistryError::CrateCollision { witnesses } => {
                write!(f, "crate-collision: {}", witnesses.join("; "))
            }
            RegistryError::StaleCandidate { candidate } => {
                write!(f, "stale-candidate: {candidate}")
            }
            RegistryError::Unreadable { path, detail } => {
                write!(f, "unreadable-registry: {path}: {detail}")
            }
        }
    }
}

fn list_field(raw: &str) -> Vec<String> {
    if raw == "-" {
        return Vec::new();
    }
    raw.split(',')
        .map(|item| item.trim().to_string())
        .filter(|item| !item.is_empty())
        .collect()
}

/// Parse the registry text. Schema line first (comments/blank lines allowed
/// before it); every non-comment line after it must be a well-formed `row`.
pub fn parse_registry(text: &str) -> Result<Registry, RegistryError> {
    let mut rows = Vec::new();
    let mut schema_seen = false;
    for (index, raw_line) in text.lines().enumerate() {
        let line_no = index + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if !schema_seen {
            match line.strip_prefix("schema ") {
                Some(found) if found.trim() == REGISTRY_SCHEMA => {
                    schema_seen = true;
                    continue;
                }
                Some(found) => {
                    return Err(RegistryError::UnsupportedSchema {
                        found: found.trim().to_string(),
                    });
                }
                None => return Err(RegistryError::MissingSchema),
            }
        }
        let Some(body) = line.strip_prefix("row ") else {
            return Err(RegistryError::MalformedRow {
                line: line_no,
                detail: format!("expected `row`, found `{line}`"),
            });
        };
        let fields: Vec<&str> = body.split('|').map(str::trim).collect();
        if fields.len() != 7 {
            return Err(RegistryError::MalformedRow {
                line: line_no,
                detail: format!("expected 7 '|'-separated fields, found {}", fields.len()),
            });
        }
        for (field, label) in [
            (fields[0], "name"),
            (fields[1], "owner"),
            (fields[2], "scope"),
        ] {
            if field.is_empty() {
                return Err(RegistryError::EmptyField {
                    line: line_no,
                    field: match label {
                        "name" => "name",
                        "owner" => "owner",
                        _ => "scope",
                    },
                });
            }
        }
        if fields[6].is_empty() {
            return Err(RegistryError::EmptyField {
                line: line_no,
                field: "reason",
            });
        }
        let Some(status) = Status::parse(fields[5]) else {
            return Err(RegistryError::UnknownStatus {
                line: line_no,
                status: fields[5].to_string(),
            });
        };
        rows.push(SubsystemRow {
            name: fields[0].to_string(),
            owner: fields[1].to_string(),
            scope: fields[2].to_string(),
            crates: list_field(fields[3]),
            aliases: list_field(fields[4]),
            status,
            reason: fields[6].to_string(),
            line: line_no,
        });
    }
    if !schema_seen {
        return Err(RegistryError::MissingSchema);
    }
    Ok(Registry { rows })
}

/// The collision model: names ∪ aliases unique case-insensitively; a crate claimed
/// by at most one row. The verdict and its witnesses are functions of the row *set*
/// (sorted canonically), never of row order.
pub fn validate_collisions(registry: &Registry) -> Result<(), RegistryError> {
    let mut claims: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for row in &registry.rows {
        claims
            .entry(row.name.to_ascii_lowercase())
            .or_default()
            .push(format!("{} (name, owner={})", row.name, row.owner));
        for alias in &row.aliases {
            claims
                .entry(alias.to_ascii_lowercase())
                .or_default()
                .push(format!(
                    "{} (alias of {}, owner={})",
                    alias, row.name, row.owner
                ));
        }
    }
    let mut name_witnesses: Vec<String> = claims
        .iter()
        .filter(|(_, holders)| holders.len() > 1)
        .map(|(key, holders)| {
            let mut sorted = holders.clone();
            sorted.sort();
            format!("`{key}` claimed by [{}]", sorted.join(", "))
        })
        .collect();
    if !name_witnesses.is_empty() {
        name_witnesses.sort();
        return Err(RegistryError::NameCollision {
            witnesses: name_witnesses,
        });
    }
    let mut crate_claims: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for row in &registry.rows {
        for krate in &row.crates {
            crate_claims
                .entry(krate.to_ascii_lowercase())
                .or_default()
                .push(row.name.clone());
        }
    }
    let mut crate_witnesses: Vec<String> = crate_claims
        .iter()
        .filter(|(_, holders)| holders.len() > 1)
        .map(|(key, holders)| {
            let mut sorted = holders.clone();
            sorted.sort();
            format!("crate `{key}` claimed by [{}]", sorted.join(", "))
        })
        .collect();
    if !crate_witnesses.is_empty() {
        crate_witnesses.sort();
        return Err(RegistryError::CrateCollision {
            witnesses: crate_witnesses,
        });
    }
    Ok(())
}

/// Load, candidate-check, parse, and collision-validate the registry under `root`.
pub fn load_registry(root: &Path) -> Result<Registry, RegistryError> {
    let path = root.join(REGISTRY_PATH);
    let candidate = root.join(format!("{REGISTRY_PATH}.candidate"));
    if candidate.exists() {
        return Err(RegistryError::StaleCandidate {
            candidate: format!("{REGISTRY_PATH}.candidate"),
        });
    }
    let text = std::fs::read_to_string(&path).map_err(|error| RegistryError::Unreadable {
        path: REGISTRY_PATH.to_string(),
        detail: error.to_string(),
    })?;
    let registry = parse_registry(&text)?;
    validate_collisions(&registry)?;
    Ok(registry)
}

/// Governed surface classes, in canonical order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SurfaceClass {
    Docs,
    Source,
    Ci,
    Contracts,
    Scripts,
    BeadsCurrent,
}

impl SurfaceClass {
    pub fn label(self) -> &'static str {
        match self {
            SurfaceClass::Docs => "docs",
            SurfaceClass::Source => "source",
            SurfaceClass::Ci => "ci",
            SurfaceClass::Contracts => "contracts",
            SurfaceClass::Scripts => "scripts",
            SurfaceClass::BeadsCurrent => "beads-current",
        }
    }
}

/// One stale use of a reserved name in current vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct StaleReference {
    pub class: SurfaceClass,
    pub path: String,
    pub line: usize,
    pub field: Option<String>,
    pub name: String,
    pub excerpt: String,
}

/// The deterministic scan result: stale references (sorted) plus the census of
/// files examined per class (sorted), so "clean" is distinguishable from "unseen".
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScanReport {
    pub stale: Vec<StaleReference>,
    pub scanned: Vec<(SurfaceClass, String)>,
}

/// A governed surface could not be read, so the census is INCONCLUSIVE rather than clean.
///
/// Typed rather than a panic, for FL-INV-07 and for this module's neighbours: `ownership.rs`
/// returns `Unreadable` and the ownership publisher returns a typed `Inconclusive` for the same
/// condition, both in `src/`. A missing surface is an environmental fact, not an invariant
/// failure, so it is reported — the *callers* are tests, and a test is where a panic belongs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScanError {
    UnreadableSurface {
        class: SurfaceClass,
        path: String,
        detail: String,
    },
}

impl fmt::Display for ScanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // The hint rides on the error, not on one caller, because this refusal's most
            // common cause names something else entirely and that is how `hugg` cost a day.
            ScanError::UnreadableSurface {
                class,
                path,
                detail,
            } => write!(
                f,
                "unreadable-surface: {}: {path}: {detail}. A census that cannot read a governed \
                 surface is inconclusive, never a clean tree. If this fired under `rch`: \
                 `.beads/` is in its `exclude_patterns`, so the worker has no copy and the \
                 PreToolUse hook intercepts a plain `cargo test` — run this suite locally \
                 (bead `fln-y0f7`).",
                class.label()
            ),
        }
    }
}

fn is_word_boundary(byte: Option<u8>) -> bool {
    match byte {
        None => true,
        Some(b) => !b.is_ascii_alphanumeric(),
    }
}

/// Case-insensitive whole-word containment (`quill` matches `Quill:`/`QUILL`,
/// never `tranquillity`).
pub fn contains_word(haystack: &str, needle: &str) -> bool {
    let hay = haystack.to_ascii_lowercase();
    let needle = needle.to_ascii_lowercase();
    let bytes = hay.as_bytes();
    let mut from = 0;
    while let Some(found) = hay[from..].find(&needle) {
        let start = from + found;
        let end = start + needle.len();
        let before = start.checked_sub(1).map(|index| bytes[index]);
        let after = bytes.get(end).copied();
        if is_word_boundary(before) && is_word_boundary(after) {
            return true;
        }
        from = start + 1;
    }
    false
}

/// The owner-context law: text may use a reserved name only if it also names the
/// owning project in the same line (or bead field).
pub fn reserved_use_is_cited(text: &str, owner: &str) -> bool {
    contains_word(text, owner)
}

/// Scan one text body line-by-line against the registry's reserved rows.
/// Used both on real files and on in-memory mutant fixtures.
pub fn scan_text(
    class: SurfaceClass,
    path: &str,
    text: &str,
    registry: &Registry,
) -> Vec<StaleReference> {
    let mut stale = Vec::new();
    for (index, line) in text.lines().enumerate() {
        for row in registry.reserved_rows() {
            let mut names: Vec<&str> = vec![row.name.as_str()];
            names.extend(row.aliases.iter().map(String::as_str));
            for name in names {
                if contains_word(line, name) && !reserved_use_is_cited(line, &row.owner) {
                    stale.push(StaleReference {
                        class,
                        path: path.to_string(),
                        line: index + 1,
                        field: None,
                        name: name.to_string(),
                        excerpt: line.trim().chars().take(160).collect(),
                    });
                }
            }
        }
    }
    stale
}

/// Extract the top-level string fields of one JSON object line (a beads issue)
/// without a JSON dependency (D1: no serde). Only top-level `"key": "string"`
/// pairs are returned; nested values (e.g. the immutable `comments` array) are
/// skipped structurally. JSON escapes never split an ASCII identifier, so
/// substring checks on the raw field body are sound for this purpose.
pub fn top_level_string_fields(line: &str) -> Vec<(String, String)> {
    struct Cursor<'a> {
        bytes: &'a [u8],
        pos: usize,
    }
    impl<'a> Cursor<'a> {
        fn peek(&self) -> Option<u8> {
            self.bytes.get(self.pos).copied()
        }
        fn bump(&mut self) -> Option<u8> {
            let byte = self.peek()?;
            self.pos += 1;
            Some(byte)
        }
        fn skip_ws(&mut self) {
            while matches!(self.peek(), Some(b' ' | b'\t' | b'\n' | b'\r')) {
                self.pos += 1;
            }
        }
        /// Consume a JSON string (opening quote already consumed) and return its
        /// raw (still-escaped) body.
        fn string_body(&mut self) -> Option<String> {
            let start = self.pos;
            loop {
                match self.bump()? {
                    b'"' => {
                        return Some(
                            String::from_utf8_lossy(&self.bytes[start..self.pos - 1]).into_owned(),
                        );
                    }
                    b'\\' => {
                        self.bump()?;
                    }
                    _ => {}
                }
            }
        }
        fn skip_value(&mut self) -> Option<()> {
            self.skip_ws();
            match self.bump()? {
                b'"' => {
                    self.string_body()?;
                }
                b'{' => loop {
                    self.skip_ws();
                    match self.peek()? {
                        b'}' => {
                            self.pos += 1;
                            break;
                        }
                        b'"' => {
                            self.pos += 1;
                            self.string_body()?;
                            self.skip_ws();
                            if self.bump()? != b':' {
                                return None;
                            }
                            self.skip_value()?;
                            self.skip_ws();
                            if self.peek() == Some(b',') {
                                self.pos += 1;
                            }
                        }
                        _ => return None,
                    }
                },
                b'[' => loop {
                    self.skip_ws();
                    if self.peek()? == b']' {
                        self.pos += 1;
                        break;
                    }
                    self.skip_value()?;
                    self.skip_ws();
                    if self.peek() == Some(b',') {
                        self.pos += 1;
                    }
                },
                _ => {
                    while let Some(byte) = self.peek() {
                        if matches!(byte, b',' | b'}' | b']') {
                            break;
                        }
                        self.pos += 1;
                    }
                }
            }
            Some(())
        }
    }

    let mut fields = Vec::new();
    let mut cursor = Cursor {
        bytes: line.as_bytes(),
        pos: 0,
    };
    cursor.skip_ws();
    if cursor.bump() != Some(b'{') {
        return fields;
    }
    loop {
        cursor.skip_ws();
        match cursor.peek() {
            Some(b'}') | None => break,
            Some(b'"') => {
                cursor.pos += 1;
                let Some(key) = cursor.string_body() else {
                    break;
                };
                cursor.skip_ws();
                if cursor.bump() != Some(b':') {
                    break;
                }
                cursor.skip_ws();
                if cursor.peek() == Some(b'"') {
                    cursor.pos += 1;
                    let Some(value) = cursor.string_body() else {
                        break;
                    };
                    fields.push((key, value));
                } else if cursor.skip_value().is_none() {
                    break;
                }
                cursor.skip_ws();
                if cursor.peek() == Some(b',') {
                    cursor.pos += 1;
                }
            }
            _ => break,
        }
    }
    fields
}

/// Scan the mutable fields of one beads JSONL body against the registry.
/// `issue_id` labels findings; comments never enter (immutable history).
pub fn scan_beads_line(line_no: usize, line: &str, registry: &Registry) -> Vec<StaleReference> {
    let fields = top_level_string_fields(line);
    let issue_id = fields
        .iter()
        .find(|(key, _)| key == "id")
        .map(|(_, value)| value.clone())
        .unwrap_or_else(|| format!("line-{line_no}"));
    let mut stale = Vec::new();
    for (key, value) in &fields {
        if !BEAD_CURRENT_FIELDS.contains(&key.as_str()) {
            continue;
        }
        for row in registry.reserved_rows() {
            let mut names: Vec<&str> = vec![row.name.as_str()];
            names.extend(row.aliases.iter().map(String::as_str));
            for name in names {
                if contains_word(value, name) && !reserved_use_is_cited(value, &row.owner) {
                    stale.push(StaleReference {
                        class: SurfaceClass::BeadsCurrent,
                        path: format!(".beads/issues.jsonl#{issue_id}"),
                        line: line_no,
                        field: Some(key.clone()),
                        name: name.to_string(),
                        excerpt: value.chars().take(160).collect(),
                    });
                }
            }
        }
    }
    stale
}

/// Directory names never scanned: build products, VCS/hidden state, vendored
/// upstream trees, and retained e2e artifacts. The immutable epoch lab
/// (`tribunal/` at the repo root) is excluded structurally — [`scan_tree`]
/// never walks it — NOT by name, so governed nested dirs like
/// `scripts/tribunal/` stay in the census.
fn skip_dir(name: &str) -> bool {
    name.starts_with('.') || matches!(name, "target" | "vendor" | "artifacts")
}

fn walk_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut children: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    children.sort();
    for child in children {
        let name = child
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        if child.is_dir() {
            if !skip_dir(&name) {
                walk_files(&child, out);
            }
        } else {
            out.push(child);
        }
    }
}

fn rel(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

/// Scan every governed surface class under `root`. Missing directories are
/// skipped (scratch fixtures carry subsets); the census records what WAS seen.
pub fn scan_tree(root: &Path, registry: &Registry) -> Result<ScanReport, ScanError> {
    let exempt: Vec<String> = CONTRACT_DEFINITION_PATHS
        .iter()
        .map(|path| (*path).to_string())
        .collect();
    let mut stale = Vec::new();
    let mut scanned = Vec::new();

    let mut class_files: Vec<(SurfaceClass, Vec<PathBuf>)> = Vec::new();

    let mut docs = Vec::new();
    if let Ok(entries) = std::fs::read_dir(root) {
        let mut top: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
        top.sort();
        for path in top {
            if path.is_file() && path.extension().is_some_and(|ext| ext == "md") {
                docs.push(path);
            }
        }
    }
    class_files.push((SurfaceClass::Docs, docs));

    let mut source = Vec::new();
    for tree in ["crates", "tools"] {
        let mut files = Vec::new();
        walk_files(&root.join(tree), &mut files);
        source.extend(
            files
                .into_iter()
                .filter(|path| path.extension().is_some_and(|ext| ext == "rs")),
        );
    }
    class_files.push((SurfaceClass::Source, source));

    let mut ci = Vec::new();
    walk_files(&root.join("ci"), &mut ci);
    class_files.push((SurfaceClass::Ci, ci));

    let mut contracts = Vec::new();
    walk_files(&root.join("contracts"), &mut contracts);
    class_files.push((SurfaceClass::Contracts, contracts));

    let mut scripts = Vec::new();
    walk_files(&root.join("scripts"), &mut scripts);
    let mut workflows = Vec::new();
    walk_files(&root.join(".github"), &mut workflows);
    scripts.extend(workflows);
    class_files.push((SurfaceClass::Scripts, scripts));

    for (class, files) in class_files {
        for path in files {
            let rel_path = rel(root, &path);
            if exempt.contains(&rel_path) {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue; // binary or unreadable: not text vocabulary
            };
            scanned.push((class, rel_path.clone()));
            stale.extend(scan_text(class, &rel_path, &text, registry));
        }
    }

    // An absent tracker is INCONCLUSIVE, never a clean surface. This read used to be
    // `if let Ok(..)`, which skipped the whole mutable-bead-field census in silence and did
    // not even record the surface as scanned — so the scan reported a clean tree having read
    // no beads. It was compensated only by `vellum_surface_inventory`'s BeadsCurrent floor, in
    // a different file with nothing binding the two, so weakening that floor reopened the
    // vacuum here without this file changing a byte (bead `fln-y0f7` R1/R2).
    //
    // The message names the cause it is most often going to have, because a refusal that
    // blames the wrong thing is this repository's most expensive recurring failure.
    let beads = root.join(".beads/issues.jsonl");
    let text = std::fs::read_to_string(&beads).map_err(|error| ScanError::UnreadableSurface {
        class: SurfaceClass::BeadsCurrent,
        path: ".beads/issues.jsonl".to_string(),
        detail: error.to_string(),
    })?;
    scanned.push((
        SurfaceClass::BeadsCurrent,
        ".beads/issues.jsonl".to_string(),
    ));
    for (index, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        stale.extend(scan_beads_line(index + 1, line, registry));
    }

    stale.sort();
    scanned.sort();
    Ok(ScanReport { stale, scanned })
}

/// Every contract-definition exemption must exist under `root`: a dangling
/// exemption is itself a defect (typed, not silent).
pub fn validate_exemptions(root: &Path) -> Result<(), Vec<String>> {
    let missing: Vec<String> = CONTRACT_DEFINITION_PATHS
        .iter()
        .filter(|path| !root.join(path).is_file())
        .map(|path| (*path).to_string())
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(missing)
    }
}

/// A required current-vocabulary anchor: proof the rename LANDED, not merely that
/// nothing stale remains.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Anchor {
    pub path: &'static str,
    pub needle: &'static str,
    pub what: &'static str,
}

/// The positive Vellum surface inventory (bead fln-7gr6 acceptance).
pub const VELLUM_ANCHORS: &[Anchor] = &[
    Anchor {
        path: "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
        needle: "## 9. Vellum: the parser & macro engine (fln-parse, fln-syntax)",
        what: "plan §9 header",
    },
    Anchor {
        path: "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
        needle: "fln-parse        Vellum engine (§9)",
        what: "plan §21 crate-map row",
    },
    Anchor {
        path: "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
        needle: "| W4 | Vellum |",
        what: "plan §22 workstream row",
    },
    Anchor {
        path: "README.md",
        needle: "VELLUM: parser & macros",
        what: "README architecture diagram",
    },
    Anchor {
        path: "README.md",
        needle: "**Vellum** (`fln-parse`, `fln-syntax`)",
        what: "README subsystem bullet",
    },
    Anchor {
        path: "AGENTS.md",
        needle: "Crucible, Vellum, Athanor/Synod",
        what: "AGENTS subsystem enumeration",
    },
    Anchor {
        path: "ci/CLOSURE_ALLOWLIST.txt",
        needle: "reason=§21 crate map: Vellum parser engine",
        what: "closure-allowlist fln-parse label",
    },
    Anchor {
        path: "crates/fln-parse/src/lib.rs",
        needle: "Vellum's engine",
        what: "fln-parse crate charter",
    },
    Anchor {
        path: "crates/fln-syntax/src/lib.rs",
        needle: "shared by Vellum and user metaprograms",
        what: "fln-syntax crate charter",
    },
    Anchor {
        path: "crates/fln-core/src/name.rs",
        needle: "Macro-scope decoration (Vellum)",
        what: "fln-core Name doc",
    },
    Anchor {
        path: "crates/fln-core/src/diag.rs",
        needle: "Vellum rejected the source text.",
        what: "fln-core SyntaxFailure doc",
    },
];

/// Check every anchor under `root`; returns the missing ones (canonical order).
pub fn missing_anchors(root: &Path) -> Vec<&'static Anchor> {
    VELLUM_ANCHORS
        .iter()
        .filter(|anchor| {
            std::fs::read_to_string(root.join(anchor.path))
                .map(|text| !text.contains(anchor.needle))
                .unwrap_or(true)
        })
        .collect()
}

fn json_string(value: &str) -> String {
    let mut out = String::with_capacity(value.len() + 2);
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            control if (control as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", control as u32));
            }
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

/// Render the canonical, timestamp-free NDJSON report: one header row, one row
/// per scanned file, one row per stale finding, one row per anchor verdict —
/// byte-identical across reruns of an identical tree (the determinism lane
/// compares two of these directly).
pub fn render_report_ndjson(report: &ScanReport, anchors_missing: &[&Anchor]) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "{{\"schema\":{},\"kind\":\"header\",\"files_scanned\":{},\"stale_count\":{},\"anchors_missing\":{}}}\n",
        json_string(REPORT_SCHEMA),
        report.scanned.len(),
        report.stale.len(),
        anchors_missing.len(),
    ));
    for (class, path) in &report.scanned {
        out.push_str(&format!(
            "{{\"schema\":{},\"kind\":\"scanned\",\"class\":{},\"path\":{}}}\n",
            json_string(REPORT_SCHEMA),
            json_string(class.label()),
            json_string(path),
        ));
    }
    for finding in &report.stale {
        out.push_str(&format!(
            "{{\"schema\":{},\"kind\":\"stale\",\"class\":{},\"path\":{},\"line\":{},\"field\":{},\"name\":{},\"excerpt\":{}}}\n",
            json_string(REPORT_SCHEMA),
            json_string(finding.class.label()),
            json_string(&finding.path),
            finding.line,
            finding
                .field
                .as_deref()
                .map_or("null".to_string(), json_string),
            json_string(&finding.name),
            json_string(&finding.excerpt),
        ));
    }
    for anchor in VELLUM_ANCHORS {
        let missing = anchors_missing
            .iter()
            .any(|candidate| std::ptr::eq(*candidate, anchor));
        out.push_str(&format!(
            "{{\"schema\":{},\"kind\":\"anchor\",\"path\":{},\"what\":{},\"present\":{}}}\n",
            json_string(REPORT_SCHEMA),
            json_string(anchor.path),
            json_string(anchor.what),
            !missing,
        ));
    }
    out
}

/// Resolve the tree to scan: `FLN_NAMING_ROOT` (the e2e harness's scratch-fixture
/// override) or the workspace root. The override is visible in evidence (the e2e
/// records it per step) — never a hidden switch.
pub fn scan_root() -> PathBuf {
    if let Ok(root) = std::env::var("FLN_NAMING_ROOT") {
        return PathBuf::from(root);
    }
    crate::checked_workspace_root!()
}
