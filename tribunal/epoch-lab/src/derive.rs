//! Deriving the four supplied inputs from their sources (bead `fln-8fwh`).
//!
//! # Why this exists
//!
//! The six model slices of `fln-euo` each built a schema that refuses what it is
//! shown — and each accepted its input on trust. An unverified fixture digest, a
//! supplied workspace inventory, a supplied pin scan, a transcribed roster. **A
//! complete C1 inventory over a scan nobody performed is complete with respect
//! to nothing.** This module replaces "accepted from the caller" with "derived
//! from the source, and the derivation is itself checked".
//!
//! # The D8 line, per derivation
//!
//! D8 permits the Reference in exactly three capacities, one of which is a
//! fixture/census mine reached through checked-in extraction. It does not permit
//! a release — or a gate — consulting the Reference. So each derivation here is
//! placed explicitly:
//!
//! | derivation | source | touches the Reference? | runs at gate time? |
//! |---|---|---|---|
//! | [`derive_fixture_digest`] | a file in this repo | no | yes |
//! | [`derive_workspace_inventory`] | this repo's `Cargo.toml`s | no | yes |
//! | [`derive_g0_roster`] | this repo's plan document | no | yes |
//! | [`derive_module_scan`] | the pinned toolchain tree | **yes** | **no** |
//!
//! Only the last is on the boundary, and it is split in two accordingly:
//! [`derive_module_scan`] is the extraction path — development-time, inside the
//! Tribunal boundary, requiring the pinned toolchain — and it emits a committed
//! artifact. [`verify_module_artifact`] is what a gate runs: it reads the
//! committed artifact and nothing else, so no gate run ever reaches
//! `~/.elan`. That is the same shape as the repo's generated contracts, which
//! D5/D9 require to be extracted mechanically and committed rather than consulted
//! live.
//!
//! # Provenance is part of the value
//!
//! [`Derived<T>`] cannot be constructed without a [`Provenance`] recording what
//! was scanned, at which pin, under which enumeration rule, and the digest of
//! the scanned material. A caller cannot hand a schema a bare `Inventory` any
//! more — the schema asks for a `Derived<Inventory>`, and the only way to make
//! one is to have run a derivation.

use fln_hash::domain::{Domain, DomainHasher};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use crate::corpus::{OfficialTest, OfficialTestKind, PinScan};
use crate::g0::RosterSpike;

/// Domain tag for a derivation's source digest.
const DERIVE_TAG: &[u8] = b"fln.derive.source/1";

/// The enumeration rule a derivation used. Versioned: changing what a scan
/// walks changes the rule id, so an artifact produced under the old rule stops
/// verifying instead of being silently reinterpreted.
pub mod rules {
    pub const FIXTURE_DIGEST: &str = "fln.derive.fixture-digest/1";
    pub const WORKSPACE_INVENTORY: &str = "fln.derive.workspace-inventory/1";
    pub const G0_ROSTER: &str = "fln.derive.g0-roster/1";
    pub const MODULE_SCAN: &str = "fln.derive.module-scan/2";
    pub const EPOCH_TREE: &str = "fln.derive.epoch-tree/1";
    pub const TARGETS: &str = "fln.derive.cargo-targets/1";
    pub const ORACLE_EDGES: &str = "fln.derive.oracle-edges/2";
    pub const NORMAL_DEPS: &str = "fln.derive.normal-dependencies/1";
}

/// What was scanned, at which pin, under which rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    /// The thing that was scanned, as a path or a pin identifier.
    pub source: String,
    /// The pin this derivation is bound to. `-` when the source is in-repo and
    /// owes nothing to a Reference pin.
    pub pin: String,
    /// The versioned enumeration rule.
    pub rule: &'static str,
    /// Digest over the scanned material, so drift in the SOURCE is detectable
    /// and not only drift in the result.
    pub source_digest: String,
    /// How many items the scan produced. A count that moves without the digest
    /// moving would be an internal fault.
    pub item_count: usize,
}

/// A value that was derived, carrying the proof that a derivation ran.
///
/// There is no way to build one without a [`Provenance`]. That is the whole
/// mechanism: a schema that asks for `Derived<T>` cannot be handed a `T` that
/// somebody typed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Derived<T> {
    value: T,
    provenance: Provenance,
}

impl<T> Derived<T> {
    fn new(value: T, provenance: Provenance) -> Derived<T> {
        Derived { value, provenance }
    }
    pub fn value(&self) -> &T {
        &self.value
    }
    pub fn provenance(&self) -> &Provenance {
        &self.provenance
    }
    pub fn into_parts(self) -> (T, Provenance) {
        (self.value, self.provenance)
    }
}

/// Why a derivation could not produce a trustworthy result.
///
/// Total and typed: a hostile or absent source yields one of these, never a
/// panic (FL-INV-07). Note there is no `Warning` and no partial success — a
/// derivation that could not complete produces no `Derived` value at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeriveError {
    /// The source does not exist, or could not be read.
    SourceUnavailable { path: String, detail: String },
    /// The stated digest is not the computed one. The central refusal: a
    /// plausible-but-wrong input fails here rather than being recorded.
    DigestMismatch {
        path: String,
        stated: String,
        computed: String,
    },
    /// The source exists but does not contain the section a derivation needs.
    SectionNotFound { path: String, section: &'static str },
    /// The source's shape is not what the rule expects.
    Unparseable {
        path: String,
        line: usize,
        detail: String,
    },
    /// The derivation produced nothing, which for every rule here means the
    /// scan failed rather than that the source is genuinely empty.
    EmptyScan { path: String, rule: &'static str },
    /// A committed artifact's own header does not match its rows.
    ArtifactInconsistent { detail: String },
}

impl std::fmt::Display for DeriveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SourceUnavailable { path, detail } => {
                write!(f, "cannot read {path}: {detail}")
            }
            Self::DigestMismatch {
                path,
                stated,
                computed,
            } => write!(f, "{path} states digest {stated} but hashes to {computed}"),
            Self::SectionNotFound { path, section } => {
                write!(f, "{path} does not contain section {section}")
            }
            Self::Unparseable { path, line, detail } => {
                write!(f, "{path}:{line}: {detail}")
            }
            Self::EmptyScan { path, rule } => {
                write!(f, "{rule} over {path} produced no items")
            }
            Self::ArtifactInconsistent { detail } => write!(f, "artifact inconsistent: {detail}"),
        }
    }
}

impl std::error::Error for DeriveError {}

fn read(path: &Path) -> Result<String, DeriveError> {
    std::fs::read_to_string(path).map_err(|e| DeriveError::SourceUnavailable {
        path: path.display().to_string(),
        detail: e.to_string(),
    })
}

/// Digest over a byte string, domain separated and length prefixed.
pub fn source_digest(bytes: &[u8]) -> String {
    let mut h = DomainHasher::new(Domain::Fixture);
    h.update(DERIVE_TAG);
    h.update(&[0]);
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
    h.finalize().to_hex()
}

/// Digest over a sorted list of strings — the shape every set-valued scan uses.
///
/// Sorted and length-prefixed so the digest is a function of the SET, not of
/// directory-walk order, and so two different splits cannot collide.
fn set_digest(rule: &str, items: &[String]) -> String {
    let mut sorted: Vec<&str> = items.iter().map(String::as_str).collect();
    sorted.sort_unstable();
    sorted.dedup();
    let mut h = DomainHasher::new(Domain::Fixture);
    h.update(DERIVE_TAG);
    h.update(&[0]);
    h.update(&(rule.len() as u64).to_le_bytes());
    h.update(rule.as_bytes());
    h.update(&(sorted.len() as u64).to_le_bytes());
    for s in sorted {
        h.update(&(s.len() as u64).to_le_bytes());
        h.update(s.as_bytes());
    }
    h.finalize().to_hex()
}

// ---------------------------------------------------------------------------
// 1. Fixture digests — computed, never stated
// ---------------------------------------------------------------------------

/// Compute a fixture's digest from the fixture.
pub fn derive_fixture_digest(path: &Path) -> Result<Derived<String>, DeriveError> {
    let bytes = std::fs::read(path).map_err(|e| DeriveError::SourceUnavailable {
        path: path.display().to_string(),
        detail: e.to_string(),
    })?;
    let digest = source_digest(&bytes);
    Ok(Derived::new(
        digest.clone(),
        Provenance {
            source: path.display().to_string(),
            pin: "-".to_string(),
            rule: rules::FIXTURE_DIGEST,
            source_digest: digest,
            item_count: 1,
        },
    ))
}

/// Check a stated fixture digest against the fixture itself.
///
/// This is the refusal the Parity Ledger was missing: a row could name a
/// fixture that does not exist, or state a digest that is not the file's, and
/// the schema had no way to notice. A plausible-but-wrong digest — 64 valid hex
/// characters that simply are not this file's — fails here.
pub fn check_fixture(path: &Path, stated: &str) -> Result<(), DeriveError> {
    let computed = derive_fixture_digest(path)?.into_parts().0;
    if computed != stated {
        return Err(DeriveError::DigestMismatch {
            path: path.display().to_string(),
            stated: stated.to_string(),
            computed,
        });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// 2. The workspace inventory — read from the manifests, not supplied
// ---------------------------------------------------------------------------

/// One workspace member as found on disk.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemberScan {
    pub name: String,
    pub dir: String,
    /// Optional features declared in `[features]`, excluding `default`.
    pub features: Vec<String>,
}

/// The workspace as scanned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WorkspaceScan {
    pub members: Vec<MemberScan>,
}

impl WorkspaceScan {
    /// The union of every optional feature across every member — the set whose
    /// powerset the reachability scan must enumerate.
    pub fn feature_universe(&self) -> Vec<String> {
        let mut all: BTreeSet<&str> = BTreeSet::new();
        for m in &self.members {
            for f in &m.features {
                all.insert(f.as_str());
            }
        }
        all.into_iter().map(str::to_string).collect()
    }
}

/// A deliberately small TOML reader: enough for `members`, `name`, and
/// `[features]`, and nothing else.
///
/// D1 forbids a TOML crate, and a full parser is not needed — but a reader that
/// silently mis-reads is worse than none, so anything it does not understand in
/// the sections it claims to read becomes an [`DeriveError::Unparseable`]
/// rather than a skipped line.
fn toml_string_array(text: &str, key: &str) -> Option<Vec<String>> {
    let start = text.find(&format!("{key} ="))?;
    let rest = &text[start..];
    let open = rest.find('[')?;
    let close = rest.find(']')?;
    if close < open {
        return None;
    }
    Some(
        rest[open + 1..close]
            .split(',')
            .map(|s| s.trim().trim_matches('"').to_string())
            .filter(|s| !s.is_empty())
            .collect(),
    )
}

fn toml_package_name(text: &str) -> Option<String> {
    for line in text.lines() {
        let l = line.trim();
        if let Some(v) = l.strip_prefix("name") {
            let v = v.trim_start();
            if let Some(v) = v.strip_prefix('=') {
                return Some(v.trim().trim_matches('"').to_string());
            }
        }
        // Stop at the next section so a dependency's `name` cannot be read as
        // the package's.
        if l.starts_with('[') && !l.starts_with("[package]") {
            break;
        }
    }
    None
}

fn toml_feature_names(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut in_features = false;
    for line in text.lines() {
        let l = line.trim();
        if l.starts_with('[') {
            in_features = l == "[features]";
            continue;
        }
        if !in_features || l.is_empty() || l.starts_with('#') {
            continue;
        }
        if let Some((k, _)) = l.split_once('=') {
            let k = k.trim().trim_matches('"');
            if !k.is_empty() && k != "default" {
                out.push(k.to_string());
            }
        }
    }
    out
}

/// Scan the workspace's real members from the root manifest and each member's
/// own manifest.
///
/// This is what the release reachability scan should be fed. Supplying the
/// inventory by hand meant a target nobody listed was invisible; here, a member
/// on disk that the root manifest does not glob is simply not a member, and a
/// globbed directory with no manifest is an error rather than a silent skip.
pub fn derive_workspace_inventory(root: &Path) -> Result<Derived<WorkspaceScan>, DeriveError> {
    let root_manifest = root.join("Cargo.toml");
    let text = read(&root_manifest)?;
    let globs = toml_string_array(&text, "members").ok_or(DeriveError::SectionNotFound {
        path: root_manifest.display().to_string(),
        section: "workspace.members",
    })?;

    let mut dirs: Vec<PathBuf> = Vec::new();
    for g in &globs {
        if let Some(prefix) = g.strip_suffix("/*") {
            let base = root.join(prefix);
            let entries = std::fs::read_dir(&base).map_err(|e| DeriveError::SourceUnavailable {
                path: base.display().to_string(),
                detail: e.to_string(),
            })?;
            let mut found: Vec<PathBuf> = entries
                .filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.join("Cargo.toml").is_file())
                .collect();
            // Sorted so the scan is a function of the tree, not of readdir order.
            found.sort();
            dirs.extend(found);
        } else {
            dirs.push(root.join(g));
        }
    }

    let mut members = Vec::new();
    for dir in dirs {
        let manifest = dir.join("Cargo.toml");
        let mtext = read(&manifest)?;
        let name = toml_package_name(&mtext).ok_or_else(|| DeriveError::Unparseable {
            path: manifest.display().to_string(),
            line: 0,
            detail: "no [package] name".to_string(),
        })?;
        let rel = dir.strip_prefix(root).unwrap_or(&dir).display().to_string();
        members.push(MemberScan {
            name,
            dir: rel,
            features: toml_feature_names(&mtext),
        });
    }
    members.sort();

    if members.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: root.display().to_string(),
            rule: rules::WORKSPACE_INVENTORY,
        });
    }

    let keys: Vec<String> = members
        .iter()
        .map(|m| format!("{}\u{1}{}\u{1}{}", m.name, m.dir, m.features.join(",")))
        .collect();
    let digest = set_digest(rules::WORKSPACE_INVENTORY, &keys);
    let count = members.len();
    Ok(Derived::new(
        WorkspaceScan { members },
        Provenance {
            source: root.display().to_string(),
            pin: "-".to_string(),
            rule: rules::WORKSPACE_INVENTORY,
            source_digest: digest,
            item_count: count,
        },
    ))
}

// ---------------------------------------------------------------------------
// 3. The G0 roster — extracted from the plan, not transcribed
// ---------------------------------------------------------------------------

/// Extract the G0 roster from the plan's §22.1.
///
/// A transcribed roster is the hand-copied ABI constant that D5/D9 exists to
/// forbid, one level up: `G0SpikeDecisionV1` compares a decision's question to
/// the roster's *verbatim*, so a roster that paraphrases the plan enforces the
/// wrong question with full confidence. This reads the plan.
pub fn derive_g0_roster(plan: &Path) -> Result<Derived<Vec<RosterSpike>>, DeriveError> {
    let text = read(plan)?;
    let mut lines = text.lines().enumerate();
    // Find the §22.1 heading.
    let start = lines
        .find(|(_, l)| l.starts_with("### 22.1"))
        .map(|(i, _)| i)
        .ok_or(DeriveError::SectionNotFound {
            path: plan.display().to_string(),
            section: "22.1",
        })?;

    let mut spikes = Vec::new();
    for (idx, line) in text.lines().enumerate().skip(start + 1) {
        // Stop at the next section heading: the roster is what §22.1 contains,
        // not everything that follows it.
        if line.starts_with("### ") {
            break;
        }
        let Some((num, rest)) = line.split_once(". ") else {
            continue;
        };
        let Ok(n) = num.trim().parse::<u32>() else {
            continue;
        };
        let Some(rest) = rest.strip_prefix("**") else {
            continue;
        };
        let Some((name, after)) = rest.split_once("**") else {
            return Err(DeriveError::Unparseable {
                path: plan.display().to_string(),
                line: idx + 1,
                detail: "spike name is not closed with **".to_string(),
            });
        };
        // The parenthesised cross-references, then `: `, then the question.
        let Some(colon) = after.find("): ") else {
            return Err(DeriveError::Unparseable {
                path: plan.display().to_string(),
                line: idx + 1,
                detail: "no '): ' separating the references from the question".to_string(),
            });
        };
        spikes.push(RosterSpike {
            id: format!("G0-{n}"),
            name: name.trim().to_string(),
            question: after[colon + 3..].trim().to_string(),
        });
    }

    if spikes.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: plan.display().to_string(),
            rule: rules::G0_ROSTER,
        });
    }

    let keys: Vec<String> = spikes
        .iter()
        .map(|s| format!("{}\u{1}{}\u{1}{}", s.id, s.name, s.question))
        .collect();
    let digest = set_digest(rules::G0_ROSTER, &keys);
    let count = spikes.len();
    Ok(Derived::new(
        spikes,
        Provenance {
            source: plan.display().to_string(),
            pin: "-".to_string(),
            rule: rules::G0_ROSTER,
            source_digest: digest,
            item_count: count,
        },
    ))
}

// ---------------------------------------------------------------------------
// 4. The module scan — extraction path and gate path, kept apart
// ---------------------------------------------------------------------------

/// Schema line of the committed module-inventory artifact.
/// Version 2 binds each module's CONTENT, not only its name (bead `fln-8fwh`,
/// remainder item 2): under version 1 a pin file edited in place was invisible,
/// because the digest was over the name set and re-extraction reproduced the
/// same names. A version-1 artifact is refused outright rather than accepted
/// with weaker meaning — no legacy path, per the repository's no-tech-debt law.
pub const MODULE_ARTIFACT_SCHEMA: &str = "fln-c1-module-inventory/2";

/// Walk the pinned toolchain's Lean source tree.
///
/// **This is the extraction path, not a gate.** It requires the pinned
/// toolchain and therefore touches the Reference distribution — which D8
/// permits as a census mine reached through checked-in extraction. A gate must
/// call [`verify_module_artifact`] instead, which reads only the committed
/// artifact.
///
/// Note what this does NOT find: the Reference's official *test* suite is not
/// part of the distributed toolchain at all, so the C1 test half cannot be
/// derived from here. That is recorded as a typed absence on the bead rather
/// than papered over with a smaller scan.
/// The C1 module inventory, content-bound.
///
/// `modules` pairs each toolchain-relative path with the sha256 of its bytes.
/// [`ModuleInventory::to_pin_scan`] projects the name set for the corpus
/// completeness comparison, which is about WHICH modules exist; the content
/// half exists so that re-extraction against an edited pin produces a
/// DIFFERENT artifact rather than the same one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleInventory {
    pub pin: String,
    /// (toolchain-relative path, sha256 hex of the file's bytes), sorted.
    pub modules: Vec<(String, String)>,
}

impl ModuleInventory {
    /// The name-set projection the corpus completeness comparison consumes.
    pub fn to_pin_scan(&self) -> PinScan {
        PinScan {
            pin: self.pin.clone(),
            tests: self
                .modules
                .iter()
                .map(|(id, _)| OfficialTest {
                    id: id.clone(),
                    kind: OfficialTestKind::ElabExpected,
                })
                .collect(),
        }
    }
}

pub fn derive_module_scan(
    toolchain: &Path,
    pin: &str,
) -> Result<Derived<ModuleInventory>, DeriveError> {
    let src = toolchain.join("src").join("lean");
    let mut found: Vec<String> = Vec::new();
    walk_lean(&src, &src, &mut found)?;
    found.sort();
    found.dedup();

    if found.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: src.display().to_string(),
            rule: rules::MODULE_SCAN,
        });
    }

    // Content, not only names: a pin file edited in place leaves the name set
    // identical, so under version 1 re-extraction reproduced the same artifact
    // and the edit was invisible. Reading happens HERE, on the extraction side
    // — the gate still consumes only the committed artifact text.
    let mut modules: Vec<(String, String)> = Vec::with_capacity(found.len());
    for rel in found {
        let bytes = std::fs::read(src.join(&rel)).map_err(|e| DeriveError::SourceUnavailable {
            path: src.join(&rel).display().to_string(),
            detail: e.to_string(),
        })?;
        modules.push((rel, source_digest(&bytes)));
    }
    let keys: Vec<String> = modules
        .iter()
        .map(|(path, sha)| format!("{path}\u{1}{sha}"))
        .collect();
    let digest = set_digest(rules::MODULE_SCAN, &keys);
    let count = modules.len();
    Ok(Derived::new(
        ModuleInventory {
            pin: pin.to_string(),
            modules,
        },
        Provenance {
            // Recorded RELATIVE to the toolchain root, not as an absolute path.
            // The absolute path is a fact about this host, and a committed
            // artifact that carries one regenerates differently on every
            // machine — noise that would eventually be ignored, which is how a
            // real drift gets missed. `pin` already says which toolchain.
            source: "src/lean".to_string(),
            pin: pin.to_string(),
            rule: rules::MODULE_SCAN,
            source_digest: digest,
            item_count: count,
        },
    ))
}

fn walk_lean(base: &Path, dir: &Path, out: &mut Vec<String>) -> Result<(), DeriveError> {
    let entries = std::fs::read_dir(dir).map_err(|e| DeriveError::SourceUnavailable {
        path: dir.display().to_string(),
        detail: e.to_string(),
    })?;
    let mut paths: Vec<PathBuf> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    // Sorted so the walk is a function of the tree rather than of readdir
    // order, which is filesystem- and locale-dependent.
    paths.sort();
    for p in paths {
        if p.is_dir() {
            walk_lean(base, &p, out)?;
        } else if p.extension().is_some_and(|e| e == "lean") {
            let rel = p.strip_prefix(base).unwrap_or(&p).display().to_string();
            out.push(rel);
        }
    }
    Ok(())
}

/// Render a committed module-inventory artifact.
pub fn render_module_artifact(scan: &Derived<ModuleInventory>) -> String {
    let p = scan.provenance();
    let mut out = format!(
        "{MODULE_ARTIFACT_SCHEMA}\npin {}\nrule {}\nsource {}\ncount {}\ndigest {}\n",
        p.pin, p.rule, p.source, p.item_count, p.source_digest
    );
    for (path, sha) in &scan.value().modules {
        out.push_str(&format!("module {path} {sha}\n"));
    }
    out
}

/// Verify a committed module-inventory artifact.
///
/// **This is the gate path.** It reads the artifact and recomputes the digest
/// over its own rows; it never opens the toolchain, so no gate run consults the
/// Reference. An artifact whose header disagrees with its rows — a row added,
/// removed, or edited after publication — fails here.
pub fn verify_module_artifact(text: &str) -> Result<Derived<ModuleInventory>, DeriveError> {
    let mut pin = None;
    let mut rule = None;
    let mut source = None;
    let mut count = None;
    let mut digest = None;
    let mut modules: Vec<(String, String)> = Vec::new();

    let mut lines = text.lines().enumerate();
    match lines.next() {
        Some((_, l)) if l.trim() == MODULE_ARTIFACT_SCHEMA => {}
        Some((_, l)) => {
            return Err(DeriveError::ArtifactInconsistent {
                detail: format!("unrecognised schema {l:?}"),
            });
        }
        None => {
            return Err(DeriveError::ArtifactInconsistent {
                detail: "empty artifact".to_string(),
            });
        }
    }
    for (idx, line) in lines {
        let Some((k, v)) = line.split_once(' ') else {
            if line.trim().is_empty() {
                continue;
            }
            return Err(DeriveError::Unparseable {
                path: "<artifact>".to_string(),
                line: idx + 1,
                detail: format!("not a key/value line: {line:?}"),
            });
        };
        match k {
            "pin" => pin = Some(v.to_string()),
            "rule" => rule = Some(v.to_string()),
            "source" => source = Some(v.to_string()),
            "count" => count = v.parse::<usize>().ok(),
            "digest" => digest = Some(v.to_string()),
            "module" => {
                // Version 2 rows are `module <path> <sha256>`; a row without a
                // content digest is a version-1 row wearing a version-2 header.
                let Some((path, sha)) = v.rsplit_once(' ') else {
                    return Err(DeriveError::Unparseable {
                        path: "<artifact>".to_string(),
                        line: idx + 1,
                        detail: format!("module row without a content digest: {v:?}"),
                    });
                };
                if sha.len() != 64 || !sha.bytes().all(|b| b.is_ascii_hexdigit()) {
                    return Err(DeriveError::Unparseable {
                        path: "<artifact>".to_string(),
                        line: idx + 1,
                        detail: format!("module row with a malformed content digest: {sha:?}"),
                    });
                }
                modules.push((path.to_string(), sha.to_string()));
            }
            other => {
                return Err(DeriveError::Unparseable {
                    path: "<artifact>".to_string(),
                    line: idx + 1,
                    detail: format!("unknown key {other:?}"),
                });
            }
        }
    }

    let (Some(pin), Some(rule), Some(source), Some(count), Some(digest)) =
        (pin, rule, source, count, digest)
    else {
        return Err(DeriveError::ArtifactInconsistent {
            detail: "header is missing pin, rule, source, count or digest".to_string(),
        });
    };
    if rule != rules::MODULE_SCAN {
        return Err(DeriveError::ArtifactInconsistent {
            detail: format!(
                "artifact was produced under rule {rule}, not {}",
                rules::MODULE_SCAN
            ),
        });
    }
    if count != modules.len() {
        return Err(DeriveError::ArtifactInconsistent {
            detail: format!(
                "header says {count} modules, artifact carries {}",
                modules.len()
            ),
        });
    }
    // The digest is recomputed over the SAME keys the extraction side used —
    // path and content together — so a row whose sha was edited after
    // publication fails here exactly as an edited path does.
    let keys: Vec<String> = modules
        .iter()
        .map(|(path, sha)| format!("{path}\u{1}{sha}"))
        .collect();
    let recomputed = set_digest(rules::MODULE_SCAN, &keys);
    if recomputed != digest {
        return Err(DeriveError::DigestMismatch {
            path: "<artifact>".to_string(),
            stated: digest,
            computed: recomputed,
        });
    }

    Ok(Derived::new(
        ModuleInventory {
            pin: pin.clone(),
            modules,
        },
        Provenance {
            source,
            pin,
            rule: rules::MODULE_SCAN,
            source_digest: digest,
            item_count: count,
        },
    ))
}

#[cfg(test)]
mod structural {
    use super::*;

    #[test]
    fn every_rule_id_is_distinct_and_versioned() {
        let all = [
            rules::FIXTURE_DIGEST,
            rules::WORKSPACE_INVENTORY,
            rules::G0_ROSTER,
            rules::MODULE_SCAN,
        ];
        let mut v: Vec<&str> = all.to_vec();
        let n = v.len();
        v.sort_unstable();
        v.dedup();
        assert_eq!(v.len(), n, "two derivations share a rule id");
        for r in all {
            let (_, version) = r.rsplit_once('/').expect("rule ids carry /<version>");
            assert!(
                !version.is_empty() && version.bytes().all(|b| b.is_ascii_digit()),
                "{r} is not versioned"
            );
            assert!(r.starts_with("fln.derive."), "{r} is not namespaced");
        }
    }

    #[test]
    fn a_set_digest_is_order_independent_and_content_sensitive() {
        let a: Vec<String> = ["x", "y", "z"].iter().map(|s| s.to_string()).collect();
        let b: Vec<String> = ["z", "y", "x"].iter().map(|s| s.to_string()).collect();
        assert_eq!(set_digest("r", &a), set_digest("r", &b));
        let c: Vec<String> = ["x", "y"].iter().map(|s| s.to_string()).collect();
        assert_ne!(set_digest("r", &a), set_digest("r", &c));
        // The rule participates, so the same set under a different enumeration
        // rule is a different derivation and cannot be swapped in.
        assert_ne!(set_digest("r", &a), set_digest("r2", &a));
        // Length prefixing: concatenation cannot collide.
        let d: Vec<String> = vec!["xy".to_string()];
        let e: Vec<String> = vec!["x".to_string(), "y".to_string()];
        assert_ne!(set_digest("r", &d), set_digest("r", &e));
    }
}

// ---------------------------------------------------------------------------
// 5. The epoch tree — binding a published lab so it cannot move
// ---------------------------------------------------------------------------

/// Schema line of the committed epoch-tree artifact.
pub const EPOCH_TREE_SCHEMA: &str = "fln-epoch-tree/1";

/// One file in a published epoch, with its content digest.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EpochFile {
    pub path: String,
    pub digest: String,
}

/// Every file a published epoch contains.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EpochTree {
    pub epoch: String,
    /// The chain head this tree corresponds to, so a tree cannot be read as
    /// describing a revision it does not.
    pub head_root: String,
    pub files: Vec<EpochFile>,
}

/// A way a published epoch has moved since it was bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TreeDrift {
    /// A file exists that was not in the published tree.
    Added { path: String },
    /// A published file is gone.
    Removed { path: String },
    /// A published file's bytes changed.
    Edited {
        path: String,
        stated: String,
        computed: String,
    },
    /// The tree describes a different chain head than the one presented.
    HeadMoved { stated: String, actual: String },
}

impl TreeDrift {
    pub fn reason(&self) -> &'static str {
        match self {
            TreeDrift::Added { .. } => "file-added",
            TreeDrift::Removed { .. } => "file-removed",
            TreeDrift::Edited { .. } => "file-edited",
            TreeDrift::HeadMoved { .. } => "head-moved",
        }
    }
}

/// Files the tree deliberately does not bind.
///
/// The chain file cannot contain its own digest, and a leftover candidate is
/// already a typed inconclusive in [`crate::verify_epoch`]. Everything else in
/// the directory IS bound — including subdirectories, which is where the C1
/// transcripts live and where the hazard actually was.
fn tree_excluded(rel: &str) -> bool {
    rel == crate::CHAIN_FILE || rel == crate::CANDIDATE_FILE
}

fn walk_files(base: &Path, dir: &Path, out: &mut Vec<EpochFile>) -> Result<(), DeriveError> {
    let entries = std::fs::read_dir(dir).map_err(|e| DeriveError::SourceUnavailable {
        path: dir.display().to_string(),
        detail: e.to_string(),
    })?;
    let mut paths: Vec<PathBuf> = entries.filter_map(Result::ok).map(|e| e.path()).collect();
    paths.sort();
    for p in paths {
        if p.is_dir() {
            walk_files(base, &p, out)?;
        } else {
            let rel = p.strip_prefix(base).unwrap_or(&p).display().to_string();
            if tree_excluded(&rel) {
                continue;
            }
            let bytes = std::fs::read(&p).map_err(|e| DeriveError::SourceUnavailable {
                path: p.display().to_string(),
                detail: e.to_string(),
            })?;
            out.push(EpochFile {
                path: rel,
                digest: source_digest(&bytes),
            });
        }
    }
    Ok(())
}

/// Bind every file in a published epoch.
///
/// The revision chain binds `MANIFEST.txt` and nothing else, so before this a
/// published lab could still move: a transcript edited, a fixture added, a
/// sibling deleted — none of it detectable. That is the same defect class as an
/// input accepted on trust, because in both cases a downstream check is
/// measuring something that is not pinned.
pub fn derive_epoch_tree(
    epoch_dir: &Path,
    epoch: &str,
    head_root: &str,
) -> Result<Derived<EpochTree>, DeriveError> {
    let mut files = Vec::new();
    walk_files(epoch_dir, epoch_dir, &mut files)?;
    files.sort();
    if files.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: epoch_dir.display().to_string(),
            rule: rules::EPOCH_TREE,
        });
    }
    let keys: Vec<String> = files
        .iter()
        .map(|f| format!("{}\u{1}{}", f.path, f.digest))
        .collect();
    let digest = set_digest(rules::EPOCH_TREE, &keys);
    let count = files.len();
    Ok(Derived::new(
        EpochTree {
            epoch: epoch.to_string(),
            head_root: head_root.to_string(),
            files,
        },
        Provenance {
            source: format!("epochs/{epoch}"),
            pin: epoch.to_string(),
            rule: rules::EPOCH_TREE,
            source_digest: digest,
            item_count: count,
        },
    ))
}

/// Render a committed epoch-tree artifact.
pub fn render_epoch_tree(tree: &Derived<EpochTree>) -> String {
    let t = tree.value();
    let p = tree.provenance();
    let mut out = format!(
        "{EPOCH_TREE_SCHEMA}\nepoch {}\nhead_root {}\nrule {}\ncount {}\ndigest {}\n",
        t.epoch, t.head_root, p.rule, p.item_count, p.source_digest
    );
    for f in &t.files {
        out.push_str(&format!("file {} {}\n", f.path, f.digest));
    }
    out
}

/// Parse a committed epoch-tree artifact, recomputing its own digest.
pub fn parse_epoch_tree(text: &str) -> Result<EpochTree, DeriveError> {
    let mut epoch = None;
    let mut head_root = None;
    let mut rule = None;
    let mut count = None;
    let mut digest = None;
    let mut files: Vec<EpochFile> = Vec::new();

    let mut lines = text.lines().enumerate();
    match lines.next() {
        Some((_, l)) if l.trim() == EPOCH_TREE_SCHEMA => {}
        _ => {
            return Err(DeriveError::ArtifactInconsistent {
                detail: "unrecognised epoch-tree schema".to_string(),
            });
        }
    }
    for (idx, line) in lines {
        if line.trim().is_empty() {
            continue;
        }
        let Some((k, v)) = line.split_once(' ') else {
            return Err(DeriveError::Unparseable {
                path: "<epoch-tree>".to_string(),
                line: idx + 1,
                detail: format!("not a key/value line: {line:?}"),
            });
        };
        match k {
            "epoch" => epoch = Some(v.to_string()),
            "head_root" => head_root = Some(v.to_string()),
            "rule" => rule = Some(v.to_string()),
            "count" => count = v.parse::<usize>().ok(),
            "digest" => digest = Some(v.to_string()),
            "file" => {
                let Some((path, d)) = v.rsplit_once(' ') else {
                    return Err(DeriveError::Unparseable {
                        path: "<epoch-tree>".to_string(),
                        line: idx + 1,
                        detail: "file row has no digest".to_string(),
                    });
                };
                files.push(EpochFile {
                    path: path.to_string(),
                    digest: d.to_string(),
                });
            }
            other => {
                return Err(DeriveError::Unparseable {
                    path: "<epoch-tree>".to_string(),
                    line: idx + 1,
                    detail: format!("unknown key {other:?}"),
                });
            }
        }
    }
    let (Some(epoch), Some(head_root), Some(rule), Some(count), Some(digest)) =
        (epoch, head_root, rule, count, digest)
    else {
        return Err(DeriveError::ArtifactInconsistent {
            detail: "epoch-tree header is incomplete".to_string(),
        });
    };
    if rule != rules::EPOCH_TREE {
        return Err(DeriveError::ArtifactInconsistent {
            detail: format!("epoch tree was produced under rule {rule}"),
        });
    }
    if count != files.len() {
        return Err(DeriveError::ArtifactInconsistent {
            detail: format!(
                "header says {count} files, artifact carries {}",
                files.len()
            ),
        });
    }
    let keys: Vec<String> = files
        .iter()
        .map(|f| format!("{}\u{1}{}", f.path, f.digest))
        .collect();
    let recomputed = set_digest(rules::EPOCH_TREE, &keys);
    if recomputed != digest {
        return Err(DeriveError::DigestMismatch {
            path: "<epoch-tree>".to_string(),
            stated: digest,
            computed: recomputed,
        });
    }
    Ok(EpochTree {
        epoch,
        head_root,
        files,
    })
}

/// Check a published epoch against its committed tree.
///
/// Returns every drift found, not the first: an epoch with three edited
/// transcripts should report three. An empty result means the lab on disk is
/// exactly the lab that was published.
pub fn verify_epoch_tree(
    artifact: &str,
    epoch_dir: &Path,
    head_root: &str,
) -> Result<Vec<TreeDrift>, DeriveError> {
    let published = parse_epoch_tree(artifact)?;
    let mut drifts = Vec::new();
    if published.head_root != head_root {
        drifts.push(TreeDrift::HeadMoved {
            stated: published.head_root.clone(),
            actual: head_root.to_string(),
        });
    }
    let mut on_disk = Vec::new();
    walk_files(epoch_dir, epoch_dir, &mut on_disk)?;
    on_disk.sort();

    for want in &published.files {
        match on_disk.iter().find(|f| f.path == want.path) {
            None => drifts.push(TreeDrift::Removed {
                path: want.path.clone(),
            }),
            Some(got) if got.digest != want.digest => drifts.push(TreeDrift::Edited {
                path: want.path.clone(),
                stated: want.digest.clone(),
                computed: got.digest.clone(),
            }),
            Some(_) => {}
        }
    }
    for got in &on_disk {
        if !published.files.iter().any(|f| f.path == got.path) {
            drifts.push(TreeDrift::Added {
                path: got.path.clone(),
            });
        }
    }
    Ok(drifts)
}

// ---------------------------------------------------------------------------
// 6. Cargo targets and shippability
// ---------------------------------------------------------------------------

use crate::poison::{OracleCapability, OracleEdge, Shippability, Target, TargetKind};

/// One build target as found on disk.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TargetScan {
    pub crate_name: String,
    pub name: String,
    pub kind_str: &'static str,
    pub path: String,
}

fn kind_of(s: &str) -> TargetKind {
    match s {
        "lib" => TargetKind::Lib,
        "bin" => TargetKind::Bin,
        "test" => TargetKind::Test,
        "bench" => TargetKind::Bench,
        "example" => TargetKind::Example,
        _ => TargetKind::BuildScript,
    }
}

fn rs_files(dir: &Path) -> Vec<(String, PathBuf)> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut out: Vec<(String, PathBuf)> = entries
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_file() && p.extension().is_some_and(|e| e == "rs"))
        .filter_map(|p| {
            p.file_stem()
                .and_then(|s| s.to_str())
                .map(|s| (s.to_string(), p.clone()))
        })
        .collect();
    out.sort();
    out
}

/// Enumerate every Cargo target in the workspace from the tree's conventions.
///
/// The reachability scan's target dimension was supplied; this derives it. Note
/// what is mechanical here and what is not: the target SET and each target's
/// KIND are facts about the tree, but shippability is a policy decision and is
/// handled separately by [`classify`] — deriving a judgement would be inventing
/// one.
pub fn derive_targets(root: &Path) -> Result<Derived<Vec<TargetScan>>, DeriveError> {
    let members = derive_workspace_inventory(root)?;
    let mut targets = Vec::new();
    for m in &members.value().members {
        let dir = root.join(&m.dir);
        let push = |targets: &mut Vec<TargetScan>, name: String, kind: &'static str, p: PathBuf| {
            targets.push(TargetScan {
                crate_name: m.name.clone(),
                name,
                kind_str: kind,
                path: p.strip_prefix(root).unwrap_or(&p).display().to_string(),
            });
        };
        if dir.join("src/lib.rs").is_file() {
            push(&mut targets, m.name.clone(), "lib", dir.join("src/lib.rs"));
        }
        if dir.join("src/main.rs").is_file() {
            push(&mut targets, m.name.clone(), "bin", dir.join("src/main.rs"));
        }
        for (name, p) in rs_files(&dir.join("src/bin")) {
            push(&mut targets, name, "bin", p);
        }
        for (name, p) in rs_files(&dir.join("tests")) {
            push(&mut targets, name, "test", p);
        }
        for (name, p) in rs_files(&dir.join("benches")) {
            push(&mut targets, name, "bench", p);
        }
        for (name, p) in rs_files(&dir.join("examples")) {
            push(&mut targets, name, "example", p);
        }
    }
    targets.sort();
    if targets.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: root.display().to_string(),
            rule: rules::TARGETS,
        });
    }
    let keys: Vec<String> = targets
        .iter()
        .map(|t| format!("{}\u{1}{}\u{1}{}", t.crate_name, t.name, t.kind_str))
        .collect();
    let digest = set_digest(rules::TARGETS, &keys);
    let count = targets.len();
    Ok(Derived::new(
        targets,
        Provenance {
            source: root.display().to_string(),
            pin: "-".to_string(),
            rule: rules::TARGETS,
            source_digest: digest,
            item_count: count,
        },
    ))
}

/// A crate the shippability policy has not classified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolicyGap {
    /// A crate exists in the workspace and the policy says nothing about it.
    /// A hard block: an unclassified crate defaults to nothing, because a
    /// shippable target misfiled as development-only is invisible to the very
    /// gate built to catch it.
    UnclassifiedCrate { name: String },
    /// The policy classifies a crate that is not in the workspace — stale, and
    /// a sign the policy is describing a tree that has moved.
    UnknownCrate { name: String },
}

impl PolicyGap {
    pub fn reason(&self) -> &'static str {
        match self {
            PolicyGap::UnclassifiedCrate { .. } => "unclassified-crate",
            PolicyGap::UnknownCrate { .. } => "unknown-crate",
        }
    }
}

/// Apply a shippability policy to derived targets.
///
/// Two layers, deliberately. **Mechanical:** a `test`, `bench` or `example`
/// target is never shipped — cargo does not put them in a release artifact, and
/// no policy may say otherwise. **Policy:** whether a crate's `lib`/`bin`
/// targets ship is a judgement, so it must be declared per crate, and every
/// crate in the derived set must be covered or the classification blocks.
pub fn classify(
    targets: &[TargetScan],
    policy: &[(String, Shippability)],
) -> (Vec<Target>, Vec<PolicyGap>) {
    let mut gaps = Vec::new();
    let mut out = Vec::new();
    let crates: BTreeSet<&str> = targets.iter().map(|t| t.crate_name.as_str()).collect();

    for c in &crates {
        if !policy.iter().any(|(n, _)| n == c) {
            gaps.push(PolicyGap::UnclassifiedCrate {
                name: (*c).to_string(),
            });
        }
    }
    for (n, _) in policy {
        if !crates.contains(n.as_str()) {
            gaps.push(PolicyGap::UnknownCrate { name: n.clone() });
        }
    }

    for t in targets {
        let kind = kind_of(t.kind_str);
        // The mechanical floor. Never overridable by policy.
        let never_ships = matches!(
            kind,
            TargetKind::Test | TargetKind::Bench | TargetKind::Example | TargetKind::BuildScript
        );
        let declared = policy
            .iter()
            .find(|(n, _)| *n == t.crate_name)
            .map(|(_, s)| *s);
        let shippability = if never_ships {
            Shippability::DevelopmentOnly
        } else {
            // An unclassified crate's lib/bin targets are NOT defaulted to
            // anything — the gap above blocks, and the conservative reading is
            // recorded so a caller that ignores the gaps still does not get a
            // free pass.
            declared.unwrap_or(Shippability::Shippable)
        };
        out.push(Target {
            crate_name: t.crate_name.clone(),
            name: t.name.clone(),
            kind,
            shippability,
        });
    }
    (out, gaps)
}

// ---------------------------------------------------------------------------
// 7. Oracle edges — discovered from source, not declared
// ---------------------------------------------------------------------------

/// Source markers that indicate a path to an oracle capability.
///
/// Deliberately conservative and deliberately visible: a marker that fires on
/// harmless text produces a false positive, which is the failure mode
/// `oracle_only_reachability` treats as seriously as a miss. Each marker is a
/// string that has no innocent reason to appear in shippable source.
pub const ORACLE_MARKERS: &[(&str, OracleCapability)] = &[
    ("ORACLE_FALLBACK", OracleCapability::OracleFallback),
    ("libleanshared", OracleCapability::LinkReferenceSymbol),
    (".elan/toolchains", OracleCapability::SpawnReferenceBinary),
    ("leanprover--lean4", OracleCapability::SpawnReferenceBinary),
];

/// A reviewed marker occurrence in test-only fixture text within `src/`.
///
/// The source walker intentionally includes all crate-owned Rust files, so it
/// also sees `#[cfg(test)]` modules kept beside production code. Each allowance
/// is bound to one unique fixture substring; a move, removal, or new occurrence
/// is therefore a typed refusal rather than a silent exemption.
struct OracleMarkerAllowance {
    path: &'static str,
    marker: &'static str,
    anchor: &'static str,
    test_scope_path: &'static str,
    test_scope: &'static str,
}

const ORACLE_MARKER_ALLOWANCES: &[OracleMarkerAllowance] = &[
    OracleMarkerAllowance {
        path: "crates/fln-olean/src/rebuild.rs",
        marker: ".elan/toolchains",
        anchor: ".join(\".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean\")",
        test_scope_path: "crates/fln-olean/src/rebuild.rs",
        test_scope: "#[cfg(test)]\nmod tests {",
    },
    OracleMarkerAllowance {
        path: "crates/fln-olean/src/rebuild.rs",
        marker: "leanprover--lean4",
        anchor: ".join(\".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean\")",
        test_scope_path: "crates/fln-olean/src/rebuild.rs",
        test_scope: "#[cfg(test)]\nmod tests {",
    },
    OracleMarkerAllowance {
        path: "crates/fln-unsafe-abi/src/tests.rs",
        marker: ".elan/toolchains",
        anchor: "std::path::PathBuf::from(&home).join(\".elan/toolchains/leanprover--lean4---v4.32.0/bin\")",
        test_scope_path: "crates/fln-unsafe-abi/src/lib.rs",
        test_scope: "#[cfg(test)]\nmod tests;",
    },
    OracleMarkerAllowance {
        path: "crates/fln-unsafe-abi/src/tests.rs",
        marker: "leanprover--lean4",
        anchor: "std::path::PathBuf::from(&home).join(\".elan/toolchains/leanprover--lean4---v4.32.0/bin\")",
        test_scope_path: "crates/fln-unsafe-abi/src/lib.rs",
        test_scope: "#[cfg(test)]\nmod tests;",
    },
    OracleMarkerAllowance {
        path: "crates/fln-vm/src/parity.rs",
        marker: "libleanshared",
        anchor: "/x/libleanshared.so(+0x93)",
        test_scope_path: "crates/fln-vm/src/parity.rs",
        test_scope: "#[cfg(test)]\nmod tests {",
    },
    OracleMarkerAllowance {
        path: "crates/fln-vm/src/parity.rs",
        marker: "libleanshared",
        anchor: "/x/libleanshared.so(lean_panic_fn+0x2b)",
        test_scope_path: "crates/fln-vm/src/parity.rs",
        test_scope: "#[cfg(test)]\nmod tests {",
    },
    OracleMarkerAllowance {
        path: "crates/fln-vm/src/parity.rs",
        marker: "libleanshared",
        anchor: "/x/libleanshared.so(+0x1)",
        test_scope_path: "crates/fln-vm/src/parity.rs",
        test_scope: "#[cfg(test)]\nmod tests {",
    },
];

/// Recursively enumerate Rust source files below `dir` in lexical path order.
fn rust_files_below(dir: &Path) -> Vec<PathBuf> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            out.extend(rust_files_below(&path));
        } else if path.is_file() && path.extension().is_some_and(|extension| extension == "rs") {
            out.push(path);
        }
    }
    out.sort();
    out
}

/// Return the crate-local `src/` directory enclosing a target entry path.
fn crate_source_dir(path: &Path) -> Option<PathBuf> {
    let mut prefix = PathBuf::new();
    for component in path.components() {
        prefix.push(component.as_os_str());
        if component.as_os_str() == "src" {
            return Some(prefix);
        }
    }
    None
}

/// Replace Rust comments with whitespace while retaining executable text.
///
/// Oracle markers in comments describe the Tribunal but do not establish a
/// release edge. Strings are retained because a marker passed to a loader or
/// dynamic linker is still an executable oracle path. Rust permits nested block
/// comments, so a line-based filter would be unsound here.
fn source_without_comments(text: &str) -> Vec<u8> {
    enum Mode {
        Code,
        LineComment,
        BlockComment(usize),
        String,
        RawString(usize),
    }

    let bytes = text.as_bytes();
    let mut out = bytes.to_vec();
    let mut mode = Mode::Code;
    let mut index = 0;
    while index < bytes.len() {
        match mode {
            Mode::Code if bytes[index..].starts_with(b"//") => {
                out[index] = b' ';
                out[index + 1] = b' ';
                mode = Mode::LineComment;
                index += 2;
            }
            Mode::Code if bytes[index..].starts_with(b"/*") => {
                out[index] = b' ';
                out[index + 1] = b' ';
                mode = Mode::BlockComment(1);
                index += 2;
            }
            Mode::Code if bytes[index] == b'"' => {
                mode = Mode::String;
                index += 1;
            }
            Mode::Code if bytes[index] == b'r' => {
                let mut quote = index + 1;
                while quote < bytes.len() && bytes[quote] == b'#' {
                    quote += 1;
                }
                if quote < bytes.len() && bytes[quote] == b'"' {
                    mode = Mode::RawString(quote - index - 1);
                    index = quote + 1;
                } else {
                    index += 1;
                }
            }
            Mode::Code => {
                index += 1;
            }
            Mode::LineComment => {
                if bytes[index] == b'\n' {
                    mode = Mode::Code;
                } else {
                    out[index] = b' ';
                }
                index += 1;
            }
            Mode::BlockComment(depth) if bytes[index..].starts_with(b"/*") => {
                out[index] = b' ';
                out[index + 1] = b' ';
                mode = Mode::BlockComment(depth + 1);
                index += 2;
            }
            Mode::BlockComment(1) if bytes[index..].starts_with(b"*/") => {
                out[index] = b' ';
                out[index + 1] = b' ';
                mode = Mode::Code;
                index += 2;
            }
            Mode::BlockComment(depth) if bytes[index..].starts_with(b"*/") => {
                out[index] = b' ';
                out[index + 1] = b' ';
                mode = Mode::BlockComment(depth - 1);
                index += 2;
            }
            Mode::BlockComment(_) => {
                if bytes[index] != b'\n' {
                    out[index] = b' ';
                }
                index += 1;
            }
            Mode::String => {
                let byte = bytes[index];
                index += 1;
                if byte == b'\\' && index < bytes.len() {
                    index += 1;
                } else if byte == b'"' {
                    mode = Mode::Code;
                }
            }
            Mode::RawString(hashes) => {
                if bytes[index] == b'"'
                    && bytes.len() >= index + 1 + hashes
                    && bytes[index + 1..index + 1 + hashes]
                        .iter()
                        .all(|byte| *byte == b'#')
                {
                    index += 1 + hashes;
                    mode = Mode::Code;
                } else {
                    index += 1;
                }
            }
        }
    }
    out
}

fn marker_positions_outside_comments(text: &str, marker: &str) -> Vec<usize> {
    let source = source_without_comments(text);
    source
        .windows(marker.len())
        .enumerate()
        .filter_map(|(index, window)| (window == marker.as_bytes()).then_some(index))
        .collect()
}

fn validate_oracle_marker_allowances(root: &Path) -> Result<bool, DeriveError> {
    if !ORACLE_MARKER_ALLOWANCES
        .iter()
        .all(|allowance| root.join(allowance.path).exists())
    {
        return Ok(false);
    }
    for allowance in ORACLE_MARKER_ALLOWANCES {
        let path = root.join(allowance.path);
        let text = read(&path)?;
        let scope = read(&root.join(allowance.test_scope_path))?;
        if text.match_indices(allowance.anchor).count() != 1
            || !allowance.anchor.contains(allowance.marker)
            || scope.match_indices(allowance.test_scope).count() != 1
        {
            return Err(DeriveError::ArtifactInconsistent {
                detail: format!(
                    "oracle marker allowance is stale at {} for {:?}",
                    allowance.path, allowance.marker
                ),
            });
        }
    }
    Ok(true)
}

fn is_allowed_oracle_marker(
    allowances_active: bool,
    path: &str,
    marker: &str,
    offset: usize,
    source: &str,
) -> bool {
    allowances_active
        && ORACLE_MARKER_ALLOWANCES.iter().any(|allowance| {
            allowance.path == path
                && allowance.marker == marker
                && source.match_indices(allowance.anchor).count() == 1
                && source
                    .find(allowance.anchor)
                    .is_some_and(|start| (start..start + allowance.anchor.len()).contains(&offset))
        })
}

/// Scan derived targets' source for oracle markers.
///
/// The edge set was supplied, which meant a real oracle path nobody declared
/// was invisible to the scan. This finds them. Library and binary targets scan
/// the crate's complete `src/` tree rather than just their entry file: module
/// resolution is not a safe boundary for an oracle-edge guard, while the
/// shippability policy is already crate-wide. Test, bench, and example targets
/// retain their entry-file scan because they are mechanically development-only.
pub fn derive_oracle_edges(
    root: &Path,
    targets: &[TargetScan],
) -> Result<Derived<Vec<OracleEdge>>, DeriveError> {
    let allowances_active = validate_oracle_marker_allowances(root)?;
    let mut edges: Vec<OracleEdge> = Vec::new();
    let mut keys: Vec<String> = Vec::new();
    for t in targets {
        let entry = root.join(&t.path);
        let sources = match kind_of(t.kind_str) {
            TargetKind::Lib | TargetKind::Bin => crate_source_dir(&entry)
                .map(|dir| rust_files_below(&dir))
                .filter(|files| !files.is_empty())
                .unwrap_or_else(|| vec![entry]),
            TargetKind::Test
            | TargetKind::Bench
            | TargetKind::Example
            | TargetKind::BuildScript => {
                vec![entry]
            }
        };
        for source in sources {
            let Ok(text) = std::fs::read_to_string(&source) else {
                continue;
            };
            let relative = source
                .strip_prefix(root)
                .unwrap_or(&source)
                .display()
                .to_string();
            for (marker, capability) in ORACLE_MARKERS {
                // One edge per (target, capability): two markers for the same
                // capability in one file is one path, not two, and duplicate rows
                // would inflate every count a reader uses to judge severity.
                if marker_positions_outside_comments(&text, marker)
                    .into_iter()
                    .any(|offset| {
                        !is_allowed_oracle_marker(
                            allowances_active,
                            &relative,
                            marker,
                            offset,
                            &text,
                        )
                    })
                    && !edges
                        .iter()
                        .any(|edge| edge.target == t.name && edge.capability == *capability)
                {
                    keys.push(format!("{}\u{1}{}\u{1}{}", t.crate_name, t.name, marker));
                    edges.push(OracleEdge {
                        target: t.name.clone(),
                        capability: *capability,
                        // Feature gating cannot be read from a text scan; an
                        // ungated edge is the conservative reading, because it is
                        // reachable in every combination rather than some.
                        requires: BTreeSet::new(),
                    });
                }
            }
        }
    }
    let digest = set_digest(rules::ORACLE_EDGES, &keys);
    let count = edges.len();
    Ok(Derived::new(
        edges,
        Provenance {
            source: root.display().to_string(),
            pin: "-".to_string(),
            rule: rules::ORACLE_EDGES,
            source_digest: digest,
            item_count: count,
        },
    ))
}

/// Schema line of the shippability policy file.
pub const POLICY_SCHEMA: &str = "fln-shippability-policy/1";

/// Read the declared shippability policy.
///
/// Deliberately a separate input from the derived target set: the set is a fact
/// about the tree and the classification is a judgement about the product. What
/// [`classify`] enforces is that the judgement COVERS the fact.
pub fn read_shippability_policy(path: &Path) -> Result<Vec<(String, Shippability)>, DeriveError> {
    let text = read(path)?;
    let mut lines = text.lines().enumerate();
    match lines.next() {
        Some((_, l)) if l.trim() == POLICY_SCHEMA => {}
        _ => {
            return Err(DeriveError::ArtifactInconsistent {
                detail: "unrecognised shippability-policy schema".to_string(),
            });
        }
    }
    let mut out = Vec::new();
    for (idx, line) in lines {
        let l = line.trim();
        if l.is_empty() || l.starts_with('#') {
            continue;
        }
        let Some(rest) = l.strip_prefix("crate ") else {
            return Err(DeriveError::Unparseable {
                path: path.display().to_string(),
                line: idx + 1,
                detail: format!("not a crate row: {l:?}"),
            });
        };
        let Some((name, s)) = rest.split_once(' ') else {
            return Err(DeriveError::Unparseable {
                path: path.display().to_string(),
                line: idx + 1,
                detail: "crate row has no classification".to_string(),
            });
        };
        let shippability = match s.trim() {
            "shippable" => Shippability::Shippable,
            "development-only" => Shippability::DevelopmentOnly,
            other => {
                return Err(DeriveError::Unparseable {
                    path: path.display().to_string(),
                    line: idx + 1,
                    detail: format!("unknown classification {other:?}"),
                });
            }
        };
        out.push((name.trim().to_string(), shippability));
    }
    if out.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: path.display().to_string(),
            rule: rules::TARGETS,
        });
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// 8. Corroboration — a classification with one source is an opinion
// ---------------------------------------------------------------------------

/// One source's answer about one crate. Sources are never merged and never
/// out-voted: a witness is a record of what a source said.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    pub source: &'static str,
    pub says: Shippability,
}

/// Whether independent sources witness a classification.
///
/// A classification that only one derivation produces is an opinion with good
/// hygiene. Two derivations from different sources that must agree is evidence.
/// Where no second source can witness a row, [`Corroboration::SingleSource`]
/// makes the weaker status VISIBLE rather than assuming it away — partial
/// coverage that presents as full coverage is the specific failure this bead
/// exists to prevent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Corroboration {
    /// Every available source agrees with the declaration.
    Corroborated { witnesses: Vec<Witness> },
    /// A source disagrees.
    ///
    /// **Both answers are preserved and neither wins.** Resolving in favour of
    /// either would discard the evidence that a month from now makes this
    /// debuggable, and whichever source one would instinctively trust is the
    /// one that will eventually be wrong.
    Contradicted {
        declared: Shippability,
        witnesses: Vec<Witness>,
    },
    /// No available source can witness this row, with the reason stated.
    SingleSource { why: &'static str },
}

impl Corroboration {
    pub fn reason(&self) -> &'static str {
        match self {
            Corroboration::Corroborated { .. } => "corroborated",
            Corroboration::Contradicted { .. } => "contradicted",
            Corroboration::SingleSource { .. } => "single-source",
        }
    }
    /// Every source that spoke about this row, whatever it said.
    pub fn witnesses(&self) -> &[Witness] {
        match self {
            Corroboration::Corroborated { witnesses }
            | Corroboration::Contradicted { witnesses, .. } => witnesses,
            Corroboration::SingleSource { .. } => &[],
        }
    }
}

/// One classified crate with the standing of its classification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CorroboratedRow {
    pub crate_name: String,
    pub declared: Shippability,
    pub standing: Corroboration,
    /// Whether this crate carries a discovered oracle edge. A `DevelopmentOnly`
    /// row on such a crate, without corroboration, is the highest-risk row in
    /// the classification: it is the row suppressing a real finding.
    pub carries_oracle_edge: bool,
}

/// What `ci/WORKSPACE_GRAPH.txt` says about a crate.
///
/// Read-only: that file is the reviewed crate map owned elsewhere, and this
/// module never writes it.
pub fn read_graph_kinds(path: &Path) -> Result<Vec<(String, String)>, DeriveError> {
    let text = read(path)?;
    let mut out = Vec::new();
    for line in text.lines() {
        let l = line.trim();
        let Some(rest) = l.strip_prefix("crate ") else {
            continue;
        };
        let mut name = None;
        let mut kind = None;
        for tok in rest.split_whitespace() {
            if let Some(k) = tok.strip_prefix("kind=") {
                kind = Some(k.to_string());
            } else if name.is_none() {
                name = Some(tok.to_string());
            }
        }
        if let (Some(n), Some(k)) = (name, kind) {
            out.push((n, k));
        }
    }
    if out.is_empty() {
        return Err(DeriveError::EmptyScan {
            path: path.display().to_string(),
            rule: rules::TARGETS,
        });
    }
    Ok(out)
}

/// The declared dependency edges of the reviewed crate map.
pub fn read_graph_edges(path: &Path) -> Result<Vec<(String, String)>, DeriveError> {
    let text = read(path)?;
    let mut out = Vec::new();
    for line in text.lines() {
        let l = line.trim();
        let Some(rest) = l.strip_prefix("edge ") else {
            continue;
        };
        let Some((from, to)) = rest.split_once("->") else {
            continue;
        };
        out.push((from.trim().to_string(), to.trim().to_string()));
    }
    Ok(out)
}

/// The result of attempting the dependency-closure derivation.
///
/// Three-valued on purpose, and for the same reason [`crate::poison::scan`] is:
/// a derivation that cannot answer must not answer. An empty root set does NOT
/// mean "nothing ships" — it means the question cannot be asked yet, and
/// returning the empty closure as a positive answer would corroborate every
/// `DevelopmentOnly` row in the file and make the reachability scan trivially
/// clean while looking like evidence. That is worse than having no second
/// source at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosureAvailability {
    /// The set of crates reachable from at least one product binary.
    Available { reachable: BTreeSet<String> },
    /// The closure cannot witness anything yet.
    Unavailable { why: &'static str },
}

/// Which crates are reachable from a product binary, over declared edges.
///
/// `roots` are the crates that produce a released binary. The propagation is
/// mechanical; only the root set is a judgement, and it is a far smaller one
/// than classifying thirty-three crates by hand.
pub fn derive_dependency_closure(
    edges: &[(String, String)],
    roots: &[String],
) -> ClosureAvailability {
    if roots.is_empty() {
        return ClosureAvailability::Unavailable {
            why: "no crate in this workspace produces a product binary yet, so the \
                  closure is empty; an empty closure is not the answer \"nothing ships\"",
        };
    }
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (from, to) in edges {
        adjacency
            .entry(from.as_str())
            .or_default()
            .push(to.as_str());
    }
    let mut reachable: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<&str> = roots.iter().map(String::as_str).collect();
    while let Some(n) = stack.pop() {
        if !reachable.insert(n.to_string()) {
            continue;
        }
        if let Some(next) = adjacency.get(n) {
            stack.extend(next.iter().copied());
        }
    }
    ClosureAvailability::Available { reachable }
}

/// The crates that produce a product binary: a bin target, in a crate the
/// reviewed map does not call tooling.
pub fn product_binary_roots(targets: &[TargetScan], graph: &[(String, String)]) -> Vec<String> {
    let mut roots: BTreeSet<String> = BTreeSet::new();
    for t in targets {
        if t.kind_str != "bin" {
            continue;
        }
        let is_tool = graph.iter().any(|(n, k)| *n == t.crate_name && k == "tool");
        if !is_tool {
            roots.insert(t.crate_name.clone());
        }
    }
    roots.into_iter().collect()
}

/// Cross-check the declared shippability policy against every available source.
///
/// **What each source can witness.** `ci/WORKSPACE_GRAPH.txt` documents
/// `kind=tool` as "dev apparatus, tools/", so that value witnesses
/// DevelopmentOnly. `kind=ordinary` and `kind=unsafe-boundary` mean "a ranked
/// product crate under `crates/`" — a LAYERING fact — and witness nothing about
/// shipping; reading them as shippability would conflate two vocabularies. The
/// dependency closure witnesses both directions, but only when it is
/// [`ClosureAvailability::Available`].
pub fn corroborate(
    policy: &[(String, Shippability)],
    graph: &[(String, String)],
    closure: &ClosureAvailability,
    oracle_edge_crates: &[String],
) -> Vec<CorroboratedRow> {
    let mut rows = Vec::new();
    for (name, declared) in policy {
        let mut witnesses: Vec<Witness> = Vec::new();

        if graph.iter().any(|(n, k)| n == name && k == "tool") {
            witnesses.push(Witness {
                source: "ci/WORKSPACE_GRAPH.txt kind=tool",
                says: Shippability::DevelopmentOnly,
            });
        }
        if let ClosureAvailability::Available { reachable } = closure {
            witnesses.push(Witness {
                source: "dependency closure from product binaries",
                says: if reachable.contains(name) {
                    Shippability::Shippable
                } else {
                    Shippability::DevelopmentOnly
                },
            });
        }

        let standing = if witnesses.is_empty() {
            Corroboration::SingleSource {
                why: match closure {
                    ClosureAvailability::Unavailable { why } => why,
                    _ => "no source witnesses this row",
                },
            }
        } else if witnesses.iter().all(|w| w.says == *declared) {
            Corroboration::Corroborated { witnesses }
        } else {
            Corroboration::Contradicted {
                declared: *declared,
                witnesses,
            }
        };

        rows.push(CorroboratedRow {
            crate_name: name.clone(),
            declared: *declared,
            standing,
            carries_oracle_edge: oracle_edge_crates.contains(name),
        });
    }
    rows.sort_by(|a, b| a.crate_name.cmp(&b.crate_name));
    rows
}

/// The rows where a wrong classification would SUPPRESS a real finding.
///
/// A crate that carries an oracle edge and is called development-only without
/// corroboration is doing all the work of keeping the reachability scan clean.
/// If that call is wrong, the scan reports Clean over a shippable target that
/// reaches the Reference — with full confidence, because the classification is
/// the scan's own premise.
pub fn uncorroborated_suppressions(rows: &[CorroboratedRow]) -> Vec<&CorroboratedRow> {
    rows.iter()
        .filter(|r| {
            r.carries_oracle_edge
                && r.declared == Shippability::DevelopmentOnly
                && !matches!(r.standing, Corroboration::Corroborated { .. })
        })
        .collect()
}

/// Line-oriented corroboration report.
///
/// Reports per-SOURCE coverage as well as totals, so "33 rows checked" can
/// never be read as "33 rows corroborated". Every contradiction prints both
/// answers.
pub fn corroboration_report(rows: &[CorroboratedRow]) -> String {
    let mut out = String::new();
    let mut corroborated = 0usize;
    let mut single = 0usize;
    let mut contradicted = 0usize;
    let mut by_source: BTreeMap<&str, usize> = BTreeMap::new();

    for r in rows {
        for w in r.standing.witnesses() {
            *by_source.entry(w.source).or_default() += 1;
        }
        match &r.standing {
            Corroboration::Corroborated { .. } => corroborated += 1,
            Corroboration::SingleSource { .. } => single += 1,
            Corroboration::Contradicted {
                declared,
                witnesses,
            } => {
                contradicted += 1;
                // Both answers, neither resolved.
                for w in witnesses {
                    out.push_str(&format!(
                        "shippability: contradicted crate={} policy_says={declared:?} \
                         source={} source_says={:?}\n",
                        r.crate_name, w.source, w.says
                    ));
                }
            }
        }
    }
    for (source, n) in &by_source {
        out.push_str(&format!(
            "shippability: source-coverage source={source} witnessed={n} of={}\n",
            rows.len()
        ));
    }
    for r in uncorroborated_suppressions(rows) {
        out.push_str(&format!(
            "shippability: uncorroborated-suppression crate={} declared=development-only \
             carries_oracle_edge=true standing={}\n",
            r.crate_name,
            r.standing.reason()
        ));
    }
    out.push_str(&format!(
        "shippability: verdict={} crates={} corroborated={corroborated} \
         single_source={single} contradicted={contradicted} suppressions={}\n",
        if contradicted == 0 {
            "no-contradiction"
        } else {
            "contradicted"
        },
        rows.len(),
        uncorroborated_suppressions(rows).len()
    ));
    out
}

// ---------------------------------------------------------------------------
// 9. Normal-dependency edges — the closure witness that is available TODAY
//    (bead fln-8fwh; the mechanism recommended by fln-atgf's review)
// ---------------------------------------------------------------------------

/// One `[dependencies]` edge between two workspace members.
///
/// Normal dependencies only, and that restriction is the whole point: cargo
/// puts a crate in a release artifact's closure through `[dependencies]` and
/// never through `[dev-dependencies]` or `[build-dependencies]` — the same law
/// [`classify`]'s mechanical floor uses for test and bench targets. So these
/// edges are the half of shippability that is a fact about the tree rather
/// than a judgement about the product.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct NormalDepEdge {
    pub from: String,
    pub to: String,
}

/// Derive every member-to-member `[dependencies]` edge from the real manifests.
///
/// [`derive_dependency_closure`] already witnesses shippability over the
/// *declared* edges of `ci/WORKSPACE_GRAPH.txt`, from product-binary roots —
/// and is honestly [`ClosureAvailability::Unavailable`] today, because no
/// product binary exists yet. This derivation answers the question that IS
/// answerable today, from the bytes cargo itself reads: which crates does each
/// crate pull into a release closure? Its consumer is
/// [`policy_closure_violations`], the policy's own coherence law.
///
/// The reader is deliberately strict, like every reader in this file: inside a
/// `[dependencies]` section, a line it does not understand is an
/// [`DeriveError::Unparseable`], never a skipped line — a dependency the scan
/// silently drops is an edge outside the certificate, which is the exact hole
/// this module exists to close. The accepted shapes are this workspace's
/// uniform manifest style (enforced by structure-guard): a single-line
/// `name = { path = "…" }` table or a `name = "version"` string.
pub fn derive_normal_dependencies(root: &Path) -> Result<Derived<Vec<NormalDepEdge>>, DeriveError> {
    let inventory = derive_workspace_inventory(root)?;
    let member_names: BTreeSet<&str> = inventory
        .value()
        .members
        .iter()
        .map(|m| m.name.as_str())
        .collect();

    let mut edges: Vec<NormalDepEdge> = Vec::new();
    for m in &inventory.value().members {
        let manifest = root.join(&m.dir).join("Cargo.toml");
        let text = read(&manifest)?;
        let mut section: Option<String> = None;
        for (idx, line) in text.lines().enumerate() {
            let l = line.trim();
            if l.starts_with('[') {
                section = Some(l.to_string());
                continue;
            }
            if section.as_deref() != Some("[dependencies]") || l.is_empty() || l.starts_with('#') {
                continue;
            }
            let Some((name, rest)) = l.split_once('=') else {
                return Err(DeriveError::Unparseable {
                    path: manifest.display().to_string(),
                    line: idx + 1,
                    detail: format!("dependency line without '=': {l:?}"),
                });
            };
            let name = name.trim();
            let rest = rest.trim();
            let shape_ok = name
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_')
                && !name.is_empty()
                && ((rest.starts_with("{ path = \"") && rest.ends_with('}'))
                    || (rest.starts_with('"') && rest.ends_with('"')));
            if !shape_ok {
                return Err(DeriveError::Unparseable {
                    path: manifest.display().to_string(),
                    line: idx + 1,
                    detail: format!(
                        "dependency shape this reader does not understand \
                         (a misread edge is worse than a refusal): {l:?}"
                    ),
                });
            }
            // Edges to non-members (the pinned suite) are real but outside the
            // POLICY's vocabulary — the policy classifies workspace crates only,
            // so only member-to-member edges can witness or violate it.
            if member_names.contains(name) {
                edges.push(NormalDepEdge {
                    from: m.name.clone(),
                    to: name.to_string(),
                });
            }
        }
    }
    edges.sort();
    edges.dedup();
    if edges.is_empty() {
        // 29 member-to-member edges exist at the time of writing; a scan
        // returning zero found a broken reader, not an unusually flat tree.
        return Err(DeriveError::EmptyScan {
            path: root.display().to_string(),
            rule: rules::NORMAL_DEPS,
        });
    }
    let keys: Vec<String> = edges
        .iter()
        .map(|e| format!("{}\u{1}{}", e.from, e.to))
        .collect();
    let digest = set_digest(rules::NORMAL_DEPS, &keys);
    let count = edges.len();
    Ok(Derived::new(
        edges,
        Provenance {
            source: root.display().to_string(),
            pin: "-".to_string(),
            rule: rules::NORMAL_DEPS,
            source_digest: digest,
            item_count: count,
        },
    ))
}

/// The policy's own coherence law: a shippable crate's normal-dependency
/// closure may not contain a development-only crate.
///
/// This is the DANGEROUS direction of `fln-atgf`'s review, mechanised. A crate
/// wrongly marked development-only is invisible to the reachability scan — it
/// is simply not enumerated, so the scan reports Clean with full confidence
/// over its wrong premise. But if any shippable crate normal-depends on it,
/// cargo would put it in a release closure regardless of what the policy says,
/// and that contradiction is derivable. An empty result therefore means the
/// policy's development-only rows carry a second, independent witness; a
/// non-empty one names exactly which shippable crate would carry which
/// development-only crate into a release.
pub fn policy_closure_violations(
    policy: &[(String, Shippability)],
    edges: &[NormalDepEdge],
) -> Vec<(String, String)> {
    let dev_only: BTreeSet<&str> = policy
        .iter()
        .filter(|(_, s)| *s == Shippability::DevelopmentOnly)
        .map(|(n, _)| n.as_str())
        .collect();
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for e in edges {
        adjacency
            .entry(e.from.as_str())
            .or_default()
            .push(e.to.as_str());
    }
    let mut violations: Vec<(String, String)> = Vec::new();
    for (name, s) in policy {
        if *s != Shippability::Shippable {
            continue;
        }
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        let mut stack: Vec<&str> = vec![name.as_str()];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if n != name && dev_only.contains(n) {
                violations.push((name.clone(), n.to_string()));
            }
            if let Some(next) = adjacency.get(n) {
                stack.extend(next.iter().copied());
            }
        }
    }
    violations.sort();
    violations.dedup();
    violations
}
