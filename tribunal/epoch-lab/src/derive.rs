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
use std::collections::BTreeSet;
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
    pub const MODULE_SCAN: &str = "fln.derive.module-scan/1";
    pub const EPOCH_TREE: &str = "fln.derive.epoch-tree/1";
    pub const TARGETS: &str = "fln.derive.cargo-targets/1";
    pub const ORACLE_EDGES: &str = "fln.derive.oracle-edges/1";
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
pub const MODULE_ARTIFACT_SCHEMA: &str = "fln-c1-module-inventory/1";

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
pub fn derive_module_scan(toolchain: &Path, pin: &str) -> Result<Derived<PinScan>, DeriveError> {
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

    let digest = set_digest(rules::MODULE_SCAN, &found);
    let count = found.len();
    let tests = found
        .into_iter()
        .map(|id| OfficialTest {
            id,
            kind: OfficialTestKind::ElabExpected,
        })
        .collect();
    Ok(Derived::new(
        PinScan {
            pin: pin.to_string(),
            tests,
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
pub fn render_module_artifact(scan: &Derived<PinScan>) -> String {
    let p = scan.provenance();
    let mut out = format!(
        "{MODULE_ARTIFACT_SCHEMA}\npin {}\nrule {}\nsource {}\ncount {}\ndigest {}\n",
        p.pin, p.rule, p.source, p.item_count, p.source_digest
    );
    for t in &scan.value().tests {
        out.push_str(&format!("module {}\n", t.id));
    }
    out
}

/// Verify a committed module-inventory artifact.
///
/// **This is the gate path.** It reads the artifact and recomputes the digest
/// over its own rows; it never opens the toolchain, so no gate run consults the
/// Reference. An artifact whose header disagrees with its rows — a row added,
/// removed, or edited after publication — fails here.
pub fn verify_module_artifact(text: &str) -> Result<Derived<PinScan>, DeriveError> {
    let mut pin = None;
    let mut rule = None;
    let mut source = None;
    let mut count = None;
    let mut digest = None;
    let mut modules: Vec<String> = Vec::new();

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
            "module" => modules.push(v.to_string()),
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
    let recomputed = set_digest(rules::MODULE_SCAN, &modules);
    if recomputed != digest {
        return Err(DeriveError::DigestMismatch {
            path: "<artifact>".to_string(),
            stated: digest,
            computed: recomputed,
        });
    }

    let tests = modules
        .into_iter()
        .map(|id| OfficialTest {
            id,
            kind: OfficialTestKind::ElabExpected,
        })
        .collect();
    Ok(Derived::new(
        PinScan {
            pin: pin.clone(),
            tests,
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
            assert!(r.ends_with("/1"), "{r} is not versioned");
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

/// Scan derived targets' source for oracle markers.
///
/// The edge set was supplied, which meant a real oracle path nobody declared
/// was invisible to the scan. This finds them. It reads only this repository.
pub fn derive_oracle_edges(
    root: &Path,
    targets: &[TargetScan],
) -> Result<Derived<Vec<OracleEdge>>, DeriveError> {
    let mut edges: Vec<OracleEdge> = Vec::new();
    let mut keys: Vec<String> = Vec::new();
    for t in targets {
        let p = root.join(&t.path);
        let Ok(text) = std::fs::read_to_string(&p) else {
            continue;
        };
        for (marker, capability) in ORACLE_MARKERS {
            // One edge per (target, capability): two markers for the same
            // capability in one file is one path, not two, and duplicate rows
            // would inflate every count a reader uses to judge severity.
            if text.contains(marker)
                && !edges
                    .iter()
                    .any(|e| e.target == t.name && e.capability == *capability)
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
