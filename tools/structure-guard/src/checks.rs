//! The structural checks. Each violation is a `Finding` with a stable code:
//!
//! * `FLN-STRUCT-001` crate on disk not declared in the graph file
//! * `FLN-STRUCT-002` declared crate missing on disk
//! * `FLN-STRUCT-003` package name does not match its directory name
//! * `FLN-STRUCT-004` edition is not 2024
//! * `FLN-STRUCT-005` dependency edge present in a manifest but not acknowledged
//! * `FLN-STRUCT-006` acknowledged edge absent from the manifests (stale)
//! * `FLN-STRUCT-007` edge violates strict downward layering / tool-direction law
//! * `FLN-STRUCT-008` prohibited transitive dependency path exists (D3)
//! * `FLN-STRUCT-009` direct dependency outside an `allow-direct` covenant
//! * `FLN-STRUCT-010` external dependency outside the closed universe (D1)
//! * `FLN-STRUCT-011` ordinary/tool crate root missing `#![forbid(unsafe_code)]`
//! * `FLN-STRUCT-012` unsafe-boundary crate root lint wrong (needs `deny`, not `forbid`)
//! * `FLN-STRUCT-013` unledgered `#[allow(unsafe_code)]` site
//! * `FLN-STRUCT-014` stale or mismatched unsafe-ledger row
//! * `FLN-STRUCT-015` line-count covenant exceeded
//! * `FLN-STRUCT-016` parse/shape error (graph file, ledger, manifest, missing roots)
//! * `FLN-STRUCT-017` crate location or naming inconsistent with its declared kind
//! * `FLN-STRUCT-021` root workspace/target graph differs from the constrained contract
//! * `FLN-STRUCT-022` unsafe-boundary export violates fail-closed D3 law (b)
//! * `FLN-STRUCT-023` dependency path does not resolve to its acknowledged package
//! * `FLN-STRUCT-024` reviewed graph weakens a constitutional baseline rule
//! * `FLN-STRUCT-025` expansion covenant violation (macro-using boundary crate whose
//!   fully expanded surface exports, synthesizes an unsafe allowance, or cannot be
//!   deterministically expanded — incl. feature-conditional unknowns)
//! * `FLN-STRUCT-026` C-ABI export covenant violation (§6.5, bead franken_lean-83r):
//!   the census ⇄ `ci/ABI_EXPORT_STATUS.txt` ⇄ `export_name`-site join is broken —
//!   an unclassified symbol, a stale or lying status row, an export outside
//!   `fln-unsafe-abi`, or an unextractable symbol string (fail closed)
//! * `FLN-STRUCT-027` a governed file could not be read as UTF-8, so structural
//!   authority over it is *inconclusive* rather than clean. It is reported per file so
//!   that one unreadable input cannot mask every other finding in the run, and it is
//!   still a finding — never a pass — because the covenant, lint posture, or ledger
//!   evidence that file carries was not established (FL-INV-07).
//! * `FLN-STRUCT-028` governed inputs changed during the scan, so the verdict is
//!   inconclusive rather than being attached to a hybrid source root.
//! * `FLN-STRUCT-029` the effective compiler identity disagrees with the complete
//!   `SUITE.lock` compiler contract, so compiler authority is inconclusive.
//! * `FLN-STRUCT-030` kernel generated authority is not source-callsite closed:
//!   a project-defined macro, unreviewed macro invocation, procedural attribute, or
//!   derive outside the exact compiler-builtin inventory could contribute checking
//!   logic without a reviewed, LOC-counted source mapping.
//! * `FLN-STRUCT-031` an active SUITE.lock checkout or its commit identity cannot be
//!   verified, so dependency-closure authority is inconclusive rather than clean.
//! * `FLN-STRUCT-032` the canonical pin/target inventory is malformed, stale, or not
//!   the exact bijective join of current `SUITE.lock` facts and reviewed policy.
//! * `FLN-STRUCT-033` pin/target inventory authority is inconclusive: a publication
//!   candidate remains, a governed source is unavailable, or a bounded publication
//!   operation could not establish one complete generation.
//! * `FLN-STRUCT-034` kernel-contract ownership publication is inconclusive because an
//!   interrupted/competing `.candidate` exists or its absence cannot be established.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use crate::boundary_api;
use crate::export_status;
use crate::graph::{self, CrateKind, GraphFile};
use crate::ledger::{self, AllowSite};
use crate::manifest::{self, Manifest};
use crate::report::fnv1a64;
use crate::{
    ABI_CENSUS_FILE, ALLOWLIST_FILE, BOUNDARY_API_FILE, EXPORT_STATUS_FILE, EXPORTING_CRATE,
    GRAPH_FILE, LEDGER_FILE, LOCK_FILE, SUITE_LOCK_FILE, TOOLCHAIN_FILE,
};

#[derive(Debug)]
pub struct Finding {
    pub code: &'static str,
    pub path: String,
    pub detail: String,
}

#[derive(Debug)]
pub struct RunOutcome {
    pub findings: Vec<Finding>,
    pub crate_count: usize,
    pub edge_count: usize,
    pub graph_digest: u64,
    pub root_identity: String,
    pub governed_root_before: u64,
    pub governed_root_after: u64,
    pub traversal: TraversalFacts,
    pub authority: Authority,
    pub authority_inventory: AuthorityInventory,
    pub compiler_identity: CompilerIdentity,
    pub admitted_environment: AdmittedEnvironment,
}

/// Whether the run established authority over its complete governed input closure.
///
/// A structural violation over a complete closure is an authoritative failure. An
/// unreadable input, compiler-identity ambiguity, or a root that changed during the
/// scan is different: it is inconclusive under FL-INV-07 and must never be rendered
/// as either a clean pass or an authoritative rejection.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Authority {
    Complete,
    Incomplete,
}

impl Authority {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Complete => "complete",
            Self::Incomplete => "incomplete",
        }
    }
}

/// Conservation facts for the dependency-free governed-input traversal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraversalFacts {
    pub directories_visited: usize,
    pub files_discovered: usize,
    pub files_scanned: usize,
    pub files_skipped_unreadable: usize,
}

impl TraversalFacts {
    pub fn count_rule_holds(&self) -> bool {
        self.files_scanned
            .checked_add(self.files_skipped_unreadable)
            .is_some_and(|total| total == self.files_discovered)
    }
}

/// Exact cardinalities behind the package/target/feature/target-triple authority axes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AuthorityInventory {
    pub packages: usize,
    pub targets: usize,
    pub features: usize,
    pub target_triples: usize,
}

/// Runtime compiler facts, compared against the mechanically parsed `SUITE.lock` rows.
///
/// Paths are deliberately not emitted: the public evidence needs identity, not a home
/// directory or other host-specific path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompilerIdentity {
    pub source: &'static str,
    pub channel: Option<String>,
    pub release: Option<String>,
    pub commit: Option<String>,
    pub host: Option<String>,
    pub contract_declared: bool,
    pub configuration_match: bool,
    pub contract_match: bool,
}

/// Names-only environment evidence. Values are never retained or rendered because
/// compiler-related environment variables can contain credentials or host paths.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdmittedEnvironment {
    pub policy: &'static str,
    pub admitted_names: Vec<String>,
    pub compiler_override_names: Vec<String>,
}

impl RunOutcome {
    pub fn verdict(&self) -> &'static str {
        if self.authority == Authority::Incomplete {
            "inconclusive"
        } else if self.findings.is_empty() {
            "pass"
        } else {
            "fail"
        }
    }

    pub fn exit_code(&self) -> u8 {
        match self.verdict() {
            "pass" => 0,
            "fail" => 1,
            "inconclusive" => 3,
            _ => 2,
        }
    }
}

#[derive(Clone, Debug)]
struct GovernedSnapshot {
    digest: u64,
    directories_visited: usize,
    files_discovered: usize,
    files_scanned: usize,
    unreadable: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
struct RustcProbe {
    source: &'static str,
    release: Option<String>,
    commit: Option<String>,
    host: Option<String>,
}

const GOVERNED_ROOT_FILES: [&str; 4] = ["Cargo.toml", LOCK_FILE, SUITE_LOCK_FILE, TOOLCHAIN_FILE];
const GOVERNED_ROOT_DIRS: [&str; 4] = ["ci", "contracts", "crates", "tools"];
pub const AUTHORITY_COUNT_RULE: &str = "files_scanned+files_skipped_unreadable=files_discovered";

fn fnv_update(mut state: u64, bytes: &[u8]) -> u64 {
    for byte in bytes {
        state ^= u64::from(*byte);
        state = state.wrapping_mul(0x0000_0100_0000_01b3);
    }
    state
}

fn bind_field(state: &mut u64, bytes: &[u8]) {
    *state = fnv_update(*state, &(bytes.len() as u64).to_le_bytes());
    *state = fnv_update(*state, bytes);
}

fn normalized_relative(root: &Path, path: &Path) -> Result<String, String> {
    path.strip_prefix(root)
        .map_err(|_| {
            format!(
                "{} escaped canonical root {}",
                path.display(),
                root.display()
            )
        })?
        .to_str()
        .map(|relative| relative.replace('\\', "/"))
        .ok_or_else(|| format!("governed path is not UTF-8: {}", path.display()))
}

fn collect_governed_entries(
    root: &Path,
    start: &Path,
    entries: &mut Vec<(String, u8, Vec<u8>)>,
    snapshot: &mut GovernedSnapshot,
) {
    let rel = match normalized_relative(root, start) {
        Ok(rel) => rel,
        Err(detail) => {
            snapshot
                .unreadable
                .push((start.display().to_string(), detail));
            return;
        }
    };
    let metadata = match fs::symlink_metadata(start) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            entries.push((rel, b'm', Vec::new()));
            return;
        }
        Err(error) => {
            snapshot.unreadable.push((
                rel.clone(),
                format!("cannot inspect governed input: {error}"),
            ));
            entries.push((rel, b'u', Vec::new()));
            return;
        }
    };
    let file_type = metadata.file_type();
    if file_type.is_symlink() {
        let target = match fs::read_link(start) {
            Ok(target) => target.to_string_lossy().as_bytes().to_vec(),
            Err(error) => {
                snapshot.unreadable.push((
                    rel.clone(),
                    format!("cannot read governed symlink: {error}"),
                ));
                Vec::new()
            }
        };
        entries.push((rel, b'l', target));
        return;
    }
    if file_type.is_file() {
        snapshot.files_discovered += 1;
        match fs::read(start) {
            Ok(bytes) => {
                snapshot.files_scanned += 1;
                entries.push((rel, b'f', bytes));
            }
            Err(error) => {
                snapshot
                    .unreadable
                    .push((rel.clone(), format!("cannot read governed input: {error}")));
                entries.push((rel, b'u', Vec::new()));
            }
        }
        return;
    }
    if !file_type.is_dir() {
        entries.push((rel, b'o', Vec::new()));
        return;
    }

    snapshot.directories_visited += 1;
    entries.push((rel.clone(), b'd', Vec::new()));
    let mut children = match fs::read_dir(start) {
        Ok(children) => match children.collect::<Result<Vec<_>, _>>() {
            Ok(children) => children,
            Err(error) => {
                snapshot.unreadable.push((
                    rel,
                    format!("cannot enumerate governed directory completely: {error}"),
                ));
                return;
            }
        },
        Err(error) => {
            snapshot
                .unreadable
                .push((rel, format!("cannot read governed directory: {error}")));
            return;
        }
    };
    children.sort_by_key(|entry| entry.file_name());
    for child in children {
        collect_governed_entries(root, &child.path(), entries, snapshot);
    }
}

fn governed_snapshot(root: &Path) -> GovernedSnapshot {
    let mut snapshot = GovernedSnapshot {
        digest: 0,
        directories_visited: 0,
        files_discovered: 0,
        files_scanned: 0,
        unreadable: Vec::new(),
    };
    let mut entries = Vec::new();
    for rel in GOVERNED_ROOT_FILES {
        collect_governed_entries(root, &root.join(rel), &mut entries, &mut snapshot);
    }
    for rel in GOVERNED_ROOT_DIRS {
        collect_governed_entries(root, &root.join(rel), &mut entries, &mut snapshot);
    }
    entries.sort_by(|left, right| (&left.0, left.1).cmp(&(&right.0, right.1)));
    let mut digest = fnv1a64(b"fln.structure-guard.governed-root/1\0");
    for (path, kind, bytes) in entries {
        bind_field(&mut digest, path.as_bytes());
        bind_field(&mut digest, &[kind]);
        bind_field(&mut digest, &bytes);
    }
    snapshot.digest = digest;
    snapshot
}

fn parse_rustc_verbose(stdout: &[u8], source: &'static str) -> RustcProbe {
    let text = String::from_utf8_lossy(stdout);
    let mut release = None;
    let mut commit = None;
    let mut host = None;
    for line in text.lines() {
        let Some((key, value)) = line.split_once(':') else {
            continue;
        };
        let value = value.trim();
        match key.trim() {
            "release" if !value.is_empty() => release = Some(value.to_string()),
            "commit-hash" if !value.is_empty() => commit = Some(value.to_ascii_lowercase()),
            "host" if !value.is_empty() => host = Some(value.to_string()),
            _ => {}
        }
    }
    RustcProbe {
        source,
        release,
        commit,
        host,
    }
}

fn effective_rustc_probe() -> RustcProbe {
    static PROBE: OnceLock<RustcProbe> = OnceLock::new();
    PROBE
        .get_or_init(|| {
            // Never execute the program named by ambient RUSTC. The evidence runner's
            // sealed lane supplies an exact RUSTC path, but a direct invocation may not:
            // treating that string as an executable would turn identity validation into
            // arbitrary command execution. Probe the fixed PATH name and compare an
            // override by canonical file identity below.
            match Command::new("rustc").arg("-Vv").output() {
                Ok(output) if output.status.success() => {
                    parse_rustc_verbose(&output.stdout, "PATH")
                }
                _ => RustcProbe {
                    source: "PATH",
                    release: None,
                    commit: None,
                    host: None,
                },
            }
        })
        .clone()
}

fn resolve_path_executable(program: &OsStr) -> Option<PathBuf> {
    let path = Path::new(program);
    if path.components().count() > 1 {
        return fs::canonicalize(path)
            .ok()
            .filter(|candidate| candidate.is_file());
    }
    std::env::var_os("PATH").and_then(|search| {
        std::env::split_paths(&search).find_map(|directory| {
            fs::canonicalize(directory.join(path))
                .ok()
                .filter(|candidate| candidate.is_file())
        })
    })
}

fn rustc_override_matches_path() -> bool {
    let Some(override_program) = std::env::var_os("RUSTC") else {
        return true;
    };
    if override_program.is_empty() {
        return false;
    }
    resolve_path_executable(OsStr::new("rustc"))
        .zip(resolve_path_executable(&override_program))
        .is_some_and(|(from_path, from_override)| from_path == from_override)
}

fn compiler_identity(root: &Path) -> CompilerIdentity {
    let expected = fs::read_to_string(root.join(SUITE_LOCK_FILE))
        .ok()
        .and_then(|text| crate::lockfile::parse_suite_lock(&text).ok());
    let probe = effective_rustc_probe();
    let channel = expected.as_ref().map(|lock| lock.rust_nightly.clone());
    let expected_release = expected
        .as_ref()
        .map(|lock| lock.rust_release.as_str())
        .filter(|release| !release.is_empty());
    let expected_commit = expected
        .as_ref()
        .map(|lock| lock.rust_commit.as_str())
        .filter(|commit| !commit.is_empty());
    let contract_declared = expected_release.is_some()
        && expected_commit.is_some()
        && expected
            .as_ref()
            .is_some_and(|lock| !lock.targets.is_empty());
    let host_is_declared = expected.as_ref().is_some_and(|lock| {
        probe
            .host
            .as_ref()
            .is_some_and(|host| lock.targets.contains(host))
    });
    // The guard invokes the PATH compiler directly for the identity probe and
    // strips Cargo/rustc tuning variables from expansion subprocesses. Those
    // ambient names are still disclosed in the robot envelope, but cannot
    // change the governed computation. RUSTC is the one identity-bearing
    // alias: require it to resolve to the same file as PATH's rustc.
    let configuration_match = rustc_override_matches_path();
    let contract_match = expected_release
        .zip(expected_commit)
        .is_some_and(|(release, commit)| {
            probe.release.as_deref() == Some(release)
                && probe.commit.as_deref() == Some(commit)
                && host_is_declared
                && configuration_match
        });
    CompilerIdentity {
        source: probe.source,
        channel,
        release: probe.release,
        commit: probe.commit,
        host: probe.host,
        contract_declared,
        configuration_match,
        contract_match,
    }
}

fn admitted_environment() -> AdmittedEnvironment {
    const ADMITTED_EXACT: [&str; 12] = [
        "CARGO_HOME",
        "CARGO_TARGET_DIR",
        "HOME",
        "LANG",
        "LOGNAME",
        "PATH",
        "SHELL",
        "TERM",
        "TMPDIR",
        "TZ",
        "USER",
        "RUSTUP_HOME",
    ];
    const COMPILER_EXACT: [&str; 14] = [
        "RUSTFLAGS",
        "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_BUILD_RUSTFLAGS",
        "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTDOC",
        "CARGO_BUILD_TARGET",
        "RUSTC",
        "RUSTC_WRAPPER",
        "RUSTC_WORKSPACE_WRAPPER",
        "RUSTDOC",
        "RUSTDOCFLAGS",
        "RUSTUP_TOOLCHAIN",
    ];
    const COMPILER_PREFIXES: [&str; 5] = [
        "CARGO_TARGET_",
        "CARGO_ALIAS_",
        "CARGO_UNSTABLE_",
        "CARGO_REGISTRIES_",
        "CARGO_PROFILE_",
    ];

    let mut admitted_names: Vec<String> = std::env::vars_os()
        .filter_map(|(name, _)| name.into_string().ok())
        .filter(|name| ADMITTED_EXACT.contains(&name.as_str()) || name.starts_with("LC_"))
        .collect();
    let mut compiler_override_names: Vec<String> = std::env::vars_os()
        .filter_map(|(name, _)| name.into_string().ok())
        .filter(|name| {
            COMPILER_EXACT.contains(&name.as_str())
                || (name != "CARGO_TARGET_DIR"
                    && COMPILER_PREFIXES
                        .iter()
                        .any(|prefix| name.starts_with(prefix)))
        })
        .collect();
    admitted_names.sort();
    admitted_names.dedup();
    compiler_override_names.sort();
    compiler_override_names.dedup();
    AdmittedEnvironment {
        policy: "names-only-no-values/1",
        admitted_names,
        compiler_override_names,
    }
}

struct DiscoveredCrate {
    name: String, // directory name
    dir: PathBuf,
    rel: String,            // e.g. "crates/fln-core"
    location: &'static str, // "crates" | "tools"
    manifest: Option<Manifest>,
}

fn is_regular_file(path: &Path) -> bool {
    fs::symlink_metadata(path).is_ok_and(|metadata| metadata.is_file())
}

fn discover(
    root: &Path,
    subdir: &'static str,
    out: &mut Vec<DiscoveredCrate>,
) -> Result<(), String> {
    let dir = root.join(subdir);
    let metadata = match fs::symlink_metadata(&dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect {subdir}/: {error}")),
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    let mut entries: Vec<_> = fs::read_dir(&dir)
        .map_err(|e| format!("cannot read {subdir}/: {e}"))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("cannot read {subdir}/: {e}"))?;
    entries.sort_by_key(|e| e.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|e| format!("cannot inspect {}: {e}", path.display()))?;
        if file_type.is_dir() && is_regular_file(&path.join("Cargo.toml")) {
            let name = entry.file_name().to_string_lossy().into_owned();
            out.push(DiscoveredCrate {
                rel: format!("{subdir}/{name}"),
                name,
                dir: path,
                location: subdir,
                manifest: None,
            });
        }
    }
    Ok(())
}

fn scan_symlinks(root: &Path, dir: &Path, findings: &mut Vec<Finding>) -> Result<(), String> {
    let metadata = match fs::symlink_metadata(dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect {}: {error}", dir.display())),
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    let mut entries: Vec<_> = fs::read_dir(dir)
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if file_type.is_symlink() {
            let rel = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: rel,
                detail: "symlinks are forbidden in governed workspace inputs; they can escape or cycle around structural scans"
                    .to_string(),
            });
        } else if file_type.is_dir() {
            scan_symlinks(root, &path, findings)?;
        }
    }
    Ok(())
}

fn audit_governed_symlinks(root: &Path, findings: &mut Vec<Finding>) -> Result<(), String> {
    for rel in [
        "Cargo.toml",
        LOCK_FILE,
        SUITE_LOCK_FILE,
        TOOLCHAIN_FILE,
        GRAPH_FILE,
        LEDGER_FILE,
        ALLOWLIST_FILE,
        "crates",
        "tools",
    ] {
        let path = root.join(rel);
        match fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.file_type().is_symlink() => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: rel.to_string(),
                detail: "symlinks are forbidden for governed workspace inputs".to_string(),
            }),
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("cannot inspect {rel}: {error}")),
        }
    }
    scan_symlinks(root, &root.join("crates"), findings)?;
    scan_symlinks(root, &root.join("tools"), findings)
}

/// Configuration files that silently re-point the compiler if a supported command runs
/// from the directory that contains them. Cargo merges `.cargo/config(.toml)` from the
/// invocation directory *upward*, and rustup resolves the toolchain the same way, so the
/// discovery surface is every directory a caller may `cd` into — not only the root.
const FORBIDDEN_CONFIG_FILES: [&str; 4] = [
    ".cargo/config.toml",
    ".cargo/config",
    "rust-toolchain",
    "rust-toolchain.toml",
];

fn audit_configuration_files_in(
    root: &Path,
    dir: &Path,
    names: &[&str],
    findings: &mut Vec<Finding>,
) -> Result<(), String> {
    for name in names {
        let path = dir.join(name);
        match fs::symlink_metadata(&path) {
            Ok(_) => {
                let rel = path
                    .strip_prefix(root)
                    .unwrap_or(&path)
                    .to_string_lossy()
                    .replace('\\', "/");
                findings.push(Finding {
                    code: "FLN-STRUCT-016",
                    path: rel,
                    detail: "repository-local Cargo/toolchain configuration is forbidden because it can change the compiler, lint, linker, runner, or dependency-source contract outside the reviewed manifests; Cargo and rustup discover it from any directory a supported command runs in"
                        .to_string(),
                });
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("cannot inspect {}: {error}", path.display())),
        }
    }
    Ok(())
}

fn audit_configuration_surface_recursive(
    root: &Path,
    dir: &Path,
    findings: &mut Vec<Finding>,
) -> Result<(), String> {
    let metadata = match fs::symlink_metadata(dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect {}: {error}", dir.display())),
    };
    // Symlinked directories are already a finding in `audit_governed_symlinks`; do not
    // follow one here, or the scan could escape the workspace or cycle.
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    audit_configuration_files_in(root, dir, &FORBIDDEN_CONFIG_FILES, findings)?;

    let mut entries: Vec<_> = fs::read_dir(dir)
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if file_type.is_dir() && !file_type.is_symlink() {
            audit_configuration_surface_recursive(root, &path, findings)?;
        }
    }
    Ok(())
}

fn audit_repository_cargo_config(root: &Path, findings: &mut Vec<Finding>) -> Result<(), String> {
    // Package and workspace manifests are intentionally constrained above, but Cargo
    // also reads repository-local configuration before it compiles anything. Such a
    // file can inject rustflags (including lint caps), wrappers, linkers, runners, or
    // source replacement without appearing in the reviewed dependency graph. There is
    // no approved repository-local Cargo configuration surface yet, so both the current
    // and legacy filenames fail closed.
    //
    // At the root, `rust-toolchain.toml` is the reviewed pin itself (validated against
    // SUITE.lock elsewhere) and is therefore the one legal member of this family; its
    // legacy no-suffix spelling is not, because rustup prefers `.toml` when both exist
    // and the unreviewed file would otherwise sit there undetected.
    audit_configuration_files_in(
        root,
        root,
        &[".cargo/config.toml", ".cargo/config", "rust-toolchain"],
        findings,
    )?;

    // Below the root every member of the family is forbidden at every depth: a file at
    // `crates/fln-kernel/.cargo/config.toml` never appears in the reviewed graph, yet
    // `cd crates/fln-kernel && cargo build` merges it.
    for subdir in ["crates", "tools"] {
        audit_configuration_surface_recursive(root, &root.join(subdir), findings)?;
    }
    Ok(())
}

/// Read a governed file that the run can survive without. A file the guard cannot decode
/// is an inconclusive input, not a setup failure: propagating the error would abort the
/// whole run at exit 2 and hide every other finding, which turns one unreadable byte into
/// a way to suppress the gate. The caller records the typed finding and skips the file, so
/// the run can never be reported clean.
fn read_governed(path: &Path, rel: &str, findings: &mut Vec<Finding>) -> Option<String> {
    match fs::read_to_string(path) {
        Ok(text) => Some(text),
        Err(error) => {
            findings.push(Finding {
                code: "FLN-STRUCT-027",
                path: rel.to_string(),
                detail: format!(
                    "governed file could not be read as UTF-8 ({error}); its structural authority is inconclusive and the scan is incomplete"
                ),
            });
            None
        }
    }
}

/// Count covenant-relevant lines: non-blank, not starting with `//` after trim.
/// Block comments count as code — the covenant is deliberately conservative.
///
/// A file that cannot be decoded is reported and skipped, so an unreadable source file
/// understates the count as a finding rather than passing the covenant silently.
fn count_loc(root: &Path, dir: &Path, findings: &mut Vec<Finding>) -> Result<usize, String> {
    let mut total = 0;
    let metadata = match fs::symlink_metadata(dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(0),
        Err(error) => return Err(format!("cannot inspect {}: {error}", dir.display())),
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(0);
    }
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let mut entries: Vec<_> = fs::read_dir(&d)
            .map_err(|e| format!("cannot read {}: {e}", d.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("cannot read {}: {e}", d.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let p = entry.path();
            let file_type = entry
                .file_type()
                .map_err(|e| format!("cannot inspect {}: {e}", p.display()))?;
            if file_type.is_symlink() {
                continue;
            }
            if file_type.is_dir() {
                stack.push(p);
            } else if file_type.is_file() && p.extension().is_some_and(|e| e == "rs") {
                let rel = p
                    .strip_prefix(root)
                    .unwrap_or(&p)
                    .to_string_lossy()
                    .replace('\\', "/");
                let Some(text) = read_governed(&p, &rel, findings) else {
                    continue;
                };
                total += text
                    .lines()
                    .filter(|l| {
                        let t = l.trim();
                        !t.is_empty() && !t.starts_with("//")
                    })
                    .count();
            }
        }
    }
    Ok(total)
}

/// Close the kernel's generated-code authority without treating expanded compiler
/// boilerplate as project-authored TCB source.
///
/// Project-defined macros are forbidden in the kernel. Every admitted function-like
/// macro, attribute, and derive is an exact compiler/std builtin whose invocation line
/// is already charged by `count_loc`; all other generated-code entrances fail closed.
/// Together with the manifest ban on build scripts/custom/proc-macro targets and the
/// source-escape ban on `include!`/`#[path]`, this gives every generated fragment one
/// reviewed source callsite inside `crates/fln-kernel/src/**`.
fn audit_kernel_generated_authority(text: &str, source_rel: &str, findings: &mut Vec<Finding>) {
    const FUNCTION_MACROS: [&str; 5] = ["assert", "format", "matches", "unreachable", "vec"];
    const ATTRIBUTES: [&str; 4] = ["cfg", "derive", "forbid", "test"];
    const DERIVES: [&str; 6] = ["Clone", "Copy", "Debug", "Default", "Eq", "PartialEq"];

    for site in ledger::macro_definition_sites(text) {
        findings.push(Finding {
            code: "FLN-STRUCT-030",
            path: format!("{source_rel}:{}", site.line),
            detail: "project-defined macro in fln-kernel has no exact expanded-authority mapping; kernel macros are forbidden".to_string(),
        });
    }
    for site in ledger::macro_invocations(text) {
        if !FUNCTION_MACROS.contains(&site.name.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-030",
                path: format!("{source_rel}:{}", site.line),
                detail: format!(
                    "macro invocation `{}` is outside the reviewed kernel builtin inventory; generated checking authority must map to an admitted LOC-counted callsite",
                    site.name
                ),
            });
        }
    }
    for site in ledger::attribute_invocations(text) {
        if !ATTRIBUTES.contains(&site.name.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-030",
                path: format!("{source_rel}:{}", site.line),
                detail: format!(
                    "attribute `{}` is outside the reviewed kernel builtin inventory; procedural generated authority is forbidden",
                    site.name
                ),
            });
        }
    }
    for site in ledger::derive_macro_invocations(text) {
        if !DERIVES.contains(&site.name.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-030",
                path: format!("{source_rel}:{}", site.line),
                detail: format!(
                    "derive `{}` is outside the reviewed kernel builtin inventory; generated checking authority is forbidden",
                    site.name
                ),
            });
        }
    }
}

/// Root files whose lint posture is checked: whichever of `src/lib.rs`/`src/main.rs` exist.
fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let metadata = match fs::symlink_metadata(dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect {}: {error}", dir.display())),
    };
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Ok(());
    }
    let mut entries: Vec<_> = fs::read_dir(dir)
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
        if file_type.is_symlink() {
            continue;
        }
        if file_type.is_dir() {
            collect_rs_files(&path, out)?;
        } else if file_type.is_file() && path.extension().is_some_and(|extension| extension == "rs")
        {
            out.push(path);
        }
    }
    Ok(())
}

fn crate_roots(c: &DiscoveredCrate) -> Result<Vec<PathBuf>, String> {
    let mut roots: Vec<PathBuf> = ["lib.rs", "main.rs"]
        .iter()
        .map(|file| c.dir.join("src").join(file))
        .filter(|path| is_regular_file(path))
        .collect();
    let build_script = c.dir.join("build.rs");
    if is_regular_file(&build_script) {
        roots.push(build_script);
    }
    for target_dir in ["src/bin", "tests", "examples", "benches"] {
        collect_rs_files(&c.dir.join(target_dir), &mut roots)?;
    }
    roots.sort();
    roots.dedup();
    Ok(roots)
}

/// Cargo's implicit target roots, distinct from every Rust source that contributes to
/// those targets. A nested `tests/support/mod.rs` is authority-bearing source and is
/// scanned by `crate_roots`, but it is not a second integration-test target. Robot
/// inventory must not inflate target cardinality by conflating those two classes.
fn cargo_target_roots(c: &DiscoveredCrate) -> Result<Vec<PathBuf>, String> {
    let mut roots: Vec<PathBuf> = ["lib.rs", "main.rs"]
        .iter()
        .map(|file| c.dir.join("src").join(file))
        .filter(|path| is_regular_file(path))
        .collect();
    let build_script = c.dir.join("build.rs");
    if is_regular_file(&build_script) {
        roots.push(build_script);
    }
    for target_dir in ["src/bin", "tests", "examples", "benches"] {
        let dir = c.dir.join(target_dir);
        let metadata = match fs::symlink_metadata(&dir) {
            Ok(metadata) => metadata,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(format!("cannot inspect {}: {error}", dir.display())),
        };
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            continue;
        }
        let mut entries: Vec<_> = fs::read_dir(&dir)
            .map_err(|error| format!("cannot read {}: {error}", dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            let path = entry.path();
            let file_type = entry
                .file_type()
                .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
            if file_type.is_file() && path.extension().is_some_and(|extension| extension == "rs") {
                roots.push(path);
            } else if file_type.is_dir() {
                let main = path.join("main.rs");
                if is_regular_file(&main) {
                    roots.push(main);
                }
            }
        }
    }
    roots.sort();
    roots.dedup();
    Ok(roots)
}

fn validate_constitutional_baseline(g: &GraphFile, findings: &mut Vec<Finding>) {
    let plan_ranks = [
        ("fln-core", 0),
        ("fln-hash", 1),
        ("fln-bignum", 1),
        ("fln-libm", 1),
        ("fln-bench", 2),
        ("fln-unsafe-abi", 2),
        ("fln-unsafe-region", 2),
        ("fln-rt", 3),
        ("fln-env", 4),
        ("fln-olean", 5),
        ("fln-kernel", 6),
        ("fln-checker", 6),
        ("fln-syntax", 7),
        ("fln-parse", 8),
        ("fln-elab", 9),
        ("fln-comp", 10),
        ("fln-vm", 11),
        ("fln-unsafe-jit", 12),
        ("fln-verdict", 13),
        ("fln-anvil", 14),
        ("fln-ledger", 15),
        ("fln-lake", 16),
        ("fln-server", 17),
        ("fln-trace", 18),
        ("fln", 19),
        ("fln-hound", 20),
        ("fln-doc", 20),
        ("fln-mcp", 20),
        ("fln-tui", 20),
        ("fln-cli", 21),
        ("fln-wasm", 21),
        ("fln-conformance", 22),
    ];
    for (name, expected_rank) in plan_ranks {
        match g.crates.get(name) {
            None => findings.push(Finding {
                code: "FLN-STRUCT-024",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "plan-defined crate `{name}` is missing; amend the plan before removing it from the constitutional crate map"
                ),
            }),
            Some(decl) if decl.rank != Some(expected_rank) => findings.push(Finding {
                code: "FLN-STRUCT-024",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "plan-defined rank for `{name}` is {expected_rank}, found {:?}; amend the plan before its constitutional rank",
                    decl.rank
                ),
            }),
            Some(_) => {}
        }
    }
    let expected_boundaries: BTreeSet<&str> =
        BTreeSet::from(["fln-unsafe-abi", "fln-unsafe-region", "fln-unsafe-jit"]);
    let actual_boundaries: BTreeSet<&str> = g
        .crates
        .values()
        .filter(|decl| decl.kind == CrateKind::UnsafeBoundary)
        .map(|decl| decl.name.as_str())
        .collect();
    if actual_boundaries != expected_boundaries {
        findings.push(Finding {
            code: "FLN-STRUCT-024",
            path: GRAPH_FILE.to_string(),
            detail: format!(
                "D3 permits exactly {:?} as unsafe boundaries; graph declares {:?}",
                expected_boundaries, actual_boundaries
            ),
        });
    }

    for (source, destination) in [
        ("fln-unsafe-*", "fln-kernel"),
        ("fln-unsafe-*", "fln-checker"),
        ("fln-kernel", "fln-checker"),
        ("fln-checker", "fln-kernel"),
        ("fln-checker", "fln-olean"),
        ("fln-checker", "fln-rt"),
        ("fln-checker", "fln-unsafe-*"),
    ] {
        if !g
            .prohibits
            .iter()
            .any(|(from, to)| from.as_str() == source && to.as_str() == destination)
        {
            findings.push(Finding {
                code: "FLN-STRUCT-024",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "constitutional prohibition `{source} ->* {destination}` is missing"
                ),
            });
        }
    }
    for (name, expected) in [
        (
            "fln-kernel",
            ["fln-core", "fln-hash", "fln-bignum", "fln-env"].as_slice(),
        ),
        (
            "fln-checker",
            ["fln-core", "fln-hash", "fln-bignum"].as_slice(),
        ),
    ] {
        let actual: BTreeSet<&str> = g
            .allow_direct
            .get(name)
            .into_iter()
            .flatten()
            .map(String::as_str)
            .collect();
        let expected: BTreeSet<&str> = expected.iter().copied().collect();
        if actual != expected {
            findings.push(Finding {
                code: "FLN-STRUCT-024",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "constitutional allow-direct covenant for `{name}` must be {:?}, found {:?}",
                    expected, actual
                ),
            });
        }
    }
    if !g
        .covenants
        .get("fln-kernel")
        .is_some_and(|limit| *limit <= 12_000)
    {
        findings.push(Finding {
            code: "FLN-STRUCT-024",
            path: GRAPH_FILE.to_string(),
            detail: "fln-kernel max-loc covenant is missing or exceeds 12000".to_string(),
        });
    }
    let allowed_suite: BTreeSet<&str> = BTreeSet::from([
        "asupersync",
        "frankensqlite",
        "franken_networkx",
        "frankensearch",
        "frankentui",
        "franken_markdown",
        "fmd-font",
        "fmd-math",
        "fastmcp_rust",
        "atp",
        "frankentorch",
        "franken_node",
    ]);
    for dependency in &g.suite_deps {
        if !allowed_suite.contains(dependency.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-024",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "suite-dep `{dependency}` is not in the constitutional FrankenSuite universe"
                ),
            });
        }
    }
}

pub fn run(root: &Path) -> Result<RunOutcome, String> {
    let canonical_root = fs::canonicalize(root)
        .map_err(|error| format!("cannot resolve authoritative workspace root: {error}"))?;
    if !canonical_root.is_dir() {
        return Err(format!(
            "authoritative workspace root is not a directory: {}",
            canonical_root.display()
        ));
    }
    let root = canonical_root.as_path();
    let root_identity = root
        .to_str()
        .map(|identity| identity.replace('\\', "/"))
        .ok_or_else(|| "authoritative workspace root is not UTF-8".to_string())?;
    let governed_before = governed_snapshot(root);
    let admitted_environment = admitted_environment();
    let compiler_identity = compiler_identity(root);
    let mut findings: Vec<Finding> = Vec::new();

    // Reject links before any recursive scanner runs. Git can store symlinks, and
    // following one here could omit authoritative code from a covenant, authorize a
    // boundary site under the wrong path, escape the workspace, or recurse forever.
    audit_governed_symlinks(root, &mut findings)?;
    audit_repository_cargo_config(root, &mut findings)?;

    // ---- load the reviewed files -------------------------------------------------------
    let graph_path = root.join(GRAPH_FILE);
    let graph_text =
        fs::read_to_string(&graph_path).map_err(|e| format!("cannot read {GRAPH_FILE}: {e}"))?;
    let graph_digest = fnv1a64(graph_text.as_bytes());
    let g: GraphFile = graph::parse(&graph_text)?;

    let ledger_text = fs::read_to_string(root.join(LEDGER_FILE))
        .map_err(|e| format!("cannot read {LEDGER_FILE}: {e}"))?;
    let unsafe_ledger = ledger::parse(&ledger_text)?;
    validate_constitutional_baseline(&g, &mut findings);

    let root_manifest_path = root.join("Cargo.toml");
    let root_manifest_text = fs::read_to_string(&root_manifest_path)
        .map_err(|error| format!("cannot read root Cargo.toml: {error}"))?;
    match manifest::parse_workspace_members(&root_manifest_text, "Cargo.toml") {
        Ok(members) => {
            let actual: BTreeSet<&str> = members.iter().map(String::as_str).collect();
            let expected = BTreeSet::from(["crates/*", "tools/*"]);
            if actual != expected {
                findings.push(Finding {
                    code: "FLN-STRUCT-021",
                    path: "Cargo.toml".to_string(),
                    detail: format!(
                        "workspace.members must be exactly {:?}; found {:?}",
                        expected, actual
                    ),
                });
            }
        }
        Err(detail) => findings.push(Finding {
            code: "FLN-STRUCT-021",
            path: "Cargo.toml".to_string(),
            detail,
        }),
    }

    // ---- discover the actual workspace -------------------------------------------------
    let mut discovered: Vec<DiscoveredCrate> = Vec::new();
    discover(root, "crates", &mut discovered)?;
    discover(root, "tools", &mut discovered)?;

    for c in &mut discovered {
        let manifest_rel = format!("{}/Cargo.toml", c.rel);
        let Some(text) = read_governed(&c.dir.join("Cargo.toml"), &manifest_rel, &mut findings)
        else {
            continue;
        };
        match manifest::parse(&text, &manifest_rel) {
            Ok(m) => c.manifest = Some(m),
            Err(e) => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: manifest_rel,
                detail: e,
            }),
        }
    }
    let feature_count = discovered
        .iter()
        .filter_map(|crate_| crate_.manifest.as_ref())
        .map(|manifest| manifest.features.len())
        .sum();
    let mut target_count = 0usize;
    for crate_ in &discovered {
        target_count = target_count
            .checked_add(cargo_target_roots(crate_)?.len())
            .ok_or_else(|| "authority target count overflow".to_string())?;
    }
    let target_triple_count = fs::read_to_string(root.join(SUITE_LOCK_FILE))
        .ok()
        .and_then(|text| crate::lockfile::parse_suite_lock(&text).ok())
        .map_or(0, |lock| lock.targets.len());

    // ---- snapshot law: crates on disk <-> crates declared ------------------------------
    let on_disk: BTreeMap<&str, &DiscoveredCrate> =
        discovered.iter().map(|c| (c.name.as_str(), c)).collect();
    for c in &discovered {
        match g.crates.get(&c.name) {
            None => findings.push(Finding {
                code: "FLN-STRUCT-001",
                path: c.rel.clone(),
                detail: format!(
                    "crate `{}` exists on disk but is not acknowledged in {GRAPH_FILE}",
                    c.name
                ),
            }),
            Some(decl) => {
                let expected_location = match decl.kind {
                    CrateKind::Tool => "tools",
                    _ => "crates",
                };
                if c.location != expected_location {
                    findings.push(Finding {
                        code: "FLN-STRUCT-017",
                        path: c.rel.clone(),
                        detail: format!(
                            "crate `{}` is declared kind={} and must live under {expected_location}/",
                            c.name,
                            decl.kind.as_str()
                        ),
                    });
                }
                let name_is_boundary = c.name.starts_with("fln-unsafe-");
                let kind_is_boundary = decl.kind == CrateKind::UnsafeBoundary;
                if name_is_boundary != kind_is_boundary {
                    findings.push(Finding {
                        code: "FLN-STRUCT-017",
                        path: c.rel.clone(),
                        detail: format!(
                            "crate `{}`: the `fln-unsafe-` prefix and kind=unsafe-boundary must coincide (D3)",
                            c.name
                        ),
                    });
                }
            }
        }
    }
    for decl in g.crates.values() {
        if !on_disk.contains_key(decl.name.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-002",
                path: GRAPH_FILE.to_string(),
                detail: format!("declared crate `{}` is missing on disk", decl.name),
            });
        }
    }

    // ---- manifest sanity: name matches dir, edition pinned -----------------------------
    for c in &discovered {
        let Some(m) = &c.manifest else { continue };
        if m.name != c.name {
            findings.push(Finding {
                code: "FLN-STRUCT-003",
                path: format!("{}/Cargo.toml", c.rel),
                detail: format!("package name `{}` != directory name `{}`", m.name, c.name),
            });
        }
        if m.edition != "2024" {
            findings.push(Finding {
                code: "FLN-STRUCT-004",
                path: format!("{}/Cargo.toml", c.rel),
                detail: format!("edition `{}` — the workspace pins edition 2024", m.edition),
            });
        }
    }

    // ---- actual edge set + closed universe ---------------------------------------------
    let suite: BTreeSet<&str> = g.suite_deps.iter().map(String::as_str).collect();
    let mut actual_edges: BTreeSet<(String, String)> = BTreeSet::new();
    for c in &discovered {
        let Some(m) = &c.manifest else { continue };
        for dep in &m.deps {
            if on_disk.contains_key(dep.name.as_str()) || g.crates.contains_key(&dep.name) {
                if dep.path.is_none() {
                    findings.push(Finding {
                        code: "FLN-STRUCT-010",
                        path: format!("{}/Cargo.toml", c.rel),
                        detail: format!(
                            "workspace dependency `{}` must be a path dependency",
                            dep.name
                        ),
                    });
                }
                if let Some(path) = &dep.path
                    && let Some(target) = on_disk.get(dep.name.as_str())
                {
                    let declared = fs::canonicalize(c.dir.join(path));
                    let expected = fs::canonicalize(&target.dir);
                    match (declared, expected) {
                        (Ok(declared), Ok(expected)) if declared == expected => {}
                        (Ok(declared), Ok(expected)) => findings.push(Finding {
                            code: "FLN-STRUCT-023",
                            path: format!("{}/Cargo.toml", c.rel),
                            detail: format!(
                                "dependency `{}` path resolves to `{}`, expected `{}`",
                                dep.name,
                                declared.display(),
                                expected.display()
                            ),
                        }),
                        (Err(error), _) => findings.push(Finding {
                            code: "FLN-STRUCT-023",
                            path: format!("{}/Cargo.toml", c.rel),
                            detail: format!(
                                "dependency `{}` path `{path}` cannot be resolved: {error}",
                                dep.name
                            ),
                        }),
                        (_, Err(error)) => findings.push(Finding {
                            code: "FLN-STRUCT-023",
                            path: format!("{}/Cargo.toml", c.rel),
                            detail: format!(
                                "acknowledged dependency `{}` directory cannot be resolved: {error}",
                                dep.name
                            ),
                        }),
                    }
                }
                actual_edges.insert((c.name.clone(), dep.name.clone()));
            } else if suite.contains(dep.name.as_str()) {
                if dep.path.is_none() {
                    findings.push(Finding {
                        code: "FLN-STRUCT-010",
                        path: format!("{}/Cargo.toml", c.rel),
                        detail: format!(
                            "FrankenSuite dependency `{}` must be a path dependency (D1; SUITE.lock pending)",
                            dep.name
                        ),
                    });
                }
            } else {
                findings.push(Finding {
                    code: "FLN-STRUCT-010",
                    path: format!("{}/Cargo.toml", c.rel),
                    detail: format!(
                        "dependency `{}` ({}) is outside the closed universe (D1)",
                        dep.name, dep.section
                    ),
                });
            }
        }
    }

    // ---- edge acknowledgment (snapshot law over edges) ---------------------------------
    let declared_edges: BTreeSet<(String, String)> = g.edges.iter().cloned().collect();
    for (from, to) in &actual_edges {
        if !declared_edges.contains(&(from.clone(), to.clone())) {
            findings.push(Finding {
                code: "FLN-STRUCT-005",
                path: format!("crates/{from}/Cargo.toml"),
                detail: format!(
                    "dependency edge `{from} -> {to}` is not acknowledged in {GRAPH_FILE}"
                ),
            });
        }
    }
    for (from, to) in &declared_edges {
        if !actual_edges.contains(&(from.clone(), to.clone())) {
            findings.push(Finding {
                code: "FLN-STRUCT-006",
                path: GRAPH_FILE.to_string(),
                detail: format!(
                    "acknowledged edge `{from} -> {to}` no longer exists in any manifest"
                ),
            });
        }
    }

    // ---- layering: strictly downward; tools are one-way --------------------------------
    for (from, to) in &actual_edges {
        let (Some(fd), Some(td)) = (g.crates.get(from), g.crates.get(to)) else {
            continue; // unacknowledged crates already reported
        };
        match (fd.kind, td.kind) {
            (CrateKind::Tool, _) => {} // tools may observe the product graph
            (_, CrateKind::Tool) => findings.push(Finding {
                code: "FLN-STRUCT-007",
                path: format!("crates/{from}/Cargo.toml"),
                detail: format!("product crate `{from}` must not depend on tool crate `{to}`"),
            }),
            _ => {
                let (fr, tr) = (fd.rank.unwrap_or(0), td.rank.unwrap_or(0));
                if fr <= tr {
                    findings.push(Finding {
                        code: "FLN-STRUCT-007",
                        path: format!("crates/{from}/Cargo.toml"),
                        detail: format!(
                            "edge `{from}` (rank {fr}) -> `{to}` (rank {tr}) violates strict downward layering (§5)"
                        ),
                    });
                }
            }
        }
    }

    // ---- D3 transitive prohibitions ----------------------------------------------------
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (from, to) in &actual_edges {
        adjacency
            .entry(from.as_str())
            .or_default()
            .push(to.as_str());
    }
    for (src_pat, dst_pat) in &g.prohibits {
        for src in g.crates.keys().filter(|n| src_pat.matches(n)) {
            // BFS with parent tracking so the finding shows the offending path.
            let mut parent: BTreeMap<&str, &str> = BTreeMap::new();
            let mut queue: VecDeque<&str> = VecDeque::new();
            queue.push_back(src.as_str());
            let mut seen: BTreeSet<&str> = BTreeSet::from([src.as_str()]);
            while let Some(cur) = queue.pop_front() {
                for next in adjacency.get(cur).into_iter().flatten() {
                    if !seen.insert(next) {
                        continue;
                    }
                    parent.insert(next, cur);
                    if dst_pat.matches(next) && *next != src.as_str() {
                        let mut path_nodes = vec![*next];
                        let mut walk = *next;
                        while let Some(p) = parent.get(walk) {
                            path_nodes.push(p);
                            walk = p;
                        }
                        path_nodes.reverse();
                        findings.push(Finding {
                            code: "FLN-STRUCT-008",
                            path: format!("crates/{src}"),
                            detail: format!(
                                "prohibited path `{}` (rule: {} ->* {})",
                                path_nodes.join(" -> "),
                                src_pat.as_str(),
                                dst_pat.as_str()
                            ),
                        });
                    }
                    queue.push_back(next);
                }
            }
        }
    }

    // ---- trust-base direct-dependency covenants ----------------------------------------
    for (crate_name, allowed) in &g.allow_direct {
        let Some(c) = on_disk.get(crate_name.as_str()) else {
            continue;
        };
        let Some(m) = &c.manifest else { continue };
        for dep in &m.deps {
            if !allowed.iter().any(|a| a == &dep.name) {
                findings.push(Finding {
                    code: "FLN-STRUCT-009",
                    path: format!("{}/Cargo.toml", c.rel),
                    detail: format!(
                        "`{crate_name}` direct dependency `{}` is outside its allow-direct covenant ({})",
                        dep.name,
                        if allowed.is_empty() {
                            "empty".to_string()
                        } else {
                            allowed.join(", ")
                        }
                    ),
                });
            }
        }
    }

    // ---- unsafe posture at crate roots -------------------------------------------------
    for c in &discovered {
        let Some(decl) = g.crates.get(&c.name) else {
            continue;
        };
        let has_primary_root = ["lib.rs", "main.rs"]
            .iter()
            .any(|file| is_regular_file(&c.dir.join("src").join(file)));
        if !has_primary_root {
            findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: c.rel.clone(),
                detail: "crate has neither src/lib.rs nor src/main.rs; auxiliary Cargo targets do not satisfy the declared product crate"
                    .to_string(),
            });
        }
        let roots = crate_roots(c)?;
        if roots.is_empty() {
            continue;
        }
        for root_file in roots {
            let relative_root = root_file
                .strip_prefix(&c.dir)
                .unwrap_or(&root_file)
                .to_string_lossy()
                .replace('\\', "/");
            let rel = format!("{}/{}", c.rel, relative_root);
            let Some(text) = read_governed(&root_file, &rel, &mut findings) else {
                continue;
            };
            let posture = ledger::lint_posture(&text);
            match decl.kind {
                CrateKind::UnsafeBoundary => {
                    if posture.forbid_unsafe {
                        findings.push(Finding {
                            code: "FLN-STRUCT-012",
                            path: rel.clone(),
                            detail: "boundary crate must use deny(unsafe_code), not forbid (D3)"
                                .to_string(),
                        });
                    }
                    if !posture.deny_unsafe {
                        findings.push(Finding {
                            code: "FLN-STRUCT-012",
                            path: rel,
                            detail: "boundary crate root missing `#![deny(unsafe_code)]` (D3)"
                                .to_string(),
                        });
                    }
                }
                _ => {
                    if !posture.forbid_unsafe {
                        findings.push(Finding {
                            code: "FLN-STRUCT-011",
                            path: rel,
                            detail: "crate root missing `#![forbid(unsafe_code)]` (D3)".to_string(),
                        });
                    }
                }
            }
        }
    }

    // ---- unsafe-ledger discipline ------------------------------------------------------
    // Only the boundary crates are scanned for allow-sites: ordinary and tool crates
    // are closed by the `#![forbid(unsafe_code)]` root check above plus rustc itself
    // (forbid cannot be overridden by an inner allow).
    let mut sites: Vec<AllowSite> = Vec::new();
    let mut unreadable_boundary_sources: Vec<String> = Vec::new();
    for c in &discovered {
        let is_boundary = g
            .crates
            .get(&c.name)
            .is_some_and(|d| d.kind == CrateKind::UnsafeBoundary);
        if !is_boundary {
            continue;
        }
        if c.dir.is_dir() {
            // Every Rust target in a boundary package is project-authored boundary code:
            // library/modules, bins, integration tests, examples, benches, and any
            // auto-discovered build script. None gets an unledgered lowering lane.
            ledger::scan_allow_sites(&c.dir, &c.rel, &mut sites, &mut unreadable_boundary_sources)?;
        }
    }
    // An undecodable file inside a boundary crate is exactly where an unledgered
    // allow-site would hide, so it is reported and the run is never clean.
    for rel in unreadable_boundary_sources {
        findings.push(Finding {
            code: "FLN-STRUCT-027",
            path: rel,
            detail:
                "boundary-crate source could not be read as UTF-8; it was not scanned for `#[allow(unsafe_code)]` sites, so the unsafe-ledger discipline is inconclusive for this file"
                    .to_string(),
        });
    }
    let mut used_ids: BTreeMap<&str, usize> = BTreeMap::new();
    for site in &sites {
        if site.level != "allow" {
            findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: format!("{}:{}", site.path, site.line),
                detail: format!(
                    "{}(unsafe_code) lowers the boundary root's deny; use only a narrow, ledgered allow(unsafe_code) site",
                    site.level
                ),
            });
            continue;
        }
        if site.inner {
            findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: format!("{}:{}", site.path, site.line),
                detail: "inner allow(unsafe_code) applies too broadly; only narrow outer attributes are ledgerable"
                    .to_string(),
            });
            continue;
        }
        match &site.id {
            None => findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: format!("{}:{}", site.path, site.line),
                detail:
                    "allow(unsafe_code) site missing its `// UNSAFE-LEDGER: FLN-UL-NNNN` marker"
                        .to_string(),
            }),
            Some(id) => {
                *used_ids.entry(id.as_str()).or_insert(0) += 1;
                match unsafe_ledger.rows.iter().find(|r| &r.id == id) {
                    None => findings.push(Finding {
                        code: "FLN-STRUCT-013",
                        path: format!("{}:{}", site.path, site.line),
                        detail: format!("marker `{id}` has no row in {LEDGER_FILE}"),
                    }),
                    Some(row) if row.path != site.path => findings.push(Finding {
                        code: "FLN-STRUCT-014",
                        path: LEDGER_FILE.to_string(),
                        detail: format!(
                            "row `{id}` names path `{}` but the site is at `{}`",
                            row.path, site.path
                        ),
                    }),
                    Some(_) => {}
                }
            }
        }
    }
    for (id, count) in &used_ids {
        if *count > 1 {
            findings.push(Finding {
                code: "FLN-STRUCT-013",
                path: LEDGER_FILE.to_string(),
                detail: format!("marker `{id}` is used by {count} sites — one row per site (D3)"),
            });
        }
    }
    for row in &unsafe_ledger.rows {
        if !used_ids.contains_key(row.id.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-014",
                path: LEDGER_FILE.to_string(),
                detail: format!(
                    "row `{}` has no matching allow(unsafe_code) site (stale)",
                    row.id
                ),
            });
        }
    }

    // D3 law (b), no-admission export covenant (bead fln-lld). Textual layer:
    // a boundary crate has no symbol-export attribute, no macro definition, no
    // source escape, and no kernel-admission token — and every bare-`pub` Rust
    // item is matched item-by-item against the reviewed BOUNDARY_API allowlist
    // (undeclared items AND stale rows both fail). Expansion layer: if the
    // crate INVOKES macros (D1 closes the macro universe to std's own), the
    // fully expanded crate — every compiled cfg — must satisfy the same
    // export-attribute rules, may not synthesize `allow(unsafe_code)` beyond
    // the ledgered source sites, and its expanded public items must be a
    // SUBSET of the declared source items. Anything that cannot be verified
    // (expansion failure, feature-conditional cfg unknowns, unrecognized
    // public-item shapes) fails closed.
    let boundary_rows = match boundary_api::load(root, BOUNDARY_API_FILE) {
        Ok(Some(api)) => api.rows,
        Ok(None) => Vec::new(),
        Err(detail) => {
            findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: BOUNDARY_API_FILE.to_string(),
                detail,
            });
            Vec::new()
        }
    };
    // The C-ABI export covenant's inputs (FLN-STRUCT-026, bead franken_lean-83r):
    // the reviewed per-symbol status ledger, loaded once, and every
    // `export_name` site found while walking the boundary crates below.
    let export_rows = match export_status::load(root, EXPORT_STATUS_FILE) {
        Ok(rows) => rows,
        Err(detail) => {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail,
            });
            None
        }
    };
    let implemented_exports: BTreeSet<String> = export_rows
        .as_ref()
        .map(|status| {
            status
                .rows
                .iter()
                .filter(|row| row.implemented())
                .map(|row| row.symbol.clone())
                .collect()
        })
        .unwrap_or_default();
    let no_exports: BTreeSet<String> = BTreeSet::new();
    let mut abi_export_sites: Vec<(String, usize, Option<String>)> = Vec::new();
    let mut used_api_rows: BTreeSet<&str> = BTreeSet::new();
    for c in &discovered {
        let is_boundary = g
            .crates
            .get(&c.name)
            .is_some_and(|decl| decl.kind == CrateKind::UnsafeBoundary);
        if !is_boundary {
            continue;
        }
        let src = c.dir.join("src");
        if !src.is_dir() {
            continue;
        }
        let findings_before = findings.len();
        let mut exports = Vec::new();
        let mut unreadable_exports = Vec::new();
        ledger::scan_external_exports(
            &src,
            &format!("{}/src", c.rel),
            &mut exports,
            &mut unreadable_exports,
        )?;
        for rel in unreadable_exports {
            findings.push(Finding {
                code: "FLN-STRUCT-027",
                path: rel,
                detail:
                    "boundary-crate source could not be read as UTF-8; it was not scanned for external export sites, so the D3 law (b) no-admission covenant is inconclusive for this file"
                        .to_string(),
            });
        }
        for site in exports {
            findings.push(Finding {
                code: "FLN-STRUCT-022",
                path: format!("{}:{}", site.path, site.line),
                detail: format!(
                    "{} in unsafe boundary `{}` is forbidden (D3 law b no-admission covenant)",
                    site.detail, c.name
                ),
            });
        }
        // Public-API allowlist matching + admission-token tripwire, per file.
        let mut sources = Vec::new();
        collect_rs_files(&src, &mut sources)?;
        sources.sort();
        let mut source_pub: BTreeSet<(String, String)> = BTreeSet::new();
        for path in &sources {
            let source_rel = path
                .strip_prefix(root)
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            let Some(text) = read_governed(path, &source_rel, &mut findings) else {
                continue;
            };
            let rel = path
                .strip_prefix(root)
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            for site in ledger::admission_token_sites(&text) {
                findings.push(Finding {
                    code: "FLN-STRUCT-022",
                    path: format!("{rel}:{}", site.line),
                    detail: format!("{} in unsafe boundary `{}` (D3 law b)", site.detail, c.name),
                });
            }
            // C-ABI export sites (FLN-STRUCT-026): only the one designated
            // exporting crate may carry them; its sites join the status
            // ledger after the walk. Everything else fails here.
            for site in ledger::export_name_attr_sites(&text) {
                if c.name == EXPORTING_CRATE {
                    abi_export_sites.push((rel.clone(), site.line, site.symbol.clone()));
                } else {
                    findings.push(Finding {
                        code: "FLN-STRUCT-026",
                        path: format!("{rel}:{}", site.line),
                        detail: format!(
                            "export_name site in `{}`; only `{EXPORTING_CRATE}` may export C symbols (D3, §21.2)",
                            c.name
                        ),
                    });
                }
            }
            for item in ledger::public_item_sites(&text) {
                if item.kind == "unknown" {
                    findings.push(Finding {
                        code: "FLN-STRUCT-022",
                        path: format!("{rel}:{}", item.line),
                        detail: format!(
                            "unrecognized public-item shape in unsafe boundary `{}`; the covenant cannot classify it (fail closed)",
                            c.name
                        ),
                    });
                    continue;
                }
                match boundary_rows
                    .iter()
                    .find(|row| row.path == rel && row.name == item.name && row.kind == item.kind)
                {
                    Some(row) => {
                        used_api_rows.insert(row.id.as_str());
                        source_pub.insert((item.kind.clone(), item.name.clone()));
                    }
                    None => findings.push(Finding {
                        code: "FLN-STRUCT-022",
                        path: format!("{rel}:{}", item.line),
                        detail: format!(
                            "undeclared public item `{} {}` in unsafe boundary `{}`; every exported item needs a reviewed {BOUNDARY_API_FILE} row (D3 law b)",
                            item.kind, item.name, c.name
                        ),
                    }),
                }
            }
        }
        // Expansion covenant trigger: any macro invocation in the crate's sources.
        // Skipped when textual findings already fail the crate (the source fix
        // comes first, and the expansion would fail on the same surface).
        if findings.len() > findings_before {
            continue;
        }
        let allowed_exports = if c.name == EXPORTING_CRATE {
            &implemented_exports
        } else {
            &no_exports
        };
        findings.extend(expansion_covenant(root, c, &source_pub, allowed_exports)?);
    }
    for row in &boundary_rows {
        if !used_api_rows.contains(row.id.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-022",
                path: BOUNDARY_API_FILE.to_string(),
                detail: format!(
                    "row `{}` ({} {} in {}) has no matching public item (stale)",
                    row.id, row.kind, row.name, row.path
                ),
            });
        }
    }
    findings.extend(c_export_covenant(
        root,
        export_rows.as_ref(),
        &abi_export_sites,
    ));

    // ---- line-count covenants ----------------------------------------------------------
    for (crate_name, limit) in &g.covenants {
        let Some(c) = on_disk.get(crate_name.as_str()) else {
            continue;
        };
        let src = c.dir.join("src");
        let mut covenant_sources = Vec::new();
        collect_rs_files(&src, &mut covenant_sources)?;
        for source in covenant_sources {
            let source_rel = source
                .strip_prefix(root)
                .unwrap_or(&source)
                .to_string_lossy()
                .replace('\\', "/");
            let Some(text) = read_governed(&source, &source_rel, &mut findings) else {
                continue;
            };
            if crate_name == "fln-kernel" {
                audit_kernel_generated_authority(&text, &source_rel, &mut findings);
            }
            for escape in ledger::source_escape_sites(&text) {
                let rel = source_rel.clone();
                findings.push(Finding {
                    code: "FLN-STRUCT-015",
                    path: format!("{rel}:{}", escape.line),
                    detail: format!(
                        "`{crate_name}` {} outside the counted source closure",
                        escape.detail
                    ),
                });
            }
        }
        let loc = count_loc(root, &src, &mut findings)?;
        if loc > *limit {
            findings.push(Finding {
                code: "FLN-STRUCT-015",
                path: format!("{}/src", c.rel),
                detail: format!(
                    "`{crate_name}` has {loc} covenant-relevant lines, exceeding max-loc={limit}; growth requires amending the plan first (§8)"
                ),
            });
        }
    }

    // ---- dependency-closure audit (D1; bead franken_lean-xwf) --------------------------
    // Cargo.lock ⇄ ci/CLOSURE_ALLOWLIST.txt ⇄ SUITE.lock ⇄ rust-toolchain.toml. Missing
    // or malformed governance files degrade to findings, never to a silent skip.
    findings.extend(crate::lockfile::audit(root, &g));
    findings.extend(crate::contract_inventory::audit(root));
    findings.extend(crate::contract_handoff::audit(root));
    findings.extend(crate::ownership_publication::audit(root));

    if compiler_identity.contract_declared && !compiler_identity.contract_match {
        findings.push(Finding {
            code: "FLN-STRUCT-029",
            path: SUITE_LOCK_FILE.to_string(),
            detail: format!(
                "effective compiler identity source={} release={} commit={} host={} configuration-match={} does not match the complete SUITE.lock compiler contract; compiler authority is inconclusive",
                compiler_identity.source,
                compiler_identity.release.as_deref().unwrap_or("unavailable"),
                compiler_identity.commit.as_deref().unwrap_or("unavailable"),
                compiler_identity.host.as_deref().unwrap_or("unavailable"),
                compiler_identity.configuration_match,
            ),
        });
    }

    let governed_after = governed_snapshot(root);
    for (path, detail) in governed_before
        .unreadable
        .iter()
        .chain(governed_after.unreadable.iter())
    {
        if !findings
            .iter()
            .any(|finding| finding.code == "FLN-STRUCT-027" && finding.path == *path)
        {
            findings.push(Finding {
                code: "FLN-STRUCT-027",
                path: path.clone(),
                detail: format!(
                    "{detail}; structural authority is inconclusive and the traversal is incomplete"
                ),
            });
        }
    }
    if governed_before.digest != governed_after.digest {
        findings.push(Finding {
            code: "FLN-STRUCT-028",
            path: root_identity.clone(),
            detail: format!(
                "governed source root changed during the scan (fnv1a64:{:016x} -> fnv1a64:{:016x}); the run is bound to no single input closure",
                governed_before.digest, governed_after.digest
            ),
        });
    }

    let inconclusive_paths: BTreeSet<&str> = findings
        .iter()
        .filter(|finding| finding.code == "FLN-STRUCT-027")
        .map(|finding| finding.path.as_str())
        .collect();
    let snapshot_unreadable_paths: BTreeSet<&str> = governed_after
        .unreadable
        .iter()
        .map(|(path, _)| path.as_str())
        .collect();
    let decoded_files_skipped = inconclusive_paths
        .difference(&snapshot_unreadable_paths)
        .count();
    let files_skipped_unreadable = governed_after
        .files_discovered
        .saturating_sub(governed_after.files_scanned)
        .saturating_add(decoded_files_skipped);
    let files_scanned = governed_after
        .files_scanned
        .saturating_sub(decoded_files_skipped);
    let traversal = TraversalFacts {
        directories_visited: governed_after.directories_visited,
        files_discovered: governed_after.files_discovered,
        files_scanned,
        files_skipped_unreadable,
    };
    if !traversal.count_rule_holds() {
        findings.push(Finding {
            code: "FLN-STRUCT-028",
            path: root_identity.clone(),
            detail: format!(
                "authority-count rule `{AUTHORITY_COUNT_RULE}` failed: scanned={} skipped={} discovered={}",
                traversal.files_scanned,
                traversal.files_skipped_unreadable,
                traversal.files_discovered
            ),
        });
    }

    let authority = if findings.iter().any(|finding| {
        matches!(
            finding.code,
            "FLN-STRUCT-027"
                | "FLN-STRUCT-028"
                | "FLN-STRUCT-029"
                | "FLN-STRUCT-031"
                | "FLN-STRUCT-033"
                | "FLN-STRUCT-034"
        )
    }) {
        Authority::Incomplete
    } else {
        Authority::Complete
    };
    findings.sort_by(|a, b| (a.code, &a.path, &a.detail).cmp(&(b.code, &b.path, &b.detail)));
    Ok(RunOutcome {
        findings,
        crate_count: discovered.len(),
        edge_count: actual_edges.len(),
        graph_digest,
        root_identity,
        governed_root_before: governed_before.digest,
        governed_root_after: governed_after.digest,
        traversal,
        authority,
        authority_inventory: AuthorityInventory {
            packages: discovered.len(),
            targets: target_count,
            features: feature_count,
            target_triples: target_triple_count,
        },
        compiler_identity,
        admitted_environment,
    })
}

/// The expansion covenant (FLN-STRUCT-025, bead fln-lld). For a boundary
/// crate whose sources invoke macros, verify the FULLY EXPANDED crate — once
/// per compiled cfg (`--lib`, and `--lib --profile test` for the
/// unit-test cfg) — still satisfies D3 law (b):
///
/// * no externally public item, symbol-export attribute, or `global_asm!`
///   in the expanded surface;
/// * no more `allow(unsafe_code)` attributes than the marker-carrying source
///   sites (a macro cannot synthesize an unledgered allowance);
/// * no feature axis at all (features make the compiled cfg set open-ended —
///   a cfg-dependent unknown, rejected outright).
///
/// Soundness rests on D1: the closed dependency universe means the only
/// macros a boundary crate can invoke are `std`'s own — after expansion,
/// whatever they produced is literal text and textual scanning is exact.
/// Every failure mode (including a failed expansion run) is a finding,
/// never a skip.
fn expansion_covenant(
    root: &Path,
    c: &DiscoveredCrate,
    source_pub: &BTreeSet<(String, String)>,
    allowed_exports: &BTreeSet<String>,
) -> Result<Vec<Finding>, String> {
    let src = c.dir.join("src");
    let mut sources = Vec::new();
    collect_rs_files(&src, &mut sources)?;
    sources.sort();
    let mut invokes_macros = false;
    let mut source_allow_count = 0usize;
    let mut findings = Vec::new();
    for path in &sources {
        let text = fs::read_to_string(path)
            .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        if !ledger::macro_invocation_lines(&text).is_empty() {
            invokes_macros = true;
        }
        source_allow_count += ledger::count_allow_unsafe_attributes(&text);
        if text.contains("cfg(feature") || text.contains("cfg_attr(feature") {
            let rel = path
                .strip_prefix(root)
                .unwrap_or(path)
                .to_string_lossy()
                .replace('\\', "/");
            findings.push(Finding {
                code: "FLN-STRUCT-025",
                path: rel,
                detail: format!(
                    "feature-conditional code in boundary `{}` is a cfg-dependent unknown; the expansion covenant rejects open cfg axes",
                    c.name
                ),
            });
        }
    }
    if !invokes_macros {
        return Ok(findings);
    }
    let manifest_path = c.dir.join("Cargo.toml");
    let manifest_text = fs::read_to_string(&manifest_path)
        .map_err(|error| format!("cannot read {}: {error}", manifest_path.display()))?;
    if manifest_text.contains("[features]") {
        findings.push(Finding {
            code: "FLN-STRUCT-025",
            path: format!("{}/Cargo.toml", c.rel),
            detail: format!(
                "boundary `{}` declares cargo features; the expansion covenant rejects open cfg axes",
                c.name
            ),
        });
    }
    if !findings.is_empty() {
        return Ok(findings);
    }
    for (label, test_cfg) in [("lib", false), ("lib+test-cfg", true)] {
        match run_expansion(root, &c.name, test_cfg) {
            Err(detail) => findings.push(Finding {
                code: "FLN-STRUCT-025",
                path: format!("{}/src", c.rel),
                detail: format!(
                    "cannot expand boundary `{}` ({label}) for the covenant; failing closed: {detail}",
                    c.name
                ),
            }),
            Ok(expanded) => {
                // Export-surface and public-item subset scans apply to the
                // shipped lib cfg only: the test harness itself synthesizes
                // `pub` test descriptors (`#[rustc_test_marker]` items), and
                // test targets never ship symbols — the laundering vector
                // that remains live in test code is a synthesized unsafe
                // allowance, which the count rule below checks for every cfg.
                if !test_cfg {
                    for site in ledger::expanded_surface_violations(&expanded, allowed_exports) {
                        findings.push(Finding {
                            code: "FLN-STRUCT-025",
                            path: format!("{}/src (expanded:{label}:{})", c.rel, site.line),
                            detail: format!(
                                "{} of boundary `{}` (D3 law b, post-expansion)",
                                site.detail, c.name
                            ),
                        });
                    }
                    for site in ledger::admission_token_sites(&expanded) {
                        findings.push(Finding {
                            code: "FLN-STRUCT-025",
                            path: format!("{}/src (expanded:{label}:{})", c.rel, site.line),
                            detail: format!(
                                "{} of boundary `{}` (post-expansion)",
                                site.detail, c.name
                            ),
                        });
                    }
                    // Subset rule: the expanded surface may not carry a public
                    // item the declared source set does not — a macro that
                    // synthesized one is a laundering attempt.
                    for item in ledger::expanded_public_items(&expanded) {
                        let key = (item.kind.clone(), item.name.clone());
                        if item.kind == "unknown" || !source_pub.contains(&key) {
                            findings.push(Finding {
                                code: "FLN-STRUCT-025",
                                path: format!("{}/src (expanded:{label}:{})", c.rel, item.line),
                                detail: format!(
                                    "expanded surface of boundary `{}` carries public item `{} {}` absent from the declared source set — macro-synthesized export",
                                    c.name, item.kind, item.name
                                ),
                            });
                        }
                    }
                }
                let expanded_allow_count = ledger::count_allow_unsafe_attributes(&expanded);
                if expanded_allow_count > source_allow_count {
                    findings.push(Finding {
                        code: "FLN-STRUCT-025",
                        path: format!("{}/src", c.rel),
                        detail: format!(
                            "expanded surface of boundary `{}` ({label}) carries {expanded_allow_count} allow(unsafe_code) attributes but only {source_allow_count} ledgered source sites exist — a macro synthesized an unsafe allowance",
                            c.name
                        ),
                    });
                }
            }
        }
    }
    Ok(findings)
}

/// The generated census's `Linkage::Export` symbol set, extracted from the
/// stable one-`AbiFn`-per-line rendering of `crates/fln-rt/src/abi.rs`.
/// Zero matches (missing file, format drift) fails closed — the covenant
/// cannot verify a join against an unreadable census.
fn census_export_symbols(root: &Path) -> Result<BTreeSet<String>, String> {
    let path = root.join(ABI_CENSUS_FILE);
    let text = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read {ABI_CENSUS_FILE}: {error}"))?;
    let mut out = BTreeSet::new();
    for line in text.lines() {
        if !line.contains("Linkage::Export") {
            continue;
        }
        let Some(idx) = line.find("name: \"") else {
            continue;
        };
        let rest = &line[idx + 7..];
        let Some(end) = rest.find('"') else {
            continue;
        };
        out.insert(rest[..end].to_string());
    }
    if out.is_empty() {
        return Err(format!(
            "{ABI_CENSUS_FILE}: no Linkage::Export census entries found (format drift?); the export covenant fails closed"
        ));
    }
    Ok(out)
}

/// FLN-STRUCT-026 — the C-ABI export covenant join (plan §6.5, bead
/// franken_lean-83r). Laws, all fail-closed:
///
/// * **census totality** — every `Linkage::Export` census symbol has exactly
///   one status row; a row naming a symbol outside the census is unknown;
///   `support` rows must NOT shadow census symbols (they exist for the
///   non-census link demands of the pin's `LEAN_MIMALLOC` inlines).
/// * **site⇄row equality** — every `export_name` site in the exporting crate
///   names a row with an implemented status (an `Unsupported` row with a
///   live site is a lie; a site without a row is unclassified), and every
///   implemented row has exactly one site (zero = stale claim, two = a
///   duplicate symbol definition the linker would reject anyway).
/// * **extractability** — a site whose symbol string cannot be recovered
///   exactly is a finding, never a skip.
fn c_export_covenant(
    root: &Path,
    status: Option<&export_status::ExportStatus>,
    sites: &[(String, usize, Option<String>)],
) -> Vec<Finding> {
    let mut findings = Vec::new();
    let Some(status) = status else {
        if !sites.is_empty() {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail: format!(
                    "{} export_name site(s) exist but {EXPORT_STATUS_FILE} is absent — every exported symbol needs a reviewed §6.5 status row",
                    sites.len()
                ),
            });
        }
        return findings;
    };
    let census = match census_export_symbols(root) {
        Ok(census) => census,
        Err(detail) => {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: ABI_CENSUS_FILE.to_string(),
                detail,
            });
            return findings;
        }
    };
    let rows: std::collections::BTreeMap<&str, &export_status::StatusRow> = status
        .rows
        .iter()
        .map(|row| (row.symbol.as_str(), row))
        .collect();
    for symbol in &census {
        if !rows.contains_key(symbol.as_str()) {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail: format!(
                    "census export symbol `{symbol}` has no status row — there is no unclassified symbol (§6.5)"
                ),
            });
        }
    }
    for row in &status.rows {
        if row.support || row.extern_row {
            if census.contains(&row.symbol) {
                findings.push(Finding {
                    code: "FLN-STRUCT-026",
                    path: EXPORT_STATUS_FILE.to_string(),
                    detail: format!(
                        "{} row `{}` shadows a lean.h census export symbol — census symbols use `row`",
                        if row.support { "support" } else { "extern" },
                        row.symbol
                    ),
                });
            }
        } else if !census.contains(&row.symbol) {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail: format!(
                    "row `{}` names a symbol absent from the census export set (stale or misspelled)",
                    row.symbol
                ),
            });
        }
    }
    let mut site_symbols: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for (path, line, symbol) in sites {
        match symbol {
            None => findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: format!("{path}:{line}"),
                detail: "export_name site whose symbol string cannot be extracted exactly; failing closed".to_string(),
            }),
            Some(symbol) => {
                *site_symbols.entry(symbol.clone()).or_insert(0) += 1;
                match rows.get(symbol.as_str()) {
                    None => findings.push(Finding {
                        code: "FLN-STRUCT-026",
                        path: format!("{path}:{line}"),
                        detail: format!(
                            "exported symbol `{symbol}` has no row in {EXPORT_STATUS_FILE} — unclassified export"
                        ),
                    }),
                    Some(row) if !row.implemented() => findings.push(Finding {
                        code: "FLN-STRUCT-026",
                        path: format!("{path}:{line}"),
                        detail: format!(
                            "exported symbol `{symbol}` is rowed `{}` — an Unsupported row with a live export site is a lie",
                            row.status
                        ),
                    }),
                    Some(_) => {}
                }
            }
        }
    }
    for (symbol, count) in &site_symbols {
        if *count > 1 {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail: format!("symbol `{symbol}` has {count} export sites — one site per symbol"),
            });
        }
    }
    for row in &status.rows {
        if row.implemented() && !site_symbols.contains_key(&row.symbol) {
            findings.push(Finding {
                code: "FLN-STRUCT-026",
                path: EXPORT_STATUS_FILE.to_string(),
                detail: format!(
                    "row `{}` claims status `{}` but no export site exists (stale claim)",
                    row.symbol, row.status
                ),
            });
        }
    }
    findings
}

/// Run `cargo rustc -- -Zunpretty=expanded` for one cfg of a boundary crate.
/// Deterministic for the pinned nightly; isolated target dir so concurrent
/// builds never contend on the workspace's primary target directory.
fn run_expansion(root: &Path, package: &str, test_cfg: bool) -> Result<String, String> {
    let mut command = std::process::Command::new("cargo");
    for name in std::env::vars_os().filter_map(|(name, _)| name.into_string().ok()) {
        if matches!(
            name.as_str(),
            "RUSTFLAGS"
                | "CARGO_ENCODED_RUSTFLAGS"
                | "CARGO_BUILD_RUSTFLAGS"
                | "CARGO_BUILD_RUSTC"
                | "CARGO_BUILD_RUSTC_WRAPPER"
                | "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"
                | "CARGO_BUILD_RUSTDOC"
                | "CARGO_BUILD_TARGET"
                | "RUSTC"
                | "RUSTC_WRAPPER"
                | "RUSTC_WORKSPACE_WRAPPER"
                | "RUSTDOC"
                | "RUSTDOCFLAGS"
        ) || (name != "CARGO_TARGET_DIR"
            && [
                "CARGO_TARGET_",
                "CARGO_ALIAS_",
                "CARGO_UNSTABLE_",
                "CARGO_REGISTRIES_",
                "CARGO_PROFILE_",
            ]
            .iter()
            .any(|prefix| name.starts_with(prefix)))
        {
            command.env_remove(name);
        }
    }
    command
        .current_dir(root)
        .arg("rustc")
        .arg("-q")
        .arg("--locked")
        .arg("-p")
        .arg(package)
        .arg("--lib");
    if test_cfg {
        command.arg("--profile").arg("test");
    }
    command
        .arg("--target-dir")
        .arg(root.join("target").join("structure-guard-expand"))
        .arg("--")
        .arg("-Zunpretty=expanded");
    let output = command
        .output()
        .map_err(|error| format!("cargo rustc did not run: {error}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let tail: String = stderr
            .lines()
            .rev()
            .take(4)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join(" | ");
        return Err(format!("cargo rustc exited {}: {tail}", output.status));
    }
    String::from_utf8(output.stdout).map_err(|_| "expanded output is not UTF-8".to_string())
}
