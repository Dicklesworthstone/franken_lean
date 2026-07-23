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

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};

use crate::boundary_api;
use crate::graph::{self, CrateKind, GraphFile};
use crate::ledger::{self, AllowSite};
use crate::manifest::{self, Manifest};
use crate::report::fnv1a64;
use crate::{
    ALLOWLIST_FILE, BOUNDARY_API_FILE, GRAPH_FILE, LEDGER_FILE, LOCK_FILE, SUITE_LOCK_FILE,
    TOOLCHAIN_FILE,
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

fn audit_repository_cargo_config(root: &Path, findings: &mut Vec<Finding>) -> Result<(), String> {
    // Package and workspace manifests are intentionally constrained above, but Cargo
    // also reads repository-local configuration before it compiles anything. Such a
    // file can inject rustflags (including lint caps), wrappers, linkers, runners, or
    // source replacement without appearing in the reviewed dependency graph. There is
    // no approved repository-local Cargo configuration surface yet, so both the current
    // and legacy filenames fail closed.
    for rel in [".cargo/config.toml", ".cargo/config"] {
        match fs::symlink_metadata(root.join(rel)) {
            Ok(_) => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: rel.to_string(),
                detail: "repository-local Cargo configuration is forbidden because it can change the compiler, lint, linker, runner, or dependency-source contract outside the reviewed manifests"
                    .to_string(),
            }),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("cannot inspect {rel}: {error}")),
        }
    }
    Ok(())
}

/// Count covenant-relevant lines: non-blank, not starting with `//` after trim.
/// Block comments count as code — the covenant is deliberately conservative.
fn count_loc(dir: &Path) -> Result<usize, String> {
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
                let text = fs::read_to_string(&p)
                    .map_err(|e| format!("cannot read {}: {e}", p.display()))?;
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

fn validate_constitutional_baseline(g: &GraphFile, findings: &mut Vec<Finding>) {
    let plan_ranks = [
        ("fln-core", 0),
        ("fln-hash", 1),
        ("fln-bignum", 1),
        ("fln-libm", 1),
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
        let text = fs::read_to_string(c.dir.join("Cargo.toml"))
            .map_err(|e| format!("cannot read {manifest_rel}: {e}"))?;
        match manifest::parse(&text, &manifest_rel) {
            Ok(m) => c.manifest = Some(m),
            Err(e) => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: manifest_rel,
                detail: e,
            }),
        }
    }

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
            let text =
                fs::read_to_string(&root_file).map_err(|e| format!("cannot read {rel}: {e}"))?;
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
            ledger::scan_allow_sites(&c.dir, &c.rel, &mut sites)?;
        }
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
        ledger::scan_external_exports(&src, &format!("{}/src", c.rel), &mut exports)?;
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
            let text = fs::read_to_string(path)
                .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
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
        findings.extend(expansion_covenant(root, c, &source_pub)?);
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

    // ---- line-count covenants ----------------------------------------------------------
    for (crate_name, limit) in &g.covenants {
        let Some(c) = on_disk.get(crate_name.as_str()) else {
            continue;
        };
        let src = c.dir.join("src");
        let mut covenant_sources = Vec::new();
        collect_rs_files(&src, &mut covenant_sources)?;
        for source in covenant_sources {
            let text = fs::read_to_string(&source)
                .map_err(|error| format!("cannot read {}: {error}", source.display()))?;
            for escape in ledger::source_escape_sites(&text) {
                let rel = source
                    .strip_prefix(root)
                    .unwrap_or(&source)
                    .to_string_lossy()
                    .replace('\\', "/");
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
        let loc = count_loc(&src)?;
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

    findings.sort_by(|a, b| (a.code, &a.path, &a.detail).cmp(&(b.code, &b.path, &b.detail)));
    Ok(RunOutcome {
        findings,
        crate_count: discovered.len(),
        edge_count: actual_edges.len(),
        graph_digest,
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
                    for site in ledger::expanded_surface_violations(&expanded) {
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

/// Run `cargo rustc -- -Zunpretty=expanded` for one cfg of a boundary crate.
/// Deterministic for the pinned nightly; isolated target dir so concurrent
/// builds never contend on the workspace's primary target directory.
fn run_expansion(root: &Path, package: &str, test_cfg: bool) -> Result<String, String> {
    let mut command = std::process::Command::new("cargo");
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
