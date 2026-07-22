//! The dependency-closure audit (plan D1, §22.1-10; bead franken_lean-xwf):
//! `Cargo.lock` ⇄ `ci/CLOSURE_ALLOWLIST.txt` ⇄ `SUITE.lock` ⇄ `rust-toolchain.toml`.
//!
//! What is enforced, both directions, on every run:
//!
//! * every `Cargo.lock` package has exactly one allowlist row (name + version + source
//!   class), and every allowlist row matches a lock package — no unlisted package, no
//!   stale approval (`FLN-STRUCT-018` / `FLN-STRUCT-019`);
//! * registry/git packages are prohibited outright: a lock package carrying a `source`
//!   or `checksum` is a finding, not a policy question (`FLN-STRUCT-018`);
//! * `build-script=no` rows are verified against the tree (no `build.rs` may exist);
//! * `SUITE.lock` agrees with `rust-toolchain.toml` (the nightly pin) and with the
//!   `suite-dep` allowlist of `ci/WORKSPACE_GRAPH.txt`, bidirectionally
//!   (`FLN-STRUCT-020`);
//! * a missing or malformed governance file is a `FLN-STRUCT-016` finding — the audit
//!   degrades to findings, never to a silent skip.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use crate::checks::Finding;
use crate::graph::{CrateKind, GraphFile};
use crate::{ALLOWLIST_FILE, LOCK_FILE, SUITE_LOCK_FILE, TOOLCHAIN_FILE};

#[derive(Debug)]
pub struct LockPackage {
    pub name: String,
    pub version: String,
    pub source: Option<String>,
    pub checksum: Option<String>,
}

type PendingLockPackage = (
    Option<String>,
    Option<String>,
    Option<String>,
    Option<String>,
);

/// Parse the constrained `Cargo.lock` shape (v4): `[[package]]` entries with
/// `name`/`version` and optional `source`/`checksum`/`dependencies` array.
pub fn parse_cargo_lock(text: &str, display_path: &str) -> Result<Vec<LockPackage>, String> {
    let mut packages: Vec<LockPackage> = Vec::new();
    let mut current: Option<PendingLockPackage> = None;
    let mut in_array = false;

    let finish =
        |cur: &mut Option<PendingLockPackage>, out: &mut Vec<LockPackage>| -> Result<(), String> {
            if let Some((name, version, source, checksum)) = cur.take() {
                out.push(LockPackage {
                    name: name.ok_or_else(|| format!("{display_path}: package without name"))?,
                    version: version
                        .ok_or_else(|| format!("{display_path}: package without version"))?,
                    source,
                    checksum,
                });
            }
            Ok(())
        };

    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if in_array {
            if line == "]" {
                in_array = false;
            }
            continue;
        }
        if line == "[[package]]" {
            finish(&mut current, &mut packages)?;
            current = Some((None, None, None, None));
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("{display_path}:{lineno}: expected `key = value`"));
        };
        let key = key.trim();
        let value = value.trim();
        if value == "[" {
            in_array = true;
            continue;
        }
        let unquoted = value.strip_prefix('"').and_then(|v| v.strip_suffix('"'));
        match (&mut current, key) {
            (None, "version") => {} // the top-level lockfile format version
            (None, _) => {
                return Err(format!(
                    "{display_path}:{lineno}: `{key}` outside any [[package]]"
                ));
            }
            (Some(cur), "name") => {
                cur.0 = Some(
                    unquoted
                        .ok_or_else(|| format!("{display_path}:{lineno}: unquoted name"))?
                        .to_string(),
                );
            }
            (Some(cur), "version") => {
                cur.1 = Some(
                    unquoted
                        .ok_or_else(|| format!("{display_path}:{lineno}: unquoted version"))?
                        .to_string(),
                );
            }
            (Some(cur), "source") => cur.2 = unquoted.map(str::to_string),
            (Some(cur), "checksum") => cur.3 = unquoted.map(str::to_string),
            (Some(_), other) => {
                return Err(format!(
                    "{display_path}:{lineno}: unsupported lockfile key `{other}`"
                ));
            }
        }
    }
    finish(&mut current, &mut packages)?;
    Ok(packages)
}

#[derive(Debug)]
pub struct AllowRow {
    pub name: String,
    pub version: String,
    /// `workspace` or `suite`.
    pub source: String,
    pub build_script: bool,
    pub policy: String,
}

const ALLOW_KEYS: [&str; 11] = [
    "version",
    "source",
    "checksum",
    "license",
    "build-script",
    "proc-macro",
    "native-link",
    "unsafe-audit",
    "policy",
    "owner",
    "upgrade",
];

pub fn parse_allowlist(text: &str) -> Result<Vec<AllowRow>, String> {
    let mut rows: Vec<AllowRow> = Vec::new();
    let mut saw_schema = false;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("CLOSURE_ALLOWLIST.txt:{lineno}: {msg}");
        if !saw_schema {
            if line == "schema fln-closure-allowlist/1" {
                saw_schema = true;
                continue;
            }
            return Err(err(
                "first directive must be `schema fln-closure-allowlist/1`",
            ));
        }
        let Some(rest) = line.strip_prefix("package ") else {
            return Err(err("expected `package <name> key=value ... reason=<text>`"));
        };
        let (head, reason) = rest
            .split_once("reason=")
            .ok_or_else(|| err("row must end with reason=<text>"))?;
        if reason.trim().is_empty() {
            return Err(err("reason must be non-empty"));
        }
        let mut tokens = head.split_whitespace();
        let name = tokens.next().ok_or_else(|| err("missing package name"))?;
        let mut kv: BTreeMap<&str, &str> = BTreeMap::new();
        for token in tokens {
            let (k, v) = token
                .split_once('=')
                .ok_or_else(|| err("fields must be key=value"))?;
            if !ALLOW_KEYS.contains(&k) {
                return Err(err(&format!("unknown field `{k}`")));
            }
            if kv.insert(k, v).is_some() {
                return Err(err(&format!("duplicate field `{k}`")));
            }
        }
        for required in ALLOW_KEYS {
            if !kv.contains_key(required) {
                return Err(err(&format!("missing field `{required}` for `{name}`")));
            }
        }
        let source = kv["source"];
        if source != "workspace" && source != "suite" {
            return Err(err(
                "source must be workspace|suite (registry is prohibited)",
            ));
        }
        let build_script = match kv["build-script"] {
            "yes" => true,
            "no" => false,
            _ => return Err(err("build-script must be yes|no")),
        };
        let policy = kv["policy"];
        if !["runtime", "build", "dev", "fuzz"].contains(&policy) {
            return Err(err("policy must be runtime|build|dev|fuzz"));
        }
        if rows.iter().any(|r| r.name == name) {
            return Err(err(&format!("duplicate row for `{name}`")));
        }
        rows.push(AllowRow {
            name: name.to_string(),
            version: kv["version"].to_string(),
            source: source.to_string(),
            build_script,
            policy: policy.to_string(),
        });
    }
    if !saw_schema {
        return Err("CLOSURE_ALLOWLIST.txt: missing schema line".to_string());
    }
    Ok(rows)
}

#[derive(Debug, Default)]
pub struct SuiteLock {
    pub rust_nightly: String,
    /// repo -> pinned commit
    pub suites: BTreeMap<String, String>,
    /// allowed suite package -> repo
    pub crates: BTreeMap<String, String>,
    pub reference: Option<(String, String, String)>,
    pub reference_tree: Option<String>,
    pub corpus: Option<(String, String, String)>,
}

fn is_hex40(s: &str) -> bool {
    s.len() == 40 && s.chars().all(|c| c.is_ascii_hexdigit())
}

pub fn parse_suite_lock(text: &str) -> Result<SuiteLock, String> {
    let mut lock = SuiteLock::default();
    let mut saw_schema = false;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |msg: &str| format!("SUITE.lock:{lineno}: {msg}");
        if !saw_schema {
            if line == "schema fln-suite-lock/1" {
                saw_schema = true;
                continue;
            }
            return Err(err("first directive must be `schema fln-suite-lock/1`"));
        }
        let tokens: Vec<&str> = line.split_whitespace().collect();
        match tokens[0] {
            "rust-nightly" if tokens.len() == 2 => lock.rust_nightly = tokens[1].to_string(),
            "rust-release" | "rust-commit" | "target" if tokens.len() == 2 => {}
            "suite" if tokens.len() == 4 => {
                let commit = tokens[2]
                    .strip_prefix("commit=")
                    .filter(|c| is_hex40(c))
                    .ok_or_else(|| err("suite row needs commit=<40-hex>"))?;
                tokens[3]
                    .strip_prefix("path=")
                    .ok_or_else(|| err("suite row needs path=<abs>"))?;
                if lock
                    .suites
                    .insert(tokens[1].to_string(), commit.to_string())
                    .is_some()
                {
                    return Err(err("duplicate suite row"));
                }
            }
            "crate" if tokens.len() == 3 => {
                let repo = tokens[2]
                    .strip_prefix("repo=")
                    .ok_or_else(|| err("crate row needs repo=<repo>"))?;
                if lock
                    .crates
                    .insert(tokens[1].to_string(), repo.to_string())
                    .is_some()
                {
                    return Err(err("duplicate crate row"));
                }
            }
            "reference" if tokens.len() == 5 => {
                let tag = tokens[2]
                    .strip_prefix("tag=")
                    .ok_or_else(|| err("needs tag=<tag>"))?;
                let commit = tokens[3]
                    .strip_prefix("commit=")
                    .filter(|c| is_hex40(c))
                    .ok_or_else(|| err("needs commit=<40-hex>"))?;
                let tree = tokens[4]
                    .strip_prefix("tree=")
                    .filter(|tree| is_hex40(tree))
                    .ok_or_else(|| err("reference needs tree=<40-hex>"))?;
                if lock
                    .reference
                    .replace((tokens[1].to_string(), tag.to_string(), commit.to_string()))
                    .is_some()
                    || lock.reference_tree.replace(tree.to_string()).is_some()
                {
                    return Err(err("duplicate reference row"));
                }
            }
            "corpus" if tokens.len() == 4 => {
                let tag = tokens[2]
                    .strip_prefix("tag=")
                    .ok_or_else(|| err("needs tag=<tag>"))?;
                let commit = tokens[3]
                    .strip_prefix("commit=")
                    .filter(|commit| is_hex40(commit))
                    .ok_or_else(|| err("needs commit=<40-hex>"))?;
                if lock
                    .corpus
                    .replace((tokens[1].to_string(), tag.to_string(), commit.to_string()))
                    .is_some()
                {
                    return Err(err("duplicate corpus row"));
                }
            }
            _ => return Err(err("unknown or malformed directive")),
        }
    }
    if !saw_schema {
        return Err("SUITE.lock: missing schema line".to_string());
    }
    if lock.rust_nightly.is_empty() {
        return Err("SUITE.lock: missing rust-nightly row".to_string());
    }
    if lock.reference.is_none() || lock.reference_tree.is_none() || lock.corpus.is_none() {
        return Err(
            "SUITE.lock: reference with tree and corpus rows are both required".to_string(),
        );
    }
    for repo in lock.crates.values() {
        if !lock.suites.contains_key(repo) {
            return Err(format!(
                "SUITE.lock: crate row names unpinned repo `{repo}`"
            ));
        }
    }
    Ok(lock)
}

fn toolchain_quoted(value: &str) -> Option<&str> {
    value
        .strip_prefix('"')
        .and_then(|inner| inner.strip_suffix('"'))
        .filter(|inner| !inner.is_empty() && !inner.contains(['"', '\\']))
}

fn toolchain_string_array(value: &str) -> Result<(), &'static str> {
    let inner = value
        .strip_prefix('[')
        .and_then(|rest| rest.strip_suffix(']'))
        .ok_or("must be a one-line array")?;
    if inner.trim().is_empty() {
        return Ok(());
    }
    let mut seen = BTreeSet::new();
    for item in inner.split(',') {
        let parsed = toolchain_quoted(item.trim())
            .ok_or("array entries must be non-empty unescaped quoted strings")?;
        if !seen.insert(parsed) {
            return Err("array entries must be unique");
        }
    }
    Ok(())
}

/// Extract the one exact `channel = "..."` from the constrained
/// `rust-toolchain.toml` shape. A section-insensitive search is not sufficient:
/// Cargo/rustup could select a path or a later toolchain section while a decoy key
/// satisfies the lock comparison.
pub fn parse_toolchain_channel(text: &str) -> Result<String, String> {
    let mut in_toolchain = false;
    let mut saw_toolchain = false;
    let mut channel: Option<String> = None;
    for (idx, raw) in text.lines().enumerate() {
        let lineno = idx + 1;
        let line = match raw.find('#') {
            Some(pos) => &raw[..pos],
            None => raw,
        }
        .trim();
        if line.is_empty() {
            continue;
        }
        let err = |message: &str| format!("rust-toolchain.toml:{lineno}: {message}: `{line}`");
        if line.starts_with('[') {
            if line != "[toolchain]" {
                return Err(err("only the `[toolchain]` section is supported"));
            }
            if saw_toolchain {
                return Err(err("duplicate `[toolchain]` section"));
            }
            saw_toolchain = true;
            in_toolchain = true;
            continue;
        }
        if !in_toolchain {
            return Err(err("content before `[toolchain]`"));
        }
        let (key, value) = line
            .split_once('=')
            .ok_or_else(|| err("expected `key = value`"))?;
        match key.trim() {
            "channel" => {
                let value = value.trim();
                let parsed = toolchain_quoted(value)
                    .ok_or_else(|| err("channel must be one non-empty unescaped quoted string"))?;
                if channel.replace(parsed.to_string()).is_some() {
                    return Err(err("duplicate channel key"));
                }
            }
            "components" | "targets" => {
                toolchain_string_array(value.trim()).map_err(&err)?;
            }
            "profile" => {
                let profile = toolchain_quoted(value.trim())
                    .ok_or_else(|| err("profile must be one unescaped quoted string"))?;
                if !matches!(profile, "minimal" | "default" | "complete") {
                    return Err(err("profile must be minimal|default|complete"));
                }
            }
            "path" => return Err(err("path-based toolchains are forbidden; pin a channel")),
            _ => return Err(err("unsupported toolchain key")),
        }
    }
    if !saw_toolchain {
        return Err("rust-toolchain.toml: missing `[toolchain]` section".to_string());
    }
    channel.ok_or_else(|| "rust-toolchain.toml: missing channel".to_string())
}

/// Run the closure audit. Missing/malformed governance files degrade to
/// `FLN-STRUCT-016` findings so the remaining structural checks still report.
pub fn audit(root: &Path, graph: &GraphFile) -> Vec<Finding> {
    let mut findings: Vec<Finding> = Vec::new();
    let read = |rel: &str, findings: &mut Vec<Finding>| -> Option<String> {
        match fs::read_to_string(root.join(rel)) {
            Ok(text) => Some(text),
            Err(e) => {
                findings.push(Finding {
                    code: "FLN-STRUCT-016",
                    path: rel.to_string(),
                    detail: format!("cannot read governance file: {e}"),
                });
                None
            }
        }
    };

    // ---- Cargo.lock vs CLOSURE_ALLOWLIST.txt -------------------------------------------
    let packages =
        read(LOCK_FILE, &mut findings).and_then(|text| match parse_cargo_lock(&text, LOCK_FILE) {
            Ok(p) => Some(p),
            Err(e) => {
                findings.push(Finding {
                    code: "FLN-STRUCT-016",
                    path: LOCK_FILE.to_string(),
                    detail: e,
                });
                None
            }
        });
    let rows = read(ALLOWLIST_FILE, &mut findings).and_then(|text| match parse_allowlist(&text) {
        Ok(r) => Some(r),
        Err(e) => {
            findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: ALLOWLIST_FILE.to_string(),
                detail: e,
            });
            None
        }
    });

    if let (Some(packages), Some(rows)) = (&packages, &rows) {
        let by_name: BTreeMap<&str, &AllowRow> =
            rows.iter().map(|r| (r.name.as_str(), r)).collect();
        for pkg in packages {
            if pkg.source.is_some() || pkg.checksum.is_some() {
                findings.push(Finding {
                    code: "FLN-STRUCT-018",
                    path: LOCK_FILE.to_string(),
                    detail: format!(
                        "package `{}` comes from a registry/git source — external packages are prohibited (D1)",
                        pkg.name
                    ),
                });
                continue;
            }
            match by_name.get(pkg.name.as_str()) {
                None => findings.push(Finding {
                    code: "FLN-STRUCT-018",
                    path: LOCK_FILE.to_string(),
                    detail: format!(
                        "package `{}` {} has no row in {ALLOWLIST_FILE}",
                        pkg.name, pkg.version
                    ),
                }),
                Some(row) if row.version != pkg.version => findings.push(Finding {
                    code: "FLN-STRUCT-018",
                    path: ALLOWLIST_FILE.to_string(),
                    detail: format!(
                        "package `{}`: lock has {}, allowlist approves {}",
                        pkg.name, pkg.version, row.version
                    ),
                }),
                Some(row) => {
                    if row.source == "workspace" && !graph.crates.contains_key(&pkg.name) {
                        findings.push(Finding {
                            code: "FLN-STRUCT-018",
                            path: ALLOWLIST_FILE.to_string(),
                            detail: format!(
                                "package `{}` claims source=workspace but is not a declared workspace crate",
                                pkg.name
                            ),
                        });
                    }
                    if row.source == "suite" && !graph.suite_deps.iter().any(|s| s == &pkg.name) {
                        findings.push(Finding {
                            code: "FLN-STRUCT-018",
                            path: ALLOWLIST_FILE.to_string(),
                            detail: format!(
                                "package `{}` claims source=suite but is not a WORKSPACE_GRAPH suite-dep",
                                pkg.name
                            ),
                        });
                    }
                }
            }
        }
        let lock_names: BTreeSet<&str> = packages.iter().map(|p| p.name.as_str()).collect();
        for row in rows {
            if !lock_names.contains(row.name.as_str()) {
                findings.push(Finding {
                    code: "FLN-STRUCT-019",
                    path: ALLOWLIST_FILE.to_string(),
                    detail: format!(
                        "allowlist row `{}` matches no Cargo.lock package (stale approval)",
                        row.name
                    ),
                });
            }
            if !row.build_script
                && row.source == "workspace"
                && let Some(decl) = graph.crates.get(&row.name)
            {
                let subdir = match decl.kind {
                    CrateKind::Tool => "tools",
                    _ => "crates",
                };
                if root.join(subdir).join(&row.name).join("build.rs").is_file() {
                    findings.push(Finding {
                        code: "FLN-STRUCT-018",
                        path: format!("{subdir}/{}/build.rs", row.name),
                        detail: format!(
                            "`{}` is approved with build-script=no but has a build.rs",
                            row.name
                        ),
                    });
                }
            }
        }
    }

    // ---- SUITE.lock vs rust-toolchain.toml and the graph suite-dep allowlist -----------
    let suite_lock =
        read(SUITE_LOCK_FILE, &mut findings).and_then(|text| match parse_suite_lock(&text) {
            Ok(l) => Some(l),
            Err(e) => {
                findings.push(Finding {
                    code: "FLN-STRUCT-016",
                    path: SUITE_LOCK_FILE.to_string(),
                    detail: e,
                });
                None
            }
        });
    if let Some(lock) = &suite_lock {
        match read(TOOLCHAIN_FILE, &mut findings).map(|text| parse_toolchain_channel(&text)) {
            Some(Ok(channel)) if channel != lock.rust_nightly => findings.push(Finding {
                code: "FLN-STRUCT-020",
                path: TOOLCHAIN_FILE.to_string(),
                detail: format!(
                    "channel `{channel}` != SUITE.lock rust-nightly `{}` — one ceremony, one pin",
                    lock.rust_nightly
                ),
            }),
            Some(Ok(_)) | None => {}
            Some(Err(e)) => findings.push(Finding {
                code: "FLN-STRUCT-016",
                path: TOOLCHAIN_FILE.to_string(),
                detail: e,
            }),
        }
        for dep in &graph.suite_deps {
            if !lock.crates.contains_key(dep) {
                findings.push(Finding {
                    code: "FLN-STRUCT-020",
                    path: SUITE_LOCK_FILE.to_string(),
                    detail: format!(
                        "WORKSPACE_GRAPH suite-dep `{dep}` has no `crate` row in SUITE.lock"
                    ),
                });
            }
        }
        for pkg in lock.crates.keys() {
            if !graph.suite_deps.iter().any(|s| s == pkg) {
                findings.push(Finding {
                    code: "FLN-STRUCT-020",
                    path: SUITE_LOCK_FILE.to_string(),
                    detail: format!(
                        "SUITE.lock crate row `{pkg}` is not a WORKSPACE_GRAPH suite-dep"
                    ),
                });
            }
        }
    }
    findings
}

#[cfg(test)]
mod tests {
    use super::*;

    const LOCK_OK: &str = "# generated\nversion = 4\n\n[[package]]\nname = \"fln-core\"\nversion = \"0.0.0\"\n\n[[package]]\nname = \"a\"\nversion = \"1.0.0\"\ndependencies = [\n \"fln-core\",\n]\n";

    #[test]
    fn parses_cargo_lock() {
        let pkgs = parse_cargo_lock(LOCK_OK, "t").expect("parses");
        assert_eq!(pkgs.len(), 2);
        assert_eq!(pkgs[0].name, "fln-core");
        assert!(pkgs[0].source.is_none());
    }

    #[test]
    fn parses_registry_source_and_rejects_malformed_lock() {
        let reg = "version = 4\n[[package]]\nname = \"serde\"\nversion = \"1.0.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"abc\"\n";
        let pkgs = parse_cargo_lock(reg, "t").expect("parses");
        assert!(pkgs[0].source.is_some());
        assert!(parse_cargo_lock("[[package]]\nversion = \"1\"\n", "t").is_err());
        assert!(parse_cargo_lock("name = \"x\"\n", "t").is_err());
    }

    const ROW_OK: &str = "schema fln-closure-allowlist/1\npackage fln-core version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit=forbid policy=runtime owner=fl upgrade=workspace reason=stub\n";

    #[test]
    fn parses_allowlist_and_rejects_bad_rows() {
        let rows = parse_allowlist(ROW_OK).expect("parses");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].source, "workspace");
        assert!(!rows[0].build_script);

        assert!(parse_allowlist("package x reason=y\n").is_err()); // no schema
        let registry = ROW_OK.replace("source=workspace", "source=registry");
        assert!(parse_allowlist(&registry).is_err());
        let noreason = ROW_OK.replace("reason=stub", "");
        assert!(parse_allowlist(&noreason).is_err());
        let dup = format!(
            "{ROW_OK}{}",
            &ROW_OK["schema fln-closure-allowlist/1\n".len()..]
        );
        assert!(parse_allowlist(&dup).is_err());
    }

    const SUITE_OK: &str = "schema fln-suite-lock/1\nrust-nightly nightly-2026-07-13\ntarget x86_64-unknown-linux-gnu\nsuite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync\ncrate asupersync repo=asupersync\nreference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91\ncorpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997\n";

    #[test]
    fn parses_suite_lock_and_enforces_required_rows() {
        let lock = parse_suite_lock(SUITE_OK).expect("parses");
        assert_eq!(lock.rust_nightly, "nightly-2026-07-13");
        assert_eq!(lock.crates["asupersync"], "asupersync");
        assert!(lock.reference.is_some());
        assert_eq!(
            lock.reference_tree.as_deref(),
            Some("ba16913719a2f6a15a826918fbe6ba9dd5413e91")
        );

        let no_ref = SUITE_OK.replace("reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91\n", "");
        assert!(parse_suite_lock(&no_ref).is_err());
        let orphan_crate =
            SUITE_OK.replace("crate asupersync repo=asupersync", "crate atp repo=atp");
        assert!(parse_suite_lock(&orphan_crate).is_err());
        let short_hash = SUITE_OK.replace(
            "commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb",
            "commit=e464",
        );
        assert!(parse_suite_lock(&short_hash).is_err());
    }

    #[test]
    fn parses_toolchain_channel() {
        let text =
            "# pin\n[toolchain]\nchannel = \"nightly-2026-07-13\"\ncomponents = [\"rustfmt\"]\n";
        assert_eq!(
            parse_toolchain_channel(text).expect("parses"),
            "nightly-2026-07-13"
        );
        assert!(parse_toolchain_channel("[toolchain]\n").is_err());
        assert!(
            parse_toolchain_channel(
                "[metadata]\nchannel = \"nightly-2026-07-13\"\n[toolchain]\nchannel = \"stable\"\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\npath = \"/tmp/toolchain\"\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\nchannel = \"stable\"\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\nunknown = true\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\ncomponents = \"rustfmt\"\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\ncomponents = [\"rustfmt\", \"rustfmt\"]\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\nprofile = \"fast\"\n"
            )
            .is_err()
        );
    }
}
