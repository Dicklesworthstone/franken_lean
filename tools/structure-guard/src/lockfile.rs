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
//! * every allowlist policy field is semantic: manifest version/license/dependency
//!   closure, path-source checksum, build script, target kind, unsafe posture, owner,
//!   lane, and upgrade authority are independently derived and compared;
//! * `SUITE.lock` agrees with `rust-toolchain.toml` (the nightly pin) and with the
//!   `suite-dep` allowlist of `ci/WORKSPACE_GRAPH.txt`, bidirectionally; every active
//!   suite package resolves to the exact mapped repo path and checked-out commit
//!   (`FLN-STRUCT-020` / `FLN-STRUCT-031`);
//! * a missing or malformed governance file is a `FLN-STRUCT-016` finding — the audit
//!   degrades to findings, never to a silent skip.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};

use crate::checks::Finding;
use crate::graph::{CrateKind, GraphFile};
use crate::manifest;
use crate::{ALLOWLIST_FILE, LOCK_FILE, SUITE_LOCK_FILE, TOOLCHAIN_FILE};

#[derive(Debug)]
pub struct LockPackage {
    pub name: String,
    pub version: String,
    pub source: Option<String>,
    pub checksum: Option<String>,
    pub dependencies: BTreeSet<String>,
}

#[derive(Default)]
struct PendingLockPackage {
    name: Option<String>,
    version: Option<String>,
    source: Option<String>,
    checksum: Option<String>,
    dependencies: Option<BTreeSet<String>>,
}

fn lock_quoted(value: &str) -> Option<&str> {
    value
        .strip_prefix('"')
        .and_then(|inner| inner.strip_suffix('"'))
        .filter(|inner| !inner.is_empty() && !inner.contains(['"', '\\']))
}

/// Parse the constrained `Cargo.lock` shape (v4): `[[package]]` entries with
/// `name`/`version` and optional `source`/`checksum`/`dependencies` array.
pub fn parse_cargo_lock(text: &str, display_path: &str) -> Result<Vec<LockPackage>, String> {
    let mut packages: Vec<LockPackage> = Vec::new();
    let mut current: Option<PendingLockPackage> = None;
    let mut lock_version: Option<u64> = None;
    let mut dependency_array_line: Option<usize> = None;
    let mut package_names = BTreeSet::new();

    let mut finish =
        |cur: &mut Option<PendingLockPackage>, out: &mut Vec<LockPackage>| -> Result<(), String> {
            if let Some(package) = cur.take() {
                let name = package
                    .name
                    .ok_or_else(|| format!("{display_path}: package without name"))?;
                if !package_names.insert(name.clone()) {
                    return Err(format!(
                        "{display_path}: duplicate package identity for `{name}`"
                    ));
                }
                out.push(LockPackage {
                    name,
                    version: package
                        .version
                        .ok_or_else(|| format!("{display_path}: package without version"))?,
                    source: package.source,
                    checksum: package.checksum,
                    dependencies: package.dependencies.unwrap_or_default(),
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
        if let Some(opened_at) = dependency_array_line {
            if line == "]" {
                dependency_array_line = None;
                continue;
            }
            let value = line.strip_suffix(',').unwrap_or(line).trim();
            let dependency = lock_quoted(value).ok_or_else(|| {
                format!(
                    "{display_path}:{lineno}: dependency array entries must be non-empty unescaped quoted strings"
                )
            })?;
            let dependencies = current
                .as_mut()
                .and_then(|package| package.dependencies.as_mut())
                .ok_or_else(|| {
                    format!(
                        "{display_path}:{opened_at}: internal parser state lost dependencies array"
                    )
                })?;
            if !dependencies.insert(dependency.to_string()) {
                return Err(format!(
                    "{display_path}:{lineno}: duplicate dependency `{dependency}`"
                ));
            }
            continue;
        }
        if line == "[[package]]" {
            if lock_version != Some(4) {
                return Err(format!(
                    "{display_path}:{lineno}: `version = 4` must appear exactly once before packages"
                ));
            }
            finish(&mut current, &mut packages)?;
            current = Some(PendingLockPackage::default());
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("{display_path}:{lineno}: expected `key = value`"));
        };
        let key = key.trim();
        let value = value.trim();
        match (&mut current, key) {
            (None, "version") => {
                if lock_version.is_some() {
                    return Err(format!(
                        "{display_path}:{lineno}: duplicate top-level version"
                    ));
                }
                let parsed = value.parse::<u64>().map_err(|_| {
                    format!("{display_path}:{lineno}: lockfile version must be integer 4")
                })?;
                if parsed != 4 {
                    return Err(format!(
                        "{display_path}:{lineno}: unsupported lockfile version {parsed}; exactly 4 is required"
                    ));
                }
                lock_version = Some(parsed);
            }
            (None, _) => {
                return Err(format!(
                    "{display_path}:{lineno}: `{key}` outside any [[package]]"
                ));
            }
            (Some(package), "name") => {
                if package.name.is_some() {
                    return Err(format!("{display_path}:{lineno}: duplicate package name"));
                }
                package.name = Some(
                    lock_quoted(value)
                        .ok_or_else(|| format!("{display_path}:{lineno}: unquoted name"))?
                        .to_string(),
                );
            }
            (Some(package), "version") => {
                if package.version.is_some() {
                    return Err(format!(
                        "{display_path}:{lineno}: duplicate package version"
                    ));
                }
                package.version = Some(
                    lock_quoted(value)
                        .ok_or_else(|| format!("{display_path}:{lineno}: unquoted version"))?
                        .to_string(),
                );
            }
            (Some(package), "source") => {
                if package.source.is_some() {
                    return Err(format!("{display_path}:{lineno}: duplicate package source"));
                }
                package.source = Some(
                    lock_quoted(value)
                        .ok_or_else(|| format!("{display_path}:{lineno}: unquoted source"))?
                        .to_string(),
                );
            }
            (Some(package), "checksum") => {
                if package.checksum.is_some() {
                    return Err(format!(
                        "{display_path}:{lineno}: duplicate package checksum"
                    ));
                }
                let checksum = lock_quoted(value)
                    .ok_or_else(|| format!("{display_path}:{lineno}: unquoted checksum"))?;
                if checksum.len() != 64
                    || !checksum
                        .chars()
                        .all(|character| character.is_ascii_hexdigit())
                {
                    return Err(format!(
                        "{display_path}:{lineno}: checksum must be exactly 64 hexadecimal digits"
                    ));
                }
                package.checksum = Some(checksum.to_ascii_lowercase());
            }
            (Some(package), "dependencies") => {
                if package.dependencies.is_some() {
                    return Err(format!(
                        "{display_path}:{lineno}: duplicate package dependencies"
                    ));
                }
                package.dependencies = Some(BTreeSet::new());
                match value {
                    "[]" => {}
                    "[" => dependency_array_line = Some(lineno),
                    _ => {
                        return Err(format!(
                            "{display_path}:{lineno}: dependencies must be `[]` or a multiline array"
                        ));
                    }
                }
            }
            (Some(_), other) => {
                return Err(format!(
                    "{display_path}:{lineno}: unsupported lockfile key `{other}`"
                ));
            }
        }
    }
    if let Some(opened_at) = dependency_array_line {
        return Err(format!(
            "{display_path}:{opened_at}: unterminated dependencies array"
        ));
    }
    finish(&mut current, &mut packages)?;
    if lock_version != Some(4) {
        return Err(format!(
            "{display_path}: missing required top-level `version = 4`"
        ));
    }
    Ok(packages)
}

#[derive(Debug)]
pub struct AllowRow {
    pub name: String,
    pub version: String,
    /// `workspace` or `suite`.
    pub source: String,
    pub checksum: String,
    pub license: String,
    pub build_script: bool,
    pub proc_macro: bool,
    pub native_link: bool,
    pub unsafe_audit: String,
    pub policy: String,
    pub owner: String,
    pub upgrade: String,
    pub reason: String,
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

fn is_safe_atom(value: &str) -> bool {
    !value.is_empty()
        && value
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.' | '+' | '/'))
}

fn parse_yes_no(value: &str, field: &str) -> Result<bool, String> {
    match value {
        "yes" => Ok(true),
        "no" => Ok(false),
        _ => Err(format!("{field} must be yes|no")),
    }
}

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
            .split_once(" reason=")
            .ok_or_else(|| err("row must end with reason=<text>"))?;
        let reason = reason.trim();
        if reason.is_empty() {
            return Err(err("reason must be non-empty"));
        }
        let mut tokens = head.split_whitespace();
        let name = tokens.next().ok_or_else(|| err("missing package name"))?;
        if !is_safe_atom(name) {
            return Err(err("package name contains unsupported characters"));
        }
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
        for field in ["version", "license", "owner"] {
            if !is_safe_atom(kv[field]) {
                return Err(err(&format!(
                    "{field} must be a non-empty path-free policy atom"
                )));
            }
        }
        let checksum = kv["checksum"];
        if checksum != "-"
            && !(checksum.len() == 64 && checksum.chars().all(|ch| ch.is_ascii_hexdigit()))
        {
            return Err(err("checksum must be `-` or exactly 64 hexadecimal digits"));
        }
        let build_script = parse_yes_no(kv["build-script"], "build-script").map_err(|e| err(&e))?;
        let proc_macro = parse_yes_no(kv["proc-macro"], "proc-macro").map_err(|e| err(&e))?;
        let native_link = parse_yes_no(kv["native-link"], "native-link").map_err(|e| err(&e))?;
        let unsafe_audit = kv["unsafe-audit"];
        if !["forbid", "deny-ledgered", "external"].contains(&unsafe_audit) {
            return Err(err("unsafe-audit must be forbid|deny-ledgered|external"));
        }
        let policy = kv["policy"];
        if !["runtime", "build", "dev", "fuzz"].contains(&policy) {
            return Err(err("policy must be runtime|build|dev|fuzz"));
        }
        let upgrade = kv["upgrade"];
        if !["workspace", "suite-lock"].contains(&upgrade) {
            return Err(err("upgrade must be workspace|suite-lock"));
        }
        if rows.iter().any(|r| r.name == name) {
            return Err(err(&format!("duplicate row for `{name}`")));
        }
        rows.push(AllowRow {
            name: name.to_string(),
            version: kv["version"].to_string(),
            source: source.to_string(),
            checksum: checksum.to_ascii_lowercase(),
            license: kv["license"].to_string(),
            build_script,
            proc_macro,
            native_link,
            unsafe_audit: unsafe_audit.to_string(),
            policy: policy.to_string(),
            owner: kv["owner"].to_string(),
            upgrade: upgrade.to_string(),
            reason: reason.to_string(),
        });
    }
    if !saw_schema {
        return Err("CLOSURE_ALLOWLIST.txt: missing schema line".to_string());
    }
    Ok(rows)
}

#[derive(Debug)]
pub struct SuitePin {
    pub commit: String,
    pub path: PathBuf,
}

#[derive(Debug, Default)]
pub struct SuiteLock {
    pub rust_nightly: String,
    pub rust_release: String,
    pub rust_commit: String,
    pub targets: BTreeSet<String>,
    /// repo -> exact commit and canonical source-root spelling
    pub suites: BTreeMap<String, SuitePin>,
    /// allowed suite package -> repo
    pub crates: BTreeMap<String, String>,
    pub reference: Option<(String, String, String)>,
    pub reference_tree: Option<String>,
    pub corpus: Option<(String, String, String)>,
}

fn is_hex40(s: &str) -> bool {
    s.len() == 40 && s.chars().all(|c| c.is_ascii_hexdigit())
}

fn absolute_normal_path(value: &str) -> Option<PathBuf> {
    let path = PathBuf::from(value);
    if !path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::RootDir | Component::Normal(_)))
    {
        return None;
    }
    let normalized: PathBuf = path.components().collect();
    (normalized.to_str() == Some(value)).then_some(normalized)
}

fn is_exact_nightly(s: &str) -> bool {
    let Some(date) = s.strip_prefix("nightly-") else {
        return false;
    };
    date.len() == 10
        && date.chars().enumerate().all(|(index, ch)| {
            matches!(index, 4 | 7) && ch == '-' || !matches!(index, 4 | 7) && ch.is_ascii_digit()
        })
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
            "rust-nightly" if tokens.len() == 2 => {
                if !lock.rust_nightly.is_empty() {
                    return Err(err("duplicate rust-nightly row"));
                }
                if !is_exact_nightly(tokens[1]) {
                    return Err(err("rust-nightly must be an exact nightly-YYYY-MM-DD pin"));
                }
                lock.rust_nightly = tokens[1].to_string();
            }
            "rust-release" if tokens.len() == 2 => {
                if !lock.rust_release.is_empty() {
                    return Err(err("duplicate rust-release row"));
                }
                if tokens[1].is_empty() {
                    return Err(err("rust-release must be non-empty"));
                }
                lock.rust_release = tokens[1].to_string();
            }
            "rust-commit" if tokens.len() == 2 => {
                if !lock.rust_commit.is_empty() {
                    return Err(err("duplicate rust-commit row"));
                }
                if !is_hex40(tokens[1]) {
                    return Err(err("rust-commit must be 40 hexadecimal digits"));
                }
                lock.rust_commit = tokens[1].to_ascii_lowercase();
            }
            "target" if tokens.len() == 2 => {
                if tokens[1].is_empty() || !lock.targets.insert(tokens[1].to_string()) {
                    return Err(err("target rows must be non-empty and unique"));
                }
            }
            "suite" if tokens.len() == 4 => {
                if !is_safe_atom(tokens[1]) {
                    return Err(err("suite repo name contains unsupported characters"));
                }
                let commit = tokens[2]
                    .strip_prefix("commit=")
                    .filter(|c| is_hex40(c))
                    .ok_or_else(|| err("suite row needs commit=<40-hex>"))?;
                let path = tokens[3]
                    .strip_prefix("path=")
                    .and_then(absolute_normal_path)
                    .ok_or_else(|| {
                        err("suite row needs one lexically normalized absolute path=<abs>")
                    })?;
                if lock
                    .suites
                    .insert(
                        tokens[1].to_string(),
                        SuitePin {
                            commit: commit.to_ascii_lowercase(),
                            path,
                        },
                    )
                    .is_some()
                {
                    return Err(err("duplicate suite row"));
                }
            }
            "crate" if tokens.len() == 3 => {
                if !is_safe_atom(tokens[1]) {
                    return Err(err("crate package name contains unsupported characters"));
                }
                let repo = tokens[2]
                    .strip_prefix("repo=")
                    .filter(|repo| is_safe_atom(repo))
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
    if lock.rust_release.is_empty() {
        return Err("SUITE.lock: missing rust-release row".to_string());
    }
    if lock.rust_commit.is_empty() {
        return Err("SUITE.lock: missing rust-commit row".to_string());
    }
    if lock.targets.is_empty() {
        return Err("SUITE.lock: at least one target row is required".to_string());
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
    let mut suite_paths = BTreeSet::new();
    for (repo, pin) in &lock.suites {
        if !suite_paths.insert(pin.path.clone()) {
            return Err(format!(
                "SUITE.lock: suite `{repo}` reuses another repo's path `{}`",
                pin.path.display()
            ));
        }
        if !lock.crates.values().any(|mapped_repo| mapped_repo == repo) {
            return Err(format!(
                "SUITE.lock: suite `{repo}` has no mapped package row"
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
    let mut seen_keys = BTreeSet::new();
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
        let key = key.trim();
        if !seen_keys.insert(key) {
            return Err(err("duplicate toolchain key"));
        }
        match key {
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

struct WorkspaceManifest {
    rel: String,
    dir: PathBuf,
    manifest: manifest::Manifest,
}

fn workspace_manifests(root: &Path, graph: &GraphFile) -> BTreeMap<String, WorkspaceManifest> {
    let mut manifests = BTreeMap::new();
    for (name, declaration) in &graph.crates {
        let subdir = match declaration.kind {
            CrateKind::Tool => "tools",
            CrateKind::Ordinary | CrateKind::UnsafeBoundary => "crates",
        };
        let rel = format!("{subdir}/{name}/Cargo.toml");
        let dir = root.join(subdir).join(name);
        let Ok(text) = fs::read_to_string(dir.join("Cargo.toml")) else {
            // The main structural pass already emits the authoritative missing or
            // undecodable-manifest finding. Do not duplicate it under the closure code.
            continue;
        };
        let Ok(parsed) = manifest::parse(&text, &rel) else {
            continue;
        };
        manifests.insert(
            name.clone(),
            WorkspaceManifest {
                rel,
                dir,
                manifest: parsed,
            },
        );
    }
    manifests
}

fn exact_policy_for_workspace(kind: CrateKind) -> &'static str {
    match kind {
        CrateKind::Tool => "dev",
        CrateKind::Ordinary | CrateKind::UnsafeBoundary => "runtime",
    }
}

fn exact_unsafe_policy(kind: CrateKind) -> &'static str {
    match kind {
        CrateKind::UnsafeBoundary => "deny-ledgered",
        CrateKind::Ordinary | CrateKind::Tool => "forbid",
    }
}

fn policy_finding(path: &str, detail: String) -> Finding {
    Finding {
        code: "FLN-STRUCT-018",
        path: path.to_string(),
        detail,
    }
}

fn suite_finding(path: &str, detail: String) -> Finding {
    Finding {
        code: "FLN-STRUCT-020",
        path: path.to_string(),
        detail,
    }
}

fn suite_unverifiable(path: &Path, detail: String) -> Finding {
    Finding {
        code: "FLN-STRUCT-031",
        path: path.display().to_string(),
        detail,
    }
}

fn git_dir(repo: &Path) -> Result<PathBuf, String> {
    let marker = repo.join(".git");
    let metadata = fs::symlink_metadata(&marker)
        .map_err(|error| format!("cannot inspect {}: {error}", marker.display()))?;
    if metadata.file_type().is_symlink() {
        return Err(format!("{} is a symlink", marker.display()));
    }
    if metadata.is_dir() {
        return Ok(marker);
    }
    if !metadata.is_file() {
        return Err(format!("{} is not a file or directory", marker.display()));
    }
    let text = fs::read_to_string(&marker)
        .map_err(|error| format!("cannot read {}: {error}", marker.display()))?;
    let value = text
        .trim()
        .strip_prefix("gitdir: ")
        .filter(|value| !value.is_empty())
        .ok_or_else(|| format!("{} is not a constrained gitdir pointer", marker.display()))?;
    let path = PathBuf::from(value);
    let resolved = if path.is_absolute() {
        path
    } else {
        repo.join(path)
    };
    let canonical = fs::canonicalize(&resolved)
        .map_err(|error| format!("cannot resolve gitdir {}: {error}", resolved.display()))?;
    let canonical_repo = fs::canonicalize(repo)
        .map_err(|error| format!("cannot resolve suite repo {}: {error}", repo.display()))?;
    if !canonical.starts_with(&canonical_repo) {
        return Err(format!(
            "gitdir {} escapes suite repo {}",
            canonical.display(),
            canonical_repo.display()
        ));
    }
    Ok(canonical)
}

fn read_git_head(repo: &Path) -> Result<String, String> {
    let git_dir = git_dir(repo)?;
    let head_path = git_dir.join("HEAD");
    let head = fs::read_to_string(&head_path)
        .map_err(|error| format!("cannot read {}: {error}", head_path.display()))?;
    let head = head.trim();
    if is_hex40(head) {
        return Ok(head.to_ascii_lowercase());
    }
    let reference = head
        .strip_prefix("ref: ")
        .filter(|reference| reference.starts_with("refs/"))
        .ok_or_else(|| format!("{} has malformed HEAD", head_path.display()))?;
    let reference_path = Path::new(reference);
    if reference_path.is_absolute()
        || reference_path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(format!(
            "{} names an unsafe reference `{reference}`",
            head_path.display()
        ));
    }
    let loose_path = git_dir.join(reference_path);
    if let Ok(value) = fs::read_to_string(&loose_path) {
        let value = value.trim();
        if is_hex40(value) {
            return Ok(value.to_ascii_lowercase());
        }
        return Err(format!("{} is not a 40-hex commit", loose_path.display()));
    }
    let packed_path = git_dir.join("packed-refs");
    let packed = fs::read_to_string(&packed_path)
        .map_err(|error| format!("cannot resolve `{reference}` in packed-refs: {error}"))?;
    for line in packed.lines() {
        if line.is_empty() || line.starts_with('#') || line.starts_with('^') {
            continue;
        }
        let Some((commit, name)) = line.split_once(' ') else {
            return Err(format!(
                "{} contains a malformed packed ref",
                packed_path.display()
            ));
        };
        if name == reference {
            return is_hex40(commit)
                .then(|| commit.to_ascii_lowercase())
                .ok_or_else(|| {
                    format!(
                        "{} contains a non-commit value for `{reference}`",
                        packed_path.display()
                    )
                });
        }
    }
    Err(format!("git reference `{reference}` is unresolved"))
}

fn policy_for_dependency_section(section: &str) -> &'static str {
    match section {
        "build-dependencies" => "build",
        "dev-dependencies" => "dev",
        "dependencies" => "runtime",
        _ => "runtime",
    }
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

    let manifests = workspace_manifests(root, graph);
    if let (Some(packages), Some(rows)) = (&packages, &rows) {
        let lock_by_name: BTreeMap<&str, &LockPackage> = packages
            .iter()
            .map(|package| (package.name.as_str(), package))
            .collect();
        let row_by_name: BTreeMap<&str, &AllowRow> =
            rows.iter().map(|row| (row.name.as_str(), row)).collect();

        for package in packages {
            if package.source.is_some() || package.checksum.is_some() {
                findings.push(policy_finding(
                    LOCK_FILE,
                    format!(
                        "package `{}` comes from a registry/git source — external packages are prohibited (D1)",
                        package.name
                    ),
                ));
                continue;
            }
            match row_by_name.get(package.name.as_str()) {
                None => findings.push(policy_finding(
                    LOCK_FILE,
                    format!(
                        "package `{}` {} has no row in {ALLOWLIST_FILE}",
                        package.name, package.version
                    ),
                )),
                Some(row) if row.version != package.version => {
                    findings.push(policy_finding(
                        ALLOWLIST_FILE,
                        format!(
                            "package `{}`: lock has {}, allowlist approves {}",
                            package.name, package.version, row.version
                        ),
                    ));
                }
                Some(row) => {
                    if row.source == "workspace" && !graph.crates.contains_key(&package.name) {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "package `{}` claims source=workspace but is not a declared workspace crate",
                                package.name
                            ),
                        ));
                    }
                    if row.source == "suite"
                        && !graph.suite_deps.iter().any(|name| name == &package.name)
                    {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "package `{}` claims source=suite but is not a WORKSPACE_GRAPH suite-dep",
                                package.name
                            ),
                        ));
                    }
                }
            }
            for dependency in &package.dependencies {
                if !lock_by_name.contains_key(dependency.as_str()) {
                    findings.push(policy_finding(
                        LOCK_FILE,
                        format!(
                            "package `{}` names dependency `{dependency}` which has no package record",
                            package.name
                        ),
                    ));
                }
            }
        }

        for (name, declaration) in &graph.crates {
            if !lock_by_name.contains_key(name.as_str()) {
                findings.push(policy_finding(
                    LOCK_FILE,
                    format!("workspace crate `{name}` has no Cargo.lock package record"),
                ));
            }
            if !row_by_name.contains_key(name.as_str()) {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!("workspace crate `{name}` has no reviewed allowlist row"),
                ));
            }

            let (Some(row), Some(info)) =
                (row_by_name.get(name.as_str()).copied(), manifests.get(name))
            else {
                continue;
            };
            if row.source != "workspace" {
                continue;
            }
            if row.checksum != "-" {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "workspace package `{name}` must carry checksum=-, found `{}`",
                        row.checksum
                    ),
                ));
            }
            if info.manifest.version.as_deref() != Some(row.version.as_str()) {
                findings.push(policy_finding(
                    &info.rel,
                    format!(
                        "package `{name}` manifest version `{}` != allowlist version `{}`",
                        info.manifest.version.as_deref().unwrap_or("missing"),
                        row.version
                    ),
                ));
            }
            if info.manifest.license.as_deref() != Some(row.license.as_str()) {
                findings.push(policy_finding(
                    &info.rel,
                    format!(
                        "package `{name}` manifest license `{}` != allowlist license `{}`",
                        info.manifest.license.as_deref().unwrap_or("missing"),
                        row.license
                    ),
                ));
            }
            let has_build_script = info.dir.join("build.rs").is_file();
            if row.build_script != has_build_script {
                findings.push(policy_finding(
                    &info.rel,
                    format!(
                        "package `{name}` allowlist build-script={} but tree build.rs presence is {}",
                        if row.build_script { "yes" } else { "no" },
                        has_build_script
                    ),
                ));
            }
            if row.proc_macro {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "package `{name}` claims proc-macro=yes, but the constrained manifest has no proc-macro target"
                    ),
                ));
            }
            if row.native_link {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "package `{name}` claims native-link=yes, but the constrained manifest has no links key"
                    ),
                ));
            }
            let expected_unsafe = exact_unsafe_policy(declaration.kind);
            if row.unsafe_audit != expected_unsafe {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "package `{name}` kind={} requires unsafe-audit={expected_unsafe}, found {}",
                        declaration.kind.as_str(),
                        row.unsafe_audit
                    ),
                ));
            }
            let expected_policy = exact_policy_for_workspace(declaration.kind);
            if row.policy != expected_policy {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "package `{name}` kind={} requires policy={expected_policy}, found {}",
                        declaration.kind.as_str(),
                        row.policy
                    ),
                ));
            }
            if row.owner != "franken_lean" {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "workspace package `{name}` requires owner=franken_lean, found `{}`",
                        row.owner
                    ),
                ));
            }
            if row.upgrade != "workspace" {
                findings.push(policy_finding(
                    ALLOWLIST_FILE,
                    format!(
                        "workspace package `{name}` requires upgrade=workspace, found `{}`",
                        row.upgrade
                    ),
                ));
            }
        }

        for (name, info) in &manifests {
            let Some(package) = lock_by_name.get(name.as_str()) else {
                continue;
            };
            let manifest_dependencies: BTreeSet<String> = info
                .manifest
                .deps
                .iter()
                .map(|dependency| dependency.name.clone())
                .collect();
            if manifest_dependencies != package.dependencies {
                let only_manifest: Vec<&str> = manifest_dependencies
                    .difference(&package.dependencies)
                    .map(String::as_str)
                    .collect();
                let only_lock: Vec<&str> = package
                    .dependencies
                    .difference(&manifest_dependencies)
                    .map(String::as_str)
                    .collect();
                findings.push(policy_finding(
                    &info.rel,
                    format!(
                        "package `{name}` manifest/Cargo.lock dependency closure differs: only-manifest={only_manifest:?}, only-lock={only_lock:?}"
                    ),
                ));
            }
        }

        let lock_names: BTreeSet<&str> = packages
            .iter()
            .map(|package| package.name.as_str())
            .collect();
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

        if let (Some(packages), Some(rows)) = (&packages, &rows) {
            let lock_by_name: BTreeMap<&str, &LockPackage> = packages
                .iter()
                .map(|package| (package.name.as_str(), package))
                .collect();
            let row_by_name: BTreeMap<&str, &AllowRow> =
                rows.iter().map(|row| (row.name.as_str(), row)).collect();
            let mut verified_repos = BTreeSet::new();

            for row in rows.iter().filter(|row| row.source == "suite") {
                if !lock_by_name.contains_key(row.name.as_str()) {
                    continue; // the stale-approval finding is complete and sufficient.
                }
                let Some(repo) = lock.crates.get(&row.name) else {
                    findings.push(suite_finding(
                        SUITE_LOCK_FILE,
                        format!(
                            "allowlisted suite package `{}` has no package→repo mapping",
                            row.name
                        ),
                    ));
                    continue;
                };
                let Some(pin) = lock.suites.get(repo) else {
                    continue; // parse_suite_lock already rejects this shape.
                };
                if row.checksum != "-" {
                    findings.push(policy_finding(
                        ALLOWLIST_FILE,
                        format!(
                            "suite package `{}` must carry checksum=-; its commit provenance is in SUITE.lock",
                            row.name
                        ),
                    ));
                }
                if row.unsafe_audit != "external" {
                    findings.push(policy_finding(
                        ALLOWLIST_FILE,
                        format!(
                            "suite package `{}` requires unsafe-audit=external, found {}",
                            row.name, row.unsafe_audit
                        ),
                    ));
                }
                if row.owner != *repo {
                    findings.push(policy_finding(
                        ALLOWLIST_FILE,
                        format!(
                            "suite package `{}` requires owner={repo}, found `{}`",
                            row.name, row.owner
                        ),
                    ));
                }
                if row.upgrade != "suite-lock" {
                    findings.push(policy_finding(
                        ALLOWLIST_FILE,
                        format!(
                            "suite package `{}` requires upgrade=suite-lock, found `{}`",
                            row.name, row.upgrade
                        ),
                    ));
                }

                if verified_repos.insert(repo.as_str()) {
                    let metadata = fs::symlink_metadata(&pin.path);
                    match metadata {
                        Ok(metadata) if metadata.file_type().is_symlink() => {
                            findings.push(suite_finding(
                                SUITE_LOCK_FILE,
                                format!(
                                    "suite repo `{repo}` path `{}` is a symlink; the authority path must be canonical",
                                    pin.path.display()
                                ),
                            ));
                        }
                        Ok(metadata) if metadata.is_dir() => match fs::canonicalize(&pin.path) {
                            Ok(canonical) if canonical == pin.path => {
                                match read_git_head(&canonical) {
                                    Ok(commit) if commit == pin.commit => {}
                                    Ok(commit) => findings.push(suite_finding(
                                        SUITE_LOCK_FILE,
                                        format!(
                                            "suite repo `{repo}` checkout HEAD `{commit}` != pinned commit `{}`",
                                            pin.commit
                                        ),
                                    )),
                                    Err(detail) => findings.push(suite_unverifiable(
                                        &pin.path,
                                        format!(
                                            "suite repo `{repo}` commit identity is unverifiable: {detail}"
                                        ),
                                    )),
                                }
                            }
                            Ok(canonical) => findings.push(suite_finding(
                                SUITE_LOCK_FILE,
                                format!(
                                    "suite repo `{repo}` path `{}` canonicalizes to `{}`",
                                    pin.path.display(),
                                    canonical.display()
                                ),
                            )),
                            Err(error) => findings.push(suite_unverifiable(
                                &pin.path,
                                format!(
                                    "suite repo `{repo}` path cannot be canonicalized: {error}"
                                ),
                            )),
                        },
                        Ok(_) => findings.push(suite_finding(
                            SUITE_LOCK_FILE,
                            format!(
                                "suite repo `{repo}` path `{}` is not a directory",
                                pin.path.display()
                            ),
                        )),
                        Err(error) => findings.push(suite_unverifiable(
                            &pin.path,
                            format!("suite repo `{repo}` checkout is unavailable: {error}"),
                        )),
                    }
                }
            }

            for (workspace_name, info) in &manifests {
                for dependency in info.manifest.deps.iter().filter(|dependency| {
                    graph.suite_deps.iter().any(|name| name == &dependency.name)
                }) {
                    let Some(repo) = lock.crates.get(&dependency.name) else {
                        continue;
                    };
                    let Some(pin) = lock.suites.get(repo) else {
                        continue;
                    };
                    let Some(row) = row_by_name.get(dependency.name.as_str()).copied() else {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "reachable suite dependency `{}` has no reviewed allowlist row",
                                dependency.name
                            ),
                        ));
                        continue;
                    };
                    if row.source != "suite" {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "reachable FrankenSuite dependency `{}` requires source=suite",
                                dependency.name
                            ),
                        ));
                    }
                    let expected_policy = policy_for_dependency_section(&dependency.section);
                    if row.policy != expected_policy {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "suite dependency `{}` used from [{}] requires policy={expected_policy}, found {}",
                                dependency.name, dependency.section, row.policy
                            ),
                        ));
                    }
                    let Some(declared_path) = &dependency.path else {
                        continue; // the main pass emits FLN-STRUCT-010.
                    };
                    let joined = info.dir.join(declared_path);
                    if fs::symlink_metadata(&joined)
                        .is_ok_and(|metadata| metadata.file_type().is_symlink())
                    {
                        findings.push(suite_finding(
                            &info.rel,
                            format!(
                                "suite dependency `{}` path is a symlink rather than the SUITE.lock authority path",
                                dependency.name
                            ),
                        ));
                        continue;
                    }
                    let declared = match fs::canonicalize(&joined) {
                        Ok(path) => path,
                        Err(error) => {
                            findings.push(Finding {
                                code: "FLN-STRUCT-023",
                                path: info.rel.clone(),
                                detail: format!(
                                    "suite dependency `{}` path `{declared_path}` cannot be resolved: {error}",
                                    dependency.name
                                ),
                            });
                            continue;
                        }
                    };
                    let expected = match fs::canonicalize(&pin.path) {
                        Ok(path) => path,
                        Err(_) => continue, // FLN-STRUCT-031 emitted above.
                    };
                    if declared != expected {
                        findings.push(suite_finding(
                            &info.rel,
                            format!(
                                "suite dependency `{}` from workspace package `{workspace_name}` resolves to `{}`, but package→repo→SUITE.lock binds `{}`",
                                dependency.name,
                                declared.display(),
                                expected.display()
                            ),
                        ));
                        continue;
                    }

                    let suite_manifest_path = declared.join("Cargo.toml");
                    let suite_text = match fs::read_to_string(&suite_manifest_path) {
                        Ok(text) => text,
                        Err(error) => {
                            findings.push(suite_unverifiable(
                                &suite_manifest_path,
                                format!(
                                    "suite package `{}` manifest is unavailable: {error}",
                                    dependency.name
                                ),
                            ));
                            continue;
                        }
                    };
                    let display = suite_manifest_path.display().to_string();
                    let suite_manifest = match manifest::parse(&suite_text, &display) {
                        Ok(manifest) => manifest,
                        Err(detail) => {
                            findings.push(suite_finding(
                                &display,
                                format!(
                                    "suite package `{}` manifest is outside the constrained closure grammar: {detail}",
                                    dependency.name
                                ),
                            ));
                            continue;
                        }
                    };
                    if suite_manifest.name != dependency.name {
                        findings.push(suite_finding(
                            &display,
                            format!(
                                "suite dependency path declares package `{}`, expected `{}`",
                                suite_manifest.name, dependency.name
                            ),
                        ));
                    }
                    if suite_manifest.version.as_deref() != Some(row.version.as_str()) {
                        findings.push(policy_finding(
                            &display,
                            format!(
                                "suite package `{}` manifest version `{}` != allowlist/lock version `{}`",
                                dependency.name,
                                suite_manifest.version.as_deref().unwrap_or("missing"),
                                row.version
                            ),
                        ));
                    }
                    if suite_manifest.license.as_deref() != Some(row.license.as_str()) {
                        findings.push(policy_finding(
                            &display,
                            format!(
                                "suite package `{}` manifest license `{}` != allowlist license `{}`",
                                dependency.name,
                                suite_manifest.license.as_deref().unwrap_or("missing"),
                                row.license
                            ),
                        ));
                    }
                    let has_build_script = declared.join("build.rs").is_file();
                    if row.build_script != has_build_script {
                        findings.push(policy_finding(
                            &display,
                            format!(
                                "suite package `{}` allowlist build-script={} but tree build.rs presence is {}",
                                dependency.name,
                                if row.build_script { "yes" } else { "no" },
                                has_build_script
                            ),
                        ));
                    }
                    if row.proc_macro {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "suite package `{}` claims proc-macro=yes, but its constrained manifest has no proc-macro target",
                                dependency.name
                            ),
                        ));
                    }
                    if row.native_link {
                        findings.push(policy_finding(
                            ALLOWLIST_FILE,
                            format!(
                                "suite package `{}` claims native-link=yes, but its constrained manifest has no links key",
                                dependency.name
                            ),
                        ));
                    }
                }
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
        let reg = "version = 4\n[[package]]\nname = \"serde\"\nversion = \"1.0.0\"\nsource = \"registry+https://github.com/rust-lang/crates.io-index\"\nchecksum = \"5f0e2c6ed6606019b4e29e69dbaba95b11854410e5347d525002456dbbb786b6\"\n";
        let pkgs = parse_cargo_lock(reg, "t").expect("parses");
        assert!(pkgs[0].source.is_some());
        assert!(parse_cargo_lock("[[package]]\nversion = \"1\"\n", "t").is_err());
        assert!(parse_cargo_lock("name = \"x\"\n", "t").is_err());
    }

    #[test]
    fn cargo_lock_v4_parser_rejects_ambiguous_or_partial_shapes() {
        let base = "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\n";
        for malformed in [
            "",
            "version = 3\n",
            "version = 4\nversion = 4\n",
            "version = \"4\"\n",
            "[[package]]\nname = \"a\"\nversion = \"1\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nname = \"a\"\nversion = \"1\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nversion = \"1\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nsource = \"x\"\nsource = \"x\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nchecksum = \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"\nchecksum = \"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\ndependencies = [\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nfeatures = [\n]\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\ndependencies = [\"b\"]\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nsource = registry\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nchecksum = unquoted\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\nchecksum = \"abc\"\n",
            "version = 4\n[[package]]\nname = \"a\"\nversion = \"1\"\n[[package]]\nname = \"a\"\nversion = \"2\"\n",
        ] {
            assert!(
                parse_cargo_lock(malformed, "Cargo.lock").is_err(),
                "accepted malformed lockfile:\n{malformed}"
            );
        }
        assert!(parse_cargo_lock(base, "Cargo.lock").is_ok());
    }

    const ROW_OK: &str = "schema fln-closure-allowlist/1\npackage fln-core version=0.0.0 source=workspace checksum=- license=MIT build-script=no proc-macro=no native-link=no unsafe-audit=forbid policy=runtime owner=franken_lean upgrade=workspace reason=stub\n";

    #[test]
    fn parses_allowlist_and_rejects_bad_rows() {
        let rows = parse_allowlist(ROW_OK).expect("parses");
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].source, "workspace");
        assert!(!rows[0].build_script);
        assert_eq!(rows[0].checksum, "-");
        assert_eq!(rows[0].unsafe_audit, "forbid");
        assert_eq!(rows[0].owner, "franken_lean");
        assert_eq!(rows[0].reason, "stub");

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
        for malformed in [
            ROW_OK.replace("checksum=-", "checksum=abc"),
            ROW_OK.replace("build-script=no", "build-script=maybe"),
            ROW_OK.replace("proc-macro=no", "proc-macro=maybe"),
            ROW_OK.replace("native-link=no", "native-link=maybe"),
            ROW_OK.replace("unsafe-audit=forbid", "unsafe-audit=unchecked"),
            ROW_OK.replace("policy=runtime", "policy=unknown"),
            ROW_OK.replace("upgrade=workspace", "upgrade=manual"),
        ] {
            assert!(
                parse_allowlist(&malformed).is_err(),
                "accepted malformed row: {malformed}"
            );
        }
    }

    const SUITE_OK: &str = "schema fln-suite-lock/1\nrust-nightly nightly-2026-07-13\nrust-release 1.99.0-nightly\nrust-commit 77cf889bc178ddb44d6a1c78e5a820b5abb31d8d\ntarget x86_64-unknown-linux-gnu\nsuite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync\ncrate asupersync repo=asupersync\nreference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91\ncorpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997\n";

    #[test]
    fn parses_suite_lock_and_enforces_required_rows() {
        let lock = parse_suite_lock(SUITE_OK).expect("parses");
        assert_eq!(lock.rust_nightly, "nightly-2026-07-13");
        assert_eq!(lock.rust_release, "1.99.0-nightly");
        assert_eq!(lock.rust_commit, "77cf889bc178ddb44d6a1c78e5a820b5abb31d8d");
        assert_eq!(
            lock.targets,
            BTreeSet::from(["x86_64-unknown-linux-gnu".to_string()])
        );
        assert_eq!(lock.crates["asupersync"], "asupersync");
        assert_eq!(
            lock.suites["asupersync"].path,
            PathBuf::from("/dp/asupersync")
        );
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
        let duplicate_nightly = SUITE_OK.replace(
            "rust-nightly nightly-2026-07-13",
            "rust-nightly nightly-2026-07-13\nrust-nightly nightly-2026-07-14",
        );
        assert!(parse_suite_lock(&duplicate_nightly).is_err());
        let undated_nightly = SUITE_OK.replace("nightly-2026-07-13", "nightly");
        assert!(parse_suite_lock(&undated_nightly).is_err());
        for required_row in [
            "rust-release 1.99.0-nightly\n",
            "rust-commit 77cf889bc178ddb44d6a1c78e5a820b5abb31d8d\n",
            "target x86_64-unknown-linux-gnu\n",
        ] {
            assert!(
                parse_suite_lock(&SUITE_OK.replace(required_row, "")).is_err(),
                "accepted missing required row: {required_row}"
            );
        }
        let duplicate_target = SUITE_OK.replace(
            "target x86_64-unknown-linux-gnu",
            "target x86_64-unknown-linux-gnu\ntarget x86_64-unknown-linux-gnu",
        );
        assert!(parse_suite_lock(&duplicate_target).is_err());
        let malformed_commit =
            SUITE_OK.replace("77cf889bc178ddb44d6a1c78e5a820b5abb31d8d", "not-a-commit");
        assert!(parse_suite_lock(&malformed_commit).is_err());
        for path in ["relative/path", "/dp/../tmp/asupersync", "/dp//asupersync"] {
            let malformed_path = SUITE_OK.replace("/dp/asupersync", path);
            assert!(
                parse_suite_lock(&malformed_path).is_err(),
                "accepted non-canonical suite path {path}"
            );
        }
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
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\ncomponents = [\"rustfmt\"]\ncomponents = [\"clippy\"]\n"
            )
            .is_err()
        );
        assert!(
            parse_toolchain_channel(
                "[toolchain]\nchannel = \"nightly-2026-07-13\"\nprofile = \"minimal\"\nprofile = \"default\"\n"
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
