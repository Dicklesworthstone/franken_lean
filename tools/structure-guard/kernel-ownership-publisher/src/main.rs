//! Race-free publisher for `ci/KERNEL_CONTRACT_OWNERSHIP.jsonl` (bead `fln-3oj6`).
//!
//! The exclusive lock covers the authoritative `.beads/issues.jsonl` read, canonical
//! projection, candidate write and sync, source-stability check, atomic rename, and
//! directory sync. A crash leaves the candidate sibling behind; structure-guard treats
//! that state as typed inconclusive instead of consuming the old publication.

#![forbid(unsafe_code)]

use fln_hash::domain::{Domain, DomainHasher};
use std::collections::BTreeSet;
use std::fmt;
use std::fs::{self, File, OpenOptions, TryLockError};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};
use std::process::ExitCode;
use std::thread;
use std::time::{Duration, Instant};

const SOURCE_RELATIVE_PATH: &str = ".beads/issues.jsonl";
const MANIFEST_RELATIVE_PATH: &str = "ci/KERNEL_CONTRACT_OWNERSHIP.jsonl";
const CANDIDATE_RELATIVE_PATH: &str = "ci/KERNEL_CONTRACT_OWNERSHIP.jsonl.candidate";
const LOCK_PATH: &str = "/data/tmp/fln-kernel-contract-ownership.lockfile";
const MANIFEST_SCHEMA: &str = "fln.kernel-contract-ownership/1";
const PROJECTION_SCHEMA: &str = "sorted-canonical-issue-ids-v1";
const HASH_ALGORITHM: &str = "fln-domain-registry-v1";
const HASH_DOMAIN: &str = "fln 2026 domain fixture/1";
const HASH_PREIMAGE: &str = "fln.kernel-contract-ownership.ids/1+nul+u64le-length-prefixed-utf8";
const PROJECTION_HASH_TAG: &[u8] = b"fln.kernel-contract-ownership.ids/1";
const SOURCE_ROOT_TAG: &[u8] = b"fln.kernel-contract-ownership.source-bytes/1";
// Measured 2026-08-21: the live export is 9,894,985 bytes over 464 records and
// HEAD carried 8,374,193, so the previous 8 MiB bound refused every
// regeneration and with it every bead-carrying commit swarm-wide. 64 MiB gives
// years of headroom at the observed growth while still bounding the read.
const MAX_FILE_BYTES: usize = 64 * 1024 * 1024;
// Measured 2026-08-21: three live records exceed the previous 256 KiB line
// bound (largest 618,651 bytes - an accumulated immutable comment log, not
// corrupt input), so regeneration refused after the file-bound raise. 1 MiB.
const MAX_LINE_BYTES: usize = 1024 * 1024;
const MAX_RECORDS: usize = 100_000;
const MAX_ID_BYTES: usize = 256;
const MAX_WAIT_MS: u64 = 30_000;
const DEFAULT_WAIT_MS: u64 = 30_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ErrorClass {
    Violation,
    InternalFault,
    Inconclusive,
}

impl ErrorClass {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Violation => "violation",
            Self::InternalFault => "internal_fault",
            Self::Inconclusive => "inconclusive",
        }
    }

    const fn exit_code(self) -> u8 {
        match self {
            Self::Violation => 1,
            Self::InternalFault => 2,
            Self::Inconclusive => 3,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PublishError {
    class: ErrorClass,
    reason: &'static str,
    path: String,
    detail: String,
}

impl PublishError {
    fn new(
        class: ErrorClass,
        reason: &'static str,
        path: impl Into<String>,
        detail: impl Into<String>,
    ) -> Self {
        Self {
            class,
            reason,
            path: path.into(),
            detail: detail.into(),
        }
    }
}

impl fmt::Display for PublishError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} reason={} path={}: {}",
            self.class.as_str(),
            self.reason,
            self.path,
            self.detail
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Receipt {
    projection_hash: String,
    source_root: String,
    record_count: usize,
    source_bytes: usize,
    manifest_bytes: usize,
    lock_wait_ms: u128,
}

fn canonical_id_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.')
}

fn parse_source(bytes: &[u8]) -> Result<BTreeSet<String>, PublishError> {
    if bytes.is_empty() {
        return Err(PublishError::new(
            ErrorClass::Violation,
            "source_empty",
            SOURCE_RELATIVE_PATH,
            "the authoritative Beads export has no records",
        ));
    }
    if bytes.len() > MAX_FILE_BYTES {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            SOURCE_RELATIVE_PATH,
            format!(
                "source is {} bytes; bounded maximum is {MAX_FILE_BYTES}",
                bytes.len()
            ),
        ));
    }
    if !bytes.ends_with(b"\n") {
        return Err(PublishError::new(
            ErrorClass::Violation,
            "source_noncanonical",
            SOURCE_RELATIVE_PATH,
            "source must end with LF",
        ));
    }

    const PREFIX: &[u8] = b"{\"id\":\"";
    let mut ids = BTreeSet::new();
    for (index, line) in bytes[..bytes.len() - 1]
        .split(|byte| *byte == b'\n')
        .enumerate()
    {
        let line_number = index + 1;
        if line.is_empty() || line.ends_with(b"\r") || line.len() > MAX_LINE_BYTES {
            return Err(PublishError::new(
                if line.len() > MAX_LINE_BYTES {
                    ErrorClass::Inconclusive
                } else {
                    ErrorClass::Violation
                },
                if line.len() > MAX_LINE_BYTES {
                    "resource_exhausted"
                } else {
                    "source_noncanonical"
                },
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} is blank, CRLF, or exceeds {MAX_LINE_BYTES} bytes"),
            ));
        }
        let rest = line.strip_prefix(PREFIX).ok_or_else(|| {
            PublishError::new(
                ErrorClass::Violation,
                "source_noncanonical",
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} must begin with an unescaped canonical id"),
            )
        })?;
        let quote = rest.iter().position(|byte| *byte == b'"').ok_or_else(|| {
            PublishError::new(
                ErrorClass::Violation,
                "source_noncanonical",
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} has an unterminated id"),
            )
        })?;
        let id_bytes = &rest[..quote];
        let tail = &rest[quote + 1..];
        if id_bytes.is_empty()
            || id_bytes.len() > MAX_ID_BYTES
            || !id_bytes.iter().copied().all(canonical_id_byte)
            || !matches!(tail.first(), Some(b',' | b'}'))
            || !line.ends_with(b"}")
        {
            return Err(PublishError::new(
                ErrorClass::Violation,
                "source_noncanonical",
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} has a noncanonical id record"),
            ));
        }
        let id = std::str::from_utf8(id_bytes).map_err(|error| {
            PublishError::new(
                ErrorClass::Violation,
                "source_noncanonical",
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} id is not UTF-8: {error}"),
            )
        })?;
        if !ids.insert(id.to_string()) {
            return Err(PublishError::new(
                ErrorClass::Violation,
                "duplicate_id",
                SOURCE_RELATIVE_PATH,
                format!("line {line_number} repeats id `{id}`"),
            ));
        }
        if ids.len() > MAX_RECORDS {
            return Err(PublishError::new(
                ErrorClass::Inconclusive,
                "resource_exhausted",
                SOURCE_RELATIVE_PATH,
                format!("source exceeds the bounded record maximum {MAX_RECORDS}"),
            ));
        }
    }
    Ok(ids)
}

fn projection_hash(ids: &BTreeSet<String>) -> String {
    let mut hasher = DomainHasher::new(Domain::Fixture);
    hasher.update(PROJECTION_HASH_TAG).update(&[0]);
    for id in ids {
        hasher
            .update(&(id.len() as u64).to_le_bytes())
            .update(id.as_bytes());
    }
    hasher.finalize().to_hex()
}

fn source_root(bytes: &[u8]) -> String {
    let mut hasher = DomainHasher::new(Domain::Fixture);
    hasher
        .update(SOURCE_ROOT_TAG)
        .update(&[0])
        .update(&(bytes.len() as u64).to_le_bytes())
        .update(bytes);
    hasher.finalize().to_hex()
}

fn render_manifest(ids: &BTreeSet<String>) -> Vec<u8> {
    let digest = projection_hash(ids);
    let mut output = format!(
        "{{\"schema\":\"{MANIFEST_SCHEMA}\",\"source\":\"{SOURCE_RELATIVE_PATH}\",\"projection\":\"{PROJECTION_SCHEMA}\",\"hash_algorithm\":\"{HASH_ALGORITHM}\",\"hash_domain\":\"{HASH_DOMAIN}\",\"hash_preimage\":\"{HASH_PREIMAGE}\",\"record_count\":{},\"projection_hash\":\"{digest}\"}}\n",
        ids.len()
    );
    for id in ids {
        output.push_str(&format!("{{\"id\":\"{id}\"}}\n"));
    }
    output.into_bytes()
}

fn safe_relative_path(relative: &str) -> bool {
    let path = Path::new(relative);
    !path.is_absolute()
        && path
            .components()
            .all(|component| matches!(component, Component::Normal(_)))
}

fn validate_parent(root: &Path, relative: &str) -> Result<(), PublishError> {
    if !safe_relative_path(relative) {
        return Err(PublishError::new(
            ErrorClass::InternalFault,
            "compiled_path_invalid",
            relative,
            "compiled evidence path is not one safe relative path",
        ));
    }
    let parent = root
        .join(relative)
        .parent()
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            PublishError::new(
                ErrorClass::InternalFault,
                "parent_missing",
                relative,
                "compiled evidence path has no parent",
            )
        })?;
    let metadata = fs::symlink_metadata(&parent).map_err(|error| {
        PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            relative,
            format!("cannot inspect parent {}: {error}", parent.display()),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_ambiguous",
            relative,
            "evidence parent must be one real directory",
        ));
    }
    Ok(())
}

fn checked_root(root: &Path) -> Result<PathBuf, PublishError> {
    let root = fs::canonicalize(root).map_err(|error| {
        PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            root.display().to_string(),
            format!("cannot resolve workspace root: {error}"),
        )
    })?;
    if !root.is_dir() {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            root.display().to_string(),
            "workspace root is not a directory",
        ));
    }
    validate_parent(&root, SOURCE_RELATIVE_PATH)?;
    validate_parent(&root, MANIFEST_RELATIVE_PATH)?;
    Ok(root)
}

fn read_regular_bounded(root: &Path, relative: &str) -> Result<Vec<u8>, PublishError> {
    validate_parent(root, relative)?;
    let path = root.join(relative);
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            relative,
            format!("cannot inspect input: {error}"),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_ambiguous",
            relative,
            "evidence input must be one regular file, never a link",
        ));
    }
    if metadata.len() > MAX_FILE_BYTES as u64 {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            format!(
                "input is {} bytes; bounded maximum is {MAX_FILE_BYTES}",
                metadata.len()
            ),
        ));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    File::open(&path)
        .and_then(|file| {
            file.take((MAX_FILE_BYTES + 1) as u64)
                .read_to_end(&mut bytes)
        })
        .map_err(|error| {
            PublishError::new(
                ErrorClass::Inconclusive,
                "source_unavailable",
                relative,
                format!("cannot read input: {error}"),
            )
        })?;
    if bytes.len() > MAX_FILE_BYTES {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            format!("input grew beyond bounded maximum {MAX_FILE_BYTES}"),
        ));
    }
    Ok(bytes)
}

fn candidate_exists(root: &Path) -> Result<bool, PublishError> {
    validate_parent(root, CANDIDATE_RELATIVE_PATH)?;
    match fs::symlink_metadata(root.join(CANDIDATE_RELATIVE_PATH)) {
        Ok(_) => Ok(true),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(false),
        Err(error) => Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            CANDIDATE_RELATIVE_PATH,
            format!("cannot inspect candidate: {error}"),
        )),
    }
}

fn validate_published_target(root: &Path) -> Result<(), PublishError> {
    match fs::symlink_metadata(root.join(MANIFEST_RELATIVE_PATH)) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
            Err(PublishError::new(
                ErrorClass::Inconclusive,
                "publication_target_ambiguous",
                MANIFEST_RELATIVE_PATH,
                "published target exists but is not one regular file",
            ))
        }
        Ok(_) => Ok(()),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(()),
        Err(error) => Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            MANIFEST_RELATIVE_PATH,
            format!("cannot inspect published target: {error}"),
        )),
    }
}

fn sync_ci_parent(root: &Path) -> Result<(), PublishError> {
    File::open(root.join("ci"))
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            PublishError::new(
                ErrorClass::InternalFault,
                "directory_sync_failed",
                "ci",
                format!("cannot sync publication directory: {error}"),
            )
        })
}

fn acquire_lock(path: &Path, wait_ms: u64) -> Result<(File, u128), PublishError> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(path)
        .map_err(|error| {
            PublishError::new(
                ErrorClass::Inconclusive,
                "lock_unavailable",
                path.display().to_string(),
                format!("cannot open the persistent publication lock: {error}"),
            )
        })?;
    let started = Instant::now();
    loop {
        match File::try_lock(&file) {
            Ok(()) => return Ok((file, started.elapsed().as_millis())),
            Err(TryLockError::WouldBlock) => {
                if started.elapsed() >= Duration::from_millis(wait_ms) {
                    return Err(PublishError::new(
                        ErrorClass::Inconclusive,
                        "lock_timeout",
                        path.display().to_string(),
                        format!("exclusive publication lock was busy for {wait_ms}ms"),
                    ));
                }
                thread::sleep(Duration::from_millis(10));
            }
            Err(TryLockError::Error(error)) => {
                return Err(PublishError::new(
                    ErrorClass::Inconclusive,
                    "lock_unavailable",
                    path.display().to_string(),
                    format!("cannot acquire exclusive publication lock: {error}"),
                ));
            }
        }
    }
}

fn write_synced_candidate(root: &Path, bytes: &[u8]) -> Result<(), PublishError> {
    let path = root.join(CANDIDATE_RELATIVE_PATH);
    let mut candidate = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|error| {
            PublishError::new(
                if matches!(error.kind(), std::io::ErrorKind::AlreadyExists) {
                    ErrorClass::Inconclusive
                } else {
                    ErrorClass::InternalFault
                },
                if matches!(error.kind(), std::io::ErrorKind::AlreadyExists) {
                    "stale_candidate"
                } else {
                    "candidate_create_failed"
                },
                CANDIDATE_RELATIVE_PATH,
                format!("cannot create candidate without overwrite: {error}"),
            )
        })?;
    candidate.write_all(bytes).map_err(|error| {
        PublishError::new(
            ErrorClass::InternalFault,
            "candidate_write_failed",
            CANDIDATE_RELATIVE_PATH,
            format!("candidate remains and old publication is untouched: {error}"),
        )
    })?;
    candidate.sync_all().map_err(|error| {
        PublishError::new(
            ErrorClass::InternalFault,
            "candidate_sync_failed",
            CANDIDATE_RELATIVE_PATH,
            format!("candidate remains and old publication is untouched: {error}"),
        )
    })?;
    drop(candidate);
    sync_ci_parent(root)
}

fn regenerate_with_hook(
    root: &Path,
    lock_path: &Path,
    wait_ms: u64,
    before_rename: impl FnOnce() -> Result<(), PublishError>,
) -> Result<Receipt, PublishError> {
    let root = checked_root(root)?;
    let (_lock, lock_wait_ms) = acquire_lock(lock_path, wait_ms)?;
    if candidate_exists(&root)? {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "stale_candidate",
            CANDIDATE_RELATIVE_PATH,
            "an interrupted publication exists; refuse every new regeneration until it is explicitly resolved",
        ));
    }
    validate_published_target(&root)?;

    let source_before = read_regular_bounded(&root, SOURCE_RELATIVE_PATH)?;
    let ids = parse_source(&source_before)?;
    let expected = render_manifest(&ids);
    write_synced_candidate(&root, &expected)?;
    let candidate = read_regular_bounded(&root, CANDIDATE_RELATIVE_PATH)?;
    if candidate != expected {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "candidate_invalid",
            CANDIDATE_RELATIVE_PATH,
            "synced candidate is not the exact canonical generation just rendered",
        ));
    }

    before_rename()?;

    let source_after = read_regular_bounded(&root, SOURCE_RELATIVE_PATH)?;
    if source_before != source_after {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            SOURCE_RELATIVE_PATH,
            "Beads export changed while the lock-held candidate was generated; old publication is untouched and candidate remains typed",
        ));
    }
    let candidate = read_regular_bounded(&root, CANDIDATE_RELATIVE_PATH)?;
    if candidate != expected {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "candidate_invalid",
            CANDIDATE_RELATIVE_PATH,
            "candidate changed after validation; old publication is untouched",
        ));
    }
    fs::rename(
        root.join(CANDIDATE_RELATIVE_PATH),
        root.join(MANIFEST_RELATIVE_PATH),
    )
    .map_err(|error| {
        PublishError::new(
            ErrorClass::InternalFault,
            "atomic_rename_failed",
            CANDIDATE_RELATIVE_PATH,
            format!("candidate promotion failed and old publication is untouched: {error}"),
        )
    })?;
    sync_ci_parent(&root)?;

    let published = read_regular_bounded(&root, MANIFEST_RELATIVE_PATH)?;
    if published != expected {
        return Err(PublishError::new(
            ErrorClass::InternalFault,
            "published_generation_invalid",
            MANIFEST_RELATIVE_PATH,
            "published bytes differ from the validated candidate after atomic rename",
        ));
    }
    let source_final = read_regular_bounded(&root, SOURCE_RELATIVE_PATH)?;
    if source_final != source_before {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "source_drift_after_commit",
            SOURCE_RELATIVE_PATH,
            "Beads export changed across atomic commit; no clean terminal receipt is emitted",
        ));
    }
    if candidate_exists(&root)? {
        return Err(PublishError::new(
            ErrorClass::Inconclusive,
            "candidate_reappeared",
            CANDIDATE_RELATIVE_PATH,
            "a competing publication candidate appeared before the clean receipt",
        ));
    }
    Ok(Receipt {
        projection_hash: projection_hash(&ids),
        source_root: source_root(&source_before),
        record_count: ids.len(),
        source_bytes: source_before.len(),
        manifest_bytes: expected.len(),
        lock_wait_ms,
    })
}

fn regenerate(root: &Path, wait_ms: u64) -> Result<Receipt, PublishError> {
    regenerate_with_hook(root, Path::new(LOCK_PATH), wait_ms, || Ok(()))
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            control if control <= '\u{1f}' => {
                use std::fmt::Write as _;
                write!(&mut escaped, "\\u{:04x}", u32::from(control))
                    .expect("writing to String cannot fail");
            }
            other => escaped.push(other),
        }
    }
    escaped
}

#[derive(Debug, Eq, PartialEq)]
struct Cli {
    root: PathBuf,
    robot: bool,
    wait_ms: u64,
}

fn parse_cli(arguments: &[String]) -> Result<Option<Cli>, String> {
    let mut root = PathBuf::from(".");
    let mut robot = false;
    let mut wait_ms = DEFAULT_WAIT_MS;
    let mut root_seen = false;
    let mut wait_seen = false;
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--root" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .filter(|value| !value.starts_with('-'))
                    .ok_or_else(|| "--root requires one path".to_string())?;
                if root_seen {
                    return Err("--root may be specified only once".to_string());
                }
                root_seen = true;
                root = PathBuf::from(value);
            }
            "--wait-ms" => {
                index += 1;
                let value = arguments
                    .get(index)
                    .filter(|value| !value.starts_with('-'))
                    .ok_or_else(|| "--wait-ms requires one integer".to_string())?;
                if wait_seen {
                    return Err("--wait-ms may be specified only once".to_string());
                }
                wait_seen = true;
                wait_ms = value
                    .parse::<u64>()
                    .map_err(|error| format!("--wait-ms must be an integer: {error}"))?;
                if wait_ms > MAX_WAIT_MS {
                    return Err(format!("--wait-ms exceeds bounded maximum {MAX_WAIT_MS}"));
                }
            }
            "--robot" => robot = true,
            "--help" | "-h" => return Ok(None),
            unknown => return Err(format!("unknown argument `{unknown}`")),
        }
        index += 1;
    }
    Ok(Some(Cli {
        root,
        robot,
        wait_ms,
    }))
}

fn usage() -> &'static str {
    "usage: kernel-ownership-publisher [--root <workspace>] [--wait-ms <0..30000>] [--robot]"
}

fn main() -> ExitCode {
    let started = Instant::now();
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let cli = match parse_cli(&arguments) {
        Ok(Some(cli)) => cli,
        Ok(None) => {
            println!("{}", usage());
            return ExitCode::SUCCESS;
        }
        Err(detail) => {
            let robot = arguments.iter().any(|argument| argument == "--robot");
            if robot {
                println!(
                    "{{\"schema\":\"fln.kernel-contract-ownership-publication/1\",\"event\":\"cli_failure\",\"verdict\":\"internal_fault\",\"exit_code\":2,\"detail\":\"{}\"}}",
                    json_escape(&detail)
                );
            } else {
                eprintln!("{detail}\n{}", usage());
            }
            return ExitCode::from(2);
        }
    };
    match regenerate(&cli.root, cli.wait_ms) {
        Ok(receipt) => {
            if cli.robot {
                println!(
                    "{{\"schema\":\"fln.kernel-contract-ownership-publication/1\",\"event\":\"run_end\",\"verdict\":\"pass\",\"exit_code\":0,\"record_count\":{},\"projection_hash\":\"{}\",\"source_root\":\"{}\",\"source_bytes\":{},\"manifest_bytes\":{},\"lock_wait_ms\":{},\"publication_stage\":\"candidate-synced-source-stable-atomic-rename-directory-synced\",\"cleanup\":\"candidate_absent\",\"duration_ms\":{}}}",
                    receipt.record_count,
                    receipt.projection_hash,
                    receipt.source_root,
                    receipt.source_bytes,
                    receipt.manifest_bytes,
                    receipt.lock_wait_ms,
                    started.elapsed().as_millis(),
                );
            } else {
                println!(
                    "kernel-ownership-publisher: pass records={} projection_hash={} source_root={} source_bytes={} manifest_bytes={} lock_wait_ms={} publication_stage=candidate-synced-source-stable-atomic-rename-directory-synced cleanup=candidate_absent duration_ms={}",
                    receipt.record_count,
                    receipt.projection_hash,
                    receipt.source_root,
                    receipt.source_bytes,
                    receipt.manifest_bytes,
                    receipt.lock_wait_ms,
                    started.elapsed().as_millis(),
                );
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            if cli.robot {
                println!(
                    "{{\"schema\":\"fln.kernel-contract-ownership-publication/1\",\"event\":\"run_end\",\"verdict\":\"{}\",\"exit_code\":{},\"reason\":\"{}\",\"path\":\"{}\",\"detail\":\"{}\",\"publication_stage\":\"refused-without-clean-terminal-receipt\",\"cleanup\":\"not_established\",\"duration_ms\":{}}}",
                    error.class.as_str(),
                    error.class.exit_code(),
                    error.reason,
                    json_escape(&error.path),
                    json_escape(&error.detail),
                    started.elapsed().as_millis(),
                );
            } else {
                eprintln!("kernel-ownership-publisher: {error}");
            }
            ExitCode::from(error.class.exit_code())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::mpsc;
    use std::time::{SystemTime, UNIX_EPOCH};

    const CHILD_ROOT: &str = "FLN_OWNERSHIP_PUBLISH_CHILD_ROOT";
    const CHILD_LOCK: &str = "FLN_OWNERSHIP_PUBLISH_CHILD_LOCK";
    const CHILD_MODE: &str = "FLN_OWNERSHIP_PUBLISH_CHILD_MODE";
    const CHILD_MARKER: &str = "FLN_OWNERSHIP_PUBLISH_CHILD_MARKER";
    const CHILD_RELEASE: &str = "FLN_OWNERSHIP_PUBLISH_CHILD_RELEASE";

    fn retained_root(tag: &str) -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        loop {
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "fln-ownership-publisher-{}-{stamp}-{sequence}-{tag}",
                std::process::id()
            ));
            match fs::create_dir(&root) {
                Ok(()) => {
                    fs::create_dir(root.join(".beads")).expect("create Beads fixture parent");
                    fs::create_dir(root.join("ci")).expect("create CI fixture parent");
                    eprintln!("retained ownership-publisher fixture: {}", root.display());
                    return root;
                }
                Err(error) if matches!(error.kind(), std::io::ErrorKind::AlreadyExists) => {}
                Err(error) => assert_eq!(
                    error.kind(),
                    std::io::ErrorKind::AlreadyExists,
                    "create retained fixture"
                ),
            }
        }
    }

    fn source(ids: &[&str]) -> Vec<u8> {
        let mut output = String::new();
        for id in ids {
            output.push_str(&format!("{{\"id\":\"{id}\"}}\n"));
        }
        output.into_bytes()
    }

    fn write_synced(path: &Path, bytes: &[u8]) {
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)
            .expect("open fixture file");
        file.write_all(bytes).expect("write fixture file");
        file.sync_all().expect("sync fixture file");
    }

    fn wait_for_file(path: &Path, failure: &str) {
        for _ in 0..500 {
            if path.is_file() {
                return;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert!(path.is_file(), "{failure}");
    }

    #[test]
    fn unlocked_last_writer_reproduces_the_silent_dropped_bead() {
        let root = retained_root("naive-race");
        let first_snapshot = source(&["fln-a", "fln-x"]);
        let latest_snapshot = source(&["fln-a", "fln-x", "fln-y"]);
        write_synced(&root.join(SOURCE_RELATIVE_PATH), &latest_snapshot);
        let stale_manifest = render_manifest(&parse_source(&first_snapshot).unwrap());
        let latest_manifest = render_manifest(&parse_source(&latest_snapshot).unwrap());
        let published = root.join(MANIFEST_RELATIVE_PATH);
        let (stale_ready_tx, stale_ready_rx) = mpsc::channel();
        let (latest_written_tx, latest_written_rx) = mpsc::channel();

        let stale_path = published.clone();
        let stale = thread::spawn(move || {
            stale_ready_tx.send(()).expect("announce stale snapshot");
            latest_written_rx.recv().expect("wait for latest writer");
            write_synced(&stale_path, &stale_manifest);
        });
        let latest_path = published.clone();
        let latest = thread::spawn(move || {
            stale_ready_rx.recv().expect("stale writer has read");
            write_synced(&latest_path, &latest_manifest);
            latest_written_tx.send(()).expect("release stale writer");
        });
        latest.join().expect("latest writer joins");
        stale.join().expect("stale writer joins");

        let final_bytes = fs::read(&published).expect("read last-writer publication");
        let internally_consistent_stale =
            render_manifest(&parse_source(&first_snapshot).expect("parse first snapshot"));
        assert_eq!(
            final_bytes, internally_consistent_stale,
            "plant failed to reproduce an internally consistent stale winner"
        );
        assert_ne!(
            final_bytes,
            render_manifest(&parse_source(&latest_snapshot).expect("parse latest snapshot")),
            "MUTANT-SURVIVED: naive last writer did not drop fln-y"
        );
    }

    #[test]
    fn publisher_child() {
        let Ok(root) = std::env::var(CHILD_ROOT) else {
            return;
        };
        let lock = PathBuf::from(std::env::var(CHILD_LOCK).expect("child lock accompanies root"));
        let mode = std::env::var(CHILD_MODE).expect("child mode accompanies root");
        let result = if mode == "pause" {
            let marker =
                PathBuf::from(std::env::var(CHILD_MARKER).expect("pause child needs marker"));
            let release =
                PathBuf::from(std::env::var(CHILD_RELEASE).expect("pause child needs release"));
            regenerate_with_hook(Path::new(&root), &lock, 5_000, || {
                write_synced(&marker, b"lock-held-candidate-synced\n");
                wait_for_file(&release, "parent did not release paused publisher");
                Ok(())
            })
        } else {
            regenerate_with_hook(Path::new(&root), &lock, 5_000, || Ok(()))
        };
        result.expect("child publication succeeds");
    }

    #[test]
    fn concurrent_publishers_serialize_the_authoritative_read_through_rename() {
        let root = retained_root("serialized-race");
        let lock = root.join("publisher.lock");
        let marker = root.join("first-publisher-paused");
        let release = root.join("release-first-publisher");
        let latest_source = source(&["fln-a", "fln-x", "fln-y"]);
        write_synced(&root.join(SOURCE_RELATIVE_PATH), &latest_source);

        let executable = std::env::current_exe().expect("current test executable");
        let mut first = Command::new(&executable)
            .args(["--exact", "tests::publisher_child", "--nocapture"])
            .env(CHILD_ROOT, &root)
            .env(CHILD_LOCK, &lock)
            .env(CHILD_MODE, "pause")
            .env(CHILD_MARKER, &marker)
            .env(CHILD_RELEASE, &release)
            .spawn()
            .expect("spawn first publisher");
        wait_for_file(
            &marker,
            "first publisher did not reach the lock-held boundary",
        );

        let mut second = Command::new(&executable)
            .args(["--exact", "tests::publisher_child", "--nocapture"])
            .env(CHILD_ROOT, &root)
            .env(CHILD_LOCK, &lock)
            .env(CHILD_MODE, "plain")
            .spawn()
            .expect("spawn competing publisher");
        thread::sleep(Duration::from_millis(150));
        assert!(
            second
                .try_wait()
                .expect("poll competing publisher")
                .is_none(),
            "competing publisher escaped the exclusive critical section"
        );

        write_synced(&release, b"release\n");
        assert!(first.wait().expect("reap first publisher").success());
        assert!(second.wait().expect("reap second publisher").success());

        let expected = render_manifest(&parse_source(&latest_source).expect("parse latest source"));
        assert_eq!(
            fs::read(root.join(MANIFEST_RELATIVE_PATH)).expect("read final publication"),
            expected,
            "serialized publishers did not preserve every live bead"
        );
        assert!(
            !root.join(CANDIDATE_RELATIVE_PATH).exists(),
            "successful serialization left a candidate behind"
        );
    }

    #[test]
    fn source_change_during_publication_fails_typed_and_preserves_old_generation() {
        let root = retained_root("source-drift");
        let lock = root.join("publisher.lock");
        let baseline = source(&["fln-a"]);
        write_synced(&root.join(SOURCE_RELATIVE_PATH), &baseline);
        regenerate_with_hook(&root, &lock, 1_000, || Ok(())).expect("publish baseline");
        let old = fs::read(root.join(MANIFEST_RELATIVE_PATH)).expect("read baseline manifest");

        let next = source(&["fln-a", "fln-x"]);
        write_synced(&root.join(SOURCE_RELATIVE_PATH), &next);
        let newest = source(&["fln-a", "fln-x", "fln-y"]);
        let error = regenerate_with_hook(&root, &lock, 1_000, || {
            write_synced(&root.join(SOURCE_RELATIVE_PATH), &newest);
            Ok(())
        })
        .expect_err("source drift must refuse atomic promotion");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "source_drift");
        assert_eq!(
            fs::read(root.join(MANIFEST_RELATIVE_PATH)).expect("old publication survives"),
            old
        );
        assert!(
            root.join(CANDIDATE_RELATIVE_PATH).is_file(),
            "typed interrupted candidate was not retained"
        );
    }

    #[test]
    fn cli_is_bounded_and_unambiguous() {
        assert_eq!(
            parse_cli(&["--root".into(), "/a".into(), "--robot".into()]),
            Ok(Some(Cli {
                root: PathBuf::from("/a"),
                robot: true,
                wait_ms: DEFAULT_WAIT_MS,
            }))
        );
        assert!(parse_cli(&["--root".into(), "/a".into(), "--root".into(), "/b".into()]).is_err());
        assert!(parse_cli(&["--wait-ms".into(), "30001".into()]).is_err());
    }
}
