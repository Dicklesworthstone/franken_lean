//! Terminal W1 contract handoff: one rooted generation over every rendered surface.
//!
//! The domain extractors remain the only authority for ABI, OLEAN/ILEAN, extern, and
//! builtin facts. This module does not extract or reinterpret those facts. It joins the
//! atomically published `PIN_TARGET_INVENTORY` to a reviewed, exact output policy and
//! binds the bytes of every checked-in projection under one handoff root. Consumers
//! refuse a changed output, an omitted or stale policy row, or any sibling candidate.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};

use crate::checks::Finding;
use crate::contract_inventory::{self, ErrorClass};
use crate::{
    CONTRACT_HANDOFF_CANDIDATE_FILE, CONTRACT_HANDOFF_FILE, CONTRACT_HANDOFF_POLICY_FILE,
    CONTRACT_HANDOFF_SCHEMA_FILE,
};

pub const DEFINITION_SCHEMA: &str = "fln-contract-handoff-definition/1";
pub const HANDOFF_SCHEMA: &str = "fln-contract-handoff/1";
pub const POLICY_SCHEMA: &str = "fln-contract-handoff-policy/1";
pub const MAX_OUTPUT_BYTES: u64 = 536_870_912;
pub const MAX_ROWS: usize = 64;
pub const MAX_LINE_BYTES: usize = 8_192;

pub const SCHEMA_DEFINITION: &str = "\
schema fln-contract-handoff-definition/1
handoff-schema fln-contract-handoff/1
policy-schema fln-contract-handoff-policy/1
inventory-authority contracts/PIN_TARGET_INVENTORY.txt
output-authority ci/CONTRACT_HANDOFF_POLICY.txt
hash fnv1a64-noncryptographic domain=required fields=u64le-length-prefixed
row-fields key,path,domain,role,bytes,content-root,identity,authority,support
root-fields definition,inventory,policy,outputs,canonical
row-order canonical-key-byte-order
policy-join exact-bijection
authority-states observed
publication candidate=contracts/CONTRACT_HANDOFF.txt.candidate commit=atomic-rename recovery=explicit-promotion
source-candidate rule=sibling-dot-candidate outcome=inconclusive
limits output-bytes=536870912 rows=64 line-bytes=8192
";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RequiredOutput {
    pub key: &'static str,
    pub path: &'static str,
    pub domain: &'static str,
    pub role: &'static str,
    pub support: &'static str,
}

/// Reviewed W1 handoff surface. This independent list makes deletion of a policy row a
/// typed mismatch instead of silently narrowing what "all generated outputs" means.
pub const REQUIRED_OUTPUTS: &[RequiredOutput] = &[
    RequiredOutput {
        key: "abi-contract-markdown",
        path: "ABI_CONTRACT.md",
        domain: "abi",
        role: "markdown",
        support: "required",
    },
    RequiredOutput {
        key: "abi-inventory",
        path: "contracts/abi_inventory.json",
        domain: "abi",
        role: "canonical-intermediate",
        support: "required",
    },
    RequiredOutput {
        key: "abi-layout",
        path: "contracts/ABI_TARGET_LAYOUT.txt",
        domain: "abi",
        role: "target-contract",
        support: "required",
    },
    RequiredOutput {
        key: "abi-rust-boundary",
        path: "crates/fln-unsafe-abi/src/contract.rs",
        domain: "abi",
        role: "rust-boundary",
        support: "required",
    },
    RequiredOutput {
        key: "abi-rust-public",
        path: "crates/fln-rt/src/abi.rs",
        domain: "abi",
        role: "rust-public",
        support: "required",
    },
    RequiredOutput {
        key: "builtin-environment-000",
        path: "contracts/builtin_environment.tsv",
        domain: "environment",
        role: "observation-shard",
        support: "required",
    },
    RequiredOutput {
        key: "builtin-environment-001",
        path: "contracts/builtin_environment.001.tsv",
        domain: "environment",
        role: "observation-shard",
        support: "required",
    },
    RequiredOutput {
        key: "builtin-environment-002",
        path: "contracts/builtin_environment.002.tsv",
        domain: "environment",
        role: "observation-shard",
        support: "required",
    },
    RequiredOutput {
        key: "builtin-partition",
        path: "contracts/builtin_partition.tsv",
        domain: "environment",
        role: "policy-projection",
        support: "required",
    },
    RequiredOutput {
        key: "contract-inventory",
        path: "contracts/PIN_TARGET_INVENTORY.txt",
        domain: "inventory",
        role: "canonical-join",
        support: "required",
    },
    RequiredOutput {
        key: "extern-census",
        path: "contracts/extern_census.tsv",
        domain: "environment",
        role: "extern-census",
        support: "required",
    },
    RequiredOutput {
        key: "extern-environment-envelope",
        path: "contracts/EXTERN_BUILTIN_ENVIRONMENT.txt",
        domain: "environment",
        role: "publication-envelope",
        support: "required",
    },
    RequiredOutput {
        key: "format-contract-markdown",
        path: "OLEAN_CONTRACT.md",
        domain: "format",
        role: "markdown",
        support: "required",
    },
    RequiredOutput {
        key: "format-inventory",
        path: "contracts/olean_inventory.json",
        domain: "format",
        role: "canonical-intermediate",
        support: "required",
    },
    RequiredOutput {
        key: "format-rust-public",
        path: "crates/fln-olean/src/format.rs",
        domain: "format",
        role: "rust-public",
        support: "required",
    },
    RequiredOutput {
        key: "format-rust-region",
        path: "crates/fln-rt/src/region_contract.rs",
        domain: "format",
        role: "rust-region",
        support: "required",
    },
    RequiredOutput {
        key: "olean-ilean-format",
        path: "contracts/OLEAN_ILEAN_FORMAT.txt",
        domain: "format",
        role: "exact-format-contract",
        support: "required",
    },
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HandoffError {
    pub class: ErrorClass,
    pub reason: &'static str,
    pub path: String,
    pub detail: String,
}

impl HandoffError {
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

impl fmt::Display for HandoffError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} {} {}: {}",
            self.class.as_str(),
            self.reason,
            self.path,
            self.detail
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HandoffSnapshot {
    pub handoff_root: String,
    pub definition_root: String,
    pub inventory_root: String,
    pub suite_lock_root: String,
    pub policy_root: String,
    pub output_root: String,
    pub row_count: usize,
    pub domain_count: usize,
    pub output_bytes: u64,
    pub canonical_bytes: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublicationAction {
    Published,
    Recovered,
}

impl PublicationAction {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Published => "published",
            Self::Recovered => "recovered",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicationReceipt {
    pub action: PublicationAction,
    pub snapshot: HandoffSnapshot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PolicyRow {
    key: String,
    path: String,
    domain: String,
    role: String,
    support: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OutputObservation {
    policy: PolicyRow,
    bytes: u64,
    content_root: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CanonicalHandoff {
    bytes: Vec<u8>,
    snapshot: HandoffSnapshot,
}

fn fnv_update(mut state: u64, bytes: &[u8]) -> u64 {
    for byte in bytes {
        state ^= u64::from(*byte);
        state = state.wrapping_mul(0x0000_0100_0000_01b3);
    }
    state
}

fn hash_fields(domain: &str, fields: &[&[u8]]) -> u64 {
    let mut state = 0xcbf2_9ce4_8422_2325;
    state = fnv_update(state, domain.as_bytes());
    state = fnv_update(state, &[0]);
    for field in fields {
        state = fnv_update(state, &(field.len() as u64).to_le_bytes());
        state = fnv_update(state, field);
    }
    state
}

fn hash_one(domain: &str, bytes: &[u8]) -> u64 {
    hash_fields(domain, &[bytes])
}

fn labeled_hash(value: u64) -> String {
    format!("fnv1a64:{value:016x}")
}

fn parse_labeled_hash(value: &str) -> Option<u64> {
    let hex = value.strip_prefix("fnv1a64:")?;
    (hex.len() == 16)
        .then(|| u64::from_str_radix(hex, 16).ok())
        .flatten()
}

fn safe_token(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_alphabetic()
                || byte.is_ascii_digit()
                || matches!(byte, b'-' | b'_' | b'.' | b'/')
        })
}

fn validate_text_shape(
    path: &str,
    text: &str,
    class: ErrorClass,
    reason: &'static str,
) -> Result<(), HandoffError> {
    if text.is_empty() || !text.ends_with('\n') || text.contains('\r') || text.contains('\0') {
        return Err(HandoffError::new(
            class,
            reason,
            path,
            "text must be nonempty canonical LF-terminated UTF-8 without NUL",
        ));
    }
    for (index, line) in text.lines().enumerate() {
        if line.len() > MAX_LINE_BYTES {
            return Err(HandoffError::new(
                class,
                reason,
                path,
                format!(
                    "line {} exceeds the bounded line limit {MAX_LINE_BYTES}",
                    index + 1
                ),
            ));
        }
    }
    Ok(())
}

fn checked_root(root: &Path) -> Result<PathBuf, HandoffError> {
    let canonical = fs::canonicalize(root).map_err(|error| {
        HandoffError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            root.display().to_string(),
            format!("cannot resolve authoritative root: {error}"),
        )
    })?;
    if !canonical.is_dir() {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            canonical.display().to_string(),
            "authoritative root is not a directory",
        ));
    }
    Ok(canonical)
}

fn validate_parent_chain(root: &Path, relative: &str) -> Result<(), HandoffError> {
    let path = Path::new(relative);
    if path.is_absolute()
        || path
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(HandoffError::new(
            ErrorClass::InternalFault,
            "invalid_governed_path",
            relative,
            "governed path must be a normalized workspace-relative path",
        ));
    }
    let mut current = root.to_path_buf();
    let components: Vec<_> = path.components().collect();
    for component in components.iter().take(components.len().saturating_sub(1)) {
        let Component::Normal(part) = component else {
            unreachable!("validated normal components")
        };
        current.push(part);
        let metadata = fs::symlink_metadata(&current).map_err(|error| {
            HandoffError::new(
                ErrorClass::Inconclusive,
                "source_unavailable",
                relative,
                format!(
                    "cannot inspect governed parent {}: {error}",
                    current.display()
                ),
            )
        })?;
        if metadata.file_type().is_symlink() || !metadata.is_dir() {
            return Err(HandoffError::new(
                ErrorClass::Inconclusive,
                "source_path_ambiguous",
                relative,
                format!(
                    "governed parent {} must be a real directory",
                    current.display()
                ),
            ));
        }
    }
    Ok(())
}

fn read_small_text(
    root: &Path,
    relative: &str,
    class: ErrorClass,
    reason: &'static str,
) -> Result<String, HandoffError> {
    validate_parent_chain(root, relative)?;
    let path = root.join(relative);
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            relative,
            format!("cannot inspect governed text: {error}"),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(HandoffError::new(
            class,
            reason,
            relative,
            "governed text must be a regular file, not a symlink",
        ));
    }
    if metadata.len() > 1_048_576 {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            "small governed text exceeds 1048576 bytes",
        ));
    }
    let bytes = fs::read(&path).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            relative,
            format!("cannot read governed text: {error}"),
        )
    })?;
    String::from_utf8(bytes).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            relative,
            format!("governed text is not UTF-8: {error}"),
        )
    })
}

fn parse_policy(text: &str) -> Result<BTreeMap<String, PolicyRow>, HandoffError> {
    validate_text_shape(
        CONTRACT_HANDOFF_POLICY_FILE,
        text,
        ErrorClass::Violation,
        "handoff_policy_invalid",
    )?;
    let mut rows = BTreeMap::new();
    let mut schema_seen = false;
    for (index, raw) in text.lines().enumerate() {
        let line_number = index + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == format!("schema {POLICY_SCHEMA}") {
            if schema_seen {
                return Err(HandoffError::new(
                    ErrorClass::Violation,
                    "handoff_policy_invalid",
                    CONTRACT_HANDOFF_POLICY_FILE,
                    format!("line {line_number} duplicates the schema"),
                ));
            }
            schema_seen = true;
            continue;
        }
        let fields: Vec<_> = line.split_ascii_whitespace().collect();
        // ubs:ignore — public schema token comparison, not secret material.
        if fields.len() != 6 || fields[0] != "row" {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "handoff_policy_invalid",
                CONTRACT_HANDOFF_POLICY_FILE,
                format!("line {line_number} is not a canonical policy row"),
            ));
        }
        let value = |token: &str, prefix: &str| -> Result<String, HandoffError> {
            let value = token.strip_prefix(prefix).ok_or_else(|| {
                HandoffError::new(
                    ErrorClass::Violation,
                    "handoff_policy_invalid",
                    CONTRACT_HANDOFF_POLICY_FILE,
                    format!("line {line_number} expected {prefix}<value>"),
                )
            })?;
            if !safe_token(value) {
                return Err(HandoffError::new(
                    ErrorClass::Violation,
                    "handoff_policy_invalid",
                    CONTRACT_HANDOFF_POLICY_FILE,
                    format!("line {line_number} has unsafe token `{value}`"),
                ));
            }
            Ok(value.to_string())
        };
        let key = fields[1].to_string();
        if !safe_token(&key) {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "handoff_policy_invalid",
                CONTRACT_HANDOFF_POLICY_FILE,
                format!("line {line_number} has unsafe key `{key}`"),
            ));
        }
        let row = PolicyRow {
            key: key.clone(),
            path: value(fields[2], "path=")?,
            domain: value(fields[3], "domain=")?,
            role: value(fields[4], "role=")?,
            support: value(fields[5], "support=")?,
        };
        if rows.insert(key.clone(), row).is_some() {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "handoff_policy_duplicate",
                CONTRACT_HANDOFF_POLICY_FILE,
                format!("line {line_number} duplicates key `{key}`"),
            ));
        }
    }
    if !schema_seen {
        return Err(HandoffError::new(
            ErrorClass::Violation,
            "handoff_policy_invalid",
            CONTRACT_HANDOFF_POLICY_FILE,
            format!("expected `schema {POLICY_SCHEMA}`"),
        ));
    }
    let expected = REQUIRED_OUTPUTS
        .iter()
        .map(|output| {
            (
                output.key.to_string(),
                PolicyRow {
                    key: output.key.to_string(),
                    path: output.path.to_string(),
                    domain: output.domain.to_string(),
                    role: output.role.to_string(),
                    support: output.support.to_string(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    // ubs:ignore — reviewed public policy rows, not credentials or tokens.
    if rows != expected {
        let actual_keys = rows.keys().cloned().collect::<BTreeSet<_>>();
        let expected_keys = expected.keys().cloned().collect::<BTreeSet<_>>();
        return Err(HandoffError::new(
            ErrorClass::Violation,
            "handoff_policy_not_exact",
            CONTRACT_HANDOFF_POLICY_FILE,
            format!(
                "reviewed output policy differs from the required W1 surface: missing={:?} stale={:?}",
                expected_keys.difference(&actual_keys).collect::<Vec<_>>(),
                actual_keys.difference(&expected_keys).collect::<Vec<_>>()
            ),
        ));
    }
    Ok(rows)
}

fn ensure_absent(root: &Path, relative: &str, reason: &'static str) -> Result<(), HandoffError> {
    validate_parent_chain(root, relative)?;
    match fs::symlink_metadata(root.join(relative)) {
        Ok(_) => Err(HandoffError::new(
            ErrorClass::Inconclusive,
            reason,
            relative,
            "candidate presence makes the handoff generation non-authoritative",
        )),
        // ubs:ignore — public OS error classification, not secret material.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "candidate_state_unknown",
            relative,
            format!("cannot inspect candidate state: {error}"),
        )),
    }
}

fn ensure_no_source_candidates(root: &Path) -> Result<(), HandoffError> {
    ensure_absent(
        root,
        &format!("{CONTRACT_HANDOFF_SCHEMA_FILE}.candidate"),
        "stale_source_candidate",
    )?;
    ensure_absent(
        root,
        &format!("{CONTRACT_HANDOFF_POLICY_FILE}.candidate"),
        "stale_source_candidate",
    )?;
    for output in REQUIRED_OUTPUTS {
        ensure_absent(
            root,
            &format!("{}.candidate", output.path),
            "stale_source_candidate",
        )?;
    }
    Ok(())
}

fn ensure_no_candidate(root: &Path) -> Result<(), HandoffError> {
    ensure_absent(root, CONTRACT_HANDOFF_CANDIDATE_FILE, "stale_candidate")?;
    ensure_no_source_candidates(root)
}

fn observe_output(
    root: &Path,
    policy: PolicyRow,
    remaining: &mut u64,
) -> Result<OutputObservation, HandoffError> {
    validate_parent_chain(root, &policy.path)?;
    let path = root.join(&policy.path);
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_unavailable",
            &policy.path,
            format!("cannot inspect required output: {error}"),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_ambiguous",
            &policy.path,
            "required output must be a regular file, not a symlink",
        ));
    }
    let bytes = metadata.len();
    if bytes > *remaining {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            &policy.path,
            format!("output generation exceeds the bounded total {MAX_OUTPUT_BYTES} bytes"),
        ));
    }
    *remaining -= bytes;
    let mut state = 0xcbf2_9ce4_8422_2325;
    state = fnv_update(state, b"fln.contract-handoff.output-content/1");
    state = fnv_update(state, &[0]);
    state = fnv_update(state, &(policy.path.len() as u64).to_le_bytes());
    state = fnv_update(state, policy.path.as_bytes());
    state = fnv_update(state, &bytes.to_le_bytes());
    let mut file = File::open(&path).map_err(|error| {
        HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_unavailable",
            &policy.path,
            format!("cannot open required output: {error}"),
        )
    })?;
    let mut read_bytes = 0_u64;
    let mut buffer = [0_u8; 65_536];
    loop {
        let count = file.read(&mut buffer).map_err(|error| {
            HandoffError::new(
                ErrorClass::Inconclusive,
                "handoff_output_unavailable",
                &policy.path,
                format!("cannot read required output: {error}"),
            )
        })?;
        if count == 0 {
            break;
        }
        read_bytes = read_bytes.checked_add(count as u64).ok_or_else(|| {
            HandoffError::new(
                ErrorClass::InternalFault,
                "resource_accounting_overflow",
                &policy.path,
                "output byte accounting overflowed u64",
            )
        })?;
        state = fnv_update(state, &buffer[..count]);
    }
    // ubs:ignore — public resource-accounting counters, not secret material.
    if read_bytes != bytes {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            &policy.path,
            format!("metadata length {bytes} changed while reading to {read_bytes} bytes"),
        ));
    }
    if matches!(
        policy.role.as_str(),
        "markdown" | "rust-boundary" | "rust-public" | "rust-region"
    ) {
        let text = fs::read_to_string(&path).map_err(|error| {
            HandoffError::new(
                ErrorClass::Violation,
                "generated_output_invalid",
                &policy.path,
                format!("generated projection is not readable UTF-8: {error}"),
            )
        })?;
        if !text.contains("@generated") {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "generated_marker_missing",
                &policy.path,
                "rendered Markdown and Rust projections must carry the generated marker",
            ));
        }
        if text.contains(".elan/toolchains") {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "reference_runtime_path_leak",
                &policy.path,
                "generated release input contains a Reference toolchain runtime path",
            ));
        }
        if text.contains("FLN_MOCK_CONSUMER") {
            return Err(HandoffError::new(
                ErrorClass::Violation,
                "mock_consumer_substitution",
                &policy.path,
                "mock consumer marker cannot satisfy the real W1 handoff",
            ));
        }
    }
    Ok(OutputObservation {
        policy,
        bytes,
        content_root: state,
    })
}

fn canonical_from_root(root: &Path) -> Result<CanonicalHandoff, HandoffError> {
    let inventory = contract_inventory::consume(root)
        .map_err(|error| HandoffError::new(error.class, error.reason, error.path, error.detail))?;
    let schema_text = read_small_text(
        root,
        CONTRACT_HANDOFF_SCHEMA_FILE,
        ErrorClass::Inconclusive,
        "handoff_schema_unavailable",
    )?;
    validate_text_shape(
        CONTRACT_HANDOFF_SCHEMA_FILE,
        &schema_text,
        ErrorClass::Violation,
        "handoff_schema_invalid",
    )?;
    // ubs:ignore — checked-in public schema bytes, not secret material.
    if schema_text != SCHEMA_DEFINITION {
        return Err(HandoffError::new(
            ErrorClass::Violation,
            "handoff_schema_mismatch",
            CONTRACT_HANDOFF_SCHEMA_FILE,
            "governed schema bytes do not match the independently implemented v1 contract",
        ));
    }
    let policy_text = read_small_text(
        root,
        CONTRACT_HANDOFF_POLICY_FILE,
        ErrorClass::Inconclusive,
        "handoff_policy_unavailable",
    )?;
    let policy = parse_policy(&policy_text)?;
    if policy.len() > MAX_ROWS {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            CONTRACT_HANDOFF_POLICY_FILE,
            format!("output policy exceeds the bounded row limit {MAX_ROWS}"),
        ));
    }
    let mut remaining = MAX_OUTPUT_BYTES;
    let mut observations = BTreeMap::new();
    for row in policy.into_values() {
        let observation = observe_output(root, row, &mut remaining)?;
        observations.insert(observation.policy.key.clone(), observation);
    }
    let output_bytes = MAX_OUTPUT_BYTES - remaining;
    let definition_root = hash_one(
        "fln.contract-handoff.definition-root/1",
        schema_text.as_bytes(),
    );
    let policy_root = hash_one("fln.contract-handoff.policy-root/1", policy_text.as_bytes());
    let mut output_projection = String::new();
    let mut domains = BTreeSet::new();
    for (key, observation) in &observations {
        domains.insert(observation.policy.domain.as_str());
        output_projection.push_str(&format!(
            "output {key} path={} domain={} role={} bytes={} content-root={} support={}\n",
            observation.policy.path,
            observation.policy.domain,
            observation.policy.role,
            observation.bytes,
            labeled_hash(observation.content_root),
            observation.policy.support,
        ));
    }
    let output_root = hash_one(
        "fln.contract-handoff.output-root/1",
        output_projection.as_bytes(),
    );
    let mut output = String::new();
    output.push_str(&format!("schema {HANDOFF_SCHEMA}\n"));
    output.push_str(&format!(
        "definition-root {}\n",
        labeled_hash(definition_root)
    ));
    output.push_str(&format!("inventory-root {}\n", inventory.inventory_root));
    output.push_str(&format!("suite-lock-root {}\n", inventory.suite_lock_root));
    output.push_str(&format!("policy-root {}\n", labeled_hash(policy_root)));
    output.push_str(&format!("output-root {}\n", labeled_hash(output_root)));
    output.push_str(&format!("row-count {}\n", observations.len()));
    output.push_str(&format!("domain-count {}\n", domains.len()));
    output.push_str(&format!("output-bytes {output_bytes}\n"));
    for (key, observation) in &observations {
        let bytes = observation.bytes.to_string();
        let content_root = labeled_hash(observation.content_root);
        let identity = hash_fields(
            "fln.contract-handoff.row-identity/1",
            &[
                inventory.inventory_root.as_bytes(),
                key.as_bytes(),
                observation.policy.path.as_bytes(),
                observation.policy.domain.as_bytes(),
                observation.policy.role.as_bytes(),
                bytes.as_bytes(),
                content_root.as_bytes(),
                b"observed",
                observation.policy.support.as_bytes(),
            ],
        );
        output.push_str(&format!(
            "row {key} path={} domain={} role={} bytes={bytes} content-root={content_root} identity={} authority=observed support={}\n",
            observation.policy.path,
            observation.policy.domain,
            observation.policy.role,
            labeled_hash(identity),
            observation.policy.support,
        ));
    }
    let handoff_root = hash_one("fln.contract-handoff.root/1", output.as_bytes());
    output.push_str(&format!("handoff-root {}\n", labeled_hash(handoff_root)));
    validate_text_shape(
        CONTRACT_HANDOFF_FILE,
        &output,
        ErrorClass::InternalFault,
        "handoff_renderer_invalid",
    )?;
    let canonical_bytes = output.len();
    Ok(CanonicalHandoff {
        bytes: output.into_bytes(),
        snapshot: HandoffSnapshot {
            handoff_root: labeled_hash(handoff_root),
            definition_root: labeled_hash(definition_root),
            inventory_root: inventory.inventory_root,
            suite_lock_root: inventory.suite_lock_root,
            policy_root: labeled_hash(policy_root),
            output_root: labeled_hash(output_root),
            row_count: observations.len(),
            domain_count: domains.len(),
            output_bytes,
            canonical_bytes,
        },
    })
}

pub fn canonical_handoff_text(root: &Path) -> Result<String, HandoffError> {
    let root = checked_root(root)?;
    ensure_no_candidate(&root)?;
    let expected = canonical_from_root(&root)?;
    String::from_utf8(expected.bytes).map_err(|error| {
        HandoffError::new(
            ErrorClass::InternalFault,
            "handoff_renderer_non_utf8",
            CONTRACT_HANDOFF_FILE,
            error.to_string(),
        )
    })
}

fn validate_artifact(
    path: &str,
    bytes: &[u8],
    expected: &CanonicalHandoff,
    class: ErrorClass,
    reason: &'static str,
) -> Result<(), HandoffError> {
    let text = std::str::from_utf8(bytes).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            path,
            format!("published handoff is not UTF-8: {error}"),
        )
    })?;
    validate_text_shape(path, text, class, reason)?;
    let (prefix, root_line) = text.rsplit_once("handoff-root ").ok_or_else(|| {
        HandoffError::new(class, reason, path, "handoff has no terminal root row")
    })?;
    if root_line.lines().count() != 1 || !root_line.ends_with('\n') {
        return Err(HandoffError::new(
            class,
            reason,
            path,
            "handoff-root must be the single terminal row",
        ));
    }
    let claimed = parse_labeled_hash(root_line.trim_end()).ok_or_else(|| {
        HandoffError::new(
            class,
            reason,
            path,
            "handoff-root must be canonical fnv1a64:<16-lower-hex>",
        )
    })?;
    let computed = hash_one("fln.contract-handoff.root/1", prefix.as_bytes());
    // ubs:ignore — public non-cryptographic artifact roots, not authentication.
    if claimed != computed {
        return Err(HandoffError::new(
            class,
            reason,
            path,
            format!(
                "handoff root mismatch: claimed={} computed={}",
                labeled_hash(claimed),
                labeled_hash(computed)
            ),
        ));
    }
    // ubs:ignore — public generated artifact bytes, not secret material.
    if bytes != expected.bytes {
        return Err(HandoffError::new(
            class,
            reason,
            path,
            "handoff is not the exact canonical join for the current inventory, policy, and output bytes",
        ));
    }
    Ok(())
}

fn read_handoff(
    root: &Path,
    relative: &str,
    class: ErrorClass,
    reason: &'static str,
) -> Result<Vec<u8>, HandoffError> {
    validate_parent_chain(root, relative)?;
    let metadata = fs::symlink_metadata(root.join(relative)).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            relative,
            format!("cannot inspect handoff artifact: {error}"),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(HandoffError::new(
            class,
            reason,
            relative,
            "handoff artifact must be a regular file, not a symlink",
        ));
    }
    if metadata.len() > 1_048_576 {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            "handoff artifact exceeds 1048576 bytes",
        ));
    }
    fs::read(root.join(relative)).map_err(|error| {
        HandoffError::new(
            class,
            reason,
            relative,
            format!("cannot read handoff artifact: {error}"),
        )
    })
}

fn sync_parent(root: &Path) -> Result<(), HandoffError> {
    let handoff_path = root.join(CONTRACT_HANDOFF_FILE);
    let parent = handoff_path.parent().ok_or_else(|| {
        HandoffError::new(
            ErrorClass::InternalFault,
            "handoff_parent_missing",
            CONTRACT_HANDOFF_FILE,
            "handoff path has no parent",
        )
    })?;
    File::open(parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            HandoffError::new(
                ErrorClass::InternalFault,
                "handoff_directory_sync_failed",
                CONTRACT_HANDOFF_FILE,
                format!("cannot sync handoff directory: {error}"),
            )
        })
}

pub fn consume(root: &Path) -> Result<HandoffSnapshot, HandoffError> {
    let root = checked_root(root)?;
    ensure_no_candidate(&root)?;
    let expected_before = canonical_from_root(&root)?;
    let published = read_handoff(
        &root,
        CONTRACT_HANDOFF_FILE,
        ErrorClass::Violation,
        "published_handoff_missing",
    )?;
    validate_artifact(
        CONTRACT_HANDOFF_FILE,
        &published,
        &expected_before,
        ErrorClass::Violation,
        "published_handoff_invalid",
    )?;
    let expected_after = canonical_from_root(&root)?;
    // ubs:ignore — public generated artifact bytes, not secret material.
    if expected_before.bytes != expected_after.bytes {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_HANDOFF_FILE,
            "governed outputs changed while consuming the handoff",
        ));
    }
    ensure_no_candidate(&root)?;
    Ok(expected_before.snapshot)
}

fn publish_with_hook(
    root: &Path,
    before_rename: impl FnOnce() -> Result<(), HandoffError>,
) -> Result<PublicationReceipt, HandoffError> {
    let root = checked_root(root)?;
    ensure_no_candidate(&root)?;
    validate_parent_chain(&root, CONTRACT_HANDOFF_FILE)?;
    if let Ok(metadata) = fs::symlink_metadata(root.join(CONTRACT_HANDOFF_FILE))
        && (metadata.file_type().is_symlink() || !metadata.is_file())
    {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "publication_target_ambiguous",
            CONTRACT_HANDOFF_FILE,
            "published handoff target must be absent or a regular file",
        ));
    }
    let expected_before = canonical_from_root(&root)?;
    let candidate_path = root.join(CONTRACT_HANDOFF_CANDIDATE_FILE);
    let mut candidate = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&candidate_path)
        .map_err(|error| {
            // ubs:ignore — public OS error classification, not secret material.
            let (class, reason) = if error.kind() == std::io::ErrorKind::AlreadyExists {
                (ErrorClass::Inconclusive, "stale_candidate")
            } else {
                (ErrorClass::InternalFault, "candidate_create_failed")
            };
            HandoffError::new(
                class,
                reason,
                CONTRACT_HANDOFF_CANDIDATE_FILE,
                format!("cannot create handoff candidate without overwrite: {error}"),
            )
        })?;
    candidate
        .write_all(&expected_before.bytes)
        .map_err(|error| {
            HandoffError::new(
                ErrorClass::InternalFault,
                "candidate_write_failed",
                CONTRACT_HANDOFF_CANDIDATE_FILE,
                format!("candidate write failed; prior handoff remains untouched: {error}"),
            )
        })?;
    candidate.sync_all().map_err(|error| {
        HandoffError::new(
            ErrorClass::InternalFault,
            "candidate_sync_failed",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            format!("candidate sync failed; prior handoff remains untouched: {error}"),
        )
    })?;
    drop(candidate);
    sync_parent(&root)?;
    let candidate_bytes = read_handoff(
        &root,
        CONTRACT_HANDOFF_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_HANDOFF_CANDIDATE_FILE,
        &candidate_bytes,
        &expected_before,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;
    before_rename()?;
    let expected_after = canonical_from_root(&root)?;
    // ubs:ignore — public generated artifact bytes, not secret material.
    if expected_before.bytes != expected_after.bytes {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            "inventory, policy, or output bytes changed between candidate derivation and commit",
        ));
    }
    fs::rename(
        root.join(CONTRACT_HANDOFF_CANDIDATE_FILE),
        root.join(CONTRACT_HANDOFF_FILE),
    )
    .map_err(|error| {
        HandoffError::new(
            ErrorClass::InternalFault,
            "atomic_rename_failed",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            format!("atomic handoff promotion failed: {error}"),
        )
    })?;
    sync_parent(&root)?;
    let published = read_handoff(
        &root,
        CONTRACT_HANDOFF_FILE,
        ErrorClass::InternalFault,
        "published_handoff_missing_after_rename",
    )?;
    validate_artifact(
        CONTRACT_HANDOFF_FILE,
        &published,
        &expected_before,
        ErrorClass::InternalFault,
        "published_handoff_invalid_after_rename",
    )?;
    ensure_no_candidate(&root)?;
    Ok(PublicationReceipt {
        action: PublicationAction::Published,
        snapshot: expected_before.snapshot,
    })
}

pub fn publish(root: &Path) -> Result<PublicationReceipt, HandoffError> {
    publish_with_hook(root, || Ok(()))
}

pub fn recover(root: &Path) -> Result<PublicationReceipt, HandoffError> {
    let root = checked_root(root)?;
    ensure_no_source_candidates(&root)?;
    validate_parent_chain(&root, CONTRACT_HANDOFF_CANDIDATE_FILE)?;
    if fs::symlink_metadata(root.join(CONTRACT_HANDOFF_CANDIDATE_FILE)).is_err() {
        return Err(HandoffError::new(
            ErrorClass::Violation,
            "candidate_missing",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            "explicit recovery requested but no candidate exists",
        ));
    }
    let expected_before = canonical_from_root(&root)?;
    let candidate = read_handoff(
        &root,
        CONTRACT_HANDOFF_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_HANDOFF_CANDIDATE_FILE,
        &candidate,
        &expected_before,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;
    let expected_after = canonical_from_root(&root)?;
    // ubs:ignore — public generated artifact bytes, not secret material.
    if expected_before.bytes != expected_after.bytes {
        return Err(HandoffError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            "outputs changed while validating handoff recovery",
        ));
    }
    fs::rename(
        root.join(CONTRACT_HANDOFF_CANDIDATE_FILE),
        root.join(CONTRACT_HANDOFF_FILE),
    )
    .map_err(|error| {
        HandoffError::new(
            ErrorClass::InternalFault,
            "atomic_recovery_rename_failed",
            CONTRACT_HANDOFF_CANDIDATE_FILE,
            format!("validated handoff recovery rename failed: {error}"),
        )
    })?;
    sync_parent(&root)?;
    ensure_no_candidate(&root)?;
    Ok(PublicationReceipt {
        action: PublicationAction::Recovered,
        snapshot: expected_before.snapshot,
    })
}

/// Whether a failed [`consume`] is the fresh-checkout census absence, which is a typed
/// inconclusive rather than a structural defect.
///
/// **Exactly one reason, and the exclusions are the content of this predicate.**
///
/// - `handoff_output_unavailable` — the required output is not there at all: a fresh clone of
///   `origin/main`, where the four census shards are gitignored and unreachable from history
///   (`fln-census-out-of-git-2ya9`, 242,966,844 bytes measured at `9d86aac2`).
/// - `handoff_output_ambiguous` — **deliberately NOT admitted.** That is what a symlink shim
///   into another checkout produces, which is the workaround people install to fake the shards.
///   Admitting it would convert the refusal of a bad workaround into a clean tree.
/// - Every `Violation`, and every other `Inconclusive` reason (`stale_candidate` among them),
///   stay findings. A predicate that widens silences the whole handoff audit.
///
/// **One producer, deliberately.** The no-mock rig's skip and this audit ask the same question,
/// and a second copy of the answer is the defect `franken_lean-m5bl` was filed for — a guard
/// over a transcription is weaker than not having the transcription.
fn is_absent_census(error: &HandoffError) -> bool {
    error.class == ErrorClass::Inconclusive && error.reason == "handoff_output_unavailable"
}

pub fn audit_with_snapshot(root: &Path) -> (Vec<Finding>, Option<HandoffSnapshot>) {
    // The lower-level inventory audit owns its own authority failures. Reporting a
    // second terminal-handoff error when that prerequisite is invalid obscures the
    // first divergence and breaks typed diagnosis.
    if contract_inventory::consume(root).is_err() {
        return (Vec::new(), None);
    }
    match consume(root) {
        Ok(snapshot) => (Vec::new(), Some(snapshot)),
        // An absent materialised artifact is NOT a structural defect. FL-INV-07: resource
        // absence yields a typed `Inconclusive` that is never rendered as rejection, and a
        // `FLN-STRUCT-036` finding asserts this tree is structurally unclean — which is a
        // rejection with a code on it. On a fresh clone the shards are simply not there, and
        // the repository is not thereby malformed (`fln-census-empty-referent-no-mock-krb0`).
        //
        // **It returns `None`, and that is what keeps this from being a hollow green.** The
        // snapshot is how a caller records complete authority evidence; withholding it is the
        // difference between "audited and clean" and "not audited", so an absent census reports
        // as unestablished rather than as success. Emitting no finding AND a snapshot would be
        // `hugg`'s shape — a verdict whose subject never ran, wearing a pass.
        Err(error) if is_absent_census(&error) => (Vec::new(), None),
        Err(error) => {
            let code = match error.class {
                ErrorClass::Violation => "FLN-STRUCT-035",
                ErrorClass::Inconclusive | ErrorClass::InternalFault => "FLN-STRUCT-036",
            };
            (
                vec![Finding {
                    code,
                    path: error.path,
                    detail: format!(
                        "contract-handoff {} reason={}: {}",
                        error.class.as_str(),
                        error.reason,
                        error.detail
                    ),
                }],
                None,
            )
        }
    }
}

pub fn audit(root: &Path) -> Vec<Finding> {
    audit_with_snapshot(root).0
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::thread;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");
    const INVENTORY_SCHEMA: &str = include_str!("../../../contracts/CONTRACT_INVENTORY_V1.txt");
    const INVENTORY_POLICY: &str = include_str!("../../../ci/PIN_TARGET_POLICY.txt");
    const ABI_LAYOUT: &str = include_str!("../../../contracts/ABI_TARGET_LAYOUT.txt");
    const FORMAT: &str = include_str!("../../../contracts/OLEAN_ILEAN_FORMAT.txt");
    const ENVIRONMENT: &str = include_str!("../../../contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");
    const HANDOFF_POLICY: &str = include_str!("../../../ci/CONTRACT_HANDOFF_POLICY.txt");

    fn retained_root(tag: &str) -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        loop {
            let path = std::env::temp_dir().join(format!(
                "contract-handoff-{tag}-{}-{stamp}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return path,
                Err(error) => assert_eq!(
                    error.kind(),
                    std::io::ErrorKind::AlreadyExists,
                    "create retained root"
                ),
            }
        }
    }

    fn write_new(root: &Path, relative: &str, bytes: &[u8]) {
        let path = root.join(relative);
        fs::create_dir_all(path.parent().expect("fixture parent")).expect("fixture directories");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("create fixture file without overwrite");
        file.write_all(bytes).expect("write fixture");
    }

    fn fixture_root(tag: &str) -> PathBuf {
        let root = retained_root(tag);
        write_new(&root, "SUITE.lock", SUITE_LOCK.as_bytes());
        write_new(
            &root,
            "contracts/CONTRACT_INVENTORY_V1.txt",
            INVENTORY_SCHEMA.as_bytes(),
        );
        write_new(
            &root,
            "ci/PIN_TARGET_POLICY.txt",
            INVENTORY_POLICY.as_bytes(),
        );
        write_new(
            &root,
            "contracts/ABI_TARGET_LAYOUT.txt",
            ABI_LAYOUT.as_bytes(),
        );
        write_new(&root, "contracts/OLEAN_ILEAN_FORMAT.txt", FORMAT.as_bytes());
        write_new(
            &root,
            "contracts/EXTERN_BUILTIN_ENVIRONMENT.txt",
            ENVIRONMENT.as_bytes(),
        );
        let inventory = contract_inventory::canonical_inventory_text(
            SUITE_LOCK,
            INVENTORY_SCHEMA,
            INVENTORY_POLICY,
            ABI_LAYOUT,
            FORMAT,
            ENVIRONMENT,
        )
        .expect("fixture canonical inventory");
        write_new(
            &root,
            "contracts/PIN_TARGET_INVENTORY.txt",
            inventory.as_bytes(),
        );
        write_new(
            &root,
            CONTRACT_HANDOFF_SCHEMA_FILE,
            SCHEMA_DEFINITION.as_bytes(),
        );
        write_new(
            &root,
            CONTRACT_HANDOFF_POLICY_FILE,
            HANDOFF_POLICY.as_bytes(),
        );
        for output in REQUIRED_OUTPUTS {
            if !root.join(output.path).exists() {
                write_new(
                    &root,
                    output.path,
                    format!("@generated fixture {}\n", output.key).as_bytes(),
                );
            }
        }
        root
    }

    #[test]
    fn contract_cross_surface_join() {
        let root = fixture_root("cross-surface");
        let receipt = publish(&root).expect("complete fixture publishes");
        assert_eq!(receipt.snapshot.row_count, REQUIRED_OUTPUTS.len());
        assert_eq!(receipt.snapshot.domain_count, 4);
        assert_eq!(consume(&root).unwrap(), receipt.snapshot);

        fs::write(
            root.join("ABI_CONTRACT.md"),
            b"@generated planted markdown-only edit\n",
        )
        .expect("plant one-sided output edit");
        let error = consume(&root).expect_err("one-sided output mutation must be refused");
        assert_eq!(error.class, ErrorClass::Violation);
        assert_eq!(error.reason, "published_handoff_invalid");
        let findings = audit(&root);
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].code, "FLN-STRUCT-035");
    }

    #[test]
    fn contract_render_determinism() {
        let root = fixture_root("render-determinism");
        let first = canonical_handoff_text(&root).expect("first canonical render");
        let second = canonical_handoff_text(&root).expect("second canonical render");
        assert_eq!(first, second);
        assert!(first.ends_with('\n'));
        assert_eq!(first.matches("handoff-root ").count(), 1);
    }

    #[test]
    fn contract_drift_policy() {
        let missing = fixture_root("policy-missing");
        let policy = fs::read_to_string(missing.join(CONTRACT_HANDOFF_POLICY_FILE))
            .expect("read fixture policy");
        let mutated = policy.replacen(
            "row abi-contract-markdown path=ABI_CONTRACT.md domain=abi role=markdown support=required\n",
            "",
            1,
        );
        fs::write(missing.join(CONTRACT_HANDOFF_POLICY_FILE), mutated)
            .expect("plant omitted policy row");
        let error = canonical_handoff_text(&missing).expect_err("omitted output policy must fail");
        assert_eq!(error.reason, "handoff_policy_not_exact");

        let stale = fixture_root("policy-stale");
        let mut policy =
            fs::read_to_string(stale.join(CONTRACT_HANDOFF_POLICY_FILE)).expect("read policy");
        policy.push_str(
            "row stale-output path=contracts/stale.txt domain=abi role=markdown support=required\n",
        );
        fs::write(stale.join(CONTRACT_HANDOFF_POLICY_FILE), policy).expect("plant stale policy");
        let error = canonical_handoff_text(&stale).expect_err("stale output policy must fail");
        assert_eq!(error.reason, "handoff_policy_not_exact");

        let duplicate = fixture_root("policy-duplicate");
        let mut policy =
            fs::read_to_string(duplicate.join(CONTRACT_HANDOFF_POLICY_FILE)).expect("read policy");
        policy.push_str(
            "row abi-contract-markdown path=ABI_CONTRACT.md domain=abi role=markdown support=required\n",
        );
        fs::write(duplicate.join(CONTRACT_HANDOFF_POLICY_FILE), policy)
            .expect("plant duplicate policy");
        let error =
            canonical_handoff_text(&duplicate).expect_err("duplicate output policy must fail");
        assert_eq!(error.reason, "handoff_policy_duplicate");

        let candidate = fixture_root("source-candidate");
        publish(&candidate).expect("baseline publication");
        write_new(
            &candidate,
            "crates/fln-rt/src/abi.rs.candidate",
            b"partial generation\n",
        );
        let error = consume(&candidate).expect_err("source candidate must mask old handoff");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "stale_source_candidate");
        let findings = audit(&candidate);
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].code, "FLN-STRUCT-036");

        let leaked = fixture_root("reference-path-leak");
        fs::write(
            leaked.join("crates/fln-rt/src/abi.rs"),
            b"//! @generated\nconst LEAK: &str = \".elan/toolchains/reference\";\n",
        )
        .expect("plant Reference path");
        let error = canonical_handoff_text(&leaked).expect_err("Reference runtime path must fail");
        assert_eq!(error.reason, "reference_runtime_path_leak");

        let mocked = fixture_root("mock-substitution");
        fs::write(
            mocked.join("crates/fln-rt/src/abi.rs"),
            b"//! @generated\nconst FLN_MOCK_CONSUMER: bool = true;\n",
        )
        .expect("plant mock consumer");
        let error = canonical_handoff_text(&mocked).expect_err("mock consumer must fail");
        assert_eq!(error.reason, "mock_consumer_substitution");

        let exhausted = fixture_root("resource-exhaustion");
        OpenOptions::new()
            .write(true)
            .open(exhausted.join("contracts/builtin_environment.tsv"))
            .expect("open sparse output")
            .set_len(MAX_OUTPUT_BYTES + 1)
            .expect("plant sparse oversized output");
        let error = canonical_handoff_text(&exhausted).expect_err("oversized output must fail");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "resource_exhausted");
    }

    const CHILD_ROOT_ENV: &str = "FLN_CONTRACT_HANDOFF_TEST_CHILD_ROOT";
    const CHILD_MARKER_ENV: &str = "FLN_CONTRACT_HANDOFF_TEST_CHILD_MARKER";

    #[test]
    fn interrupted_handoff_publication_helper() {
        let Ok(root) = std::env::var(CHILD_ROOT_ENV) else {
            return;
        };
        let marker =
            PathBuf::from(std::env::var(CHILD_MARKER_ENV).expect("marker accompanies child root"));
        publish_with_hook(Path::new(&root), || {
            fs::write(&marker, b"candidate-synced-before-rename\n").map_err(|error| {
                HandoffError::new(
                    ErrorClass::InternalFault,
                    "test_plant_failed",
                    marker.display().to_string(),
                    error.to_string(),
                )
            })?;
            loop {
                thread::park();
            }
        })
        .expect("parent kills helper at hook");
    }

    #[test]
    fn contract_publication_atomicity() {
        let root = fixture_root("publication-atomicity");
        publish(&root).expect("baseline publishes");
        let old = fs::read(root.join(CONTRACT_HANDOFF_FILE)).expect("old publication");
        fs::write(
            root.join("ABI_CONTRACT.md"),
            b"@generated second valid generation\n",
        )
        .expect("change governed output");
        let marker = root.join("candidate-ready");
        let mut child = Command::new(std::env::current_exe().expect("test executable"))
            .args([
                "--exact",
                "contract_handoff::tests::interrupted_handoff_publication_helper",
                "--nocapture",
            ])
            .env(CHILD_ROOT_ENV, &root)
            .env(CHILD_MARKER_ENV, &marker)
            .spawn()
            .expect("spawn handoff publisher");
        let mut ready = false;
        for _ in 0..1_000 {
            if marker.is_file() {
                ready = true;
                break;
            }
            if child.try_wait().expect("poll child").is_some() {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert!(ready, "publisher did not reach durable candidate boundary");
        child.kill().expect("kill between write and rename");
        assert!(!child.wait().expect("reap child").success());
        assert_eq!(
            fs::read(root.join(CONTRACT_HANDOFF_FILE)).expect("old handoff remains"),
            old
        );
        let error = consume(&root).expect_err("interrupted candidate must be refused");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "stale_candidate");
        let receipt = recover(&root).expect("valid candidate recovers atomically");
        assert_eq!(receipt.action, PublicationAction::Recovered);
        assert!(!root.join(CONTRACT_HANDOFF_CANDIDATE_FILE).exists());
        assert_eq!(consume(&root).unwrap(), receipt.snapshot);
    }

    // `is_absent_census` is the module-level predicate above, used by BOTH the no-mock rig's
    // skip and `audit_with_snapshot`. It had a second copy here for one commit; a guard over a
    // transcription is weaker than not having the transcription (`franken_lean-m5bl` R1), and
    // the two copies would have been free to drift in exactly the direction that silences the
    // audit while the rig still refuses.

    /// What a typed skip here does NOT earn, kept next to the tests that exercise it.
    ///
    /// It reports that nothing was established; it does not discharge the no-mock obligation.
    /// The notice goes to stderr, which cargo captures and discards for a *passing* test — so a
    /// skipped run is still not distinguishable from a real one by reading the terminal. That is
    /// `fln-rgha`'s subject and is NOT closed by this change. Making the skip visible needs the
    /// artifact stating the claim to name the artifact supplying its evidence, and that artifact
    /// is `ci/VERIFICATION_MANIFEST.jsonl`.
    const _SKIP_VISIBILITY_IS_NOT_EARNED: () = ();

    #[test]
    fn the_census_skip_admits_absence_and_refuses_every_neighbouring_failure() {
        let absent = HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_unavailable",
            "contracts/builtin_environment.tsv",
            "cannot inspect required output: No such file or directory",
        );
        assert!(is_absent_census(&absent));

        // The symlink shim. If this ever becomes skippable, the lane starts passing on trees
        // that borrowed another checkout's census.
        let shim = HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_ambiguous",
            "contracts/builtin_environment.tsv",
            "required output is a symlink",
        );
        assert!(!is_absent_census(&shim));

        // A different Inconclusive reason is a real refusal, not a missing file.
        let stale = HandoffError::new(
            ErrorClass::Inconclusive,
            "stale_candidate",
            "contracts/CONTRACT_HANDOFF.txt",
            "interrupted candidate",
        );
        assert!(!is_absent_census(&stale));

        // Class is checked as well as reason: a Violation carrying the same reason string must
        // not be skipped, or the predicate keys on text alone.
        let violation = HandoffError::new(
            ErrorClass::Violation,
            "handoff_output_unavailable",
            "contracts/builtin_environment.tsv",
            "declared present and absent",
        );
        assert!(!is_absent_census(&violation));
    }

    /// The join the skip rests on: a genuinely missing required output really does produce the
    /// one reason [`is_absent_census`] keys on.
    ///
    /// Without this the predicate is a claim about a string nothing produces. If `observe_output`
    /// ever classified absence differently, the skip would never fire and a fresh clone would go
    /// back to failing the gate — the exact condition
    /// `fln-census-empty-referent-no-mock-krb0` exists to remove — while every unit test above
    /// stayed green, because they construct their inputs by hand.
    ///
    /// The shard is **moved aside, never deleted**, and it is asserted to be a required output
    /// first: a test that removed a path no policy row names would prove nothing.
    #[test]
    fn a_missing_required_output_produces_the_reason_the_skip_keys_on() {
        let root = fixture_root("absent-census");
        publish(&root).expect("complete fixture publishes");
        consume(&root).expect("the complete fixture is consumable before the shard moves");

        let shard = "contracts/builtin_environment.tsv";
        assert!(
            REQUIRED_OUTPUTS.iter().any(|output| output.path == shard),
            "{shard} must be a required output, or moving it aside proves nothing"
        );
        fs::rename(
            root.join(shard),
            root.join("builtin_environment.tsv.moved-aside"),
        )
        .expect("move the shard aside");

        let error = consume(&root).expect_err("a missing required output must refuse");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "handoff_output_unavailable");
        assert_eq!(error.path, shard);
        assert!(
            is_absent_census(&error),
            "the real refusal must be the one the skip admits, or the skip is unreachable \
             in the condition it was written for: {error}"
        );
    }

    /// An absent shard is inconclusive, and inconclusive is neither a finding nor a pass.
    ///
    /// Both halves are asserted because either alone is a different defect. No finding with a
    /// snapshot would be `hugg`'s hollow green — a tree reported clean by an audit that never
    /// ran. A finding would be the FL-INV-07 violation this commit removes, rendering resource
    /// absence as a structural rejection.
    #[test]
    fn an_absent_shard_is_inconclusive_and_neither_a_finding_nor_authority_evidence() {
        let root = fixture_root("absent-census-audit");
        publish(&root).expect("complete fixture publishes");

        let (findings, snapshot) = audit_with_snapshot(&root);
        assert!(findings.is_empty(), "complete tree: {findings:?}");
        assert!(
            snapshot.is_some(),
            "a complete tree must yield authority evidence, or the control proves nothing"
        );

        fs::rename(
            root.join("contracts/builtin_environment.tsv"),
            root.join("builtin_environment.tsv.moved-aside"),
        )
        .expect("move the shard aside");

        let (findings, snapshot) = audit_with_snapshot(&root);
        assert!(
            findings.is_empty(),
            "an absent materialised artifact must not assert the tree is structurally \
             unclean: {findings:?}"
        );
        assert!(
            snapshot.is_none(),
            "...and it must not report authority evidence either, or the skip is a hollow green"
        );
    }

    /// Whether a typed skip's stated reason is **true of the tree it was taken at**.
    ///
    /// An absent census and a misdirected root produce the identical `handoff_output_unavailable`,
    /// so a skip that trusts the string is correct about what it saw and wrong about what it
    /// claims.
    ///
    /// Lifted out of [`contract_handoff_no_mock_e2e`], where it was an inline `assert!` no test
    /// could reach: an independent-gut campaign for `fln-census-empty-referent-no-mock-krb0`
    /// disabled it and **no test failed**, because in every tree the campaign could reach the
    /// shard was either genuinely absent — where the assertion holds vacuously — or present,
    /// where the skip never fires at all. A check unreachable from a test is carried by review,
    /// and review does not survive a context restart.
    ///
    /// It lives in this module rather than beside [`is_absent_census`] because the rig is its
    /// only caller: at module scope it is dead code in a non-test build, which `-D warnings`
    /// refuses. `is_absent_census` is module-scope for the opposite reason — `audit_with_snapshot`
    /// needs it too, and a second copy of that answer is `franken_lean-m5bl`'s defect.
    fn skip_reason_holds_at(root: &Path, error: &HandoffError) -> bool {
        !root.join(&error.path).exists()
    }

    /// The no-mock skip's stated reason is checked against the tree, and BOTH directions matter.
    ///
    /// This is `krb0`'s reported-reason half, which had no test until an independent-gut campaign
    /// disabled the check and nothing went red. The fixture carries the shard, so the identical
    /// `handoff_output_unavailable` that is truthful on a fresh clone is **false here** — a
    /// misdirected probe wearing a fresh-clone reason. Without the negative control below, a
    /// predicate hardwired to `false` would satisfy this cell and refuse every real skip.
    #[test]
    fn a_skip_reason_is_false_when_the_named_output_exists_at_the_probed_root() {
        let root = fixture_root("skip-reason");
        publish(&root).expect("complete fixture publishes");
        let error = HandoffError::new(
            ErrorClass::Inconclusive,
            "handoff_output_unavailable",
            "contracts/builtin_environment.tsv",
            "cannot inspect required output: No such file or directory",
        );
        assert!(
            root.join(&error.path).exists(),
            "the fixture must carry the shard, or this cell proves nothing"
        );
        assert!(
            !skip_reason_holds_at(&root, &error),
            "a skip claiming an output is unavailable while it EXISTS at the probed root must \
             not be admitted: that is a misdirected probe, not a fresh clone"
        );

        // The negative control: move it aside and the identical error becomes truthful.
        fs::rename(
            root.join(&error.path),
            root.join("builtin_environment.tsv.moved-aside"),
        )
        .expect("move the shard aside");
        assert!(
            skip_reason_holds_at(&root, &error),
            "a genuinely absent output must still be admitted, or the rig can never skip"
        );
    }

    /// The symlink shim must survive the change above as a finding.
    ///
    /// This is the cell that stops the repair widening: the shim and the absence differ only by
    /// `handoff_output_ambiguous` vs `handoff_output_unavailable`, and absorbing the former would
    /// let a tree that borrowed another checkout's census audit clean.
    #[cfg(unix)]
    #[test]
    fn the_symlink_shim_is_still_a_finding_after_absence_stops_being_one() {
        let root = fixture_root("shim-audit");
        publish(&root).expect("complete fixture publishes");

        let shard = root.join("contracts/builtin_environment.tsv");
        let moved = root.join("builtin_environment.tsv.moved-aside");
        fs::rename(&shard, &moved).expect("move the shard aside");
        std::os::unix::fs::symlink(&moved, &shard).expect("install the shim");

        let (findings, snapshot) = audit_with_snapshot(&root);
        assert!(
            !findings.is_empty(),
            "the symlink shim must not be absorbed as an absent census"
        );
        assert_eq!(findings[0].code, "FLN-STRUCT-036");
        assert!(snapshot.is_none());
    }

    #[test]
    fn contract_handoff_no_mock_e2e() {
        // Resolved through the tree check, not from this file's compile-time manifest
        // dir: a binary compiled in another checkout would otherwise consume that
        // tree's untracked census — 242,966,844 bytes across four shards, measured at
        // `9d86aac2` — and report the verdict here. This comment read "53 MB" until then,
        // which is `builtin_environment.tsv` ALONE, one shard of the four; the same figure
        // was wrong in AGENTS.md's green-bar row and right in `fln-census-out-of-git-2ya9`.
        // The `canonicalize` is kept so the root is spelled exactly as it was before the
        // conversion. Bead fln-cross-tree-baked-root-k60n.
        let root = fln_conformance::checked_workspace_root!()
            .canonicalize()
            .expect("real repository root");
        let snapshot = match consume(&root) {
            Ok(snapshot) => snapshot,
            Err(error) if is_absent_census(&error) => {
                // The reason is CHECKED against the filesystem at the root we probed, never
                // trusted from the string. An absent census and a misdirected root produce the
                // identical `handoff_output_unavailable`, and a skip that cannot tell them apart
                // is correct about what it saw and wrong about what it claims — recorded on
                // `fln-census-empty-referent-no-mock-krb0` after a cached binary consumed
                // another worktree's census. `checked_workspace_root!()` closes the baked-root
                // half (`fln-cross-tree-baked-root-k60n`); this closes the reported-reason half.
                assert!(
                    skip_reason_holds_at(&root, &error),
                    "typed skip claims {} is unavailable, but it EXISTS at the probed root {}. \
                     The skip's stated reason is false for this checkout, so this is a \
                     misdirected probe rather than a fresh clone with no census.",
                    error.path,
                    root.display()
                );
                eprintln!(
                    "SKIP contract_handoff_no_mock_e2e: required handoff output {} is absent at \
                     {}. This is a typed skip: NOTHING this no-mock rig checks has been \
                     established by this run. The census shards are gitignored and unreachable \
                     from main (bead `fln-census-out-of-git-2ya9`); regenerate them with \
                     `scripts/extract/census_materialize.sh`, which proves the result against \
                     tracked pins and exits 3 when the Reference toolchain is absent.",
                    error.path,
                    root.display()
                );
                return;
            }
            Err(error) => panic!("real checked-in handoff is not consumable: {error}"),
        };
        assert_eq!(snapshot.row_count, REQUIRED_OUTPUTS.len());
        assert_eq!(snapshot.domain_count, 4);
        assert!(snapshot.output_bytes > 200_000_000);
        for output in REQUIRED_OUTPUTS {
            let path = root.join(output.path);
            assert!(
                path.is_file(),
                "real handoff output missing: {}",
                output.path
            );
            if matches!(output.role, "rust-public" | "rust-boundary" | "rust-region") {
                let text = fs::read_to_string(path).expect("generated Rust is UTF-8");
                assert!(text.contains("@generated"));
                assert!(
                    !text.contains(".elan/toolchains"),
                    "generated release input leaked a Reference runtime path: {}",
                    output.path
                );
            }
        }
    }
}
