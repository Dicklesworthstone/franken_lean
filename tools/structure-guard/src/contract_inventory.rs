//! Canonical pin/target inventory and failure-atomic publication (bead `fln-k5rr`).
//!
//! `SUITE.lock` remains the only authority for exact toolchain, target, suite,
//! Reference, and Corpus values. The published inventory contains opaque evidence
//! roots and source locators, never a second copy of those values. A reviewed policy
//! classifies the derived raw rows, and the join must be bijective.
//!
//! Publication is candidate-first: create a sibling without overwrite, write and sync
//! the complete canonical generation, validate it, re-read its governed sources, then
//! atomically rename it over the published path and sync the parent directory. A
//! candidate left by cancellation or process death is never silently consumed.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};

use crate::checks::Finding;
use crate::lockfile::{SuiteLock, parse_suite_lock};
use crate::{
    CONTRACT_INVENTORY_CANDIDATE_FILE, CONTRACT_INVENTORY_FILE, CONTRACT_INVENTORY_POLICY_FILE,
    CONTRACT_INVENTORY_SCHEMA_FILE, SUITE_LOCK_FILE,
};

pub const DEFINITION_SCHEMA: &str = "fln-contract-inventory-definition/1";
pub const INVENTORY_SCHEMA: &str = "fln-contract-inventory/1";
pub const POLICY_SCHEMA: &str = "fln-contract-inventory-policy/1";
pub const EXTRACTOR_ID: &str = "suite-lock";
pub const EXTRACTOR_VERSION: &str = "1";
pub const MAX_SOURCE_BYTES: usize = 1_048_576;
pub const MAX_ROWS: usize = 4_096;
pub const MAX_LINE_BYTES: usize = 8_192;

/// The independently implemented schema contract. The governed file must match these
/// bytes exactly; changing the prose alone cannot silently widen what the consumer
/// accepts.
pub const SCHEMA_DEFINITION: &str = "\
schema fln-contract-inventory-definition/1
inventory-schema fln-contract-inventory/1
policy-schema fln-contract-inventory-policy/1
source-authority SUITE.lock
extractor suite-lock version=1
hash fnv1a64-noncryptographic domain=required fields=u64le-length-prefixed
row-fields key,kind,extractor,extractor-version,source,target-class,abi-class,raw-evidence-hash,identity,authority,support
root-fields schema,suite-lock,raw,policy,reference,canonical
row-order canonical-key-byte-order
pin-values forbidden-outside-source-authority
policy-join exact-bijection
authority-states observed
publication candidate=contracts/PIN_TARGET_INVENTORY.txt.candidate commit=atomic-rename recovery=explicit-promotion
limits source-bytes=1048576 rows=4096 line-bytes=8192
";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ErrorClass {
    Violation,
    Inconclusive,
    InternalFault,
}

impl ErrorClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Violation => "violation",
            Self::Inconclusive => "inconclusive",
            Self::InternalFault => "internal_fault",
        }
    }

    pub const fn exit_code(self) -> u8 {
        match self {
            Self::Violation => 1,
            Self::Inconclusive => 3,
            Self::InternalFault => 2,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InventoryError {
    pub class: ErrorClass,
    pub reason: &'static str,
    pub path: String,
    pub detail: String,
}

impl InventoryError {
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

impl fmt::Display for InventoryError {
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
pub struct InventorySnapshot {
    pub inventory_root: String,
    pub schema_root: String,
    pub suite_lock_root: String,
    pub raw_root: String,
    pub policy_root: String,
    pub reference_root: String,
    pub row_count: usize,
    pub target_row_count: usize,
    pub abi_row_count: usize,
    pub unresolved_row_count: usize,
    pub source_bytes: usize,
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
    pub snapshot: InventorySnapshot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PolicyRow {
    kind: String,
    support: String,
    target_class: String,
    abi_class: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RawRow {
    key: String,
    kind: &'static str,
    source: String,
    evidence_hash: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceSet {
    schema: Vec<u8>,
    suite_lock: Vec<u8>,
    policy: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CanonicalInventory {
    bytes: Vec<u8>,
    snapshot: InventorySnapshot,
}

fn fnv_update(mut state: u64, bytes: &[u8]) -> u64 {
    for byte in bytes {
        state ^= u64::from(*byte);
        state = state.wrapping_mul(0x0000_0100_0000_01b3);
    }
    state
}

/// Dependency-free, deterministic, domain-separated provenance hash. This is labeled
/// non-cryptographic in the schema; authority comes from exact derivation and byte
/// comparison against `SUITE.lock`, not collision-resistance claims.
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

fn validate_text_shape(
    path: &str,
    text: &str,
    class: ErrorClass,
    reason: &'static str,
) -> Result<(), InventoryError> {
    if text.len() > MAX_SOURCE_BYTES {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            path,
            format!(
                "input is {} bytes; the bounded limit is {MAX_SOURCE_BYTES}",
                text.len()
            ),
        ));
    }
    if !text.ends_with('\n') {
        return Err(InventoryError::new(
            class,
            reason,
            path,
            "canonical line-oriented input must end with LF",
        ));
    }
    if text.contains('\r') {
        return Err(InventoryError::new(
            class,
            reason,
            path,
            "CR bytes are forbidden; canonical line endings are LF",
        ));
    }
    if let Some((index, line)) = text
        .split_terminator('\n')
        .enumerate()
        .find(|(_, line)| line.len() > MAX_LINE_BYTES)
    {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            path,
            format!(
                "line {} is {} bytes; the bounded limit is {MAX_LINE_BYTES}",
                index + 1,
                line.len()
            ),
        ));
    }
    Ok(())
}

fn safe_key(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.' | b':' | b'/')
        })
}

fn parse_field<'a>(
    token: &'a str,
    name: &str,
    path: &str,
    line: usize,
) -> Result<&'a str, InventoryError> {
    token
        .strip_prefix(name)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                path,
                format!("line {line} needs `{name}<value>` in canonical field order"),
            )
        })
}

fn parse_policy(text: &str) -> Result<BTreeMap<String, PolicyRow>, InventoryError> {
    validate_text_shape(
        CONTRACT_INVENTORY_POLICY_FILE,
        text,
        ErrorClass::Violation,
        "policy_invalid",
    )?;
    let mut saw_schema = false;
    let mut rows = BTreeMap::new();
    let mut previous_key: Option<String> = None;

    for (index, raw) in text.lines().enumerate() {
        let line_number = index + 1;
        let line = raw.split_once('#').map_or(raw, |(prefix, _)| prefix).trim();
        if line.is_empty() {
            continue;
        }
        if !saw_schema {
            if !matches!(line, "schema fln-contract-inventory-policy/1") {
                return Err(InventoryError::new(
                    ErrorClass::Violation,
                    "policy_invalid",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    format!("line {line_number} must be `schema {POLICY_SCHEMA}`"),
                ));
            }
            saw_schema = true;
            continue;
        }
        if rows.len() >= MAX_ROWS {
            return Err(InventoryError::new(
                ErrorClass::Inconclusive,
                "resource_exhausted",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("policy exceeds the bounded row limit {MAX_ROWS}"),
            ));
        }
        let tokens: Vec<_> = line.split_whitespace().collect();
        let [
            directive,
            key_token,
            kind_token,
            support_token,
            target_token,
            abi_token,
        ] = tokens.as_slice()
        else {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!(
                    "line {line_number} must be `row <key> kind=... support=... target-class=... abi-class=...`"
                ),
            ));
        };
        if !matches!(*directive, "row") || !safe_key(key_token) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!(
                    "line {line_number} must be `row <key> kind=... support=... target-class=... abi-class=...`"
                ),
            ));
        }
        let key = (*key_token).to_string();
        if previous_key
            .as_ref()
            .is_some_and(|previous| previous >= &key)
        {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_not_canonical",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} row keys must be unique and byte-sorted"),
            ));
        }
        let kind = parse_field(
            kind_token,
            "kind=",
            CONTRACT_INVENTORY_POLICY_FILE,
            line_number,
        )?;
        let support = parse_field(
            support_token,
            "support=",
            CONTRACT_INVENTORY_POLICY_FILE,
            line_number,
        )?;
        let target_class = parse_field(
            target_token,
            "target-class=",
            CONTRACT_INVENTORY_POLICY_FILE,
            line_number,
        )?;
        let abi_class = parse_field(
            abi_token,
            "abi-class=",
            CONTRACT_INVENTORY_POLICY_FILE,
            line_number,
        )?;
        if !matches!(
            kind,
            "toolchain" | "target" | "suite" | "reference" | "corpus"
        ) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} has unsupported kind `{kind}`"),
            ));
        }
        if !matches!(support, "required" | "optional") {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} has unsupported support `{support}`"),
            ));
        }
        if !matches!(target_class, "none" | "certified") || !matches!(abi_class, "none") {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!(
                    "line {line_number} has an unsupported target/ABI classification for inventory v1"
                ),
            ));
        }
        if matches!(kind, "target") {
            if !matches!(support, "required") || !matches!(target_class, "certified") {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "target_class_ambiguous",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    format!("line {line_number} target rows must be required and certified"),
                ));
            }
        } else if !matches!(target_class, "none") {
            return Err(InventoryError::new(
                ErrorClass::Inconclusive,
                "target_class_ambiguous",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} non-target row claims a target class"),
            ));
        }
        if matches!(support, "optional") && !matches!(kind, "suite") {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_invalid",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} only suite rows may be optional"),
            ));
        }

        previous_key = Some(key.clone());
        rows.insert(
            key,
            PolicyRow {
                kind: kind.to_string(),
                support: support.to_string(),
                target_class: target_class.to_string(),
                abi_class: abi_class.to_string(),
            },
        );
    }
    if !saw_schema {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "policy_invalid",
            CONTRACT_INVENTORY_POLICY_FILE,
            "missing policy schema line",
        ));
    }
    Ok(rows)
}

fn evidence_hash(kind: &str, source: &str, facts: &[&str]) -> u64 {
    let mut fields: Vec<&[u8]> = Vec::with_capacity(facts.len() + 2);
    fields.push(kind.as_bytes());
    fields.push(source.as_bytes());
    fields.extend(facts.iter().map(|fact| fact.as_bytes()));
    hash_fields("fln.contract-inventory.raw-evidence/1", &fields)
}

fn raw_rows(lock: &SuiteLock) -> Result<BTreeMap<String, RawRow>, InventoryError> {
    let mut rows = BTreeMap::new();
    let mut insert = |row: RawRow| -> Result<(), InventoryError> {
        if rows.insert(row.key.clone(), row).is_some() {
            return Err(InventoryError::new(
                ErrorClass::InternalFault,
                "duplicate_raw_identity",
                SUITE_LOCK_FILE,
                "derived raw row identities are not unique",
            ));
        }
        Ok(())
    };

    let toolchain_source = "SUITE.lock:rust-toolchain";
    insert(RawRow {
        key: "toolchain".to_string(),
        kind: "toolchain",
        source: toolchain_source.to_string(),
        evidence_hash: evidence_hash(
            "toolchain",
            toolchain_source,
            &[&lock.rust_nightly, &lock.rust_release, &lock.rust_commit],
        ),
    })?;

    for (index, target) in lock.targets.iter().enumerate() {
        let key = format!("target:{:04}", index + 1);
        let source = format!("SUITE.lock:{key}");
        insert(RawRow {
            key,
            kind: "target",
            evidence_hash: evidence_hash("target", &source, &[target]),
            source,
        })?;
    }

    for (repo, pin) in &lock.suites {
        let source = format!("SUITE.lock:suite:{repo}");
        let path = pin.path.to_str().ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "non_utf8_suite_path",
                SUITE_LOCK_FILE,
                format!("suite `{repo}` path ceased to be UTF-8 after parsing"),
            )
        })?;
        insert(RawRow {
            key: format!("suite:{repo}"),
            kind: "suite",
            evidence_hash: evidence_hash("suite", &source, &[repo, &pin.commit, path]),
            source,
        })?;
    }

    let (reference_repo, reference_tag, reference_commit) =
        lock.reference.as_ref().ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "missing_parsed_reference",
                SUITE_LOCK_FILE,
                "strict SUITE.lock parser returned no Reference row",
            )
        })?;
    let reference_tree = lock.reference_tree.as_ref().ok_or_else(|| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "missing_parsed_reference_tree",
            SUITE_LOCK_FILE,
            "strict SUITE.lock parser returned no Reference tree",
        )
    })?;
    let reference_source = "SUITE.lock:reference";
    insert(RawRow {
        key: "reference".to_string(),
        kind: "reference",
        source: reference_source.to_string(),
        evidence_hash: evidence_hash(
            "reference",
            reference_source,
            &[
                reference_repo,
                reference_tag,
                reference_commit,
                reference_tree,
            ],
        ),
    })?;

    let (corpus_repo, corpus_tag, corpus_commit) = lock.corpus.as_ref().ok_or_else(|| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "missing_parsed_corpus",
            SUITE_LOCK_FILE,
            "strict SUITE.lock parser returned no Corpus row",
        )
    })?;
    let corpus_source = "SUITE.lock:corpus";
    insert(RawRow {
        key: "corpus".to_string(),
        kind: "corpus",
        source: corpus_source.to_string(),
        evidence_hash: evidence_hash(
            "corpus",
            corpus_source,
            &[corpus_repo, corpus_tag, corpus_commit],
        ),
    })?;

    Ok(rows)
}

fn canonical_inventory(
    suite_lock_text: &str,
    schema_text: &str,
    policy_text: &str,
) -> Result<CanonicalInventory, InventoryError> {
    validate_text_shape(
        SUITE_LOCK_FILE,
        suite_lock_text,
        ErrorClass::Violation,
        "suite_lock_invalid",
    )?;
    validate_text_shape(
        CONTRACT_INVENTORY_SCHEMA_FILE,
        schema_text,
        ErrorClass::Violation,
        "schema_invalid",
    )?;
    if !schema_text.eq(SCHEMA_DEFINITION) {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "schema_contract_mismatch",
            CONTRACT_INVENTORY_SCHEMA_FILE,
            "governed schema bytes do not match the independently implemented v1 contract",
        ));
    }
    let lock = parse_suite_lock(suite_lock_text).map_err(|detail| {
        InventoryError::new(
            ErrorClass::Violation,
            "suite_lock_invalid",
            SUITE_LOCK_FILE,
            detail,
        )
    })?;
    let raw = raw_rows(&lock)?;
    let policy = parse_policy(policy_text)?;
    if raw.len() > MAX_ROWS {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            SUITE_LOCK_FILE,
            format!("raw inventory exceeds the bounded row limit {MAX_ROWS}"),
        ));
    }

    let raw_keys: BTreeSet<_> = raw.keys().cloned().collect();
    let policy_keys: BTreeSet<_> = policy.keys().cloned().collect();
    if raw_keys.ne(&policy_keys) {
        let missing: Vec<_> = raw_keys.difference(&policy_keys).cloned().collect();
        let stale: Vec<_> = policy_keys.difference(&raw_keys).cloned().collect();
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "policy_join_not_bijective",
            CONTRACT_INVENTORY_POLICY_FILE,
            format!("missing raw-row policies={missing:?}; stale policy rows={stale:?}"),
        ));
    }

    let schema_root = hash_one(
        "fln.contract-inventory.schema-root/1",
        schema_text.as_bytes(),
    );
    let suite_lock_root = hash_one(
        "fln.contract-inventory.suite-lock-root/1",
        suite_lock_text.as_bytes(),
    );
    let policy_root = hash_one(
        "fln.contract-inventory.policy-root/1",
        policy_text.as_bytes(),
    );
    let mut raw_projection = String::new();
    for (key, row) in &raw {
        raw_projection.push_str(&format!(
            "row {key} kind={} source={} raw-evidence-hash={}\n",
            row.kind,
            row.source,
            labeled_hash(row.evidence_hash),
        ));
    }
    let raw_root = hash_one(
        "fln.contract-inventory.raw-root/1",
        raw_projection.as_bytes(),
    );
    let reference = raw.get("reference").ok_or_else(|| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "reference_raw_row_missing",
            SUITE_LOCK_FILE,
            "raw inventory lost the mandatory Reference row",
        )
    })?;
    let reference_evidence = labeled_hash(reference.evidence_hash);
    let reference_root = hash_fields(
        "fln.contract-inventory.reference-root/1",
        &[
            reference.key.as_bytes(),
            reference.kind.as_bytes(),
            reference.source.as_bytes(),
            reference_evidence.as_bytes(),
        ],
    );
    let target_row_count = raw
        .values()
        .filter(|row| matches!(row.kind, "target"))
        .count();
    let abi_row_count = policy
        .values()
        .filter(|row| !matches!(row.abi_class.as_str(), "none"))
        .count();
    let unresolved_row_count = 0;
    let source_bytes = suite_lock_text
        .len()
        .checked_add(schema_text.len())
        .and_then(|total| total.checked_add(policy_text.len()))
        .ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "resource_accounting_overflow",
                CONTRACT_INVENTORY_FILE,
                "source byte accounting overflowed usize",
            )
        })?;
    let mut output = String::new();
    output.push_str(&format!("schema {INVENTORY_SCHEMA}\n"));
    output.push_str(&format!("schema-root {}\n", labeled_hash(schema_root)));
    output.push_str(&format!(
        "suite-lock-root {}\n",
        labeled_hash(suite_lock_root)
    ));
    output.push_str(&format!("raw-root {}\n", labeled_hash(raw_root)));
    output.push_str(&format!("policy-root {}\n", labeled_hash(policy_root)));
    output.push_str(&format!(
        "reference-root {}\n",
        labeled_hash(reference_root)
    ));
    output.push_str(&format!(
        "extractor {EXTRACTOR_ID} version={EXTRACTOR_VERSION}\n"
    ));
    output.push_str(&format!("row-count {}\n", raw.len()));
    output.push_str(&format!("target-row-count {target_row_count}\n"));
    output.push_str(&format!("abi-row-count {abi_row_count}\n"));
    output.push_str(&format!("unresolved-row-count {unresolved_row_count}\n"));

    for (key, raw_row) in &raw {
        let policy_row = policy.get(key).ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "policy_join_lost_row",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("bijective join lost key `{key}`"),
            )
        })?;
        if !policy_row.kind.eq(raw_row.kind) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "policy_kind_mismatch",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!(
                    "row `{key}` classifies kind `{}` but raw source derives `{}`",
                    policy_row.kind, raw_row.kind
                ),
            ));
        }
        let evidence = labeled_hash(raw_row.evidence_hash);
        let suite_lock_root_label = labeled_hash(suite_lock_root);
        let identity = hash_fields(
            "fln.contract-inventory.row-identity/1",
            &[
                suite_lock_root_label.as_bytes(),
                key.as_bytes(),
                raw_row.kind.as_bytes(),
                EXTRACTOR_ID.as_bytes(),
                EXTRACTOR_VERSION.as_bytes(),
                raw_row.source.as_bytes(),
                policy_row.target_class.as_bytes(),
                policy_row.abi_class.as_bytes(),
                evidence.as_bytes(),
                b"observed",
                policy_row.support.as_bytes(),
            ],
        );
        output.push_str(&format!(
            "row {key} kind={} extractor={EXTRACTOR_ID} extractor-version={EXTRACTOR_VERSION} source={} target-class={} abi-class={} raw-evidence-hash={evidence} identity={} authority=observed support={}\n",
            raw_row.kind,
            raw_row.source,
            policy_row.target_class,
            policy_row.abi_class,
            labeled_hash(identity),
            policy_row.support,
        ));
    }

    let inventory_root = hash_one("fln.contract-inventory.inventory-root/1", output.as_bytes());
    output.push_str(&format!(
        "inventory-root {}\n",
        labeled_hash(inventory_root)
    ));
    validate_text_shape(
        CONTRACT_INVENTORY_FILE,
        &output,
        ErrorClass::InternalFault,
        "canonical_renderer_invalid",
    )?;
    let canonical_bytes = output.len();
    Ok(CanonicalInventory {
        bytes: output.into_bytes(),
        snapshot: InventorySnapshot {
            inventory_root: labeled_hash(inventory_root),
            schema_root: labeled_hash(schema_root),
            suite_lock_root: labeled_hash(suite_lock_root),
            raw_root: labeled_hash(raw_root),
            policy_root: labeled_hash(policy_root),
            reference_root: labeled_hash(reference_root),
            row_count: raw.len(),
            target_row_count,
            abi_row_count,
            unresolved_row_count,
            source_bytes,
            canonical_bytes,
        },
    })
}

/// Pure canonical renderer for fixtures and independent callers. Exact pin values are
/// accepted only as `suite_lock_text` and are never emitted in the returned inventory.
pub fn canonical_inventory_text(
    suite_lock_text: &str,
    schema_text: &str,
    policy_text: &str,
) -> Result<String, InventoryError> {
    let inventory = canonical_inventory(suite_lock_text, schema_text, policy_text)?;
    String::from_utf8(inventory.bytes).map_err(|error| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "canonical_renderer_non_utf8",
            CONTRACT_INVENTORY_FILE,
            error.to_string(),
        )
    })
}

fn checked_root(root: &Path) -> Result<PathBuf, InventoryError> {
    let canonical = fs::canonicalize(root).map_err(|error| {
        InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            root.display().to_string(),
            format!("cannot resolve authoritative root: {error}"),
        )
    })?;
    if !canonical.is_dir() {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            canonical.display().to_string(),
            "authoritative root is not a directory",
        ));
    }
    Ok(canonical)
}

fn validate_parent_chain(root: &Path, relative: &str) -> Result<(), InventoryError> {
    let relative_path = Path::new(relative);
    if relative_path.is_absolute()
        || relative_path
            .components()
            .any(|component| !matches!(component, Component::Normal(_) | Component::CurDir))
    {
        return Err(InventoryError::new(
            ErrorClass::InternalFault,
            "invalid_governed_path",
            relative,
            "compiled governed path is not a safe workspace-relative path",
        ));
    }
    let mut current = root.to_path_buf();
    if let Some(parent) = relative_path.parent() {
        for component in parent.components() {
            let Component::Normal(name) = component else {
                continue;
            };
            current.push(name);
            let metadata = fs::symlink_metadata(&current).map_err(|error| {
                InventoryError::new(
                    ErrorClass::Inconclusive,
                    "source_unavailable",
                    relative,
                    format!(
                        "cannot inspect governed parent `{}`: {error}",
                        current.display()
                    ),
                )
            })?;
            if metadata.file_type().is_symlink() || !metadata.is_dir() {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "source_ambiguous",
                    relative,
                    format!(
                        "governed parent `{}` must be a real directory, never a link",
                        current.display()
                    ),
                ));
            }
        }
    }
    Ok(())
}

fn read_bounded(
    root: &Path,
    relative: &str,
    missing_class: ErrorClass,
    missing_reason: &'static str,
) -> Result<Vec<u8>, InventoryError> {
    validate_parent_chain(root, relative)?;
    let path = root.join(relative);
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        let (class, reason) = if matches!(error.kind(), std::io::ErrorKind::NotFound) {
            (missing_class, missing_reason)
        } else {
            (ErrorClass::Inconclusive, "source_unavailable")
        };
        InventoryError::new(
            class,
            reason,
            relative,
            format!("cannot inspect bounded input: {error}"),
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_ambiguous",
            relative,
            "governed inventory inputs and artifacts must be regular files, never links",
        ));
    }
    if metadata.len() > MAX_SOURCE_BYTES as u64 {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            format!(
                "input is {} bytes; the bounded limit is {MAX_SOURCE_BYTES}",
                metadata.len()
            ),
        ));
    }
    let file = File::open(&path).map_err(|error| {
        InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            relative,
            format!("cannot open bounded input: {error}"),
        )
    })?;
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.take((MAX_SOURCE_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| {
            InventoryError::new(
                ErrorClass::Inconclusive,
                "source_unavailable",
                relative,
                format!("cannot read bounded input: {error}"),
            )
        })?;
    if bytes.len() > MAX_SOURCE_BYTES {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            relative,
            format!("input grew beyond the bounded limit {MAX_SOURCE_BYTES} while reading"),
        ));
    }
    Ok(bytes)
}

fn utf8<'a>(
    path: &str,
    bytes: &'a [u8],
    class: ErrorClass,
    reason: &'static str,
) -> Result<&'a str, InventoryError> {
    std::str::from_utf8(bytes).map_err(|error| {
        InventoryError::new(class, reason, path, format!("input is not UTF-8: {error}"))
    })
}

fn read_sources(root: &Path) -> Result<SourceSet, InventoryError> {
    Ok(SourceSet {
        schema: read_bounded(
            root,
            CONTRACT_INVENTORY_SCHEMA_FILE,
            ErrorClass::Inconclusive,
            "source_unavailable",
        )?,
        suite_lock: read_bounded(
            root,
            SUITE_LOCK_FILE,
            ErrorClass::Inconclusive,
            "source_unavailable",
        )?,
        policy: read_bounded(
            root,
            CONTRACT_INVENTORY_POLICY_FILE,
            ErrorClass::Inconclusive,
            "source_unavailable",
        )?,
    })
}

fn canonical_from_sources(sources: &SourceSet) -> Result<CanonicalInventory, InventoryError> {
    canonical_inventory(
        utf8(
            SUITE_LOCK_FILE,
            &sources.suite_lock,
            ErrorClass::Violation,
            "suite_lock_invalid",
        )?,
        utf8(
            CONTRACT_INVENTORY_SCHEMA_FILE,
            &sources.schema,
            ErrorClass::Violation,
            "schema_invalid",
        )?,
        utf8(
            CONTRACT_INVENTORY_POLICY_FILE,
            &sources.policy,
            ErrorClass::Violation,
            "policy_invalid",
        )?,
    )
}

fn candidate_exists(root: &Path) -> Result<bool, InventoryError> {
    validate_parent_chain(root, CONTRACT_INVENTORY_CANDIDATE_FILE)?;
    match fs::symlink_metadata(root.join(CONTRACT_INVENTORY_CANDIDATE_FILE)) {
        Ok(_) => Ok(true),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(false),
        Err(error) => Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            format!("cannot inspect publication candidate: {error}"),
        )),
    }
}

fn ensure_no_candidate(root: &Path) -> Result<(), InventoryError> {
    if candidate_exists(root)? {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "stale_candidate",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            "interrupted publication candidate exists; refuse the published inventory until explicit validated recovery",
        ));
    }
    Ok(())
}

fn parse_labeled_hash(value: &str) -> Option<u64> {
    let hex = value.strip_prefix("fnv1a64:")?;
    (hex.len() == 16)
        .then(|| u64::from_str_radix(hex, 16).ok())
        .flatten()
}

fn validate_artifact(
    path: &str,
    bytes: &[u8],
    expected: &CanonicalInventory,
    class: ErrorClass,
    reason: &'static str,
) -> Result<(), InventoryError> {
    let text = utf8(path, bytes, class, reason)?;
    validate_text_shape(path, text, class, reason)?;
    let (prefix, root_line) = text.rsplit_once("inventory-root ").ok_or_else(|| {
        InventoryError::new(
            class,
            reason,
            path,
            "inventory has no terminal inventory-root row",
        )
    })?;
    if root_line.contains('\n') && !root_line.ends_with('\n') || root_line.lines().count().ne(&1) {
        return Err(InventoryError::new(
            class,
            reason,
            path,
            "inventory-root must be the single terminal row",
        ));
    }
    let claimed = parse_labeled_hash(root_line.trim_end()).ok_or_else(|| {
        InventoryError::new(
            class,
            reason,
            path,
            "inventory-root must be canonical `fnv1a64:<16-lower-hex>`",
        )
    })?;
    let computed = hash_one("fln.contract-inventory.inventory-root/1", prefix.as_bytes());
    if claimed.ne(&computed) {
        return Err(InventoryError::new(
            class,
            reason,
            path,
            format!(
                "inventory root mismatch: claimed={} computed={}",
                labeled_hash(claimed),
                labeled_hash(computed)
            ),
        ));
    }
    if bytes.ne(&expected.bytes) {
        return Err(InventoryError::new(
            class,
            reason,
            path,
            "inventory is not the exact canonical generation for current SUITE.lock, schema, and reviewed policy",
        ));
    }
    Ok(())
}

fn validate_published_target(root: &Path) -> Result<(), InventoryError> {
    validate_parent_chain(root, CONTRACT_INVENTORY_FILE)?;
    match fs::symlink_metadata(root.join(CONTRACT_INVENTORY_FILE)) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
            Err(InventoryError::new(
                ErrorClass::Inconclusive,
                "publication_target_ambiguous",
                CONTRACT_INVENTORY_FILE,
                "published target exists but is not one regular file",
            ))
        }
        Ok(_) => Ok(()),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(()),
        Err(error) => Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            CONTRACT_INVENTORY_FILE,
            format!("cannot inspect publication target: {error}"),
        )),
    }
}

fn sync_parent(root: &Path) -> Result<(), InventoryError> {
    let parent = root
        .join(CONTRACT_INVENTORY_FILE)
        .parent()
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "publication_parent_missing",
                CONTRACT_INVENTORY_FILE,
                "published path has no parent directory",
            )
        })?;
    File::open(&parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "publication_directory_sync_failed",
                CONTRACT_INVENTORY_FILE,
                format!("atomic rename completed but parent directory sync failed: {error}"),
            )
        })
}

fn sync_candidate_parent(root: &Path) -> Result<(), InventoryError> {
    let parent = root
        .join(CONTRACT_INVENTORY_CANDIDATE_FILE)
        .parent()
        .map(Path::to_path_buf)
        .ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "candidate_parent_missing",
                CONTRACT_INVENTORY_CANDIDATE_FILE,
                "candidate path has no parent directory",
            )
        })?;
    File::open(&parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "candidate_directory_sync_failed",
                CONTRACT_INVENTORY_CANDIDATE_FILE,
                format!(
                    "candidate file is synced but its parent directory could not be synced: {error}"
                ),
            )
        })
}

/// Consume only a complete current generation. Candidate presence is checked first so
/// a valid old publication can never mask an interrupted newer attempt.
pub fn consume(root: &Path) -> Result<InventorySnapshot, InventoryError> {
    let root = checked_root(root)?;
    ensure_no_candidate(&root)?;
    let sources = read_sources(&root)?;
    let expected = canonical_from_sources(&sources)?;
    let published = read_bounded(
        &root,
        CONTRACT_INVENTORY_FILE,
        ErrorClass::Violation,
        "published_inventory_missing",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_FILE,
        &published,
        &expected,
        ErrorClass::Violation,
        "published_inventory_invalid",
    )?;
    let sources_after = read_sources(&root)?;
    if sources.ne(&sources_after) {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_INVENTORY_FILE,
            "governed sources changed while consuming the publication; no single source generation was established",
        ));
    }
    ensure_no_candidate(&root)?;
    Ok(expected.snapshot)
}

fn publish_with_hook(
    root: &Path,
    before_rename: impl FnOnce() -> Result<(), InventoryError>,
) -> Result<PublicationReceipt, InventoryError> {
    let root = checked_root(root)?;
    ensure_no_candidate(&root)?;
    validate_published_target(&root)?;
    let sources_before = read_sources(&root)?;
    let expected = canonical_from_sources(&sources_before)?;
    let candidate_path = root.join(CONTRACT_INVENTORY_CANDIDATE_FILE);
    let mut candidate = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&candidate_path)
        .map_err(|error| {
            let (class, reason) = if matches!(error.kind(), std::io::ErrorKind::AlreadyExists) {
                (ErrorClass::Inconclusive, "stale_candidate")
            } else {
                (ErrorClass::InternalFault, "candidate_create_failed")
            };
            InventoryError::new(
                class,
                reason,
                CONTRACT_INVENTORY_CANDIDATE_FILE,
                format!("cannot create publication candidate without overwrite: {error}"),
            )
        })?;
    candidate.write_all(&expected.bytes).map_err(|error| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "candidate_write_failed",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            format!(
                "candidate write did not complete; previous publication is untouched and the candidate remains for diagnosis: {error}"
            ),
        )
    })?;
    candidate.sync_all().map_err(|error| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "candidate_sync_failed",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            format!(
                "candidate sync failed; previous publication is untouched and the candidate remains for diagnosis: {error}"
            ),
        )
    })?;
    drop(candidate);
    sync_candidate_parent(&root)?;

    let candidate_bytes = read_bounded(
        &root,
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        &candidate_bytes,
        &expected,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;

    // Test and embedding callers may observe this exact durability boundary. Process
    // death here is the planted failure used to falsify the atomicity claim.
    before_rename()?;

    let sources_after = read_sources(&root)?;
    if sources_before.ne(&sources_after) {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            "governed sources changed between candidate derivation and commit; previous publication is untouched and candidate recovery requires validation against one stable source generation",
        ));
    }
    let candidate_bytes = read_bounded(
        &root,
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        &candidate_bytes,
        &expected,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;
    fs::rename(
        root.join(CONTRACT_INVENTORY_CANDIDATE_FILE),
        root.join(CONTRACT_INVENTORY_FILE),
    )
    .map_err(|error| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "atomic_rename_failed",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            format!(
                "atomic candidate promotion failed; previous publication is untouched: {error}"
            ),
        )
    })?;
    sync_parent(&root)?;
    let published = read_bounded(
        &root,
        CONTRACT_INVENTORY_FILE,
        ErrorClass::InternalFault,
        "published_inventory_missing_after_rename",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_FILE,
        &published,
        &expected,
        ErrorClass::InternalFault,
        "published_inventory_invalid_after_rename",
    )?;
    ensure_no_candidate(&root)?;
    Ok(PublicationReceipt {
        action: PublicationAction::Published,
        snapshot: expected.snapshot,
    })
}

/// Publish one canonical generation through a synced sibling and atomic rename.
pub fn publish(root: &Path) -> Result<PublicationReceipt, InventoryError> {
    publish_with_hook(root, || Ok(()))
}

/// Explicitly validate and promote a candidate left by cancellation or process death.
/// An invalid/stale candidate is retained and the previous publication is untouched.
pub fn recover(root: &Path) -> Result<PublicationReceipt, InventoryError> {
    let root = checked_root(root)?;
    if !candidate_exists(&root)? {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "candidate_missing",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            "explicit recovery requested but no candidate exists",
        ));
    }
    validate_published_target(&root)?;
    let sources_before = read_sources(&root)?;
    let expected = canonical_from_sources(&sources_before)?;
    let candidate = read_bounded(
        &root,
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        &candidate,
        &expected,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;
    let sources_after = read_sources(&root)?;
    if sources_before.ne(&sources_after) {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_drift",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            "governed sources changed while validating recovery; previous publication remains untouched",
        ));
    }
    let candidate = read_bounded(
        &root,
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        ErrorClass::Inconclusive,
        "candidate_missing",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_CANDIDATE_FILE,
        &candidate,
        &expected,
        ErrorClass::Inconclusive,
        "candidate_invalid",
    )?;
    fs::rename(
        root.join(CONTRACT_INVENTORY_CANDIDATE_FILE),
        root.join(CONTRACT_INVENTORY_FILE),
    )
    .map_err(|error| {
        InventoryError::new(
            ErrorClass::InternalFault,
            "atomic_recovery_rename_failed",
            CONTRACT_INVENTORY_CANDIDATE_FILE,
            format!("validated candidate recovery rename failed: {error}"),
        )
    })?;
    sync_parent(&root)?;
    let published = read_bounded(
        &root,
        CONTRACT_INVENTORY_FILE,
        ErrorClass::InternalFault,
        "published_inventory_missing_after_recovery",
    )?;
    validate_artifact(
        CONTRACT_INVENTORY_FILE,
        &published,
        &expected,
        ErrorClass::InternalFault,
        "published_inventory_invalid_after_recovery",
    )?;
    ensure_no_candidate(&root)?;
    Ok(PublicationReceipt {
        action: PublicationAction::Recovered,
        snapshot: expected.snapshot,
    })
}

/// Structure-gate adapter. Contract violations are authoritative failures; missing
/// authority and interrupted publication are FL-INV-07 inconclusive findings.
pub fn audit(root: &Path) -> Vec<Finding> {
    match consume(root) {
        Ok(_) => Vec::new(),
        // The dependency-closure audit owns SUITE.lock presence and grammar. Avoid
        // reporting the same malformed authority twice; every inventory-specific
        // failure (including resource exhaustion) remains independently typed.
        Err(error)
            if matches!(error.path.as_str(), SUITE_LOCK_FILE)
                && matches!(error.reason, "source_unavailable" | "suite_lock_invalid") =>
        {
            Vec::new()
        }
        Err(error) => {
            let code = match error.class {
                ErrorClass::Violation => "FLN-STRUCT-032",
                ErrorClass::Inconclusive | ErrorClass::InternalFault => "FLN-STRUCT-033",
            };
            vec![Finding {
                code,
                path: error.path,
                detail: format!(
                    "contract-inventory {} reason={}: {}",
                    error.class.as_str(),
                    error.reason,
                    error.detail
                ),
            }]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::thread;
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    const TEST_SUITE_LOCK: &str = "\
schema fln-suite-lock/1
rust-nightly nightly-2026-07-13
rust-release 1.99.0-nightly
rust-commit 77cf889bc178ddb44d6a1c78e5a820b5abb31d8d
target x86_64-unknown-linux-gnu
suite asupersync commit=e464a484cb65c1a55be0d9c925e6e9c20318edcb path=/dp/asupersync
crate asupersync repo=asupersync
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b28d64dab099da31a4c09229a9e6a2ef35 tree=ba16913719a2f6a15a826918fbe6ba9dd5413e91
corpus leanprover-community/mathlib4 tag=v4.32.0 commit=81a5d257c8e410db227a6665ed08f64fea08e997
";

    const REQUIRED_POLICY: &str = "\
schema fln-contract-inventory-policy/1
row corpus kind=corpus support=required target-class=none abi-class=none
row reference kind=reference support=required target-class=none abi-class=none
row suite:asupersync kind=suite support=required target-class=none abi-class=none
row target:0001 kind=target support=required target-class=certified abi-class=none
row toolchain kind=toolchain support=required target-class=none abi-class=none
";

    const OPTIONAL_POLICY: &str = "\
schema fln-contract-inventory-policy/1
row corpus kind=corpus support=required target-class=none abi-class=none
row reference kind=reference support=required target-class=none abi-class=none
row suite:asupersync kind=suite support=optional target-class=none abi-class=none
row target:0001 kind=target support=required target-class=certified abi-class=none
row toolchain kind=toolchain support=required target-class=none abi-class=none
";

    fn retained_root(tag: &str) -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock after epoch")
            .as_nanos();
        loop {
            let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "fln-contract-inventory-{}-{stamp}-{sequence}-{tag}",
                std::process::id()
            ));
            match fs::create_dir(&root) {
                Ok(()) => {
                    eprintln!("retained contract-inventory fixture: {}", root.display());
                    return root;
                }
                Err(error) if matches!(error.kind(), std::io::ErrorKind::AlreadyExists) => {
                    continue;
                }
                Err(error) => {
                    assert!(
                        matches!(error.kind(), std::io::ErrorKind::AlreadyExists),
                        "create retained fixture: {error}"
                    );
                    continue;
                }
            }
        }
    }

    fn write_new(path: &Path, bytes: &[u8]) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create fixture parent");
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("create fixture file without overwrite");
        file.write_all(bytes).expect("write fixture file");
        file.sync_all().expect("sync fixture file");
    }

    fn fixture_root(tag: &str, policy: &str) -> PathBuf {
        let root = retained_root(tag);
        write_new(&root.join(SUITE_LOCK_FILE), TEST_SUITE_LOCK.as_bytes());
        write_new(
            &root.join(CONTRACT_INVENTORY_SCHEMA_FILE),
            SCHEMA_DEFINITION.as_bytes(),
        );
        write_new(
            &root.join(CONTRACT_INVENTORY_POLICY_FILE),
            policy.as_bytes(),
        );
        root
    }

    #[test]
    fn canonical_generation_is_deterministic_bijective_and_not_a_second_pin_authority() {
        let first =
            canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, REQUIRED_POLICY).unwrap();
        let second =
            canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, REQUIRED_POLICY).unwrap();
        assert_eq!(first, second);
        for required_header in [
            "raw-root fnv1a64:",
            "reference-root fnv1a64:",
            "row-count 5\n",
            "target-row-count 1\n",
            "abi-row-count 0\n",
            "unresolved-row-count 0\n",
        ] {
            assert!(
                first.contains(required_header),
                "canonical inventory lost `{required_header}`"
            );
        }
        for forbidden_pin in [
            "nightly-2026-07-13",
            "x86_64-unknown-linux-gnu",
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35",
            "v4.32.0",
            "/dp/asupersync",
        ] {
            assert!(
                !first.contains(forbidden_pin),
                "derived inventory copied authoritative pin `{forbidden_pin}`"
            );
        }
        let changed_reference = TEST_SUITE_LOCK.replace(
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35",
            "9c9756b28d64dab099da31a4c09229a9e6a2ef35",
        );
        let changed =
            canonical_inventory_text(&changed_reference, SCHEMA_DEFINITION, REQUIRED_POLICY)
                .expect("another well-shaped Reference pin remains derivable");
        assert_ne!(
            first, changed,
            "Reference pin drift must change the opaque Reference and canonical roots"
        );
        assert!(
            !changed.contains("9c9756b28d64dab099da31a4c09229a9e6a2ef35"),
            "Reference drift binding must remain opaque rather than becoming a second pin authority"
        );

        let missing = REQUIRED_POLICY.replace(
            "row target:0001 kind=target support=required target-class=certified abi-class=none\n",
            "",
        );
        let error = canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, &missing)
            .expect_err("missing policy row must fail the bijection");
        assert_eq!(error.reason, "policy_join_not_bijective");

        let stale = REQUIRED_POLICY.to_string()
            + "row zzzz:stale kind=suite support=required target-class=none abi-class=none\n";
        let error = canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, &stale)
            .expect_err("stale policy row must fail the bijection");
        assert_eq!(error.reason, "policy_join_not_bijective");

        let duplicate = REQUIRED_POLICY.replace(
            "row reference kind=reference support=required target-class=none abi-class=none\n",
            "row reference kind=reference support=required target-class=none abi-class=none\nrow reference kind=reference support=required target-class=none abi-class=none\n",
        );
        let error = canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, &duplicate)
            .expect_err("duplicate policy row must fail before the join");
        assert_eq!(error.reason, "policy_not_canonical");
    }

    #[test]
    fn consumer_kills_torn_and_root_preserving_artifact_mutants() {
        let root = fixture_root("artifact-mutants", REQUIRED_POLICY);
        publish(&root).expect("initial generation publishes");
        let published = root.join(CONTRACT_INVENTORY_FILE);
        let canonical = fs::read(&published).expect("read canonical publication");

        fs::write(&published, &canonical[..canonical.len() / 2]).expect("plant torn artifact");
        let error = consume(&root).expect_err("torn publication must be refused");
        assert_eq!(error.class, ErrorClass::Violation);
        assert_eq!(error.reason, "published_inventory_invalid");

        let canonical_text = std::str::from_utf8(&canonical).expect("canonical UTF-8");
        let (prefix, _) = canonical_text
            .rsplit_once("inventory-root ")
            .expect("terminal root row");
        let mutated_prefix = prefix.replacen("authority=observed", "authority=observeD", 1);
        let root_preserving = format!(
            "{mutated_prefix}inventory-root {}\n",
            labeled_hash(hash_one(
                "fln.contract-inventory.inventory-root/1",
                mutated_prefix.as_bytes()
            ))
        );
        fs::write(&published, root_preserving).expect("plant root-preserving body mutant");
        let error = consume(&root).expect_err("body mutation must be refused");
        assert_eq!(error.reason, "published_inventory_invalid");
    }

    #[test]
    fn resource_exhaustion_is_typed_inconclusive() {
        let oversized = "x".repeat(MAX_SOURCE_BYTES + 1);
        let error = canonical_inventory_text(&oversized, SCHEMA_DEFINITION, REQUIRED_POLICY)
            .expect_err("bounded input must refuse exhaustion");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "resource_exhausted");
    }

    #[test]
    fn publication_state_model_refuses_ambiguous_and_partial_generations() {
        let root = fixture_root("publication-state-model", REQUIRED_POLICY);
        let missing = consume(&root).expect_err("no published generation is not success");
        assert_eq!(missing.class, ErrorClass::Violation);
        assert_eq!(missing.reason, "published_inventory_missing");

        let canonical =
            canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, REQUIRED_POLICY).unwrap();
        write_new(
            &root.join(CONTRACT_INVENTORY_CANDIDATE_FILE),
            canonical.as_bytes(),
        );
        let ambiguous = consume(&root).expect_err("candidate-only state is ambiguous");
        assert_eq!(ambiguous.class, ErrorClass::Inconclusive);
        assert_eq!(ambiguous.reason, "stale_candidate");
        recover(&root).expect("valid candidate-only state recovers atomically");
        let stable = fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("stable publication");
        assert!(consume(&root).is_ok());

        write_new(
            &root.join(CONTRACT_INVENTORY_CANDIDATE_FILE),
            &canonical.as_bytes()[..canonical.len() / 2],
        );
        let ambiguous = consume(&root).expect_err("published plus candidate is ambiguous");
        assert_eq!(ambiguous.reason, "stale_candidate");
        let partial = recover(&root).expect_err("partial candidate cannot be promoted");
        assert_eq!(partial.class, ErrorClass::Inconclusive);
        assert_eq!(partial.reason, "candidate_invalid");
        assert_eq!(
            fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("old generation survives"),
            stable
        );
    }

    #[test]
    fn non_authoritative_source_outcomes_are_typed_and_preserve_publication() {
        let unavailable = retained_root("source-unavailable");
        write_new(
            &unavailable.join(SUITE_LOCK_FILE),
            TEST_SUITE_LOCK.as_bytes(),
        );
        write_new(
            &unavailable.join(CONTRACT_INVENTORY_POLICY_FILE),
            REQUIRED_POLICY.as_bytes(),
        );
        let error = consume(&unavailable).expect_err("missing schema is not a verdict");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "source_unavailable");

        let ambiguous_policy =
            REQUIRED_POLICY.replace("target-class=certified", "target-class=none");
        let error = canonical_inventory_text(TEST_SUITE_LOCK, SCHEMA_DEFINITION, &ambiguous_policy)
            .expect_err("ambiguous target classification is not authoritative");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "target_class_ambiguous");

        let drift = fixture_root("source-drift", REQUIRED_POLICY);
        publish(&drift).expect("baseline publication");
        let stable =
            fs::read(drift.join(CONTRACT_INVENTORY_FILE)).expect("read stable publication");
        let error = publish_with_hook(&drift, || {
            fs::write(
                drift.join(CONTRACT_INVENTORY_POLICY_FILE),
                OPTIONAL_POLICY.as_bytes(),
            )
            .map_err(|write_error| {
                InventoryError::new(
                    ErrorClass::InternalFault,
                    "test_plant_failed",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    write_error.to_string(),
                )
            })
        })
        .expect_err("source drift prevents atomic promotion");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "source_drift");
        assert_eq!(
            fs::read(drift.join(CONTRACT_INVENTORY_FILE)).expect("old publication remains"),
            stable
        );
        assert!(drift.join(CONTRACT_INVENTORY_CANDIDATE_FILE).exists());
    }

    const CHILD_ROOT_ENV: &str = "FLN_CONTRACT_INVENTORY_TEST_CHILD_ROOT";
    const CHILD_MARKER_ENV: &str = "FLN_CONTRACT_INVENTORY_TEST_CHILD_MARKER";

    #[test]
    fn interrupted_publication_helper() {
        let Ok(root) = std::env::var(CHILD_ROOT_ENV) else {
            return;
        };
        let marker = PathBuf::from(
            std::env::var(CHILD_MARKER_ENV).expect("child marker accompanies child root"),
        );
        publish_with_hook(Path::new(&root), || {
            write_new(&marker, b"candidate-synced-before-rename\n");
            loop {
                thread::park();
            }
        })
        .expect("parent kills helper at the hook");
    }

    #[test]
    fn killed_publisher_is_refused_and_valid_candidate_recovers_atomically() {
        let root = fixture_root("killed-publisher", REQUIRED_POLICY);
        publish(&root).expect("baseline generation publishes");
        let published_path = root.join(CONTRACT_INVENTORY_FILE);
        let old_publication = fs::read(&published_path).expect("read baseline");
        fs::write(
            root.join(CONTRACT_INVENTORY_POLICY_FILE),
            OPTIONAL_POLICY.as_bytes(),
        )
        .expect("reviewed policy changes for next generation");
        let marker = root.join("publisher-ready-before-rename");

        let mut child = Command::new(std::env::current_exe().expect("current test executable"))
            .args([
                "--exact",
                "contract_inventory::tests::interrupted_publication_helper",
                "--nocapture",
            ])
            .env(CHILD_ROOT_ENV, &root)
            .env(CHILD_MARKER_ENV, &marker)
            .spawn()
            .expect("spawn publication helper");

        let mut reached_boundary = false;
        for _ in 0..1_000 {
            if marker.is_file() {
                reached_boundary = true;
                break;
            }
            if let Some(status) = child.try_wait().expect("poll helper") {
                assert!(
                    !status.success() && marker.is_file(),
                    "publisher exited before kill boundary: {status}"
                );
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert!(
            reached_boundary,
            "publisher did not reach durable candidate boundary"
        );
        child
            .kill()
            .expect("kill publisher between write and rename");
        let status = child.wait().expect("reap killed publisher");
        assert!(
            !status.success(),
            "planted kill must terminate the publisher"
        );

        assert_eq!(
            fs::read(&published_path).expect("old publication remains readable"),
            old_publication,
            "interrupted publication changed the previously published generation"
        );
        let candidate_path = root.join(CONTRACT_INVENTORY_CANDIDATE_FILE);
        let candidate = fs::read(&candidate_path).expect("synced candidate remains");
        assert_ne!(
            candidate, old_publication,
            "second generation must differ so the atomicity assertion is meaningful"
        );
        let error = consume(&root).expect_err("consumer must refuse interrupted publication");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "stale_candidate");

        let receipt = recover(&root).expect("valid candidate recovers by atomic promotion");
        assert_eq!(receipt.action, PublicationAction::Recovered);
        assert!(
            !candidate_path.exists(),
            "atomic promotion moves the candidate; it does not copy then delete"
        );
        assert_eq!(
            fs::read(&published_path).expect("read recovered publication"),
            candidate
        );
        assert_eq!(consume(&root).unwrap(), receipt.snapshot);
    }
}
