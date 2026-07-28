//! Canonical pin/target inventory and failure-atomic publication (bead `fln-k5rr`).
//!
//! `SUITE.lock` remains the only authority for exact toolchain, target, suite,
//! Reference, and Corpus values. Target-indexed ABI observations come from the
//! mechanically extracted `contracts/ABI_TARGET_LAYOUT.txt`; it carries opaque target
//! keys that join by position to `SUITE.lock`, never copied target or pin values. The
//! published inventory contains opaque evidence roots and source locators. A reviewed
//! policy classifies the derived raw rows, and the join must be bijective.
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
    ABI_TARGET_LAYOUT_CANDIDATE_FILE, ABI_TARGET_LAYOUT_FILE,
    BUILTIN_ENVIRONMENT_001_CANDIDATE_FILE, BUILTIN_ENVIRONMENT_002_CANDIDATE_FILE,
    BUILTIN_ENVIRONMENT_CANDIDATE_FILE, BUILTIN_PARTITION_CANDIDATE_FILE,
    CONTRACT_INVENTORY_CANDIDATE_FILE, CONTRACT_INVENTORY_FILE, CONTRACT_INVENTORY_POLICY_FILE,
    CONTRACT_INVENTORY_SCHEMA_FILE, EXTERN_BUILTIN_ENVIRONMENT_CANDIDATE_FILE,
    EXTERN_BUILTIN_ENVIRONMENT_FILE, EXTERN_CENSUS_CANDIDATE_FILE,
    OLEAN_ILEAN_FORMAT_CANDIDATE_FILE, OLEAN_ILEAN_FORMAT_FILE, SUITE_LOCK_FILE,
};

pub const DEFINITION_SCHEMA: &str = "fln-contract-inventory-definition/1";
pub const INVENTORY_SCHEMA: &str = "fln-contract-inventory/1";
pub const POLICY_SCHEMA: &str = "fln-contract-inventory-policy/1";
pub const EXTRACTOR_ID: &str = "suite-lock";
pub const EXTRACTOR_VERSION: &str = "1";
pub const ABI_EXTRACTOR_ID: &str = "lean-h-clang-layout";
pub const ABI_EXTRACTOR_VERSION: &str = "1";
pub const ABI_TARGET_LAYOUT_SCHEMA: &str = "fln-abi-target-layout/1";
pub const FORMAT_EXTRACTOR_ID: &str = "lean-format-source-and-pin-artifacts";
pub const FORMAT_EXTRACTOR_VERSION: &str = "1";
pub const OLEAN_ILEAN_FORMAT_SCHEMA: &str = "fln-olean-ilean-format/1";
pub const CENSUS_EXTRACTOR_ID: &str = "lean-reference-environment-walk";
pub const CENSUS_EXTRACTOR_VERSION: &str = "2";
pub const EXTERN_BUILTIN_ENVIRONMENT_SCHEMA: &str = "fln-extern-builtin-environment/1";
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
source-authority SUITE.lock,contracts/ABI_TARGET_LAYOUT.txt,contracts/OLEAN_ILEAN_FORMAT.txt,contracts/EXTERN_BUILTIN_ENVIRONMENT.txt
extractor suite-lock version=1
extractor lean-h-clang-layout version=1
extractor lean-format-source-and-pin-artifacts version=1
extractor lean-reference-environment-walk version=2
hash fnv1a64-noncryptographic domain=required fields=u64le-length-prefixed
row-fields key,kind,extractor,extractor-version,source,target-class,abi-class,raw-evidence-hash,identity,authority,support
root-fields schema,suite-lock,abi-target-layout,olean-ilean-format,raw,policy,reference,canonical
row-order canonical-key-byte-order
pin-values forbidden-outside-source-authority
policy-join exact-bijection
authority-states observed
publication candidate=contracts/PIN_TARGET_INVENTORY.txt.candidate commit=atomic-rename recovery=explicit-promotion
source-publication contracts/ABI_TARGET_LAYOUT.txt candidate=contracts/ABI_TARGET_LAYOUT.txt.candidate commit=atomic-rename
source-publication contracts/OLEAN_ILEAN_FORMAT.txt candidate=contracts/OLEAN_ILEAN_FORMAT.txt.candidate commit=atomic-rename
source-publication contracts/EXTERN_BUILTIN_ENVIRONMENT.txt candidate=contracts/EXTERN_BUILTIN_ENVIRONMENT.txt.candidate commit=atomic-rename group=extern-builtin-census
source-publication contracts/extern_census.tsv candidate=contracts/extern_census.tsv.candidate commit=atomic-rename group=extern-builtin-census
source-publication contracts/builtin_environment.tsv candidate=contracts/builtin_environment.tsv.candidate commit=atomic-rename group=extern-builtin-census
source-publication contracts/builtin_environment.001.tsv candidate=contracts/builtin_environment.001.tsv.candidate commit=atomic-rename group=extern-builtin-census
source-publication contracts/builtin_environment.002.tsv candidate=contracts/builtin_environment.002.tsv.candidate commit=atomic-rename group=extern-builtin-census
source-publication contracts/builtin_partition.tsv candidate=contracts/builtin_partition.tsv.candidate commit=atomic-rename group=extern-builtin-census
source-group-hash builtin-environment algorithm=sha256 framing=ordered-concatenation paths=contracts/builtin_environment.tsv,contracts/builtin_environment.001.tsv,contracts/builtin_environment.002.tsv
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
    pub abi_target_layout_root: String,
    pub olean_ilean_format_root: String,
    pub raw_root: String,
    pub policy_root: String,
    pub reference_root: String,
    pub row_count: usize,
    pub target_row_count: usize,
    pub abi_row_count: usize,
    pub format_row_count: usize,
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
    extractor: &'static str,
    extractor_version: &'static str,
    source: String,
    observed_abi_class: Option<String>,
    evidence_hash: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AbiLayoutRow {
    key: String,
    abi_class: String,
    target_root: u64,
    source_sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FormatSummaryRow {
    key: String,
    abi_class: Option<String>,
    section_root: u64,
    inventory_root: u64,
    source_root: u64,
    row_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CensusManifest {
    extern_sha256: String,
    builtin_sha256: String,
    partition_sha256: String,
    policy_sha256: String,
    constant_count: usize,
    extern_count: usize,
    module_count: usize,
    attribute_count: usize,
    toolchain_api_count: usize,
    library_code_count: usize,
    user_facing_data_count: usize,
    manifest_root: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SourceSet {
    schema: Vec<u8>,
    suite_lock: Vec<u8>,
    policy: Vec<u8>,
    abi_target_layout: Vec<u8>,
    olean_ilean_format: Vec<u8>,
    extern_builtin_environment: Vec<u8>,
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
            "abi-layout"
                | "artifact-format"
                | "environment-census"
                | "toolchain"
                | "target"
                | "suite"
                | "reference"
                | "corpus"
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
        if !matches!(target_class, "none" | "certified")
            || !matches!(
                abi_class,
                "none" | "lp64-le" | "lp64-be" | "llp64-le" | "llp64-be" | "ilp32-le" | "ilp32-be"
            )
        {
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
            if !matches!(abi_class, "none") {
                return Err(InventoryError::new(
                    ErrorClass::Violation,
                    "policy_invalid",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    format!("line {line_number} target rows cannot duplicate ABI class"),
                ));
            }
        } else if matches!(kind, "abi-layout") {
            if !matches!(support, "required")
                || !matches!(target_class, "certified")
                || matches!(abi_class, "none")
            {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "abi_class_ambiguous",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    format!(
                        "line {line_number} ABI layout rows must be required, certified, and carry one observed ABI class"
                    ),
                ));
            }
        } else if matches!(kind, "artifact-format") {
            let is_ilean = key == "artifact-format:ilean";
            let is_olean_target = key.starts_with("artifact-format:olean:target:");
            let classification_valid = if is_ilean {
                matches!(target_class, "none") && matches!(abi_class, "none")
            } else if is_olean_target {
                matches!(target_class, "certified") && !matches!(abi_class, "none")
            } else {
                false
            };
            if !matches!(support, "required") || !classification_valid {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "format_class_ambiguous",
                    CONTRACT_INVENTORY_POLICY_FILE,
                    format!(
                        "line {line_number} artifact-format rows must be required; ILEAN is target-independent and OLEAN rows are certified with one observed ABI class"
                    ),
                ));
            }
        } else if !matches!(target_class, "none") || !matches!(abi_class, "none") {
            return Err(InventoryError::new(
                ErrorClass::Inconclusive,
                "target_class_ambiguous",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!("line {line_number} non-target/non-ABI row claims a target or ABI class"),
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

fn abi_layout_error(line: usize, detail: impl Into<String>) -> InventoryError {
    InventoryError::new(
        ErrorClass::Violation,
        "abi_target_layout_invalid",
        ABI_TARGET_LAYOUT_FILE,
        format!("line {line}: {}", detail.into()),
    )
}

fn abi_field<'a>(token: &'a str, prefix: &str, line: usize) -> Result<&'a str, InventoryError> {
    token
        .strip_prefix(prefix)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            abi_layout_error(
                line,
                format!("expected `{prefix}<value>` in canonical field order"),
            )
        })
}

fn abi_u64(token: &str, prefix: &str, line: usize) -> Result<u64, InventoryError> {
    abi_field(token, prefix, line)?
        .parse()
        .map_err(|_| abi_layout_error(line, format!("`{token}` is not a canonical u64 field")))
}

fn abi_i128(token: &str, prefix: &str, line: usize) -> Result<i128, InventoryError> {
    abi_field(token, prefix, line)?
        .parse()
        .map_err(|_| abi_layout_error(line, format!("`{token}` is not a canonical integer field")))
}

fn abi_name(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

fn lower_hex(value: &str, digits: usize) -> bool {
    value.len().eq(&digits)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn parse_abi_target_layout(
    text: &str,
    expected_target_count: usize,
) -> Result<BTreeMap<String, AbiLayoutRow>, InventoryError> {
    validate_text_shape(
        ABI_TARGET_LAYOUT_FILE,
        text,
        ErrorClass::Violation,
        "abi_target_layout_invalid",
    )?;
    let lines: Vec<_> = text.lines().collect();
    if lines.len() < 6 {
        return Err(abi_layout_error(1, "target-layout table is truncated"));
    }
    if !matches!(lines[0], "schema fln-abi-target-layout/1") {
        return Err(abi_layout_error(
            1,
            format!("expected `schema {ABI_TARGET_LAYOUT_SCHEMA}`"),
        ));
    }
    if !matches!(lines[1], "extractor lean-h-clang-layout version=1") {
        return Err(abi_layout_error(
            2,
            format!("expected `extractor {ABI_EXTRACTOR_ID} version={ABI_EXTRACTOR_VERSION}`"),
        ));
    }
    let source_tokens: Vec<_> = lines[2].split_whitespace().collect();
    let [source, path, authority, sha_token] = source_tokens.as_slice() else {
        return Err(abi_layout_error(
            3,
            "source row must be `source path=include/lean/lean.h authority=SUITE.lock:reference sha256=<64-lower-hex>`",
        ));
    };
    if !matches!(*source, "source")
        || !matches!(*path, "path=include/lean/lean.h")
        || !matches!(*authority, "authority=SUITE.lock:reference")
    {
        return Err(abi_layout_error(
            3,
            "source locator must point opaquely to the Reference row in SUITE.lock",
        ));
    }
    let source_sha256 = abi_field(sha_token, "sha256=", 3)?;
    if !lower_hex(source_sha256, 64) {
        return Err(abi_layout_error(
            3,
            "source SHA-256 must be exactly 64 lowercase hexadecimal digits",
        ));
    }
    let count_tokens: Vec<_> = lines[3].split_whitespace().collect();
    let [count_directive, count_value] = count_tokens.as_slice() else {
        return Err(abi_layout_error(
            4,
            "target count must be `target-count <decimal>`",
        ));
    };
    let target_count = count_value
        .parse::<usize>()
        .map_err(|_| abi_layout_error(4, "target count is not a canonical usize"))?;
    if !matches!(*count_directive, "target-count") || target_count != expected_target_count {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "abi_target_matrix_mismatch",
            ABI_TARGET_LAYOUT_FILE,
            format!(
                "target-count={target_count} but SUITE.lock has {expected_target_count} certified targets"
            ),
        ));
    }
    if target_count == 0 || target_count > MAX_ROWS {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "resource_exhausted",
            ABI_TARGET_LAYOUT_FILE,
            format!("target-count must be within 1..={MAX_ROWS}, got {target_count}"),
        ));
    }

    let mut rows = BTreeMap::new();
    let mut index = 4;
    for target_index in 1..=target_count {
        let line_number = index + 1;
        let target_tokens: Vec<_> = lines
            .get(index)
            .ok_or_else(|| abi_layout_error(line_number, "missing target row"))?
            .split_whitespace()
            .collect();
        let [
            directive,
            key_token,
            abi_token,
            model_token,
            endian_token,
            pointer_token,
            size_t_token,
            char_token,
            int_token,
            unsigned_token,
            long_token,
            long_long_token,
            max_align_token,
        ] = target_tokens.as_slice()
        else {
            return Err(abi_layout_error(
                line_number,
                "target row fields are missing, extra, or not canonically ordered",
            ));
        };
        let target_key = format!("target:{target_index:04}");
        if !matches!(*directive, "target") || key_token.ne(&target_key) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "abi_target_matrix_mismatch",
                ABI_TARGET_LAYOUT_FILE,
                format!(
                    "line {line_number}: expected opaque key `{target_key}`, got `{key_token}`"
                ),
            ));
        }
        let abi_class = abi_field(abi_token, "abi-class=", line_number)?;
        let data_model = abi_field(model_token, "data-model=", line_number)?;
        let endianness = abi_field(endian_token, "endianness=", line_number)?;
        let endian_class = match endianness {
            "little" => "le",
            "big" => "be",
            _ => {
                return Err(abi_layout_error(
                    line_number,
                    format!("unsupported endianness `{endianness}`"),
                ));
            }
        };
        if !matches!(data_model, "lp64" | "llp64" | "ilp32")
            || abi_class.ne(&format!("{data_model}-{endian_class}"))
        {
            return Err(abi_layout_error(
                line_number,
                format!(
                    "ABI class `{abi_class}` does not canonically encode data model `{data_model}` and endianness `{endianness}`"
                ),
            ));
        }
        let pointer_bits = abi_u64(pointer_token, "pointer-bits=", line_number)?;
        let size_t_bits = abi_u64(size_t_token, "size-t-bits=", line_number)?;
        let char_bits = abi_u64(char_token, "char-bits=", line_number)?;
        let int_bits = abi_u64(int_token, "int-bits=", line_number)?;
        let unsigned_bits = abi_u64(unsigned_token, "unsigned-bits=", line_number)?;
        let long_bits = abi_u64(long_token, "long-bits=", line_number)?;
        let long_long_bits = abi_u64(long_long_token, "long-long-bits=", line_number)?;
        let max_align_bytes = abi_u64(max_align_token, "max-align-bytes=", line_number)?;
        let expected_shape = match data_model {
            "lp64" => (64, 64, 32, 32, 64, 64),
            "llp64" => (64, 64, 32, 32, 32, 64),
            "ilp32" => (32, 32, 32, 32, 32, 64),
            _ => unreachable!("data model checked above"),
        };
        if (
            pointer_bits,
            size_t_bits,
            int_bits,
            unsigned_bits,
            long_bits,
            long_long_bits,
        ) != expected_shape
            || char_bits != 8
            || max_align_bytes == 0
            || !max_align_bytes.is_power_of_two()
        {
            return Err(abi_layout_error(
                line_number,
                "primitive widths or maximum alignment contradict the declared ABI class",
            ));
        }

        let block_start = index;
        index += 1;
        let mut phase = 0_u8;
        let mut define_names = BTreeSet::new();
        let mut tag_names = BTreeSet::new();
        let mut struct_names = BTreeSet::new();
        let mut field_names = BTreeSet::new();
        let mut current_struct: Option<(String, u64, usize)> = None;
        let mut detail_rows = 0_usize;
        loop {
            let detail_line_number = index + 1;
            let line = lines
                .get(index)
                .ok_or_else(|| abi_layout_error(detail_line_number, "missing target-root row"))?;
            if line.starts_with("target-root ") {
                if let Some((name, _, fields)) = &current_struct
                    && fields.eq(&0)
                {
                    return Err(abi_layout_error(
                        detail_line_number,
                        format!("struct `{name}` has no field observations"),
                    ));
                }
                break;
            }
            if detail_rows >= MAX_ROWS {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "resource_exhausted",
                    ABI_TARGET_LAYOUT_FILE,
                    format!("target `{target_key}` exceeds {MAX_ROWS} bounded detail rows"),
                ));
            }
            detail_rows += 1;
            let tokens: Vec<_> = line.split_whitespace().collect();
            let Some(kind) = tokens.first().copied() else {
                return Err(abi_layout_error(detail_line_number, "blank detail row"));
            };
            match kind {
                "define" | "tag" => {
                    let [_, detail_key, name_token, value_token, source_line_token] =
                        tokens.as_slice()
                    else {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("`{kind}` row fields are not canonical"),
                        ));
                    };
                    if detail_key.ne(&target_key) {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("`{kind}` row does not belong to `{target_key}`"),
                        ));
                    }
                    let name = abi_field(name_token, "name=", detail_line_number)?;
                    if !abi_name(name) {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("`{name}` is not a canonical C identifier"),
                        ));
                    }
                    let _value = abi_i128(value_token, "value=", detail_line_number)?;
                    let source_line =
                        abi_u64(source_line_token, "source-line=", detail_line_number)?;
                    if source_line == 0 {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "source-line must be positive",
                        ));
                    }
                    if matches!(kind, "define") {
                        if phase != 0 || !define_names.insert(name.to_string()) {
                            return Err(abi_layout_error(
                                detail_line_number,
                                "define rows must be unique and precede tag/struct rows",
                            ));
                        }
                    } else {
                        if phase > 1 {
                            return Err(abi_layout_error(
                                detail_line_number,
                                "tag rows must precede struct rows",
                            ));
                        }
                        phase = 1;
                        let value = abi_i128(value_token, "value=", detail_line_number)?;
                        if !(0..=255).contains(&value) || !tag_names.insert(name.to_string()) {
                            return Err(abi_layout_error(
                                detail_line_number,
                                "tag rows must be unique u8 observations",
                            ));
                        }
                    }
                }
                "struct" => {
                    if let Some((name, _, fields)) = &current_struct
                        && fields.eq(&0)
                    {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("struct `{name}` has no field observations"),
                        ));
                    }
                    phase = 2;
                    let [
                        _,
                        detail_key,
                        name_token,
                        size_token,
                        align_token,
                        source_lines_token,
                    ] = tokens.as_slice()
                    else {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "struct row fields are not canonical",
                        ));
                    };
                    if detail_key.ne(&target_key) {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("struct row does not belong to `{target_key}`"),
                        ));
                    }
                    let name = abi_field(name_token, "name=", detail_line_number)?;
                    if !abi_name(name) || !struct_names.insert(name.to_string()) {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("struct name `{name}` is invalid or duplicated"),
                        ));
                    }
                    let size_bytes = abi_u64(size_token, "size-bytes=", detail_line_number)?;
                    let align_bytes = abi_u64(align_token, "align-bytes=", detail_line_number)?;
                    let source_lines =
                        abi_field(source_lines_token, "source-lines=", detail_line_number)?;
                    let Some((start, end)) = source_lines.split_once('-') else {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "source-lines must be `<positive>-<positive>`",
                        ));
                    };
                    let start = start.parse::<u64>().map_err(|_| {
                        abi_layout_error(detail_line_number, "invalid source-lines start")
                    })?;
                    let end = end.parse::<u64>().map_err(|_| {
                        abi_layout_error(detail_line_number, "invalid source-lines end")
                    })?;
                    if size_bytes == 0
                        || align_bytes == 0
                        || !align_bytes.is_power_of_two()
                        || size_bytes % align_bytes != 0
                        || start == 0
                        || end < start
                    {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "struct size/alignment/source range is impossible",
                        ));
                    }
                    let size_bits = size_bytes.checked_mul(char_bits).ok_or_else(|| {
                        abi_layout_error(detail_line_number, "struct size in bits overflowed u64")
                    })?;
                    current_struct = Some((name.to_string(), size_bits, 0));
                    field_names.clear();
                }
                "field" => {
                    if phase != 2 {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "field row must follow its struct row",
                        ));
                    }
                    let [
                        _,
                        detail_key,
                        struct_token,
                        name_token,
                        offset_token,
                        width_token,
                        storage_token,
                        element_token,
                        source_line_token,
                    ] = tokens.as_slice()
                    else {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "field row fields are not canonical",
                        ));
                    };
                    if detail_key.ne(&target_key) {
                        return Err(abi_layout_error(
                            detail_line_number,
                            format!("field row does not belong to `{target_key}`"),
                        ));
                    }
                    let struct_name = abi_field(struct_token, "struct=", detail_line_number)?;
                    let name = abi_field(name_token, "name=", detail_line_number)?;
                    let (current_name, struct_bits, field_count) =
                        current_struct.as_mut().ok_or_else(|| {
                            abi_layout_error(detail_line_number, "field row has no current struct")
                        })?;
                    if struct_name.ne(current_name)
                        || !abi_name(name)
                        || !field_names.insert(name.to_string())
                    {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "field struct/name is invalid, duplicated, or not current",
                        ));
                    }
                    let offset_bits = abi_u64(offset_token, "offset-bits=", detail_line_number)?;
                    let width_bits = abi_u64(width_token, "width-bits=", detail_line_number)?;
                    let storage = abi_field(storage_token, "storage=", detail_line_number)?;
                    let element_width_bits =
                        abi_u64(element_token, "element-width-bits=", detail_line_number)?;
                    let source_line =
                        abi_u64(source_line_token, "source-line=", detail_line_number)?;
                    let end_bits = offset_bits.checked_add(width_bits).ok_or_else(|| {
                        abi_layout_error(detail_line_number, "field bit range overflowed u64")
                    })?;
                    let storage_valid = match storage {
                        "scalar" | "bitfield" => {
                            width_bits > 0 && element_width_bits == 0 && end_bits <= *struct_bits
                        }
                        "flexible-array" => {
                            width_bits == 0 && element_width_bits > 0 && offset_bits <= *struct_bits
                        }
                        _ => false,
                    };
                    if !storage_valid || source_line == 0 {
                        return Err(abi_layout_error(
                            detail_line_number,
                            "field range/storage/source observation is impossible",
                        ));
                    }
                    *field_count += 1;
                }
                _ => {
                    return Err(abi_layout_error(
                        detail_line_number,
                        format!("unsupported target detail row `{kind}`"),
                    ));
                }
            }
            index += 1;
        }
        if define_names.is_empty()
            || tag_names.is_empty()
            || struct_names.is_empty()
            || detail_rows == 0
        {
            return Err(abi_layout_error(
                index + 1,
                "each target requires define, tag, struct, and field observations",
            ));
        }
        let root_line_number = index + 1;
        let root_tokens: Vec<_> = lines[index].split_whitespace().collect();
        let [root_directive, root_key, root_token] = root_tokens.as_slice() else {
            return Err(abi_layout_error(
                root_line_number,
                "target-root row is not canonical",
            ));
        };
        if !matches!(*root_directive, "target-root") || root_key.ne(&target_key) {
            return Err(abi_layout_error(
                root_line_number,
                format!("expected `target-root {target_key} <root>`"),
            ));
        }
        let claimed_root = parse_labeled_hash(root_token).ok_or_else(|| {
            abi_layout_error(
                root_line_number,
                "target root must be `fnv1a64:<16-lower-hex>`",
            )
        })?;
        let block = format!("{}\n", lines[block_start..index].join("\n"));
        let computed_root = hash_fields("fln.abi-target-layout.target-root/1", &[block.as_bytes()]);
        if claimed_root != computed_root {
            return Err(abi_layout_error(
                root_line_number,
                format!(
                    "target root mismatch: claimed={} computed={}",
                    labeled_hash(claimed_root),
                    labeled_hash(computed_root)
                ),
            ));
        }
        let row_key = format!("abi-layout:{target_key}");
        rows.insert(
            row_key.clone(),
            AbiLayoutRow {
                key: row_key,
                abi_class: abi_class.to_string(),
                target_root: claimed_root,
                source_sha256: source_sha256.to_string(),
            },
        );
        index += 1;
    }

    if index + 1 != lines.len() {
        return Err(abi_layout_error(
            index + 1,
            "inventory-root must be the single terminal row",
        ));
    }
    let root_tokens: Vec<_> = lines[index].split_whitespace().collect();
    let [directive, root_token] = root_tokens.as_slice() else {
        return Err(abi_layout_error(
            index + 1,
            "inventory-root row is not canonical",
        ));
    };
    if !matches!(*directive, "inventory-root") {
        return Err(abi_layout_error(
            index + 1,
            "inventory-root must be the single terminal row",
        ));
    }
    let claimed_root = parse_labeled_hash(root_token).ok_or_else(|| {
        abi_layout_error(index + 1, "inventory root must be `fnv1a64:<16-lower-hex>`")
    })?;
    let prefix = format!("{}\n", lines[..index].join("\n"));
    let computed_root = hash_fields(
        "fln.abi-target-layout.inventory-root/1",
        &[prefix.as_bytes()],
    );
    if claimed_root != computed_root {
        return Err(abi_layout_error(
            index + 1,
            format!(
                "inventory root mismatch: claimed={} computed={}",
                labeled_hash(claimed_root),
                labeled_hash(computed_root)
            ),
        ));
    }
    Ok(rows)
}

fn format_error(line: usize, detail: impl Into<String>) -> InventoryError {
    InventoryError::new(
        ErrorClass::Violation,
        "olean_ilean_format_invalid",
        OLEAN_ILEAN_FORMAT_FILE,
        format!("line {line}: {}", detail.into()),
    )
}

fn format_field<'a>(token: &'a str, prefix: &str, line: usize) -> Result<&'a str, InventoryError> {
    token
        .strip_prefix(prefix)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            format_error(
                line,
                format!("expected `{prefix}<value>` in canonical field order"),
            )
        })
}

fn safe_fact_token(value: &str) -> bool {
    !value.is_empty()
        && value.bytes().all(|byte| {
            byte.is_ascii_alphanumeric()
                || matches!(
                    byte,
                    b'%' | b'.'
                        | b'_'
                        | b':'
                        | b'/'
                        | b','
                        | b';'
                        | b'='
                        | b'+'
                        | b'('
                        | b')'
                        | b'['
                        | b']'
                        | b'{'
                        | b'}'
                        | b'*'
                        | b'-'
                )
        })
}

fn fact_has(fact: &str, field: &str, value: &str) -> bool {
    fact.split(';').any(|part| {
        part.split_once('=')
            .is_some_and(|pair| pair == (field, value))
    })
}

fn parse_ordinal_fact(fact: &str, line: usize) -> Result<usize, InventoryError> {
    let Some(first) = fact.split(';').next() else {
        return Err(format_error(line, "ordinal fact is empty"));
    };
    format_field(first, "ordinal=", line)?
        .parse::<usize>()
        .map_err(|_| format_error(line, "ordinal is not a canonical usize"))
}

fn parse_olean_ilean_format(
    text: &str,
    expected_abi_layouts: &BTreeMap<String, AbiLayoutRow>,
) -> Result<BTreeMap<String, FormatSummaryRow>, InventoryError> {
    validate_text_shape(
        OLEAN_ILEAN_FORMAT_FILE,
        text,
        ErrorClass::Violation,
        "olean_ilean_format_invalid",
    )?;
    let lines: Vec<_> = text.lines().collect();
    if lines.len() < 16 {
        return Err(format_error(1, "exact-format table is truncated"));
    }
    if !matches!(lines[0], "schema fln-olean-ilean-format/1") {
        return Err(format_error(
            1,
            format!("expected `schema {OLEAN_ILEAN_FORMAT_SCHEMA}`"),
        ));
    }
    if !matches!(
        lines[1],
        "extractor lean-format-source-and-pin-artifacts version=1"
    ) {
        return Err(format_error(
            2,
            format!(
                "expected `extractor {FORMAT_EXTRACTOR_ID} version={FORMAT_EXTRACTOR_VERSION}`"
            ),
        ));
    }

    let required_source_keys: BTreeSet<_> = [
        "abi-target-layout",
        "compact-cpp",
        "compact-h",
        "compacted-region-lean",
        "environment-lean",
        "frontend-lean",
        "lsp-internal-lean",
        "module-cpp",
        "references-lean",
        "setup-lean",
    ]
    .into_iter()
    .collect();
    let mut source_keys = BTreeSet::new();
    let mut source_lines = Vec::new();
    let mut previous_source: Option<&str> = None;
    let mut index = 2;
    while let Some(line) = lines.get(index)
        && line.starts_with("source ")
    {
        let line_number = index + 1;
        let tokens: Vec<_> = line.split_whitespace().collect();
        let [directive, key, path_token, authority_token, sha_token] = tokens.as_slice() else {
            return Err(format_error(
                line_number,
                "source row fields are missing, extra, or not canonically ordered",
            ));
        };
        if !matches!(*directive, "source") || !safe_key(key) {
            return Err(format_error(line_number, "source key is not canonical"));
        }
        if previous_source.is_some_and(|previous| previous >= *key) || !source_keys.insert(*key) {
            return Err(format_error(
                line_number,
                "source keys must be unique and byte-sorted",
            ));
        }
        previous_source = Some(key);
        let path = format_field(path_token, "path=", line_number)?;
        let authority = format_field(authority_token, "authority=", line_number)?;
        let sha = format_field(sha_token, "sha256=", line_number)?;
        if !safe_key(path)
            || !matches!(authority, "SUITE.lock:reference" | "derived-target-layout")
            || (*key == "abi-target-layout") != (authority == "derived-target-layout")
            || !lower_hex(sha, 64)
        {
            return Err(format_error(
                line_number,
                "source locator, authority, or SHA-256 is not canonical",
            ));
        }
        source_lines.push(*line);
        index += 1;
    }
    if source_keys != required_source_keys {
        return Err(format_error(
            index + 1,
            format!(
                "source inventory differs: expected={required_source_keys:?} observed={source_keys:?}"
            ),
        ));
    }
    let source_projection = format!("{}\n", source_lines.join("\n"));
    let source_root = hash_fields(
        "fln.olean-ilean-format.source-root/1",
        &[source_projection.as_bytes()],
    );

    let count_line = lines
        .get(index)
        .ok_or_else(|| format_error(index + 1, "missing target-count row"))?;
    let count_tokens: Vec<_> = count_line.split_whitespace().collect();
    let [count_directive, count_token] = count_tokens.as_slice() else {
        return Err(format_error(
            index + 1,
            "target count must be `target-count <decimal>`",
        ));
    };
    let target_count = count_token
        .parse::<usize>()
        .map_err(|_| format_error(index + 1, "target count is not a canonical usize"))?;
    if !matches!(*count_directive, "target-count")
        || target_count != expected_abi_layouts.len()
        || target_count == 0
    {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "format_target_matrix_mismatch",
            OLEAN_ILEAN_FORMAT_FILE,
            format!(
                "format target-count={target_count} but ABI layout has {} targets",
                expected_abi_layouts.len()
            ),
        ));
    }
    index += 1;

    let mut summaries = BTreeMap::new();
    for section_index in 0..=target_count {
        let line_number = index + 1;
        let header_line = lines
            .get(index)
            .ok_or_else(|| format_error(line_number, "missing section row"))?;
        let tokens: Vec<_> = header_line.split_whitespace().collect();
        let [directive, section_name, abi_token, count_token] = tokens.as_slice() else {
            return Err(format_error(
                line_number,
                "section row fields are missing, extra, or not canonically ordered",
            ));
        };
        if !matches!(*directive, "section") {
            return Err(format_error(line_number, "expected section row"));
        }
        let expected_name = if section_index == 0 {
            "ilean".to_string()
        } else {
            format!("olean:target:{section_index:04}")
        };
        if section_name.ne(&expected_name) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "format_target_matrix_mismatch",
                OLEAN_ILEAN_FORMAT_FILE,
                format!(
                    "line {line_number}: expected section `{expected_name}`, got `{section_name}`"
                ),
            ));
        }
        let abi_class = format_field(abi_token, "abi-class=", line_number)?;
        let expected_abi = if section_index == 0 {
            None
        } else {
            let abi_key = format!("abi-layout:target:{section_index:04}");
            Some(
                expected_abi_layouts
                    .get(&abi_key)
                    .ok_or_else(|| {
                        InventoryError::new(
                            ErrorClass::InternalFault,
                            "format_abi_join_lost_row",
                            OLEAN_ILEAN_FORMAT_FILE,
                            format!("validated ABI map lost `{abi_key}`"),
                        )
                    })?
                    .abi_class
                    .as_str(),
            )
        };
        if expected_abi.unwrap_or("none") != abi_class {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "format_abi_policy_mismatch",
                OLEAN_ILEAN_FORMAT_FILE,
                format!(
                    "line {line_number}: section `{section_name}` claims ABI `{abi_class}`, expected `{}`",
                    expected_abi.unwrap_or("none")
                ),
            ));
        }
        let row_count = format_field(count_token, "row-count=", line_number)?
            .parse::<usize>()
            .map_err(|_| format_error(line_number, "row-count is not canonical"))?;
        if row_count == 0 || row_count > MAX_ROWS {
            return Err(InventoryError::new(
                ErrorClass::Inconclusive,
                "resource_exhausted",
                OLEAN_ILEAN_FORMAT_FILE,
                format!("section `{section_name}` row-count must be within 1..={MAX_ROWS}"),
            ));
        }
        let block_start = index;
        index += 1;
        let mut categories = BTreeSet::new();
        let mut previous_key: Option<&str> = None;
        let mut ordinal_next: BTreeMap<(String, String), usize> = BTreeMap::new();
        let mut saw_epoch_contract = false;
        let mut saw_target_binding = false;
        for _ in 0..row_count {
            let row_line_number = index + 1;
            let row_line = lines
                .get(index)
                .ok_or_else(|| format_error(row_line_number, "section rows are truncated"))?;
            let row_tokens: Vec<_> = row_line.split_whitespace().collect();
            let [row_directive, key, category_token, fact_token, source_token] =
                row_tokens.as_slice()
            else {
                return Err(format_error(
                    row_line_number,
                    "format row fields are missing, extra, or not canonically ordered",
                ));
            };
            if !matches!(*row_directive, "row") || !safe_key(key) {
                return Err(format_error(
                    row_line_number,
                    "format row key is not canonical",
                ));
            }
            if previous_key.is_some_and(|previous| previous >= *key) {
                return Err(format_error(
                    row_line_number,
                    "format row keys must be unique and byte-sorted within each section",
                ));
            }
            previous_key = Some(key);
            let category = format_field(category_token, "category=", row_line_number)?;
            let fact = format_field(fact_token, "fact=", row_line_number)?;
            let source = format_field(source_token, "source=", row_line_number)?;
            if !safe_key(category) || !safe_fact_token(fact) || !safe_fact_token(source) {
                return Err(format_error(
                    row_line_number,
                    "format row category, fact, or source token is not canonical",
                ));
            }
            categories.insert(category);

            if matches!(
                category,
                "field"
                    | "import-field"
                    | "decl-field"
                    | "ref-ident-constructor"
                    | "loader"
                    | "header-field"
                    | "compactor"
                    | "level"
                    | "module-field"
                    | "section"
            ) {
                let ordinal = parse_ordinal_fact(fact, row_line_number)?;
                let sequence = if category == "section" {
                    key.rsplit_once(':')
                        .map(|(prefix, _)| prefix)
                        .unwrap_or(key)
                } else {
                    category
                };
                let counter_key = (category.to_string(), sequence.to_string());
                let expected = ordinal_next.entry(counter_key).or_default();
                if ordinal != *expected {
                    return Err(format_error(
                        row_line_number,
                        format!(
                            "category `{category}` sequence `{sequence}` expected ordinal {}, got {ordinal}",
                            *expected
                        ),
                    ));
                }
                *expected += 1;
            }
            if section_index == 0 && key == &"epoch" && fact_has(fact, "unknown", "reject") {
                saw_epoch_contract = true;
            }
            if section_index > 0
                && key == &"validation:epoch"
                && fact_has(fact, "unknown", "reject-incompatible-header")
            {
                saw_epoch_contract = true;
            }
            if section_index > 0 && key == &"target" && fact_has(fact, "abi-class", abi_class) {
                saw_target_binding = true;
            }
            index += 1;
        }

        let required_categories: BTreeSet<_> = if section_index == 0 {
            [
                "artifact-corpus",
                "decls",
                "decl-field",
                "encoding",
                "epoch",
                "field",
                "import-field",
                "loader",
                "location",
                "module-refs",
                "producer",
                "ref-ident-constructor",
                "validation",
            ]
            .into_iter()
            .collect()
        } else {
            [
                "artifact-corpus",
                "compactor",
                "extension",
                "flag",
                "header",
                "header-field",
                "level",
                "module-field",
                "relocation",
                "scalar",
                "section",
                "sharing",
                "target",
                "validation",
                "version",
            ]
            .into_iter()
            .collect()
        };
        if !required_categories.is_subset(&categories)
            || !saw_epoch_contract
            || (section_index > 0 && !saw_target_binding)
        {
            return Err(format_error(
                index,
                format!(
                    "section `{section_name}` lacks required exactness categories or epoch/target binding: required={required_categories:?} observed={categories:?}"
                ),
            ));
        }

        let root_line_number = index + 1;
        let root_tokens: Vec<_> = lines
            .get(index)
            .ok_or_else(|| format_error(root_line_number, "missing section-root row"))?
            .split_whitespace()
            .collect();
        let [root_directive, root_name, root_token] = root_tokens.as_slice() else {
            return Err(format_error(
                root_line_number,
                "section-root row is not canonical",
            ));
        };
        if !matches!(*root_directive, "section-root") || root_name.ne(section_name) {
            return Err(format_error(
                root_line_number,
                format!("expected `section-root {section_name} <root>`"),
            ));
        }
        let claimed_root = parse_labeled_hash(root_token).ok_or_else(|| {
            format_error(
                root_line_number,
                "section root must be `fnv1a64:<16-lower-hex>`",
            )
        })?;
        let block = format!("{}\n", lines[block_start..index].join("\n"));
        let computed_root =
            hash_fields("fln.olean-ilean-format.section-root/1", &[block.as_bytes()]);
        if claimed_root != computed_root {
            return Err(format_error(
                root_line_number,
                format!(
                    "section root mismatch: claimed={} computed={}",
                    labeled_hash(claimed_root),
                    labeled_hash(computed_root)
                ),
            ));
        }
        let key = if section_index == 0 {
            "artifact-format:ilean".to_string()
        } else {
            format!("artifact-format:olean:target:{section_index:04}")
        };
        summaries.insert(
            key.clone(),
            FormatSummaryRow {
                key,
                abi_class: expected_abi.map(str::to_string),
                section_root: claimed_root,
                inventory_root: 0,
                source_root,
                row_count,
            },
        );
        index += 1;
    }

    if index + 1 != lines.len() {
        return Err(format_error(
            index + 1,
            "inventory-root must be the single terminal row",
        ));
    }
    let root_tokens: Vec<_> = lines[index].split_whitespace().collect();
    let [directive, root_token] = root_tokens.as_slice() else {
        return Err(format_error(
            index + 1,
            "inventory-root row is not canonical",
        ));
    };
    if !matches!(*directive, "inventory-root") {
        return Err(format_error(
            index + 1,
            "inventory-root must be the single terminal row",
        ));
    }
    let claimed_root = parse_labeled_hash(root_token).ok_or_else(|| {
        format_error(index + 1, "inventory root must be `fnv1a64:<16-lower-hex>`")
    })?;
    let prefix = format!("{}\n", lines[..index].join("\n"));
    let computed_root = hash_fields(
        "fln.olean-ilean-format.inventory-root/1",
        &[prefix.as_bytes()],
    );
    if claimed_root != computed_root {
        return Err(format_error(
            index + 1,
            format!(
                "inventory root mismatch: claimed={} computed={}",
                labeled_hash(claimed_root),
                labeled_hash(computed_root)
            ),
        ));
    }
    for summary in summaries.values_mut() {
        summary.inventory_root = claimed_root;
    }
    Ok(summaries)
}

fn evidence_hash(kind: &str, source: &str, facts: &[&str]) -> u64 {
    let mut fields: Vec<&[u8]> = Vec::with_capacity(facts.len() + 2);
    fields.push(kind.as_bytes());
    fields.push(source.as_bytes());
    fields.extend(facts.iter().map(|fact| fact.as_bytes()));
    hash_fields("fln.contract-inventory.raw-evidence/1", &fields)
}

fn parse_census_manifest(text: &str) -> Result<CensusManifest, InventoryError> {
    validate_text_shape(
        EXTERN_BUILTIN_ENVIRONMENT_FILE,
        text,
        ErrorClass::Violation,
        "census_manifest_invalid",
    )?;
    let mut schema_seen = false;
    let mut fields = BTreeMap::new();
    for (index, raw) in text.lines().enumerate() {
        let line_number = index + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == format!("schema {EXTERN_BUILTIN_ENVIRONMENT_SCHEMA}") {
            if schema_seen {
                return Err(InventoryError::new(
                    ErrorClass::Violation,
                    "census_manifest_invalid",
                    EXTERN_BUILTIN_ENVIRONMENT_FILE,
                    format!("line {line_number} duplicates the schema"),
                ));
            }
            schema_seen = true;
            continue;
        }
        let (key, value) = line.split_once('\t').ok_or_else(|| {
            InventoryError::new(
                ErrorClass::Violation,
                "census_manifest_invalid",
                EXTERN_BUILTIN_ENVIRONMENT_FILE,
                format!("line {line_number} must contain one tab-separated field"),
            )
        })?;
        if key.is_empty()
            || value.is_empty()
            || value.contains('\t')
            || fields.insert(key.to_string(), value.to_string()).is_some()
        {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "census_manifest_invalid",
                EXTERN_BUILTIN_ENVIRONMENT_FILE,
                format!("line {line_number} is duplicate or noncanonical"),
            ));
        }
    }
    if !schema_seen {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "census_manifest_invalid",
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
            format!("expected `schema {EXTERN_BUILTIN_ENVIRONMENT_SCHEMA}`"),
        ));
    }
    let expected_keys = BTreeSet::from([
        "attribute-count",
        "builtin-environment-sha256",
        "builtin-partition-sha256",
        "constant-count",
        "extern-count",
        "extern-census-sha256",
        "extractor",
        "library-code-count",
        "manifest-root",
        "module-count",
        "partition-policy-sha256",
        "toolchain-api-count",
        "unresolved-count",
        "user-facing-data-count",
    ]);
    let actual_keys = fields.keys().map(String::as_str).collect::<BTreeSet<_>>();
    if actual_keys != expected_keys {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "census_manifest_invalid",
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
            format!(
                "manifest field set differs: missing={:?} extra={:?}",
                expected_keys.difference(&actual_keys).collect::<Vec<_>>(),
                actual_keys.difference(&expected_keys).collect::<Vec<_>>()
            ),
        ));
    }
    if fields.get("extractor").map(String::as_str) != Some("lean-reference-environment-walk-v2") {
        return Err(InventoryError::new(
            ErrorClass::Violation,
            "census_manifest_invalid",
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
            "extractor must be lean-reference-environment-walk-v2",
        ));
    }
    let sha = |key: &str| -> Result<String, InventoryError> {
        let value = fields.get(key).expect("validated key set");
        if !lower_hex(value, 64) {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "census_manifest_invalid",
                EXTERN_BUILTIN_ENVIRONMENT_FILE,
                format!("{key} must be 64 lowercase hexadecimal digits"),
            ));
        }
        Ok(value.clone())
    };
    let count = |key: &str| -> Result<usize, InventoryError> {
        fields
            .get(key)
            .expect("validated key set")
            .parse::<usize>()
            .map_err(|error| {
                InventoryError::new(
                    ErrorClass::Violation,
                    "census_manifest_invalid",
                    EXTERN_BUILTIN_ENVIRONMENT_FILE,
                    format!("{key} is not a canonical count: {error}"),
                )
            })
    };
    let constant_count = count("constant-count")?;
    let extern_count = count("extern-count")?;
    let module_count = count("module-count")?;
    let attribute_count = count("attribute-count")?;
    let toolchain_api_count = count("toolchain-api-count")?;
    let library_code_count = count("library-code-count")?;
    let user_facing_data_count = count("user-facing-data-count")?;
    let unresolved_count = count("unresolved-count")?;
    if constant_count == 0
        || extern_count == 0
        || extern_count > constant_count
        || module_count == 0
        || attribute_count == 0
        || unresolved_count != 0
        || toolchain_api_count
            .checked_add(library_code_count)
            .and_then(|total| total.checked_add(user_facing_data_count))
            != Some(constant_count)
    {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "census_manifest_incomplete",
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
            "counts must be nonzero, externs bounded by declarations, partitions total, and unresolved zero",
        ));
    }
    let manifest_root = fields
        .get("manifest-root")
        .expect("validated key set")
        .strip_prefix("sha256:")
        .filter(|value| lower_hex(value, 64))
        .ok_or_else(|| {
            InventoryError::new(
                ErrorClass::Violation,
                "census_manifest_invalid",
                EXTERN_BUILTIN_ENVIRONMENT_FILE,
                "manifest-root must be sha256:<64-lower-hex>",
            )
        })?
        .to_string();
    Ok(CensusManifest {
        extern_sha256: sha("extern-census-sha256")?,
        builtin_sha256: sha("builtin-environment-sha256")?,
        partition_sha256: sha("builtin-partition-sha256")?,
        policy_sha256: sha("partition-policy-sha256")?,
        constant_count,
        extern_count,
        module_count,
        attribute_count,
        toolchain_api_count,
        library_code_count,
        user_facing_data_count,
        manifest_root,
    })
}

fn raw_rows(
    lock: &SuiteLock,
    abi_layout_text: &str,
    olean_ilean_format_text: &str,
    extern_builtin_environment_text: &str,
) -> Result<BTreeMap<String, RawRow>, InventoryError> {
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
        extractor: EXTRACTOR_ID,
        extractor_version: EXTRACTOR_VERSION,
        source: toolchain_source.to_string(),
        observed_abi_class: None,
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
            extractor: EXTRACTOR_ID,
            extractor_version: EXTRACTOR_VERSION,
            evidence_hash: evidence_hash("target", &source, &[target]),
            source,
            observed_abi_class: None,
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
            extractor: EXTRACTOR_ID,
            extractor_version: EXTRACTOR_VERSION,
            evidence_hash: evidence_hash("suite", &source, &[repo, &pin.commit, path]),
            source,
            observed_abi_class: None,
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
        extractor: EXTRACTOR_ID,
        extractor_version: EXTRACTOR_VERSION,
        source: reference_source.to_string(),
        observed_abi_class: None,
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
        extractor: EXTRACTOR_ID,
        extractor_version: EXTRACTOR_VERSION,
        source: corpus_source.to_string(),
        observed_abi_class: None,
        evidence_hash: evidence_hash(
            "corpus",
            corpus_source,
            &[corpus_repo, corpus_tag, corpus_commit],
        ),
    })?;

    let abi_layouts = parse_abi_target_layout(abi_layout_text, lock.targets.len())?;
    for layout in abi_layouts.values() {
        let target_key = layout
            .key
            .strip_prefix("abi-layout:")
            .ok_or_else(|| {
                InventoryError::new(
                    ErrorClass::InternalFault,
                    "abi_layout_identity_invalid",
                    ABI_TARGET_LAYOUT_FILE,
                    format!("validated ABI layout key lost its prefix: `{}`", layout.key),
                )
            })?
            .to_string();
        let source = format!("{ABI_TARGET_LAYOUT_FILE}:{target_key}");
        let target_root = labeled_hash(layout.target_root);
        insert(RawRow {
            key: layout.key.clone(),
            kind: "abi-layout",
            extractor: ABI_EXTRACTOR_ID,
            extractor_version: ABI_EXTRACTOR_VERSION,
            observed_abi_class: Some(layout.abi_class.clone()),
            evidence_hash: evidence_hash(
                "abi-layout",
                &source,
                &[&layout.abi_class, &target_root, &layout.source_sha256],
            ),
            source,
        })?;
    }

    for format in parse_olean_ilean_format(olean_ilean_format_text, &abi_layouts)?.into_values() {
        let source_suffix = format.key.strip_prefix("artifact-format:").ok_or_else(|| {
            InventoryError::new(
                ErrorClass::InternalFault,
                "format_identity_invalid",
                OLEAN_ILEAN_FORMAT_FILE,
                format!("validated format key lost its prefix: `{}`", format.key),
            )
        })?;
        let source = format!("{OLEAN_ILEAN_FORMAT_FILE}:{source_suffix}");
        let section_root = labeled_hash(format.section_root);
        let inventory_root = labeled_hash(format.inventory_root);
        let source_root = labeled_hash(format.source_root);
        let row_count = format.row_count.to_string();
        insert(RawRow {
            key: format.key,
            kind: "artifact-format",
            extractor: FORMAT_EXTRACTOR_ID,
            extractor_version: FORMAT_EXTRACTOR_VERSION,
            observed_abi_class: format.abi_class.clone(),
            evidence_hash: evidence_hash(
                "artifact-format",
                &source,
                &[
                    format.abi_class.as_deref().unwrap_or("none"),
                    &section_root,
                    &inventory_root,
                    &source_root,
                    &row_count,
                ],
            ),
            source,
        })?;
    }

    let census = parse_census_manifest(extern_builtin_environment_text)?;
    let manifest_source_root = labeled_hash(hash_one(
        "fln.contract-inventory.extern-builtin-manifest/1",
        extern_builtin_environment_text.as_bytes(),
    ));
    let extern_count = census.extern_count.to_string();
    let extern_source = format!("{EXTERN_BUILTIN_ENVIRONMENT_FILE}:extern");
    insert(RawRow {
        key: "environment-census:extern".to_string(),
        kind: "environment-census",
        extractor: CENSUS_EXTRACTOR_ID,
        extractor_version: CENSUS_EXTRACTOR_VERSION,
        source: extern_source.clone(),
        observed_abi_class: None,
        evidence_hash: evidence_hash(
            "environment-census",
            &extern_source,
            &[
                &census.extern_sha256,
                &extern_count,
                &census.policy_sha256,
                &census.manifest_root,
                &manifest_source_root,
            ],
        ),
    })?;
    let constant_count = census.constant_count.to_string();
    let module_count = census.module_count.to_string();
    let attribute_count = census.attribute_count.to_string();
    let toolchain_api_count = census.toolchain_api_count.to_string();
    let library_code_count = census.library_code_count.to_string();
    let user_facing_data_count = census.user_facing_data_count.to_string();
    let builtin_source = format!("{EXTERN_BUILTIN_ENVIRONMENT_FILE}:builtin");
    insert(RawRow {
        key: "environment-census:builtin".to_string(),
        kind: "environment-census",
        extractor: CENSUS_EXTRACTOR_ID,
        extractor_version: CENSUS_EXTRACTOR_VERSION,
        source: builtin_source.clone(),
        observed_abi_class: None,
        evidence_hash: evidence_hash(
            "environment-census",
            &builtin_source,
            &[
                &census.builtin_sha256,
                &census.partition_sha256,
                &census.policy_sha256,
                &constant_count,
                &module_count,
                &attribute_count,
                &toolchain_api_count,
                &library_code_count,
                &user_facing_data_count,
                &census.manifest_root,
                &manifest_source_root,
            ],
        ),
    })?;

    Ok(rows)
}

fn canonical_inventory(
    suite_lock_text: &str,
    schema_text: &str,
    policy_text: &str,
    abi_target_layout_text: &str,
    olean_ilean_format_text: &str,
    extern_builtin_environment_text: &str,
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
    let raw = raw_rows(
        &lock,
        abi_target_layout_text,
        olean_ilean_format_text,
        extern_builtin_environment_text,
    )?;
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
    let abi_target_layout_root = hash_one(
        "fln.contract-inventory.abi-target-layout-root/1",
        abi_target_layout_text.as_bytes(),
    );
    let olean_ilean_format_root = hash_one(
        "fln.contract-inventory.olean-ilean-format-root/1",
        olean_ilean_format_text.as_bytes(),
    );
    let policy_root = hash_one(
        "fln.contract-inventory.policy-root/1",
        policy_text.as_bytes(),
    );
    let mut raw_projection = String::new();
    for (key, row) in &raw {
        let observed_abi_class = row.observed_abi_class.as_deref().unwrap_or("none");
        raw_projection.push_str(&format!(
            "row {key} kind={} extractor={} extractor-version={} source={} observed-abi-class={observed_abi_class} raw-evidence-hash={}\n",
            row.kind,
            row.extractor,
            row.extractor_version,
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
    let abi_row_count = raw
        .values()
        .filter(|row| matches!(row.kind, "abi-layout"))
        .count();
    let format_row_count = raw
        .values()
        .filter(|row| matches!(row.kind, "artifact-format"))
        .count();
    let unresolved_row_count = 0;
    let source_bytes = suite_lock_text
        .len()
        .checked_add(schema_text.len())
        .and_then(|total| total.checked_add(policy_text.len()))
        .and_then(|total| total.checked_add(abi_target_layout_text.len()))
        .and_then(|total| total.checked_add(olean_ilean_format_text.len()))
        .and_then(|total| total.checked_add(extern_builtin_environment_text.len()))
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
    output.push_str(&format!(
        "abi-target-layout-root {}\n",
        labeled_hash(abi_target_layout_root)
    ));
    output.push_str(&format!(
        "olean-ilean-format-root {}\n",
        labeled_hash(olean_ilean_format_root)
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
    output.push_str(&format!(
        "extractor {ABI_EXTRACTOR_ID} version={ABI_EXTRACTOR_VERSION}\n"
    ));
    output.push_str(&format!(
        "extractor {FORMAT_EXTRACTOR_ID} version={FORMAT_EXTRACTOR_VERSION}\n"
    ));
    output.push_str(&format!(
        "extractor {CENSUS_EXTRACTOR_ID} version={CENSUS_EXTRACTOR_VERSION}\n"
    ));
    output.push_str(&format!("row-count {}\n", raw.len()));
    output.push_str(&format!("target-row-count {target_row_count}\n"));
    output.push_str(&format!("abi-row-count {abi_row_count}\n"));
    output.push_str(&format!("format-row-count {format_row_count}\n"));
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
        if let Some(observed_abi_class) = &raw_row.observed_abi_class
            && policy_row.abi_class.ne(observed_abi_class)
        {
            return Err(InventoryError::new(
                ErrorClass::Violation,
                "abi_policy_mismatch",
                CONTRACT_INVENTORY_POLICY_FILE,
                format!(
                    "row `{key}` classifies ABI `{}` but mechanical extraction observes `{observed_abi_class}`",
                    policy_row.abi_class
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
                raw_row.extractor.as_bytes(),
                raw_row.extractor_version.as_bytes(),
                raw_row.source.as_bytes(),
                policy_row.target_class.as_bytes(),
                policy_row.abi_class.as_bytes(),
                evidence.as_bytes(),
                b"observed",
                policy_row.support.as_bytes(),
            ],
        );
        output.push_str(&format!(
            "row {key} kind={} extractor={} extractor-version={} source={} target-class={} abi-class={} raw-evidence-hash={evidence} identity={} authority=observed support={}\n",
            raw_row.kind,
            raw_row.extractor,
            raw_row.extractor_version,
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
            abi_target_layout_root: labeled_hash(abi_target_layout_root),
            olean_ilean_format_root: labeled_hash(olean_ilean_format_root),
            raw_root: labeled_hash(raw_root),
            policy_root: labeled_hash(policy_root),
            reference_root: labeled_hash(reference_root),
            row_count: raw.len(),
            target_row_count,
            abi_row_count,
            format_row_count,
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
    abi_target_layout_text: &str,
    olean_ilean_format_text: &str,
    extern_builtin_environment_text: &str,
) -> Result<String, InventoryError> {
    let inventory = canonical_inventory(
        suite_lock_text,
        schema_text,
        policy_text,
        abi_target_layout_text,
        olean_ilean_format_text,
        extern_builtin_environment_text,
    )?;
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
        abi_target_layout: read_bounded(
            root,
            ABI_TARGET_LAYOUT_FILE,
            ErrorClass::Inconclusive,
            "source_unavailable",
        )?,
        olean_ilean_format: read_bounded(
            root,
            OLEAN_ILEAN_FORMAT_FILE,
            ErrorClass::Inconclusive,
            "source_unavailable",
        )?,
        extern_builtin_environment: read_bounded(
            root,
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
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
        utf8(
            ABI_TARGET_LAYOUT_FILE,
            &sources.abi_target_layout,
            ErrorClass::Violation,
            "abi_target_layout_invalid",
        )?,
        utf8(
            OLEAN_ILEAN_FORMAT_FILE,
            &sources.olean_ilean_format,
            ErrorClass::Violation,
            "olean_ilean_format_invalid",
        )?,
        utf8(
            EXTERN_BUILTIN_ENVIRONMENT_FILE,
            &sources.extern_builtin_environment,
            ErrorClass::Violation,
            "census_manifest_invalid",
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

fn abi_source_candidate_exists(root: &Path) -> Result<bool, InventoryError> {
    validate_parent_chain(root, ABI_TARGET_LAYOUT_CANDIDATE_FILE)?;
    match fs::symlink_metadata(root.join(ABI_TARGET_LAYOUT_CANDIDATE_FILE)) {
        Ok(_) => Ok(true),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(false),
        Err(error) => Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            ABI_TARGET_LAYOUT_CANDIDATE_FILE,
            format!("cannot inspect ABI target-layout publication candidate: {error}"),
        )),
    }
}

fn format_source_candidate_exists(root: &Path) -> Result<bool, InventoryError> {
    validate_parent_chain(root, OLEAN_ILEAN_FORMAT_CANDIDATE_FILE)?;
    match fs::symlink_metadata(root.join(OLEAN_ILEAN_FORMAT_CANDIDATE_FILE)) {
        Ok(_) => Ok(true),
        Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => Ok(false),
        Err(error) => Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "source_unavailable",
            OLEAN_ILEAN_FORMAT_CANDIDATE_FILE,
            format!("cannot inspect OLEAN/ILEAN publication candidate: {error}"),
        )),
    }
}

fn ensure_no_abi_source_candidate(root: &Path) -> Result<(), InventoryError> {
    if abi_source_candidate_exists(root)? {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "stale_source_candidate",
            ABI_TARGET_LAYOUT_CANDIDATE_FILE,
            "interrupted ABI target-layout publication candidate exists; refuse both the raw table and its derived canonical inventory",
        ));
    }
    Ok(())
}

fn ensure_no_format_source_candidate(root: &Path) -> Result<(), InventoryError> {
    if format_source_candidate_exists(root)? {
        return Err(InventoryError::new(
            ErrorClass::Inconclusive,
            "stale_source_candidate",
            OLEAN_ILEAN_FORMAT_CANDIDATE_FILE,
            "interrupted OLEAN/ILEAN format publication candidate exists; refuse both the raw table and its derived canonical inventory",
        ));
    }
    Ok(())
}

fn ensure_no_census_source_candidate(root: &Path) -> Result<(), InventoryError> {
    for candidate in [
        EXTERN_CENSUS_CANDIDATE_FILE,
        BUILTIN_ENVIRONMENT_CANDIDATE_FILE,
        BUILTIN_ENVIRONMENT_001_CANDIDATE_FILE,
        BUILTIN_ENVIRONMENT_002_CANDIDATE_FILE,
        BUILTIN_PARTITION_CANDIDATE_FILE,
        EXTERN_BUILTIN_ENVIRONMENT_CANDIDATE_FILE,
    ] {
        validate_parent_chain(root, candidate)?;
        match fs::symlink_metadata(root.join(candidate)) {
            Ok(_) => {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "stale_source_candidate",
                    candidate,
                    "interrupted extern/builtin census group exists; refuse every raw projection and the derived canonical inventory",
                ));
            }
            Err(error) if matches!(error.kind(), std::io::ErrorKind::NotFound) => {}
            Err(error) => {
                return Err(InventoryError::new(
                    ErrorClass::Inconclusive,
                    "source_unavailable",
                    candidate,
                    format!("cannot inspect extern/builtin census candidate: {error}"),
                ));
            }
        }
    }
    Ok(())
}

fn ensure_no_candidate(root: &Path) -> Result<(), InventoryError> {
    ensure_no_abi_source_candidate(root)?;
    ensure_no_format_source_candidate(root)?;
    ensure_no_census_source_candidate(root)?;
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
    ensure_no_abi_source_candidate(&root)?;
    ensure_no_format_source_candidate(&root)?;
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
    use crate::scratch::{INVENTORY_PREFIX, ScratchRoot};
    use std::process::Command;
    use std::thread;
    use std::time::Duration;

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

    const TEST_ABI_TARGET_LAYOUT: &str = include_str!("../../../contracts/ABI_TARGET_LAYOUT.txt");
    const TEST_OLEAN_ILEAN_FORMAT: &str = include_str!("../../../contracts/OLEAN_ILEAN_FORMAT.txt");
    const TEST_EXTERN_BUILTIN_ENVIRONMENT: &str =
        include_str!("../../../contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");

    const REQUIRED_POLICY: &str = "\
schema fln-contract-inventory-policy/1
row abi-layout:target:0001 kind=abi-layout support=required target-class=certified abi-class=lp64-le
row artifact-format:ilean kind=artifact-format support=required target-class=none abi-class=none
row artifact-format:olean:target:0001 kind=artifact-format support=required target-class=certified abi-class=lp64-le
row corpus kind=corpus support=required target-class=none abi-class=none
row environment-census:builtin kind=environment-census support=required target-class=none abi-class=none
row environment-census:extern kind=environment-census support=required target-class=none abi-class=none
row reference kind=reference support=required target-class=none abi-class=none
row suite:asupersync kind=suite support=required target-class=none abi-class=none
row target:0001 kind=target support=required target-class=certified abi-class=none
row toolchain kind=toolchain support=required target-class=none abi-class=none
";

    const OPTIONAL_POLICY: &str = "\
schema fln-contract-inventory-policy/1
row abi-layout:target:0001 kind=abi-layout support=required target-class=certified abi-class=lp64-le
row artifact-format:ilean kind=artifact-format support=required target-class=none abi-class=none
row artifact-format:olean:target:0001 kind=artifact-format support=required target-class=certified abi-class=lp64-le
row corpus kind=corpus support=required target-class=none abi-class=none
row environment-census:builtin kind=environment-census support=required target-class=none abi-class=none
row environment-census:extern kind=environment-census support=required target-class=none abi-class=none
row reference kind=reference support=required target-class=none abi-class=none
row suite:asupersync kind=suite support=optional target-class=none abi-class=none
row target:0001 kind=target support=required target-class=certified abi-class=none
row toolchain kind=toolchain support=required target-class=none abi-class=none
";

    /// A fixture root that reclaims itself when its test passes and is retained when the test
    /// fails (bead `franken_lean-s2sn`). The fence, the `Drop` body and the retention message
    /// live once in [`crate::scratch`]; this file holds no second copy of them.
    ///
    /// The unconditional retention this replaces had reached **1,267 directories / 76.4 MiB**
    /// allocated on 2026-07-28, and it announced itself on every passing run: the old body
    /// printed `retained contract-inventory fixture: …` on the success path, so the line that
    /// looked like a diagnostic was in fact the leak reporting itself once per test.
    fn retained_root(tag: &str) -> ScratchRoot {
        ScratchRoot::create(INVENTORY_PREFIX, "contract-inventory", tag)
            .expect("create retained fixture")
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

    fn fixture_root(tag: &str, policy: &str) -> ScratchRoot {
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
        write_new(
            &root.join(ABI_TARGET_LAYOUT_FILE),
            TEST_ABI_TARGET_LAYOUT.as_bytes(),
        );
        write_new(
            &root.join(OLEAN_ILEAN_FORMAT_FILE),
            TEST_OLEAN_ILEAN_FORMAT.as_bytes(),
        );
        write_new(
            &root.join(EXTERN_BUILTIN_ENVIRONMENT_FILE),
            TEST_EXTERN_BUILTIN_ENVIRONMENT.as_bytes(),
        );
        root
    }

    fn reroot_format_table(text: &str, section_name: &str) -> String {
        let mut lines: Vec<String> = text.lines().map(str::to_string).collect();
        let section_start = lines
            .iter()
            .position(|line| line.starts_with(&format!("section {section_name} ")))
            .expect("section to reroot exists");
        let section_end = lines
            .iter()
            .position(|line| line.starts_with(&format!("section-root {section_name} ")))
            .expect("section root to reroot exists");
        let block = format!("{}\n", lines[section_start..section_end].join("\n"));
        lines[section_end] = format!(
            "section-root {section_name} {}",
            labeled_hash(hash_fields(
                "fln.olean-ilean-format.section-root/1",
                &[block.as_bytes()]
            ))
        );
        let inventory_index = lines
            .iter()
            .position(|line| line.starts_with("inventory-root "))
            .expect("inventory root exists");
        let prefix = format!("{}\n", lines[..inventory_index].join("\n"));
        lines[inventory_index] = format!(
            "inventory-root {}",
            labeled_hash(hash_fields(
                "fln.olean-ilean-format.inventory-root/1",
                &[prefix.as_bytes()]
            ))
        );
        format!("{}\n", lines.join("\n"))
    }

    #[test]
    fn abi_contract_inventory_model_is_deterministic_bijective_and_not_a_second_pin_authority() {
        let first = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            REQUIRED_POLICY,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .unwrap();
        let second = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            REQUIRED_POLICY,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .unwrap();
        assert_eq!(first, second);
        for required_header in [
            "raw-root fnv1a64:",
            "reference-root fnv1a64:",
            "row-count 10\n",
            "target-row-count 1\n",
            "abi-row-count 1\n",
            "format-row-count 2\n",
            "unresolved-row-count 0\n",
            "extractor lean-reference-environment-walk version=2\n",
            "row environment-census:builtin kind=environment-census ",
            "row environment-census:extern kind=environment-census ",
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
        let changed = canonical_inventory_text(
            &changed_reference,
            SCHEMA_DEFINITION,
            REQUIRED_POLICY,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
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
        let error = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            &missing,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .expect_err("missing policy row must fail the bijection");
        assert_eq!(error.reason, "policy_join_not_bijective");

        let stale = REQUIRED_POLICY.to_string()
            + "row zzzz:stale kind=suite support=required target-class=none abi-class=none\n";
        let error = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            &stale,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .expect_err("stale policy row must fail the bijection");
        assert_eq!(error.reason, "policy_join_not_bijective");

        let duplicate = REQUIRED_POLICY.replace(
            "row reference kind=reference support=required target-class=none abi-class=none\n",
            "row reference kind=reference support=required target-class=none abi-class=none\nrow reference kind=reference support=required target-class=none abi-class=none\n",
        );
        let error = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            &duplicate,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .expect_err("duplicate policy row must fail before the join");
        assert_eq!(error.reason, "policy_not_canonical");
    }

    #[test]
    fn abi_target_matrix_rejects_torn_or_misindexed_observations() {
        let parsed = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 1)
            .expect("checked-in fixture is a complete one-target observation");
        let row = parsed
            .get("abi-layout:target:0001")
            .expect("opaque first target is present");
        assert_eq!(row.abi_class, "lp64-le");

        let mismatch = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 2)
            .expect_err("one layout cannot silently stand in for two certified targets");
        assert_eq!(mismatch.reason, "abi_target_matrix_mismatch");

        let torn = &TEST_ABI_TARGET_LAYOUT[..TEST_ABI_TARGET_LAYOUT.len() / 2];
        let torn_error =
            parse_abi_target_layout(torn, 1).expect_err("a torn table has no authority");
        assert_eq!(torn_error.reason, "abi_target_layout_invalid");
    }

    #[test]
    fn olean_ilean_inventory_model() {
        let abi = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 1)
            .expect("ABI observation joins format targets");
        let parsed = parse_olean_ilean_format(TEST_OLEAN_ILEAN_FORMAT, &abi)
            .expect("checked-in exact-format table validates");
        assert_eq!(parsed.len(), 2);
        assert_eq!(
            parsed
                .get("artifact-format:ilean")
                .expect("ILEAN section")
                .abi_class,
            None
        );
        assert_eq!(
            parsed
                .get("artifact-format:olean:target:0001")
                .expect("OLEAN section")
                .abi_class
                .as_deref(),
            Some("lp64-le")
        );

        let first = "row field:0000 category=field";
        let second = "row field:0001 category=field";
        let mut lines: Vec<_> = TEST_OLEAN_ILEAN_FORMAT
            .lines()
            .map(str::to_string)
            .collect();
        let first_index = lines
            .iter()
            .position(|line| line.starts_with(first))
            .expect("first field");
        let second_index = lines
            .iter()
            .position(|line| line.starts_with(second))
            .expect("second field");
        lines.swap(first_index, second_index);
        let reordered = reroot_format_table(&format!("{}\n", lines.join("\n")), "ilean");
        let error = parse_olean_ilean_format(&reordered, &abi)
            .expect_err("field-order mutant must be rejected after roots are recomputed");
        assert_eq!(error.reason, "olean_ilean_format_invalid");
    }

    #[test]
    fn compact_encoding_contract() {
        let abi = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 1).unwrap();
        for category in ["decls", "producer"] {
            let mutated = TEST_OLEAN_ILEAN_FORMAT.replace(
                &format!(" category={category} "),
                &format!(" category={category}-mutant "),
            );
            let rerooted = reroot_format_table(&mutated, "ilean");
            let error = parse_olean_ilean_format(&rerooted, &abi)
                .expect_err("removing an ILEAN compact-format category must fail");
            assert_eq!(error.reason, "olean_ilean_format_invalid");
            assert!(error.detail.contains("exactness categories"));
        }

        let mutated = TEST_OLEAN_ILEAN_FORMAT.replacen(
            "row scalar-encoding category=scalar ",
            "row scalar-encoding category=scalar-mutant ",
            1,
        );
        let rerooted = reroot_format_table(&mutated, "olean:target:0001");
        let error = parse_olean_ilean_format(&rerooted, &abi)
            .expect_err("removing the compact scalar contract must fail");
        assert_eq!(error.reason, "olean_ilean_format_invalid");
        assert!(error.detail.contains("exactness categories"));
    }

    #[test]
    fn relocation_and_sharing_contract() {
        let abi = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 1).unwrap();
        let without_relocation = TEST_OLEAN_ILEAN_FORMAT
            .replace(" category=relocation ", " category=relocation-mutant ");
        let rerooted = reroot_format_table(&without_relocation, "olean:target:0001");
        let error = parse_olean_ilean_format(&rerooted, &abi)
            .expect_err("relocation category loss must fail with internally valid roots");
        assert_eq!(error.reason, "olean_ilean_format_invalid");

        let without_sharing =
            TEST_OLEAN_ILEAN_FORMAT.replace(" category=sharing ", " category=sharing-mutant ");
        let rerooted = reroot_format_table(&without_sharing, "olean:target:0001");
        let error = parse_olean_ilean_format(&rerooted, &abi)
            .expect_err("sharing category loss must fail with internally valid roots");
        assert_eq!(error.reason, "olean_ilean_format_invalid");
    }

    #[test]
    fn artifact_epoch_boundary() {
        let abi = parse_abi_target_layout(TEST_ABI_TARGET_LAYOUT, 1).unwrap();
        let ilean_accepts_unknown = TEST_OLEAN_ILEAN_FORMAT.replacen(
            "supported=5;unknown=reject",
            "supported=5;unknown=accept",
            1,
        );
        let rerooted = reroot_format_table(&ilean_accepts_unknown, "ilean");
        let error = parse_olean_ilean_format(&rerooted, &abi)
            .expect_err("unknown ILEAN epoch cannot be promoted by recomputing roots");
        assert_eq!(error.reason, "olean_ilean_format_invalid");

        let olean_accepts_unknown = TEST_OLEAN_ILEAN_FORMAT.replacen(
            "unknown=reject-incompatible-header",
            "unknown=accept",
            1,
        );
        let rerooted = reroot_format_table(&olean_accepts_unknown, "olean:target:0001");
        let error = parse_olean_ilean_format(&rerooted, &abi)
            .expect_err("unknown OLEAN epoch cannot be promoted by recomputing roots");
        assert_eq!(error.reason, "olean_ilean_format_invalid");
    }

    #[test]
    fn abi_policy_bijection_rejects_a_class_not_observed_by_the_extractor() {
        let wrong_class = REQUIRED_POLICY.replace("abi-class=lp64-le", "abi-class=llp64-le");
        let error = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            &wrong_class,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .expect_err("review policy cannot relabel the mechanically observed ABI");
        assert_eq!(error.class, ErrorClass::Violation);
        assert_eq!(error.reason, "abi_policy_mismatch");
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
        let error = canonical_inventory_text(
            &oversized,
            SCHEMA_DEFINITION,
            REQUIRED_POLICY,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
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

        let canonical = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            REQUIRED_POLICY,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
        .unwrap();
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
    fn abi_source_candidate_is_typed_and_cannot_be_hidden_by_a_stable_inventory() {
        let root = fixture_root("abi-source-candidate", REQUIRED_POLICY);
        publish(&root).expect("baseline canonical inventory publishes");
        let stable = fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("read stable publication");
        write_new(
            &root.join(ABI_TARGET_LAYOUT_CANDIDATE_FILE),
            &TEST_ABI_TARGET_LAYOUT.as_bytes()[..TEST_ABI_TARGET_LAYOUT.len() / 2],
        );
        let error = consume(&root)
            .expect_err("leftover raw-table candidate must mask the older stable projection");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "stale_source_candidate");
        assert_eq!(
            fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("old projection remains intact"),
            stable
        );
    }

    #[test]
    fn format_source_candidate_is_typed_and_cannot_be_hidden_by_a_stable_inventory() {
        let root = fixture_root("format-source-candidate", REQUIRED_POLICY);
        publish(&root).expect("baseline canonical inventory publishes");
        let stable = fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("read stable publication");
        write_new(
            &root.join(OLEAN_ILEAN_FORMAT_CANDIDATE_FILE),
            &TEST_OLEAN_ILEAN_FORMAT.as_bytes()[..TEST_OLEAN_ILEAN_FORMAT.len() / 2],
        );
        let error = consume(&root)
            .expect_err("leftover format candidate must mask the older stable projection");
        assert_eq!(error.class, ErrorClass::Inconclusive);
        assert_eq!(error.reason, "stale_source_candidate");
        assert_eq!(error.path, OLEAN_ILEAN_FORMAT_CANDIDATE_FILE);
        assert_eq!(
            fs::read(root.join(CONTRACT_INVENTORY_FILE)).expect("old projection remains intact"),
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

        let ambiguous_policy = REQUIRED_POLICY.replace(
            "row target:0001 kind=target support=required target-class=certified abi-class=none",
            "row target:0001 kind=target support=required target-class=none abi-class=none",
        );
        let error = canonical_inventory_text(
            TEST_SUITE_LOCK,
            SCHEMA_DEFINITION,
            &ambiguous_policy,
            TEST_ABI_TARGET_LAYOUT,
            TEST_OLEAN_ILEAN_FORMAT,
            TEST_EXTERN_BUILTIN_ENVIRONMENT,
        )
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

#[cfg(test)]
const EXTERN_BUILTIN_MANIFEST_FIXTURE: &str =
    include_str!("../../../contracts/EXTERN_BUILTIN_ENVIRONMENT.txt");

#[test]
fn extern_builtin_census_model() {
    let parsed = parse_census_manifest(EXTERN_BUILTIN_MANIFEST_FIXTURE)
        .expect("checked-in census envelope is structurally total");
    assert_eq!(parsed.constant_count, 204_543);
    assert_eq!(parsed.extern_count, 954);
    assert_eq!(parsed.toolchain_api_count, 76_938);
    assert_eq!(parsed.library_code_count, 117_149);
    assert_eq!(parsed.user_facing_data_count, 10_456);
}

#[test]
fn reference_environment_walk_completeness() {
    let parsed = parse_census_manifest(EXTERN_BUILTIN_MANIFEST_FIXTURE)
        .expect("checked-in census envelope is structurally total");
    assert_eq!(parsed.module_count, 2_270);
    assert_eq!(parsed.attribute_count, 175);
    assert_eq!(
        parsed.toolchain_api_count + parsed.library_code_count + parsed.user_facing_data_count,
        parsed.constant_count
    );

    let unresolved =
        EXTERN_BUILTIN_MANIFEST_FIXTURE.replace("unresolved-count\t0", "unresolved-count\t1");
    let error = parse_census_manifest(&unresolved)
        .expect_err("an unresolved partition row cannot be authoritative");
    assert_eq!(error.reason, "census_manifest_incomplete");
}

#[test]
fn census_policy_bijection() {
    let dropped_partition = EXTERN_BUILTIN_MANIFEST_FIXTURE
        .replace("library-code-count\t117149", "library-code-count\t117148");
    let error = parse_census_manifest(&dropped_partition)
        .expect_err("partition counts must conserve the environment walk");
    assert_eq!(error.reason, "census_manifest_incomplete");
}

#[test]
fn oracle_only_census_boundary() {
    let parsed =
        parse_census_manifest(EXTERN_BUILTIN_MANIFEST_FIXTURE).expect("manifest is authoritative");
    assert!(!parsed.manifest_root.is_empty());
    assert!(
        EXTERN_BUILTIN_MANIFEST_FIXTURE.contains("extractor\tlean-reference-environment-walk-v2\n")
    );
    assert!(SCHEMA_DEFINITION.contains(
        "source-authority SUITE.lock,contracts/ABI_TARGET_LAYOUT.txt,contracts/OLEAN_ILEAN_FORMAT.txt,contracts/EXTERN_BUILTIN_ENVIRONMENT.txt\n"
    ));
    assert!(!SCHEMA_DEFINITION.contains(".elan"));
    assert!(!SCHEMA_DEFINITION.contains("lean --run"));
}
