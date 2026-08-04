//! Pinned `lean` / `leanc` / `lake` command-surface contract.
//!
//! This module consumes the mechanically generated
//! `contracts/CLI_LAKE_INVENTORY.txt` artifact. It owns only the compatibility
//! model and its evidence representation; it does not implement the three CLI
//! personalities or Lake's build engine.
//!
//! The boundary is intentionally sharp:
//!
//! * source facts, reviewed policy, normalized oracle transcripts, and their
//!   roots remain separate;
//! * `leanc` is recorded as an inherited compiler-delegation surface, not as a
//!   native copy of every flag exposed by the pinned Clang build;
//! * process cancellation and resource exhaustion are typed
//!   [`CliDisposition::Inconclusive`], never promoted to rejection; and
//! * semantic NDJSON excludes elapsed time and byte-volume telemetry.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

use fln_hash::domain::{Domain, hash};

pub const INVENTORY_SCHEMA: &str = "fln-cli-lake-inventory/1";
pub const POLICY_SCHEMA: &str = "fln-cli-lake-policy/1";
pub const TRANSCRIPT_SCHEMA: &str = "fln-cli-lake-transcripts/1";
pub const EMBEDDED_INVENTORY: &str = include_str!("../../../contracts/CLI_LAKE_INVENTORY.txt");
pub const EMBEDDED_POLICY: &str = include_str!("../../../ci/CLI_LAKE_POLICY.txt");

const RAW_DOMAIN: &str = "fln-cli-lake-raw/1";
const INVENTORY_DOMAIN: &str = "fln-cli-lake-inventory/1";
const EXPECTED_PROBES: &[&str] = &[
    "lean:help",
    "lean:version",
    "lean:short-version",
    "lean:githash",
    "lean:features",
    "lean:print-prefix",
    "lean:print-libdir",
    "lean:unknown-option",
    "lean:malformed-timeout",
    "lean:stdin-success",
    "lean:json-error",
    "lake:usage",
    "lake:help",
    "lake:help-build",
    "lake:help-query",
    "lake:help-env",
    "lake:version",
    "lake:unknown-command",
    "lake:unknown-option",
    "lake:missing-dir-value",
    "lake:missing-root",
    "lake:json-help",
    "leanc:help",
    "leanc:version",
    "leanc:unknown-option",
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CensusError {
    message: String,
}

impl CensusError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CensusError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl std::error::Error for CensusError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceIdentity {
    pub repo: String,
    pub tag: String,
    pub commit: String,
    pub tree: String,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SurfaceKind {
    Command,
    ConfigDefault,
    Environment,
    Executable,
    Facet,
    LeancRule,
    Option,
    Outcome,
    Personality,
}

impl SurfaceKind {
    fn parse(value: &str) -> Result<Self, CensusError> {
        match value {
            "command" => Ok(Self::Command),
            "config-default" => Ok(Self::ConfigDefault),
            "environment" => Ok(Self::Environment),
            "executable" => Ok(Self::Executable),
            "facet" => Ok(Self::Facet),
            "leanc-rule" => Ok(Self::LeancRule),
            "option" => Ok(Self::Option),
            "outcome" => Ok(Self::Outcome),
            "personality" => Ok(Self::Personality),
            other => Err(CensusError::new(format!(
                "unknown CLI/Lake surface kind {other:?}"
            ))),
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Command => "command",
            Self::ConfigDefault => "config-default",
            Self::Environment => "environment",
            Self::Executable => "executable",
            Self::Facet => "facet",
            Self::LeancRule => "leanc-rule",
            Self::Option => "option",
            Self::Outcome => "outcome",
            Self::Personality => "personality",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfacePolicy {
    pub support: String,
    pub comparison: String,
    pub precedence: String,
    pub channel: String,
    pub platform: String,
    pub authority: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Surface {
    pub key: String,
    pub kind: SurfaceKind,
    pub attributes: BTreeMap<String, String>,
    pub source: String,
    pub evidence: String,
    pub policy: SurfacePolicy,
}

impl Surface {
    pub fn attribute(&self, name: &str) -> Option<&str> {
        self.attributes.get(name).map(String::as_str)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceBinding {
    pub path: String,
    pub hash: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProbeTranscript {
    pub key: String,
    pub personality: String,
    pub argv: String,
    pub stdin_hash: String,
    pub exit_code: i32,
    pub stdout_hash: String,
    pub stderr_hash: String,
    pub stdout_bytes: usize,
    pub stderr_bytes: usize,
    pub channel: String,
    pub normalizer: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CliLakeInventory {
    pub reference: ReferenceIdentity,
    pub platform: String,
    pub surfaces: Vec<Surface>,
    pub transcripts: Vec<ProbeTranscript>,
    pub sources: Vec<SourceBinding>,
    pub raw_root: String,
    pub policy_root: String,
    pub transcript_root: String,
    pub inventory_root: String,
}

impl CliLakeInventory {
    pub fn load_embedded() -> Result<Self, CensusError> {
        Self::parse(EMBEDDED_INVENTORY, EMBEDDED_POLICY)
    }

    pub fn parse(inventory: &str, policy: &str) -> Result<Self, CensusError> {
        let lines = inventory.lines().collect::<Vec<_>>();
        if lines.first().copied() != Some(&format!("schema {INVENTORY_SCHEMA}")) {
            return Err(CensusError::new("CLI/Lake inventory schema mismatch"));
        }
        if lines.len() < 16 {
            return Err(CensusError::new("CLI/Lake inventory is truncated"));
        }
        let raw_begin = unique_line(&lines, "raw-begin")?;
        let raw_end = unique_line(&lines, "raw-end")?;
        if raw_end <= raw_begin + 1 {
            return Err(CensusError::new("CLI/Lake raw census is empty"));
        }
        let raw = &lines[raw_begin + 1..raw_end];
        let raw_root = single_value_after(&lines, "raw-root")?;
        let policy_root = single_value_after(&lines, "policy-root")?;
        let transcript_root = single_value_after(&lines, "transcript-root")?;
        let inventory_root = single_value_after(&lines, "inventory-root")?;
        let computed_raw = framed_hash(RAW_DOMAIN, raw.iter().copied());
        if raw_root != computed_raw {
            return Err(CensusError::new(format!(
                "CLI/Lake raw root mismatch: recorded {raw_root}, computed {computed_raw}"
            )));
        }
        let inventory_root_index = unique_prefix_line(&lines, "inventory-root ")?;
        if inventory_root_index + 1 != lines.len() {
            return Err(CensusError::new(
                "CLI/Lake inventory root is not the final line",
            ));
        }
        let computed_inventory = framed_hash(
            INVENTORY_DOMAIN,
            lines[..inventory_root_index].iter().copied(),
        );
        if inventory_root != computed_inventory {
            return Err(CensusError::new(format!(
                "CLI/Lake inventory root mismatch: recorded {inventory_root}, \
                 computed {computed_inventory}"
            )));
        }
        let parsed_policy = parse_policy(policy)?;
        let computed_policy = framed_hash(POLICY_SCHEMA, policy.lines());
        if policy_root != computed_policy {
            return Err(CensusError::new(format!(
                "CLI/Lake policy root mismatch: recorded {policy_root}, \
                 computed {computed_policy}"
            )));
        }
        let platform = single_value_after(&lines[..raw_begin], "platform")?;
        let expected_surface_count =
            parse_usize(single_value_after(&lines[..raw_begin], "surface-count")?)?;
        let expected_transcript_count =
            parse_usize(single_value_after(&lines[..raw_begin], "transcript-count")?)?;
        let expected_source_count =
            parse_usize(single_value_after(&lines[..raw_begin], "source-count")?)?;

        let mut reference = None;
        let mut sources = Vec::new();
        let mut surfaces_without_policy = Vec::new();
        let mut transcripts = Vec::new();
        let mut transcript_lines = Vec::new();
        let mut last_surface_key = String::new();
        for line in raw {
            if let Some(rest) = line.strip_prefix("reference ") {
                if reference.is_some() {
                    return Err(CensusError::new("duplicate Reference row"));
                }
                let fields = parse_fields(rest)?;
                reference = Some(ReferenceIdentity {
                    repo: required(&fields, "repo")?.to_string(),
                    tag: required(&fields, "tag")?.to_string(),
                    commit: required(&fields, "commit")?.to_string(),
                    tree: required(&fields, "tree")?.to_string(),
                });
            } else if let Some(rest) = line.strip_prefix("source ") {
                let fields = parse_fields(rest)?;
                sources.push(SourceBinding {
                    path: required(&fields, "path")?.to_string(),
                    hash: required(&fields, "hash")?.to_string(),
                });
            } else if let Some(rest) = line.strip_prefix("surface ") {
                let mut fields = parse_fields(rest)?;
                let key = take_required(&mut fields, "key")?;
                if key <= last_surface_key {
                    return Err(CensusError::new(
                        "CLI/Lake surface keys are not strictly sorted",
                    ));
                }
                last_surface_key = key.clone();
                let kind = SurfaceKind::parse(&take_required(&mut fields, "kind")?)?;
                let source = take_required(&mut fields, "source")?;
                let evidence = take_required(&mut fields, "evidence")?;
                surfaces_without_policy.push((key, kind, fields, source, evidence));
            } else if let Some(rest) = line.strip_prefix("transcript ") {
                transcript_lines.push(format!("probe {rest}"));
                transcripts.push(parse_transcript(rest)?);
            } else {
                return Err(CensusError::new(format!(
                    "unknown CLI/Lake raw row {line:?}"
                )));
            }
        }
        let reference = reference.ok_or_else(|| CensusError::new("missing Reference row"))?;
        validate_reference(&reference)?;
        if sources.len() != expected_source_count {
            return Err(CensusError::new(format!(
                "source count mismatch: parsed {}, declared {expected_source_count}",
                sources.len()
            )));
        }
        if surfaces_without_policy.len() != expected_surface_count {
            return Err(CensusError::new(format!(
                "surface count mismatch: parsed {}, declared {expected_surface_count}",
                surfaces_without_policy.len()
            )));
        }
        if transcripts.len() != expected_transcript_count {
            return Err(CensusError::new(format!(
                "transcript count mismatch: parsed {}, declared {expected_transcript_count}",
                transcripts.len()
            )));
        }
        let computed_transcript = framed_hash(
            TRANSCRIPT_SCHEMA,
            transcript_lines.iter().map(String::as_str),
        );
        if transcript_root != computed_transcript {
            return Err(CensusError::new(format!(
                "transcript root mismatch: recorded {transcript_root}, \
                 computed {computed_transcript}"
            )));
        }
        let actual_probe_keys = transcripts
            .iter()
            .map(|probe| probe.key.as_str())
            .collect::<Vec<_>>();
        if actual_probe_keys != EXPECTED_PROBES {
            return Err(CensusError::new(
                "real CLI probe set/order does not match the compiled complete matrix",
            ));
        }

        let raw_keys = surfaces_without_policy
            .iter()
            .map(|(key, ..)| key.clone())
            .collect::<BTreeSet<_>>();
        let policy_keys = parsed_policy.keys().cloned().collect::<BTreeSet<_>>();
        if raw_keys != policy_keys {
            return Err(CensusError::new(format!(
                "surface/policy bijection mismatch: missing={:?} stale={:?}",
                raw_keys.difference(&policy_keys).collect::<Vec<_>>(),
                policy_keys.difference(&raw_keys).collect::<Vec<_>>()
            )));
        }
        let surfaces = surfaces_without_policy
            .into_iter()
            .map(|(key, kind, attributes, source, evidence)| {
                let policy = parsed_policy.get(&key).cloned().ok_or_else(|| {
                    CensusError::new(format!("policy vanished for surface {key}"))
                })?;
                Ok(Surface {
                    key,
                    kind,
                    attributes,
                    source,
                    evidence,
                    policy,
                })
            })
            .collect::<Result<Vec<_>, CensusError>>()?;
        validate_required_laws(&surfaces)?;
        Ok(Self {
            reference,
            platform: platform.to_string(),
            surfaces,
            transcripts,
            sources,
            raw_root: raw_root.to_string(),
            policy_root: policy_root.to_string(),
            transcript_root: transcript_root.to_string(),
            inventory_root: inventory_root.to_string(),
        })
    }

    pub fn surface(&self, key: &str) -> Option<&Surface> {
        self.surfaces
            .binary_search_by_key(&key, |surface| surface.key.as_str())
            .ok()
            .map(|index| &self.surfaces[index])
    }

    pub fn transcript(&self, key: &str) -> Option<&ProbeTranscript> {
        self.transcripts.iter().find(|probe| probe.key == key)
    }

    pub fn surfaces_of_kind(&self, kind: SurfaceKind) -> impl Iterator<Item = &Surface> {
        self.surfaces
            .iter()
            .filter(move |surface| surface.kind == kind)
    }

    pub fn facet_names(&self, target_kind: &str) -> BTreeSet<&str> {
        self.surfaces_of_kind(SurfaceKind::Facet)
            .filter(|surface| surface.attribute("target-kind") == Some(target_kind))
            .filter_map(|surface| surface.attribute("name"))
            .collect()
    }

    pub fn validate_workspace_sources(&self, root: &Path) -> Result<(), CensusError> {
        if self.sources.is_empty() {
            return Err(CensusError::new(
                "zero source bindings cannot establish a source-derived census",
            ));
        }
        for source in &self.sources {
            let path = checked_source_path(root, &source.path)?;
            let bytes = std::fs::read(&path).map_err(|error| {
                CensusError::new(format!("read source binding {}: {error}", path.display()))
            })?;
            let actual = fnv(&bytes);
            if actual != source.hash {
                return Err(CensusError::new(format!(
                    "source binding drifted for {}: recorded {}, actual {actual}",
                    source.path, source.hash
                )));
            }
        }
        Ok(())
    }
}

fn validate_reference(reference: &ReferenceIdentity) -> Result<(), CensusError> {
    if reference.repo != "leanprover/lean4"
        || !reference.tag.starts_with('v')
        || !is_lower_hex(&reference.commit, 40)
        || !is_lower_hex(&reference.tree, 40)
    {
        return Err(CensusError::new(
            "CLI/Lake Reference identity is malformed or names the wrong repository",
        ));
    }
    Ok(())
}

fn validate_required_laws(surfaces: &[Surface]) -> Result<(), CensusError> {
    let by_key = surfaces
        .iter()
        .map(|surface| (surface.key.as_str(), surface))
        .collect::<BTreeMap<_, _>>();
    for personality in ["lean", "leanc", "lake"] {
        if !by_key.contains_key(format!("personality:{personality}").as_str()) {
            return Err(CensusError::new(format!(
                "missing CLI personality {personality}"
            )));
        }
        let executable = by_key
            .get(format!("executable:{personality}").as_str())
            .ok_or_else(|| CensusError::new(format!("missing executable {personality}")))?;
        if executable.policy.authority != "epoch-manifest"
            || executable.policy.platform != "linux-x86_64"
        {
            return Err(CensusError::new(format!(
                "executable {personality} lost its epoch/platform authority"
            )));
        }
    }
    for (name, disposition) in [
        ("cancelled", "inconclusive"),
        ("resource-exhausted", "inconclusive"),
        ("internal-fault", "internal-fault"),
    ] {
        let row = by_key
            .get(format!("outcome:{name}").as_str())
            .ok_or_else(|| CensusError::new(format!("missing outcome law {name}")))?;
        if row.attribute("disposition") != Some(disposition) {
            return Err(CensusError::new(format!(
                "outcome {name} is not typed {disposition}"
            )));
        }
    }
    let leanc_rules = surfaces
        .iter()
        .filter(|surface| surface.kind == SurfaceKind::LeancRule)
        .collect::<Vec<_>>();
    if leanc_rules.len() < 5
        || leanc_rules.iter().any(|surface| {
            surface.policy.authority != "inherited"
                || surface.policy.channel != "delegated"
                || surface.policy.platform != "linux-x86_64"
        })
    {
        return Err(CensusError::new(
            "leanc delegation is incomplete or overclaims native authority",
        ));
    }
    Ok(())
}

fn checked_source_path(root: &Path, relative: &str) -> Result<PathBuf, CensusError> {
    let path = Path::new(relative);
    if path.is_absolute()
        || path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        return Err(CensusError::new(format!(
            "source path escapes workspace: {relative:?}"
        )));
    }
    Ok(root.join(path))
}

fn parse_transcript(rest: &str) -> Result<ProbeTranscript, CensusError> {
    let fields = parse_fields(rest)?;
    let transcript = ProbeTranscript {
        key: required(&fields, "key")?.to_string(),
        personality: required(&fields, "personality")?.to_string(),
        argv: required(&fields, "argv")?.to_string(),
        stdin_hash: required(&fields, "stdin")?.to_string(),
        exit_code: required(&fields, "exit")?
            .parse()
            .map_err(|_| CensusError::new("probe exit is not an i32"))?,
        stdout_hash: required(&fields, "stdout")?.to_string(),
        stderr_hash: required(&fields, "stderr")?.to_string(),
        stdout_bytes: parse_usize(required(&fields, "stdout-bytes")?)?,
        stderr_bytes: parse_usize(required(&fields, "stderr-bytes")?)?,
        channel: required(&fields, "channel")?.to_string(),
        normalizer: required(&fields, "normalizer")?.to_string(),
    };
    let expected = [
        "argv",
        "channel",
        "exit",
        "key",
        "normalizer",
        "personality",
        "stderr",
        "stderr-bytes",
        "stdin",
        "stdout",
        "stdout-bytes",
    ]
    .into_iter()
    .collect::<BTreeSet<_>>();
    let actual = fields.keys().map(String::as_str).collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(CensusError::new("probe transcript has the wrong field set"));
    }
    if !matches!(transcript.personality.as_str(), "lean" | "leanc" | "lake")
        || !matches!(
            transcript.channel.as_str(),
            "stdout" | "stderr" | "split" | "silent"
        )
        || transcript.normalizer != "paths-crlf-ansi-v1"
        || !is_fnv(&transcript.stdout_hash)
        || !is_fnv(&transcript.stderr_hash)
    {
        return Err(CensusError::new(format!(
            "probe transcript {} has an invalid personality/channel/hash/normalizer",
            transcript.key
        )));
    }
    Ok(transcript)
}

fn parse_policy(text: &str) -> Result<BTreeMap<String, SurfacePolicy>, CensusError> {
    let mut lines = text.lines();
    if lines.next() != Some(&format!("schema {POLICY_SCHEMA}")) {
        return Err(CensusError::new("CLI/Lake policy schema mismatch"));
    }
    let mut rows = BTreeMap::new();
    let mut previous = String::new();
    for (offset, line) in lines.enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let rest = line
            .strip_prefix("row ")
            .ok_or_else(|| CensusError::new(format!("policy line {} is not a row", offset + 2)))?;
        let mut tokens = rest.split_whitespace();
        let encoded_key = tokens
            .next()
            .ok_or_else(|| CensusError::new("policy row has no key"))?;
        let key = decode(encoded_key)?;
        if key <= previous {
            return Err(CensusError::new(
                "CLI/Lake policy keys are not strictly sorted",
            ));
        }
        previous = key.clone();
        let fields = parse_fields(&tokens.collect::<Vec<_>>().join(" "))?;
        let expected = [
            "authority",
            "channel",
            "comparison",
            "platform",
            "precedence",
            "support",
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        let actual = fields.keys().map(String::as_str).collect::<BTreeSet<_>>();
        if actual != expected {
            return Err(CensusError::new(format!(
                "policy row {key} has the wrong field set"
            )));
        }
        let row = SurfacePolicy {
            support: required(&fields, "support")?.to_string(),
            comparison: required(&fields, "comparison")?.to_string(),
            precedence: required(&fields, "precedence")?.to_string(),
            channel: required(&fields, "channel")?.to_string(),
            platform: required(&fields, "platform")?.to_string(),
            authority: required(&fields, "authority")?.to_string(),
        };
        if !matches!(row.support.as_str(), "required" | "optional")
            || !matches!(row.comparison.as_str(), "exact" | "normalized")
        {
            return Err(CensusError::new(format!(
                "policy row {key} has an unsupported class"
            )));
        }
        if rows.insert(key.clone(), row).is_some() {
            return Err(CensusError::new(format!("duplicate policy row {key}")));
        }
    }
    if rows.is_empty() {
        return Err(CensusError::new("CLI/Lake policy is empty"));
    }
    Ok(rows)
}

fn parse_fields(text: &str) -> Result<BTreeMap<String, String>, CensusError> {
    let mut fields = BTreeMap::new();
    for token in text.split_whitespace() {
        let (name, encoded) = token
            .split_once('=')
            .ok_or_else(|| CensusError::new(format!("malformed key=value field {token:?}")))?;
        if name.is_empty() || encoded.is_empty() || encoded.contains('=') {
            return Err(CensusError::new(format!(
                "noncanonical key=value field {token:?}"
            )));
        }
        let value = decode(encoded)?;
        if fields.insert(name.to_string(), value).is_some() {
            return Err(CensusError::new(format!("duplicate field {name:?}")));
        }
    }
    Ok(fields)
}

fn required<'a>(fields: &'a BTreeMap<String, String>, name: &str) -> Result<&'a str, CensusError> {
    fields
        .get(name)
        .map(String::as_str)
        .ok_or_else(|| CensusError::new(format!("required field {name:?} is absent")))
}

fn take_required(fields: &mut BTreeMap<String, String>, name: &str) -> Result<String, CensusError> {
    fields
        .remove(name)
        .ok_or_else(|| CensusError::new(format!("required field {name:?} is absent")))
}

fn decode(value: &str) -> Result<String, CensusError> {
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] == b'%' {
            let hi = *bytes
                .get(index + 1)
                .ok_or_else(|| CensusError::new("truncated percent escape"))?;
            let lo = *bytes
                .get(index + 2)
                .ok_or_else(|| CensusError::new("truncated percent escape"))?;
            decoded.push(hex_value(hi)? << 4 | hex_value(lo)?);
            index += 3;
        } else {
            decoded.push(bytes[index]);
            index += 1;
        }
    }
    String::from_utf8(decoded).map_err(|_| CensusError::new("percent-decoded field is not UTF-8"))
}

fn hex_value(byte: u8) -> Result<u8, CensusError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(CensusError::new(
            "percent escape is not uppercase hexadecimal",
        )),
    }
}

fn unique_line(lines: &[&str], needle: &str) -> Result<usize, CensusError> {
    let matches = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == needle).then_some(index))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(CensusError::new(format!(
            "expected exactly one {needle:?} line, found {}",
            matches.len()
        ))),
    }
}

fn unique_prefix_line(lines: &[&str], prefix: &str) -> Result<usize, CensusError> {
    let matches = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| line.starts_with(prefix).then_some(index))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(CensusError::new(format!(
            "expected exactly one line starting {prefix:?}, found {}",
            matches.len()
        ))),
    }
}

fn single_value_after<'a>(lines: &'a [&str], key: &str) -> Result<&'a str, CensusError> {
    let prefix = format!("{key} ");
    let matches = lines
        .iter()
        .filter_map(|line| line.strip_prefix(&prefix))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [value] if !value.is_empty() && !value.contains(' ') => Ok(*value),
        _ => Err(CensusError::new(format!(
            "expected exactly one scalar {key} row"
        ))),
    }
}

fn parse_usize(value: &str) -> Result<usize, CensusError> {
    value
        .parse()
        .map_err(|_| CensusError::new(format!("{value:?} is not a usize")))
}

fn is_lower_hex(value: &str, len: usize) -> bool {
    value.len() == len
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn is_fnv(value: &str) -> bool {
    value
        .strip_prefix("fnv1a64:")
        .is_some_and(|hex| is_lower_hex(hex, 16))
}

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn framed_hash<'a>(domain: &'a str, lines: impl IntoIterator<Item = &'a str>) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(lines) {
        let bytes = field.as_bytes();
        payload.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
        payload.extend_from_slice(bytes);
    }
    fnv(&payload)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CliPersonality {
    Lean,
    Leanc,
    Lake,
}

impl CliPersonality {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Lean => "lean",
            Self::Leanc => "leanc",
            Self::Lake => "lake",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CliModelError {
    UnknownOption(String),
    MissingOptionArgument(String),
    UnknownCommand(String),
    UnexpectedArgument(String),
    UnknownFacet { target_kind: String, facet: String },
    MalformedJsonEnvironment(String),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvocationProjection {
    pub personality: CliPersonality,
    pub command: Option<String>,
    pub options: BTreeMap<String, String>,
    pub positionals: Vec<String>,
    pub forwarded: Vec<String>,
}

pub fn project_arguments(
    inventory: &CliLakeInventory,
    personality: CliPersonality,
    args: &[&str],
) -> Result<InvocationProjection, CliModelError> {
    match personality {
        CliPersonality::Lean => project_lean(inventory, args),
        CliPersonality::Lake => project_lake(inventory, args),
        CliPersonality::Leanc => Ok(InvocationProjection {
            personality,
            command: Some("delegate".to_string()),
            options: BTreeMap::new(),
            positionals: Vec::new(),
            forwarded: args.iter().map(|value| (*value).to_string()).collect(),
        }),
    }
}

fn project_lean(
    inventory: &CliLakeInventory,
    args: &[&str],
) -> Result<InvocationProjection, CliModelError> {
    let mut projection = InvocationProjection {
        personality: CliPersonality::Lean,
        command: None,
        options: BTreeMap::new(),
        positionals: Vec::new(),
        forwarded: Vec::new(),
    };
    let mut index = 0;
    while index < args.len() {
        let argument = args[index];
        if projection.command.as_deref() == Some("run") {
            projection.forwarded.push(argument.to_string());
            index += 1;
            continue;
        }
        if argument == "--run" {
            projection
                .options
                .insert("--run".to_string(), "true".to_string());
            projection.command = Some("run".to_string());
            index += 1;
            continue;
        }
        if argument.starts_with('-') && argument != "-" {
            let (spelling, inline_value) = split_option(argument);
            let key = format!("option:lean:{spelling}");
            let surface = inventory
                .surface(&key)
                .ok_or_else(|| CliModelError::UnknownOption(spelling.to_string()))?;
            let value = option_value(surface, inline_value, args, &mut index)?;
            projection.options.insert(spelling.to_string(), value);
        } else {
            projection.positionals.push(argument.to_string());
        }
        index += 1;
    }
    if projection.command.is_none() {
        projection.command = Some("frontend".to_string());
    }
    Ok(projection)
}

fn project_lake(
    inventory: &CliLakeInventory,
    args: &[&str],
) -> Result<InvocationProjection, CliModelError> {
    let mut projection = InvocationProjection {
        personality: CliPersonality::Lake,
        command: None,
        options: BTreeMap::new(),
        positionals: Vec::new(),
        forwarded: Vec::new(),
    };
    let mut index = 0;
    while index < args.len() {
        let argument = args[index];
        if argument == "--" {
            projection
                .forwarded
                .extend(args[index + 1..].iter().map(|value| (*value).to_string()));
            break;
        }
        if argument.starts_with('-') && argument != "-" {
            let (spelling, inline_value) = split_option(argument);
            let key = format!("option:lake:{spelling}");
            let surface = inventory
                .surface(&key)
                .ok_or_else(|| CliModelError::UnknownOption(spelling.to_string()))?;
            let value = option_value(surface, inline_value, args, &mut index)?;
            projection.options.insert(spelling.to_string(), value);
        } else if projection.command.is_none() {
            let key = format!("command:lake:{argument}");
            if inventory.surface(&key).is_none() {
                return Err(CliModelError::UnknownCommand(argument.to_string()));
            }
            projection.command = Some(argument.to_string());
        } else {
            projection.positionals.push(argument.to_string());
        }
        index += 1;
    }
    Ok(projection)
}

fn split_option(argument: &str) -> (&str, Option<&str>) {
    argument
        .split_once('=')
        .map_or((argument, None), |(name, value)| (name, Some(value)))
}

fn option_value(
    surface: &Surface,
    inline: Option<&str>,
    args: &[&str],
    index: &mut usize,
) -> Result<String, CliModelError> {
    let required = matches!(surface.attribute("argument"), Some("required" | "optional"));
    if let Some(value) = inline {
        return Ok(value.to_string());
    }
    if required {
        let next = args
            .get(*index + 1)
            .ok_or_else(|| CliModelError::MissingOptionArgument(surface.key.clone()))?;
        *index += 1;
        Ok((*next).to_string())
    } else {
        Ok("true".to_string())
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ValueSource {
    Default,
    Environment,
    Config,
    Cli,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedValue {
    pub value: String,
    pub source: ValueSource,
}

pub fn resolve_value(
    cli: Option<&str>,
    config: Option<&str>,
    environment: Option<&str>,
    default: &str,
) -> ResolvedValue {
    if let Some(value) = cli {
        ResolvedValue {
            value: value.to_string(),
            source: ValueSource::Cli,
        }
    } else if let Some(value) = config {
        ResolvedValue {
            value: value.to_string(),
            source: ValueSource::Config,
        }
    } else if let Some(value) = environment {
        ResolvedValue {
            value: value.to_string(),
            source: ValueSource::Environment,
        }
    } else {
        ResolvedValue {
            value: default.to_string(),
            source: ValueSource::Default,
        }
    }
}

pub fn parse_package_url_map(value: &str) -> Result<BTreeMap<String, String>, CliModelError> {
    let trimmed = value.trim();
    if trimmed == "{}" {
        return Ok(BTreeMap::new());
    }
    if !trimmed.starts_with('{') || !trimmed.ends_with('}') {
        return Err(CliModelError::MalformedJsonEnvironment(
            "LAKE_PKG_URL_MAP".to_string(),
        ));
    }
    let inner = &trimmed[1..trimmed.len() - 1];
    let mut result = BTreeMap::new();
    for entry in inner.split(',') {
        let (raw_key, raw_value) = entry.split_once(':').ok_or_else(|| {
            CliModelError::MalformedJsonEnvironment("LAKE_PKG_URL_MAP".to_string())
        })?;
        let key = simple_json_string(raw_key)?;
        let value = simple_json_string(raw_value)?;
        if result.insert(key, value).is_some() {
            return Err(CliModelError::MalformedJsonEnvironment(
                "LAKE_PKG_URL_MAP".to_string(),
            ));
        }
    }
    Ok(result)
}

fn simple_json_string(value: &str) -> Result<String, CliModelError> {
    let value = value.trim();
    if value.len() < 2
        || !value.starts_with('"')
        || !value.ends_with('"')
        || value[1..value.len() - 1].contains(['"', '\\'])
    {
        return Err(CliModelError::MalformedJsonEnvironment(
            "LAKE_PKG_URL_MAP".to_string(),
        ));
    }
    Ok(value[1..value.len() - 1].to_string())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LakeTargetKind {
    Package,
    Module,
    File,
    Named,
    RootFacet,
}

impl LakeTargetKind {
    const fn inventory_kind(self) -> Option<&'static str> {
        match self {
            Self::Package => Some("Package"),
            Self::Module => Some("Module"),
            Self::File | Self::Named | Self::RootFacet => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LakeTargetSpec {
    pub package: Option<String>,
    pub target: String,
    pub facet: Option<String>,
    pub kind: LakeTargetKind,
}

pub fn parse_lake_target_spec(
    inventory: &CliLakeInventory,
    value: &str,
) -> Result<LakeTargetSpec, CliModelError> {
    let (body, facet) = value
        .rsplit_once(':')
        .map_or((value, None), |(left, right)| (left, Some(right)));
    let (package, target) = if let Some(rest) = body.strip_prefix('@') {
        match rest.split_once('/') {
            Some((package, target)) => (Some(package.to_string()), target),
            None => (Some(rest.to_string()), ""),
        }
    } else {
        (None, body)
    };
    let kind = if body.is_empty() && facet.is_some() {
        LakeTargetKind::RootFacet
    } else if target.starts_with('+') {
        LakeTargetKind::Module
    } else if target.ends_with(".lean") {
        LakeTargetKind::File
    } else if package.is_some() && target.is_empty() {
        LakeTargetKind::Package
    } else {
        LakeTargetKind::Named
    };
    if let Some(facet) = facet {
        if facet.is_empty() {
            return Err(CliModelError::UnknownFacet {
                target_kind: format!("{kind:?}"),
                facet: facet.to_string(),
            });
        }
        let admitted = kind.inventory_kind().map_or_else(
            || {
                inventory
                    .surfaces_of_kind(SurfaceKind::Facet)
                    .filter_map(|surface| surface.attribute("name"))
                    .any(|name| name == facet)
            },
            |target_kind| inventory.facet_names(target_kind).contains(facet),
        );
        if !admitted {
            return Err(CliModelError::UnknownFacet {
                target_kind: format!("{kind:?}"),
                facet: facet.to_string(),
            });
        }
    }
    Ok(LakeTargetSpec {
        package,
        target: target.strip_prefix('+').unwrap_or(target).to_string(),
        facet: facet.map(str::to_string),
        kind,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProcessOutcome {
    Exited(i32),
    Cancelled,
    TimedOut,
    OutputBudgetExceeded,
    SpawnFault,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CliDisposition {
    Accepted,
    Rejected,
    Inconclusive,
    InternalFault,
}

impl CliDisposition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Inconclusive => "inconclusive",
            Self::InternalFault => "internal-fault",
        }
    }
}

pub const fn classify_process(outcome: ProcessOutcome) -> CliDisposition {
    match outcome {
        ProcessOutcome::Exited(0) => CliDisposition::Accepted,
        ProcessOutcome::Exited(_) => CliDisposition::Rejected,
        ProcessOutcome::Cancelled
        | ProcessOutcome::TimedOut
        | ProcessOutcome::OutputBudgetExceeded => CliDisposition::Inconclusive,
        ProcessOutcome::SpawnFault => CliDisposition::InternalFault,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticRecord {
    pub sequence: u64,
    pub epoch_id: String,
    pub probe_id: String,
    pub personality: String,
    pub expected_exit: i32,
    pub actual_exit: i32,
    pub expected_stdout: String,
    pub actual_stdout: String,
    pub expected_stderr: String,
    pub actual_stderr: String,
    pub authority_root: String,
    pub disposition: CliDisposition,
    pub final_state: String,
}

impl SemanticRecord {
    pub fn render(&self) -> String {
        format!(
            "{{\"schema\":\"fln.cli-lake.semantic/1\",\"sequence\":{},\
             \"epoch_id\":{},\"probe_id\":{},\"personality\":{},\
             \"expected_exit\":{},\"actual_exit\":{},\
             \"expected_stdout\":{},\"actual_stdout\":{},\
             \"expected_stderr\":{},\"actual_stderr\":{},\
             \"authority_root\":{},\"disposition\":{},\"final_state\":{}}}",
            self.sequence,
            json_quote(&self.epoch_id),
            json_quote(&self.probe_id),
            json_quote(&self.personality),
            self.expected_exit,
            self.actual_exit,
            json_quote(&self.expected_stdout),
            json_quote(&self.actual_stdout),
            json_quote(&self.expected_stderr),
            json_quote(&self.actual_stderr),
            json_quote(&self.authority_root),
            json_quote(self.disposition.as_str()),
            json_quote(&self.final_state),
        )
    }

    pub fn parse(line: &str) -> Result<Self, CensusError> {
        let fields = parse_json_object(line)?;
        exact_json_fields(
            &fields,
            &[
                "schema",
                "sequence",
                "epoch_id",
                "probe_id",
                "personality",
                "expected_exit",
                "actual_exit",
                "expected_stdout",
                "actual_stdout",
                "expected_stderr",
                "actual_stderr",
                "authority_root",
                "disposition",
                "final_state",
            ],
        )?;
        if json_string(&fields, "schema")? != "fln.cli-lake.semantic/1" {
            return Err(CensusError::new("semantic NDJSON schema mismatch"));
        }
        let disposition = match json_string(&fields, "disposition")? {
            "accepted" => CliDisposition::Accepted,
            "rejected" => CliDisposition::Rejected,
            "inconclusive" => CliDisposition::Inconclusive,
            "internal-fault" => CliDisposition::InternalFault,
            other => {
                return Err(CensusError::new(format!(
                    "unknown semantic disposition {other:?}"
                )));
            }
        };
        let record = Self {
            sequence: json_u64(&fields, "sequence")?,
            epoch_id: json_string(&fields, "epoch_id")?.to_string(),
            probe_id: json_string(&fields, "probe_id")?.to_string(),
            personality: json_string(&fields, "personality")?.to_string(),
            expected_exit: json_i32(&fields, "expected_exit")?,
            actual_exit: json_i32(&fields, "actual_exit")?,
            expected_stdout: json_string(&fields, "expected_stdout")?.to_string(),
            actual_stdout: json_string(&fields, "actual_stdout")?.to_string(),
            expected_stderr: json_string(&fields, "expected_stderr")?.to_string(),
            actual_stderr: json_string(&fields, "actual_stderr")?.to_string(),
            authority_root: json_string(&fields, "authority_root")?.to_string(),
            disposition,
            final_state: json_string(&fields, "final_state")?.to_string(),
        };
        if record.render() != line {
            return Err(CensusError::new(
                "semantic NDJSON line is valid-shaped but noncanonical",
            ));
        }
        Ok(record)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TelemetryRecord {
    pub sequence: u64,
    pub probe_id: String,
    pub elapsed_micros: u64,
    pub output_bytes: u64,
}

impl TelemetryRecord {
    pub fn render(&self) -> String {
        format!(
            "{{\"schema\":\"fln.cli-lake.telemetry/1\",\"sequence\":{},\
             \"probe_id\":{},\"elapsed_micros\":{},\"output_bytes\":{}}}",
            self.sequence,
            json_quote(&self.probe_id),
            self.elapsed_micros,
            self.output_bytes,
        )
    }

    pub fn parse(line: &str) -> Result<Self, CensusError> {
        let fields = parse_json_object(line)?;
        exact_json_fields(
            &fields,
            &[
                "schema",
                "sequence",
                "probe_id",
                "elapsed_micros",
                "output_bytes",
            ],
        )?;
        if json_string(&fields, "schema")? != "fln.cli-lake.telemetry/1" {
            return Err(CensusError::new("telemetry NDJSON schema mismatch"));
        }
        let record = Self {
            sequence: json_u64(&fields, "sequence")?,
            probe_id: json_string(&fields, "probe_id")?.to_string(),
            elapsed_micros: json_u64(&fields, "elapsed_micros")?,
            output_bytes: json_u64(&fields, "output_bytes")?,
        };
        if record.render() != line {
            return Err(CensusError::new(
                "telemetry NDJSON line is valid-shaped but noncanonical",
            ));
        }
        Ok(record)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranscriptBundle {
    semantic: Vec<SemanticRecord>,
    telemetry: Vec<TelemetryRecord>,
}

impl TranscriptBundle {
    pub fn new(
        semantic: Vec<SemanticRecord>,
        telemetry: Vec<TelemetryRecord>,
    ) -> Result<Self, CensusError> {
        validate_sequence(semantic.iter().map(|record| record.sequence), "semantic")?;
        validate_sequence(telemetry.iter().map(|record| record.sequence), "telemetry")?;
        Ok(Self {
            semantic,
            telemetry,
        })
    }

    pub fn from_ndjson(semantic: &str, telemetry: &str) -> Result<Self, CensusError> {
        let semantic = parse_ndjson(semantic, SemanticRecord::parse)?;
        let telemetry = parse_ndjson(telemetry, TelemetryRecord::parse)?;
        Self::new(semantic, telemetry)
    }

    pub fn semantic_ndjson(&self) -> String {
        render_ndjson(self.semantic.iter().map(SemanticRecord::render))
    }

    pub fn telemetry_ndjson(&self) -> String {
        render_ndjson(self.telemetry.iter().map(TelemetryRecord::render))
    }

    pub fn semantic_root(&self) -> String {
        hash(Domain::Fixture, self.semantic_ndjson().as_bytes()).to_hex()
    }

    pub fn telemetry_root(&self) -> String {
        hash(Domain::OperationalMeta, self.telemetry_ndjson().as_bytes()).to_hex()
    }

    pub fn semantic_records(&self) -> &[SemanticRecord] {
        &self.semantic
    }

    pub fn telemetry_records(&self) -> &[TelemetryRecord] {
        &self.telemetry
    }

    pub fn validate_authority(&self, inventory: &CliLakeInventory) -> Result<(), CensusError> {
        if self.semantic.len() != inventory.transcripts.len() {
            return Err(CensusError::new(
                "semantic CLI transcript is not manifest-complete",
            ));
        }
        for (record, expected) in self.semantic.iter().zip(&inventory.transcripts) {
            if record.probe_id != expected.key
                || record.epoch_id != inventory.reference.commit
                || record.authority_root != inventory.inventory_root
                || record.expected_exit != expected.exit_code
                || record.expected_stdout != expected.stdout_hash
                || record.expected_stderr != expected.stderr_hash
                || record.disposition == CliDisposition::Inconclusive
                || record.disposition == CliDisposition::InternalFault
            {
                return Err(CensusError::new(format!(
                    "semantic CLI record {} is incomplete, stale or non-authoritative",
                    record.probe_id
                )));
            }
        }
        Ok(())
    }
}

fn validate_sequence(
    sequence: impl IntoIterator<Item = u64>,
    name: &str,
) -> Result<(), CensusError> {
    for (expected, actual) in sequence.into_iter().enumerate() {
        if actual != expected as u64 {
            return Err(CensusError::new(format!(
                "{name} NDJSON sequence is noncanonical at {expected}: found {actual}"
            )));
        }
    }
    Ok(())
}

fn parse_ndjson<T>(
    text: &str,
    parse: impl Fn(&str) -> Result<T, CensusError>,
) -> Result<Vec<T>, CensusError> {
    if text.is_empty() {
        return Ok(Vec::new());
    }
    if !text.ends_with('\n') {
        return Err(CensusError::new("NDJSON is missing its final newline"));
    }
    text.lines().map(parse).collect()
}

fn render_ndjson(lines: impl IntoIterator<Item = String>) -> String {
    let mut rendered = String::new();
    for line in lines {
        rendered.push_str(&line);
        rendered.push('\n');
    }
    rendered
}

fn json_quote(value: &str) -> String {
    let mut result = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character < ' ' => {
                result.push_str(&format!("\\u{:04X}", character as u32));
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum JsonAtom {
    String(String),
    Integer(i64),
}

fn parse_json_object(line: &str) -> Result<BTreeMap<String, JsonAtom>, CensusError> {
    let bytes = line.as_bytes();
    let mut cursor = 0;
    skip_json_ws(bytes, &mut cursor);
    consume_json(bytes, &mut cursor, b'{')?;
    let mut fields = BTreeMap::new();
    loop {
        skip_json_ws(bytes, &mut cursor);
        if bytes.get(cursor) == Some(&b'}') {
            cursor += 1;
            break;
        }
        let key = parse_json_string(bytes, &mut cursor)?;
        skip_json_ws(bytes, &mut cursor);
        consume_json(bytes, &mut cursor, b':')?;
        skip_json_ws(bytes, &mut cursor);
        let value = if bytes.get(cursor) == Some(&b'"') {
            JsonAtom::String(parse_json_string(bytes, &mut cursor)?)
        } else {
            JsonAtom::Integer(parse_json_integer(bytes, &mut cursor)?)
        };
        if fields.insert(key.clone(), value).is_some() {
            return Err(CensusError::new(format!("duplicate JSON field {key:?}")));
        }
        skip_json_ws(bytes, &mut cursor);
        match bytes.get(cursor) {
            Some(b',') => cursor += 1,
            Some(b'}') => {
                cursor += 1;
                break;
            }
            _ => return Err(CensusError::new("malformed JSON object separator")),
        }
    }
    skip_json_ws(bytes, &mut cursor);
    if cursor != bytes.len() {
        return Err(CensusError::new("trailing bytes after JSON object"));
    }
    Ok(fields)
}

fn skip_json_ws(bytes: &[u8], cursor: &mut usize) {
    while bytes
        .get(*cursor)
        .is_some_and(|byte| byte.is_ascii_whitespace())
    {
        *cursor += 1;
    }
}

fn consume_json(bytes: &[u8], cursor: &mut usize, expected: u8) -> Result<(), CensusError> {
    if bytes.get(*cursor) != Some(&expected) {
        return Err(CensusError::new(format!(
            "expected JSON byte {:?}",
            expected as char
        )));
    }
    *cursor += 1;
    Ok(())
}

fn parse_json_string(bytes: &[u8], cursor: &mut usize) -> Result<String, CensusError> {
    consume_json(bytes, cursor, b'"')?;
    let mut value = String::new();
    while let Some(byte) = bytes.get(*cursor).copied() {
        *cursor += 1;
        match byte {
            b'"' => return Ok(value),
            b'\\' => {
                let escape = bytes
                    .get(*cursor)
                    .copied()
                    .ok_or_else(|| CensusError::new("truncated JSON escape"))?;
                *cursor += 1;
                match escape {
                    b'"' => value.push('"'),
                    b'\\' => value.push('\\'),
                    b'n' => value.push('\n'),
                    b'r' => value.push('\r'),
                    b't' => value.push('\t'),
                    b'u' => {
                        let scalar = parse_json_hex_quad(bytes, cursor)?;
                        let character = char::from_u32(u32::from(scalar))
                            .ok_or_else(|| CensusError::new("invalid JSON Unicode escape"))?;
                        value.push(character);
                    }
                    _ => return Err(CensusError::new("unsupported JSON escape")),
                }
            }
            0x00..=0x1f => {
                return Err(CensusError::new("unescaped JSON control character"));
            }
            0x20..=0x7f => value.push(char::from(byte)),
            _ => {
                *cursor -= 1;
                let tail = std::str::from_utf8(&bytes[*cursor..])
                    .map_err(|_| CensusError::new("JSON string is not UTF-8"))?;
                let character = tail
                    .chars()
                    .next()
                    .ok_or_else(|| CensusError::new("truncated UTF-8 JSON string"))?;
                value.push(character);
                *cursor += character.len_utf8();
            }
        }
    }
    Err(CensusError::new("unterminated JSON string"))
}

fn parse_json_hex_quad(bytes: &[u8], cursor: &mut usize) -> Result<u16, CensusError> {
    let mut value = 0_u16;
    for _ in 0..4 {
        let byte = bytes
            .get(*cursor)
            .copied()
            .ok_or_else(|| CensusError::new("truncated JSON Unicode escape"))?;
        *cursor += 1;
        let digit = match byte {
            b'0'..=b'9' => u16::from(byte - b'0'),
            b'a'..=b'f' => u16::from(byte - b'a' + 10),
            b'A'..=b'F' => u16::from(byte - b'A' + 10),
            _ => return Err(CensusError::new("invalid JSON Unicode escape")),
        };
        value = value * 16 + digit;
    }
    Ok(value)
}

fn parse_json_integer(bytes: &[u8], cursor: &mut usize) -> Result<i64, CensusError> {
    let start = *cursor;
    if bytes.get(*cursor) == Some(&b'-') {
        *cursor += 1;
    }
    while bytes.get(*cursor).is_some_and(u8::is_ascii_digit) {
        *cursor += 1;
    }
    if *cursor == start || (*cursor == start + 1 && bytes[start] == b'-') {
        return Err(CensusError::new("JSON value is not a string or integer"));
    }
    std::str::from_utf8(&bytes[start..*cursor])
        .map_err(|_| CensusError::new("JSON integer is not UTF-8"))?
        .parse()
        .map_err(|_| CensusError::new("JSON integer is out of range"))
}

fn exact_json_fields(
    fields: &BTreeMap<String, JsonAtom>,
    expected: &[&str],
) -> Result<(), CensusError> {
    let actual = fields.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(CensusError::new(format!(
            "NDJSON field set mismatch: missing={:?} extra={:?}",
            expected.difference(&actual).collect::<Vec<_>>(),
            actual.difference(&expected).collect::<Vec<_>>()
        )));
    }
    Ok(())
}

fn json_string<'a>(
    fields: &'a BTreeMap<String, JsonAtom>,
    key: &str,
) -> Result<&'a str, CensusError> {
    match fields.get(key) {
        Some(JsonAtom::String(value)) => Ok(value),
        _ => Err(CensusError::new(format!(
            "NDJSON field {key:?} is not a string"
        ))),
    }
}

fn json_u64(fields: &BTreeMap<String, JsonAtom>, key: &str) -> Result<u64, CensusError> {
    match fields.get(key) {
        Some(JsonAtom::Integer(value)) => u64::try_from(*value)
            .map_err(|_| CensusError::new(format!("NDJSON field {key:?} is not a u64"))),
        _ => Err(CensusError::new(format!(
            "NDJSON field {key:?} is not an integer"
        ))),
    }
}

fn json_i32(fields: &BTreeMap<String, JsonAtom>, key: &str) -> Result<i32, CensusError> {
    match fields.get(key) {
        Some(JsonAtom::Integer(value)) => i32::try_from(*value)
            .map_err(|_| CensusError::new(format!("NDJSON field {key:?} is not an i32"))),
        _ => Err(CensusError::new(format!(
            "NDJSON field {key:?} is not an integer"
        ))),
    }
}
