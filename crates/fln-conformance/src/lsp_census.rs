//! Pinned Lean LSP and `$/lean` protocol authority (plan §14; bead `fln-i9so`).
//!
//! This module consumes the immutable output of
//! `scripts/extract/gen_lsp_wire_census.py`.  It does not invent a protocol:
//! every method, direction, top-level schema, field, capability, semantic-token
//! legend entry, lifecycle fact, and Reference transcript fixture comes from the
//! tree and epoch named by `SUITE.lock`.
//!
//! Three boundaries are intentional:
//!
//! * raw extracted facts and reviewed support policy have independent roots and
//!   an exact method-key bijection;
//! * protocol state transitions are atomic, with malformed, unknown, stale,
//!   cancelled, closed-document, expired-RPC, and platform-absence outcomes
//!   represented as data rather than panics;
//! * deterministic semantic NDJSON is hashed under [`Domain::Fixture`], while
//!   timing/worker telemetry is separate and hashed under
//!   [`Domain::OperationalMeta`].

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Component, Path};

use fln_hash::domain::{Domain, hash};

pub const INVENTORY_TEXT: &str = include_str!("../../../contracts/LSP_WIRE_INVENTORY.txt");
pub const POLICY_TEXT: &str = include_str!("../../../ci/LSP_WIRE_POLICY.txt");

const INVENTORY_SCHEMA: &str = "fln-lsp-wire-inventory/1";
const POLICY_SCHEMA: &str = "fln-lsp-wire-policy/1";
const SEMANTIC_SCHEMA: &str = "fln.lsp.semantic/1";
const TELEMETRY_SCHEMA: &str = "fln.lsp.telemetry/1";
const RPC_KEEP_ALIVE_MS: u64 = 30_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CensusError(String);

impl CensusError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for CensusError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for CensusError {}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MessageFamily {
    Request,
    Notification,
    RpcRequest,
}

impl MessageFamily {
    fn parse(value: &str) -> Result<Self, CensusError> {
        match value {
            "request" => Ok(Self::Request),
            "notification" => Ok(Self::Notification),
            "rpc_request" => Ok(Self::RpcRequest),
            other => Err(CensusError::new(format!(
                "unsupported protocol family {other:?}"
            ))),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum MessageDirection {
    ClientToServer,
    ServerToClient,
}

impl MessageDirection {
    fn parse(value: &str) -> Result<Self, CensusError> {
        match value {
            "client_to_server" => Ok(Self::ClientToServer),
            "server_to_client" => Ok(Self::ServerToClient),
            other => Err(CensusError::new(format!(
                "unsupported protocol direction {other:?}"
            ))),
        }
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::ClientToServer => "client_to_server",
            Self::ServerToClient => "server_to_client",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MethodPolicy {
    pub support: String,
    pub comparison: String,
    pub lifecycle: String,
    pub client: String,
    pub platform: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProtocolMethod {
    pub key: String,
    pub ordinal: usize,
    pub family: MessageFamily,
    pub direction: MessageDirection,
    pub wire_carrier: String,
    pub method: String,
    pub parameter_type: String,
    pub response_type: String,
    pub extension_kinds: String,
    pub description: String,
    pub probe: String,
    pub fixture: String,
    pub source: String,
    pub evidence: String,
    pub policy: MethodPolicy,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceBinding {
    pub path: String,
    pub hash: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SchemaDeclaration {
    pub id: String,
    pub name: String,
    pub kind: String,
    pub source: String,
    pub declaration_hash: String,
    pub declared_field_count: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SchemaField {
    pub schema: String,
    pub name: String,
    pub wire_name: String,
    pub type_expression: String,
    pub optional: bool,
    pub defaulted: bool,
    pub source: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Capability {
    pub name: String,
    pub value: String,
    pub source: String,
    pub evidence: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LifecycleFact {
    pub key: String,
    pub value: String,
    pub source: String,
    pub evidence: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixtureBinding {
    pub name: String,
    pub source: String,
    pub source_hash: String,
    pub expected: String,
    pub expected_hash: String,
    pub normalizer: String,
    pub directives: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceIdentity {
    pub repository: String,
    pub tag: String,
    pub commit: String,
    pub tree: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LspInventory {
    pub reference: ReferenceIdentity,
    pub sources: Vec<SourceBinding>,
    pub methods: Vec<ProtocolMethod>,
    pub schemas: Vec<SchemaDeclaration>,
    pub fields: Vec<SchemaField>,
    pub capabilities: Vec<Capability>,
    pub token_types: Vec<String>,
    pub token_modifiers: Vec<String>,
    pub lifecycle: Vec<LifecycleFact>,
    pub fixtures: Vec<FixtureBinding>,
    pub raw_root: String,
    pub policy_root: String,
    pub inventory_root: String,
}

impl LspInventory {
    pub fn load_embedded() -> Result<Self, CensusError> {
        Self::parse(INVENTORY_TEXT, POLICY_TEXT)
    }

    pub fn parse(inventory_text: &str, policy_text: &str) -> Result<Self, CensusError> {
        if !inventory_text.ends_with('\n') {
            return Err(CensusError::new(
                "LSP inventory lacks its canonical final newline",
            ));
        }
        if !policy_text.ends_with('\n') {
            return Err(CensusError::new(
                "LSP policy lacks its canonical final newline",
            ));
        }
        let lines = inventory_text.lines().collect::<Vec<_>>();
        let expected_schema = format!("schema {INVENTORY_SCHEMA}");
        if lines.first().copied() != Some(expected_schema.as_str()) {
            return Err(CensusError::new("LSP inventory schema mismatch"));
        }
        let raw_begin = unique_line(&lines, "raw-begin")?;
        let raw_end = unique_line(&lines, "raw-end")?;
        if raw_begin >= raw_end {
            return Err(CensusError::new("LSP raw section markers are reversed"));
        }
        if raw_end + 4 != lines.len() {
            return Err(CensusError::new(
                "LSP inventory must end with raw-end and exactly three root rows",
            ));
        }
        require_header(&lines[..raw_begin])?;

        let raw_lines = &lines[raw_begin + 1..raw_end];
        let raw_root = root_field(lines[raw_end + 1], "raw-root")?;
        let policy_root = root_field(lines[raw_end + 2], "policy-root")?;
        let inventory_root = root_field(lines[raw_end + 3], "inventory-root")?;
        let computed_raw = framed_hash("fln-lsp-wire-raw/1", raw_lines.iter().copied());
        if raw_root != computed_raw {
            return Err(CensusError::new(format!(
                "LSP raw root mismatch: recorded {raw_root}, computed {computed_raw}"
            )));
        }
        let computed_policy = framed_hash("fln-lsp-wire-policy/1", policy_text.lines());
        if policy_root != computed_policy {
            return Err(CensusError::new(format!(
                "LSP policy root mismatch: recorded {policy_root}, computed {computed_policy}"
            )));
        }
        let computed_inventory = framed_hash(
            "fln-lsp-wire-inventory/1",
            lines[..lines.len() - 1].iter().copied(),
        );
        if inventory_root != computed_inventory {
            return Err(CensusError::new(format!(
                "LSP inventory root mismatch: recorded {inventory_root}, \
                 computed {computed_inventory}"
            )));
        }

        let policies = parse_policy(policy_text)?;
        let mut reference = None;
        let mut sources = Vec::new();
        let mut raw_methods = Vec::new();
        let mut schemas = Vec::new();
        let mut fields = Vec::new();
        let mut capabilities = Vec::new();
        let mut token_types = BTreeMap::new();
        let mut token_modifiers = BTreeMap::new();
        let mut lifecycle = Vec::new();
        let mut fixtures = Vec::new();

        for (offset, line) in raw_lines.iter().enumerate() {
            let line_number = raw_begin + offset + 2;
            let (kind, values) = parse_row(line, line_number)?;
            match kind.as_str() {
                "reference" => {
                    require_field_set(&values, &["repo", "tag", "commit", "tree"], line_number)?;
                    if reference.is_some() {
                        return Err(CensusError::new("duplicate Reference identity row"));
                    }
                    reference = Some(ReferenceIdentity {
                        repository: field(&values, "repo", line_number)?.to_string(),
                        tag: field(&values, "tag", line_number)?.to_string(),
                        commit: full_hash(field(&values, "commit", line_number)?, "commit")?,
                        tree: full_hash(field(&values, "tree", line_number)?, "tree")?,
                    });
                }
                "source" => {
                    require_field_set(&values, &["path", "hash"], line_number)?;
                    sources.push(SourceBinding {
                        path: decode_percent_escapes(field(&values, "path", line_number)?)?,
                        hash: parse_fnv(field(&values, "hash", line_number)?)?,
                    });
                }
                "method" => {
                    require_field_set(
                        &values,
                        &[
                            "key",
                            "ordinal",
                            "family",
                            "direction",
                            "wire",
                            "method",
                            "parameter",
                            "response",
                            "kinds",
                            "description",
                            "probe",
                            "fixture",
                            "source",
                            "evidence",
                        ],
                        line_number,
                    )?;
                    raw_methods.push(RawMethod {
                        key: decode_percent_escapes(field(&values, "key", line_number)?)?,
                        ordinal: parse_usize(field(&values, "ordinal", line_number)?, "ordinal")?,
                        family: MessageFamily::parse(field(&values, "family", line_number)?)?,
                        direction: MessageDirection::parse(field(
                            &values,
                            "direction",
                            line_number,
                        )?)?,
                        wire_carrier: decode_percent_escapes(field(&values, "wire", line_number)?)?,
                        method: decode_percent_escapes(field(&values, "method", line_number)?)?,
                        parameter_type: decode_percent_escapes(field(
                            &values,
                            "parameter",
                            line_number,
                        )?)?,
                        response_type: decode_percent_escapes(field(
                            &values,
                            "response",
                            line_number,
                        )?)?,
                        extension_kinds: decode_percent_escapes(field(
                            &values,
                            "kinds",
                            line_number,
                        )?)?,
                        description: decode_percent_escapes(field(
                            &values,
                            "description",
                            line_number,
                        )?)?,
                        probe: field(&values, "probe", line_number)?.to_string(),
                        fixture: field(&values, "fixture", line_number)?.to_string(),
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                        evidence: parse_fnv(field(&values, "evidence", line_number)?)?,
                    });
                }
                "schema-decl" => {
                    require_field_set(
                        &values,
                        &["id", "name", "kind", "source", "declaration", "field-count"],
                        line_number,
                    )?;
                    schemas.push(SchemaDeclaration {
                        id: decode_percent_escapes(field(&values, "id", line_number)?)?,
                        name: decode_percent_escapes(field(&values, "name", line_number)?)?,
                        kind: field(&values, "kind", line_number)?.to_string(),
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                        declaration_hash: parse_fnv(field(&values, "declaration", line_number)?)?,
                        declared_field_count: parse_usize(
                            field(&values, "field-count", line_number)?,
                            "field-count",
                        )?,
                    });
                }
                "schema-field" => {
                    require_field_set(
                        &values,
                        &[
                            "schema",
                            "name",
                            "wire-name",
                            "type",
                            "optional",
                            "defaulted",
                            "source",
                        ],
                        line_number,
                    )?;
                    fields.push(SchemaField {
                        schema: decode_percent_escapes(field(&values, "schema", line_number)?)?,
                        name: decode_percent_escapes(field(&values, "name", line_number)?)?,
                        wire_name: decode_percent_escapes(field(
                            &values,
                            "wire-name",
                            line_number,
                        )?)?,
                        type_expression: decode_percent_escapes(field(
                            &values,
                            "type",
                            line_number,
                        )?)?,
                        optional: match field(&values, "optional", line_number)? {
                            "yes" => true,
                            "no" => false,
                            other => {
                                return Err(CensusError::new(format!(
                                    "line {line_number}: unsupported optionality {other:?}"
                                )));
                            }
                        },
                        defaulted: match field(&values, "defaulted", line_number)? {
                            "yes" => true,
                            "no" => false,
                            other => {
                                return Err(CensusError::new(format!(
                                    "line {line_number}: unsupported default marker {other:?}"
                                )));
                            }
                        },
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                    });
                }
                "capability" => {
                    require_field_set(
                        &values,
                        &["name", "value", "source", "evidence"],
                        line_number,
                    )?;
                    capabilities.push(Capability {
                        name: decode_percent_escapes(field(&values, "name", line_number)?)?,
                        value: decode_percent_escapes(field(&values, "value", line_number)?)?,
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                        evidence: parse_fnv(field(&values, "evidence", line_number)?)?,
                    });
                }
                "legend-type" | "legend-modifier" => {
                    require_field_set(&values, &["index", "name"], line_number)?;
                    let index = parse_usize(field(&values, "index", line_number)?, "index")?;
                    let name = decode_percent_escapes(field(&values, "name", line_number)?)?;
                    let destination = if kind == "legend-type" {
                        &mut token_types
                    } else {
                        &mut token_modifiers
                    };
                    if destination.insert(index, name).is_some() {
                        return Err(CensusError::new(format!(
                            "line {line_number}: duplicate legend index {index}"
                        )));
                    }
                }
                "lifecycle" => {
                    require_field_set(
                        &values,
                        &["key", "value", "source", "evidence"],
                        line_number,
                    )?;
                    lifecycle.push(LifecycleFact {
                        key: decode_percent_escapes(field(&values, "key", line_number)?)?,
                        value: decode_percent_escapes(field(&values, "value", line_number)?)?,
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                        evidence: parse_fnv(field(&values, "evidence", line_number)?)?,
                    });
                }
                "fixture" => {
                    require_field_set(
                        &values,
                        &[
                            "name",
                            "source",
                            "source-hash",
                            "expected",
                            "expected-hash",
                            "normalizer",
                            "directives",
                        ],
                        line_number,
                    )?;
                    fixtures.push(FixtureBinding {
                        name: decode_percent_escapes(field(&values, "name", line_number)?)?,
                        source: decode_percent_escapes(field(&values, "source", line_number)?)?,
                        source_hash: parse_fnv(field(&values, "source-hash", line_number)?)?,
                        expected: decode_percent_escapes(field(&values, "expected", line_number)?)?,
                        expected_hash: parse_fnv(field(&values, "expected-hash", line_number)?)?,
                        normalizer: field(&values, "normalizer", line_number)?.to_string(),
                        directives: decode_percent_escapes(field(
                            &values,
                            "directives",
                            line_number,
                        )?)?,
                    });
                }
                other => {
                    return Err(CensusError::new(format!(
                        "line {line_number}: unsupported raw row {other:?}"
                    )));
                }
            }
        }

        let raw_keys = raw_methods
            .iter()
            .map(|method| method.key.clone())
            .collect::<BTreeSet<_>>();
        let policy_keys = policies.keys().cloned().collect::<BTreeSet<_>>();
        if raw_keys != policy_keys || raw_keys.len() != raw_methods.len() {
            return Err(CensusError::new(format!(
                "method/policy join is not bijective: raw={} unique_raw={} policy={}",
                raw_methods.len(),
                raw_keys.len(),
                policy_keys.len()
            )));
        }
        let methods = raw_methods
            .into_iter()
            .map(|method| {
                let policy = policies.get(&method.key).cloned().ok_or_else(|| {
                    CensusError::new(format!("method {} has no policy", method.key))
                })?;
                Ok(ProtocolMethod {
                    key: method.key,
                    ordinal: method.ordinal,
                    family: method.family,
                    direction: method.direction,
                    wire_carrier: method.wire_carrier,
                    method: method.method,
                    parameter_type: method.parameter_type,
                    response_type: method.response_type,
                    extension_kinds: method.extension_kinds,
                    description: method.description,
                    probe: method.probe,
                    fixture: method.fixture,
                    source: method.source,
                    evidence: method.evidence,
                    policy,
                })
            })
            .collect::<Result<Vec<_>, CensusError>>()?;

        let inventory = Self {
            reference: reference
                .ok_or_else(|| CensusError::new("LSP inventory has no Reference row"))?,
            sources,
            methods,
            schemas,
            fields,
            capabilities,
            token_types: contiguous_values(token_types, "semantic token type")?,
            token_modifiers: contiguous_values(token_modifiers, "semantic token modifier")?,
            lifecycle,
            fixtures,
            raw_root,
            policy_root,
            inventory_root,
        };
        inventory.validate_cardinality(&lines[..raw_begin])?;
        inventory.validate_relations()?;
        Ok(inventory)
    }

    fn validate_cardinality(&self, header: &[&str]) -> Result<(), CensusError> {
        let expected = [
            ("method-count", self.methods.len()),
            (
                "request-count",
                self.methods
                    .iter()
                    .filter(|method| method.family == MessageFamily::Request)
                    .count(),
            ),
            (
                "notification-count",
                self.methods
                    .iter()
                    .filter(|method| method.family == MessageFamily::Notification)
                    .count(),
            ),
            (
                "rpc-request-count",
                self.methods
                    .iter()
                    .filter(|method| method.family == MessageFamily::RpcRequest)
                    .count(),
            ),
            ("schema-count", self.schemas.len()),
            ("schema-field-count", self.fields.len()),
            ("capability-count", self.capabilities.len()),
            ("legend-type-count", self.token_types.len()),
            ("legend-modifier-count", self.token_modifiers.len()),
            ("lifecycle-count", self.lifecycle.len()),
            ("fixture-count", self.fixtures.len()),
        ];
        for (name, actual) in expected {
            let recorded = header_count(header, name)?;
            if recorded != actual {
                return Err(CensusError::new(format!(
                    "{name} records {recorded}, parsed {actual}"
                )));
            }
        }
        if self.methods.len() != 59
            || self
                .methods
                .iter()
                .filter(|method| method.family == MessageFamily::Request)
                .count()
                != 37
            || self
                .methods
                .iter()
                .filter(|method| method.family == MessageFamily::Notification)
                .count()
                != 12
            || self
                .methods
                .iter()
                .filter(|method| method.family == MessageFamily::RpcRequest)
                .count()
                != 10
            || self.schemas.len() != 208
            || self.fields.len() != 491
            || self.capabilities.len() != 19
            || self.lifecycle.len() != 21
        {
            return Err(CensusError::new(
                "pinned protocol cardinality is not the reviewed method/schema/capability/lifecycle census",
            ));
        }
        if self.token_types.len() != 24
            || self.token_modifiers.len() != 10
            || self.fixtures.len() != 8
        {
            return Err(CensusError::new(
                "legend or real-transcript anti-vacuity floor failed",
            ));
        }
        Ok(())
    }

    fn validate_relations(&self) -> Result<(), CensusError> {
        unique_by(
            self.sources.iter().map(|row| row.path.as_str()),
            "source path",
        )?;
        unique_by(
            self.methods.iter().map(|row| row.key.as_str()),
            "method key",
        )?;
        unique_by(self.schemas.iter().map(|row| row.id.as_str()), "schema id")?;
        unique_by(
            self.capabilities.iter().map(|row| row.name.as_str()),
            "capability",
        )?;
        unique_by(
            self.lifecycle.iter().map(|row| row.key.as_str()),
            "lifecycle fact",
        )?;
        unique_by(self.fixtures.iter().map(|row| row.name.as_str()), "fixture")?;

        let ordinals = self
            .methods
            .iter()
            .map(|method| method.ordinal)
            .collect::<BTreeSet<_>>();
        if ordinals != (0..self.methods.len()).collect() {
            return Err(CensusError::new(
                "method source ordinals are not a complete contiguous set",
            ));
        }
        let schema_ids = self
            .schemas
            .iter()
            .map(|schema| schema.id.as_str())
            .collect::<BTreeSet<_>>();
        if let Some(field) = self
            .fields
            .iter()
            .find(|field| !schema_ids.contains(field.schema.as_str()))
        {
            return Err(CensusError::new(format!(
                "schema field {} names absent declaration {}",
                field.name, field.schema
            )));
        }
        if let Some(field) = self
            .fields
            .iter()
            .find(|field| field.defaulted && !field.optional)
        {
            return Err(CensusError::new(format!(
                "defaulted schema field {} is not marked omittable",
                field.name
            )));
        }
        for schema in &self.schemas {
            let actual = self
                .fields
                .iter()
                .filter(|field| field.schema == schema.id)
                .count();
            if actual != schema.declared_field_count {
                return Err(CensusError::new(format!(
                    "schema {} records {} fields but owns {actual}",
                    schema.name, schema.declared_field_count
                )));
            }
        }
        let server_to_client = self
            .methods
            .iter()
            .filter(|method| method.direction == MessageDirection::ServerToClient)
            .map(|method| method.method.as_str())
            .collect::<BTreeSet<_>>();
        let expected_server_to_client = BTreeSet::from([
            "$/lean/fileProgress",
            "client/registerCapability",
            "textDocument/publishDiagnostics",
            "workspace/inlayHint/refresh",
            "workspace/semanticTokens/refresh",
        ]);
        if server_to_client != expected_server_to_client {
            return Err(CensusError::new(format!(
                "server-initiated method set drifted: {server_to_client:?}"
            )));
        }
        let expected_token_types = [
            "keyword",
            "variable",
            "property",
            "function",
            "namespace",
            "type",
            "class",
            "enum",
            "interface",
            "struct",
            "typeParameter",
            "parameter",
            "enumMember",
            "event",
            "method",
            "macro",
            "modifier",
            "comment",
            "string",
            "number",
            "regexp",
            "operator",
            "decorator",
            "leanSorryLike",
        ];
        let expected_token_modifiers = [
            "declaration",
            "definition",
            "readonly",
            "static",
            "deprecated",
            "abstract",
            "async",
            "modification",
            "documentation",
            "defaultLibrary",
        ];
        if self
            .token_types
            .iter()
            .map(String::as_str)
            .ne(expected_token_types)
            || self
                .token_modifiers
                .iter()
                .map(String::as_str)
                .ne(expected_token_modifiers)
        {
            return Err(CensusError::new(
                "semantic token legend differs from the pinned ordered legend",
            ));
        }
        for method in &self.methods {
            let expected_probe = match (method.family, method.direction) {
                (MessageFamily::RpcRequest, MessageDirection::ClientToServer) => {
                    "real-rpc-dispatch"
                }
                (_, MessageDirection::ServerToClient) => "real-server-emission",
                (MessageFamily::Request, MessageDirection::ClientToServer) => {
                    "real-request-dispatch"
                }
                (MessageFamily::Notification, MessageDirection::ClientToServer) => {
                    "real-notification-dispatch"
                }
            };
            if method.probe != expected_probe || method.fixture != "lsp-census-no-mock-e2e" {
                return Err(CensusError::new(format!(
                    "method {} is not bound to its manifest-complete real probe",
                    method.key
                )));
            }
            let expected_lifecycle = expected_method_lifecycle(method);
            let expected_comparison = if expected_lifecycle == "rpc_session" {
                "normalized"
            } else {
                "exact"
            };
            let expected_client = if method.direction == MessageDirection::ServerToClient {
                "server_initiated"
            } else if matches!(
                method.method.as_str(),
                "initialize" | "initialized" | "shutdown" | "exit"
            ) {
                "mandatory_client"
            } else {
                "capability_gated_client"
            };
            if method.policy.support != "required"
                || method.policy.comparison != expected_comparison
                || method.policy.lifecycle != expected_lifecycle
                || method.policy.client != expected_client
                || method.policy.platform != "all"
            {
                return Err(CensusError::new(format!(
                    "method {} has policy that disagrees with its extracted wire role",
                    method.key
                )));
            }
        }
        Ok(())
    }

    pub fn validate_workspace_sources(&self, root: &Path) -> Result<(), CensusError> {
        for source in &self.sources {
            let relative_path = Path::new(&source.path);
            if relative_path.is_absolute()
                || relative_path
                    .components()
                    .any(|component| !matches!(component, Component::Normal(_)))
            {
                return Err(CensusError::new(format!(
                    "source path is not a repository-relative normal path: {}",
                    source.path
                )));
            }
            let path = root.join(relative_path);
            let bytes = std::fs::read(&path).map_err(|error| {
                CensusError::new(format!("read bound source {}: {error}", path.display()))
            })?;
            let actual = format!("fnv1a64:{:016x}", fnv1a64(&bytes));
            if actual != source.hash {
                return Err(CensusError::new(format!(
                    "bound source {} drifted: inventory {}, working tree {}",
                    source.path, source.hash, actual
                )));
            }
        }
        let lock = std::fs::read_to_string(root.join("SUITE.lock"))
            .map_err(|error| CensusError::new(format!("read SUITE.lock: {error}")))?;
        let reference_line = lock
            .lines()
            .find(|line| line.starts_with("reference leanprover/lean4 "))
            .ok_or_else(|| CensusError::new("SUITE.lock has no Reference row"))?;
        for binding in [
            format!("tag={}", self.reference.tag),
            format!("commit={}", self.reference.commit),
            format!("tree={}", self.reference.tree),
        ] {
            if !reference_line
                .split_whitespace()
                .any(|field| field == binding)
            {
                return Err(CensusError::new(format!(
                    "SUITE.lock Reference row does not contain {binding}"
                )));
            }
        }
        Ok(())
    }

    pub fn method(&self, name: &str) -> Option<&ProtocolMethod> {
        self.methods.iter().find(|method| method.method == name)
    }

    pub fn rpc_method(&self, name: &str) -> Option<&ProtocolMethod> {
        self.methods
            .iter()
            .find(|method| method.family == MessageFamily::RpcRequest && method.method == name)
    }

    pub fn accepts_client_request(&self, name: &str) -> bool {
        self.methods.iter().any(|method| {
            method.method == name
                && method.family == MessageFamily::Request
                && method.direction == MessageDirection::ClientToServer
        })
    }

    pub fn accepts_client_notification(&self, name: &str) -> bool {
        self.methods.iter().any(|method| {
            method.method == name
                && method.family == MessageFamily::Notification
                && method.direction == MessageDirection::ClientToServer
        })
    }

    pub fn capability(&self, name: &str) -> Option<&Capability> {
        self.capabilities
            .iter()
            .find(|capability| capability.name == name)
    }

    pub fn lifecycle_fact(&self, key: &str) -> Option<&LifecycleFact> {
        self.lifecycle.iter().find(|fact| fact.key == key)
    }

    pub fn fixture(&self, name: &str) -> Option<&FixtureBinding> {
        self.fixtures.iter().find(|fixture| fixture.name == name)
    }

    pub fn schema_named(&self, name: &str) -> Option<&SchemaDeclaration> {
        let exact = self
            .schemas
            .iter()
            .filter(|schema| schema.name == name)
            .collect::<Vec<_>>();
        if exact.len() == 1 {
            return exact.into_iter().next();
        }
        let suffix = format!(".{name}");
        let suffix_matches = self
            .schemas
            .iter()
            .filter(|schema| schema.name.ends_with(&suffix))
            .collect::<Vec<_>>();
        (suffix_matches.len() == 1)
            .then(|| suffix_matches.into_iter().next())
            .flatten()
    }

    pub fn schema_fields(&self, schema: &SchemaDeclaration) -> Vec<&SchemaField> {
        self.fields
            .iter()
            .filter(|field| field.schema == schema.id)
            .collect()
    }

    pub fn validate_semantic_manifest(&self, events: &[SemanticEvent]) -> Result<(), CensusError> {
        let manifest = events
            .iter()
            .filter(|event| event.fixture_id == "lsp-census-no-mock-e2e")
            .collect::<Vec<_>>();
        let mut by_method = BTreeMap::new();
        for event in manifest {
            if by_method.insert(event.method_id.as_str(), event).is_some() {
                return Err(CensusError::new(format!(
                    "semantic manifest repeats method {}",
                    event.method_id
                )));
            }
        }
        let expected_keys = self
            .methods
            .iter()
            .map(|method| method.key.as_str())
            .collect::<BTreeSet<_>>();
        let actual_keys = by_method.keys().copied().collect::<BTreeSet<_>>();
        if actual_keys != expected_keys {
            return Err(CensusError::new(format!(
                "semantic manifest is not method-complete: missing={:?} extra={:?}",
                expected_keys.difference(&actual_keys).collect::<Vec<_>>(),
                actual_keys.difference(&expected_keys).collect::<Vec<_>>()
            )));
        }
        for method in &self.methods {
            let event = by_method[method.key.as_str()];
            let document_bound =
                matches!(method.policy.lifecycle.as_str(), "document" | "rpc_session");
            if event.epoch_id != self.reference.commit
                || event.client_id != method.policy.client
                || event.capability_id.is_empty()
                || event.session_id.is_empty()
                || event.document_id.is_empty()
                || event.document_version != u64::from(document_bound) * 2
                || event.request_id.is_empty()
                || event.comparison_id != method.policy.comparison
                || event.direction != method.direction
                || event.parameter_schema_id != method.parameter_type
                || event.response_schema_id != method.response_type
                || event.expected_disposition != event.actual_disposition
                || event.expected_message_root != event.actual_message_root
                || event.expected_error_code != event.actual_error_code
                || event.authority_root != self.inventory_root
                || !event.resource_state.contains(&method.probe)
                || event.cleanup_state != "document=closed;rpc=released;server=exited"
                || event.final_state != "manifest-complete"
            {
                return Err(CensusError::new(format!(
                    "semantic manifest row {} is stale, incomplete, or non-deterministic",
                    method.key
                )));
            }
        }
        Ok(())
    }

    pub fn validate_object_shape(
        &self,
        schema_name: &str,
        values: &BTreeMap<String, WireValueKind>,
    ) -> Result<ObjectShape, ProtocolFault> {
        let schema = self
            .schema_named(schema_name)
            .ok_or_else(|| ProtocolFault::UnknownSchema(schema_name.to_string()))?;
        let fields = self.schema_fields(schema);
        let mut unknown_fields = Vec::new();
        for field in &fields {
            let Some(value) = values.get(&field.wire_name) else {
                if field.optional {
                    continue;
                }
                return Err(ProtocolFault::MissingField {
                    schema: schema_name.to_string(),
                    field: field.wire_name.clone(),
                });
            };
            if *value == WireValueKind::Null && field.optional {
                continue;
            }
            let liberal_initialize_option =
                schema.name.ends_with(".InitializeParams") && field.optional;
            if !liberal_initialize_option
                && let Some(expected) = expected_wire_kind(&field.type_expression)
                && expected != *value
            {
                return Err(ProtocolFault::WrongFieldType {
                    schema: schema_name.to_string(),
                    field: field.wire_name.clone(),
                    expected,
                    actual: *value,
                });
            }
        }
        let known = fields
            .iter()
            .map(|field| field.wire_name.as_str())
            .collect::<BTreeSet<_>>();
        for name in values.keys() {
            if !known.contains(name.as_str()) {
                unknown_fields.push(name.clone());
            }
        }
        Ok(ObjectShape { unknown_fields })
    }
}

#[derive(Clone, Debug)]
struct RawMethod {
    key: String,
    ordinal: usize,
    family: MessageFamily,
    direction: MessageDirection,
    wire_carrier: String,
    method: String,
    parameter_type: String,
    response_type: String,
    extension_kinds: String,
    description: String,
    probe: String,
    fixture: String,
    source: String,
    evidence: String,
}

fn expected_method_lifecycle(method: &ProtocolMethod) -> &'static str {
    let name = method.method.as_str();
    if matches!(name, "initialize" | "initialized" | "shutdown" | "exit") {
        "process"
    } else if name == "$/cancelRequest" {
        "request"
    } else if method.family == MessageFamily::RpcRequest || name.starts_with("$/lean/rpc/") {
        "rpc_session"
    } else if name.starts_with("textDocument/")
        || name.starts_with("$/lean/plain")
        || name.starts_with("callHierarchy/")
    {
        "document"
    } else if name.starts_with("$/lean/moduleHierarchy")
        || name.starts_with("$/lean/prepareModule")
        || name.starts_with("workspace/")
    {
        "workspace"
    } else if name == "$/lean/fileProgress" {
        "document"
    } else if name == "client/registerCapability" {
        "process"
    } else {
        "request"
    }
}

fn require_header(header: &[&str]) -> Result<(), CensusError> {
    let required_exact = [
        format!("schema {INVENTORY_SCHEMA}"),
        "extractor lean-protocol-overview-source-walk version=1".to_string(),
        "hash fnv1a64-noncryptographic framing=u64le-length-prefixed".to_string(),
        "policy-join exact-method-bijection".to_string(),
    ];
    if header.len() != 18 {
        return Err(CensusError::new(format!(
            "LSP inventory header has {} rows, expected 18",
            header.len()
        )));
    }
    for (index, expected) in required_exact.iter().enumerate() {
        if header[index] != expected {
            return Err(CensusError::new(format!(
                "LSP inventory header row {} is {:?}, expected {:?}",
                index + 1,
                header[index],
                expected
            )));
        }
    }
    let trailing = [
        "position-units utf16-code-units",
        "unknown-object-fields ignored-by-derived-decoders",
        "malformed-known-fields typed-invalid-params",
    ];
    if header[15..] != trailing {
        return Err(CensusError::new(
            "LSP position/unknown/malformed contract header drifted",
        ));
    }
    Ok(())
}

fn unique_line(lines: &[&str], needle: &str) -> Result<usize, CensusError> {
    let positions = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == needle).then_some(index))
        .collect::<Vec<_>>();
    if positions.len() != 1 {
        return Err(CensusError::new(format!(
            "expected exactly one {needle:?} row, found {}",
            positions.len()
        )));
    }
    Ok(positions[0])
}

fn header_count(header: &[&str], name: &str) -> Result<usize, CensusError> {
    let prefix = format!("{name} ");
    let values = header
        .iter()
        .filter_map(|line| line.strip_prefix(&prefix))
        .collect::<Vec<_>>();
    if values.len() != 1 {
        return Err(CensusError::new(format!(
            "expected exactly one {name} header, found {}",
            values.len()
        )));
    }
    parse_usize(values[0], name)
}

fn root_field(line: &str, name: &str) -> Result<String, CensusError> {
    let prefix = format!("{name} ");
    let value = line
        .strip_prefix(&prefix)
        .ok_or_else(|| CensusError::new(format!("expected {name} root row, found {line:?}")))?;
    parse_fnv(value)
}

fn parse_row(
    line: &str,
    line_number: usize,
) -> Result<(String, BTreeMap<String, String>), CensusError> {
    let mut tokens = line.split_whitespace();
    let kind = tokens
        .next()
        .ok_or_else(|| CensusError::new(format!("line {line_number}: empty raw row")))?
        .to_string();
    let mut values = BTreeMap::new();
    for token in tokens {
        let (name, value) = token.split_once('=').ok_or_else(|| {
            CensusError::new(format!(
                "line {line_number}: raw field has no equals sign: {token:?}"
            ))
        })?;
        if name.is_empty()
            || value.is_empty()
            || values.insert(name.to_string(), value.to_string()).is_some()
        {
            return Err(CensusError::new(format!(
                "line {line_number}: duplicate or empty raw field {name:?}"
            )));
        }
    }
    Ok((kind, values))
}

fn require_field_set(
    values: &BTreeMap<String, String>,
    expected: &[&str],
    line_number: usize,
) -> Result<(), CensusError> {
    let actual = values.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(CensusError::new(format!(
            "line {line_number}: field set is {actual:?}, expected {expected:?}"
        )));
    }
    Ok(())
}

fn field<'a>(
    values: &'a BTreeMap<String, String>,
    name: &str,
    line_number: usize,
) -> Result<&'a str, CensusError> {
    values
        .get(name)
        .map(String::as_str)
        .ok_or_else(|| CensusError::new(format!("line {line_number}: missing field {name}")))
}

fn parse_policy(text: &str) -> Result<BTreeMap<String, MethodPolicy>, CensusError> {
    let mut lines = text.lines();
    let expected_schema = format!("schema {POLICY_SCHEMA}");
    if lines.next() != Some(expected_schema.as_str()) {
        return Err(CensusError::new("LSP policy schema mismatch"));
    }
    let mut policies = BTreeMap::new();
    let mut previous = String::new();
    for (offset, line) in lines.enumerate() {
        let line_number = offset + 2;
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut tokens = line.split_whitespace();
        if tokens.next() != Some("row") {
            return Err(CensusError::new(format!(
                "policy line {line_number}: expected row"
            )));
        }
        let encoded_key = tokens.next().ok_or_else(|| {
            CensusError::new(format!("policy line {line_number}: missing method key"))
        })?;
        let key = decode_percent_escapes(encoded_key)?;
        if key <= previous {
            return Err(CensusError::new(format!(
                "policy line {line_number}: keys are not strictly sorted"
            )));
        }
        previous = key.clone();
        let mut policy_fields = BTreeMap::new();
        for token in tokens {
            let (name, value) = token.split_once('=').ok_or_else(|| {
                CensusError::new(format!(
                    "policy line {line_number}: malformed field {token:?}"
                ))
            })?;
            if policy_fields
                .insert(name.to_string(), value.to_string())
                .is_some()
            {
                return Err(CensusError::new(format!(
                    "policy line {line_number}: duplicate field {name}"
                )));
            }
        }
        require_field_set(
            &policy_fields,
            &["support", "comparison", "lifecycle", "client", "platform"],
            line_number,
        )?;
        let policy = MethodPolicy {
            support: field(&policy_fields, "support", line_number)?.to_string(),
            comparison: field(&policy_fields, "comparison", line_number)?.to_string(),
            lifecycle: field(&policy_fields, "lifecycle", line_number)?.to_string(),
            client: field(&policy_fields, "client", line_number)?.to_string(),
            platform: field(&policy_fields, "platform", line_number)?.to_string(),
        };
        if !matches!(policy.support.as_str(), "required" | "optional")
            || !matches!(policy.comparison.as_str(), "exact" | "normalized")
            || !matches!(
                policy.lifecycle.as_str(),
                "process" | "request" | "document" | "workspace" | "rpc_session"
            )
            || !matches!(
                policy.client.as_str(),
                "mandatory_client" | "capability_gated_client" | "server_initiated"
            )
            || policy.platform != "all"
        {
            return Err(CensusError::new(format!(
                "policy line {line_number}: unsupported policy vocabulary"
            )));
        }
        if policies.insert(key.clone(), policy).is_some() {
            return Err(CensusError::new(format!(
                "policy line {line_number}: duplicate method {key}"
            )));
        }
    }
    if policies.is_empty() {
        return Err(CensusError::new("LSP policy contains no rows"));
    }
    Ok(policies)
}

fn full_hash(value: &str, label: &str) -> Result<String, CensusError> {
    if value.len() != 40
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(CensusError::new(format!(
            "Reference {label} is not a full lowercase Git hash: {value:?}"
        )));
    }
    Ok(value.to_string())
}

fn parse_fnv(value: &str) -> Result<String, CensusError> {
    let Some(hex) = value.strip_prefix("fnv1a64:") else {
        return Err(CensusError::new(format!(
            "digest does not use fnv1a64: {value:?}"
        )));
    };
    if hex.len() != 16
        || !hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(CensusError::new(format!(
            "malformed fnv1a64 digest {value:?}"
        )));
    }
    Ok(value.to_string())
}

fn parse_usize(value: &str, label: &str) -> Result<usize, CensusError> {
    value
        .parse::<usize>()
        .map_err(|_| CensusError::new(format!("{label} is not a canonical usize: {value:?}")))
}

fn contiguous_values(
    values: BTreeMap<usize, String>,
    label: &str,
) -> Result<Vec<String>, CensusError> {
    let expected = (0..values.len()).collect::<BTreeSet<_>>();
    let actual = values.keys().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(CensusError::new(format!(
            "{label} indices are not contiguous: {actual:?}"
        )));
    }
    Ok(values.into_values().collect())
}

fn unique_by<'a>(
    values: impl IntoIterator<Item = &'a str>,
    label: &str,
) -> Result<(), CensusError> {
    let mut seen = BTreeSet::new();
    for value in values {
        if !seen.insert(value) {
            return Err(CensusError::new(format!("duplicate {label} {value:?}")));
        }
    }
    Ok(())
}

fn decode_percent_escapes(value: &str) -> Result<String, CensusError> {
    let bytes = value.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'%' {
            decoded.push(bytes[index]);
            index += 1;
            continue;
        }
        if index + 2 >= bytes.len() {
            return Err(CensusError::new(format!(
                "truncated percent escape in {value:?}"
            )));
        }
        let high = hex_nibble(bytes[index + 1])
            .ok_or_else(|| CensusError::new(format!("invalid percent escape in {value:?}")))?;
        let low = hex_nibble(bytes[index + 2])
            .ok_or_else(|| CensusError::new(format!("invalid percent escape in {value:?}")))?;
        decoded.push((high << 4) | low);
        index += 3;
    }
    String::from_utf8(decoded)
        .map_err(|_| CensusError::new(format!("percent-decoded value is not UTF-8: {value:?}")))
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    value
}

pub fn fixture_content_hash(bytes: &[u8]) -> String {
    format!("fnv1a64:{:016x}", fnv1a64(bytes))
}

/// Apply the pinned Lean test suite's declared semantic normalizers without
/// invoking Perl or the shell. The first two transformations are the exact
/// behavior documented in `vendor/lean4-src/tests/util.sh`; the third maps an
/// installed toolchain's source prefix to the source-tree form that
/// `Lean.Server.Test.Runner.patchUri` emits in upstream builds.
pub fn normalize_reference_transcript(
    transcript: &str,
    toolchain_root: &Path,
) -> Result<String, CensusError> {
    let without_mvar_suffixes = normalize_mvar_suffixes(transcript)?;
    let with_reference_urls = normalize_reference_urls(&without_mvar_suffixes);
    let source_prefix = toolchain_root.join("src/lean");
    let mut source_prefix = source_prefix.to_string_lossy().replace('\\', "/");
    if !source_prefix.ends_with('/') {
        source_prefix.push('/');
    }
    canonicalize_json_regions(&with_reference_urls.replace(&source_prefix, "/src/"))
}

fn normalize_mvar_suffixes(input: &str) -> Result<String, CensusError> {
    let bytes = input.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index] != b'?' || index + 1 >= bytes.len() {
            output.push(bytes[index]);
            index += 1;
            continue;
        }
        let identifier_end = if bytes[index + 1] == b'_' {
            let mut end = index + 2;
            while bytes
                .get(end)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            {
                end += 1;
            }
            (end > index + 2).then_some(end)
        } else if bytes[index + 1].is_ascii_alphanumeric() || bytes[index + 1] == b'_' {
            Some(index + 2)
        } else {
            None
        };
        let Some(identifier_end) = identifier_end else {
            output.push(bytes[index]);
            index += 1;
            continue;
        };
        if bytes.get(identifier_end) != Some(&b'.') {
            output.push(bytes[index]);
            index += 1;
            continue;
        }
        let mut suffix_end = identifier_end + 1;
        while bytes.get(suffix_end).is_some_and(u8::is_ascii_digit) {
            suffix_end += 1;
        }
        if suffix_end == identifier_end + 1 {
            output.push(bytes[index]);
            index += 1;
            continue;
        }
        output.extend_from_slice(&bytes[index..identifier_end]);
        index = suffix_end;
    }
    String::from_utf8(output)
        .map_err(|_| CensusError::new("metavariable normalization did not preserve UTF-8"))
}

fn normalize_reference_urls(input: &str) -> String {
    const PREFIX: &str = "https://lean-lang.org/doc/reference/";
    let mut output = String::with_capacity(input.len());
    let mut remainder = input;
    while let Some(offset) = remainder.find(PREFIX) {
        output.push_str(&remainder[..offset]);
        let after_prefix = &remainder[offset + PREFIX.len()..];
        let segment_end = after_prefix.find('/').unwrap_or(after_prefix.len());
        let segment = &after_prefix[..segment_end];
        if reference_version_segment(segment) {
            output.push_str("REFERENCE");
            remainder = &after_prefix[segment_end..];
        } else {
            output.push_str(PREFIX);
            remainder = after_prefix;
        }
    }
    output.push_str(remainder);
    output
}

fn reference_version_segment(segment: &str) -> bool {
    if segment == "latest" {
        return true;
    }
    let segment = segment.strip_prefix('v').unwrap_or(segment);
    let (version, release_candidate) = segment
        .split_once("-rc")
        .map_or((segment, None), |(version, candidate)| {
            (version, Some(candidate))
        });
    !version.is_empty()
        && version
            .bytes()
            .all(|byte| byte.is_ascii_digit() || byte == b'.')
        && version.bytes().any(|byte| byte.is_ascii_digit())
        && release_candidate.is_none_or(|candidate| {
            !candidate.is_empty() && candidate.bytes().all(|byte| byte.is_ascii_digit())
        })
}

fn canonicalize_json_regions(input: &str) -> Result<String, CensusError> {
    let bytes = input.as_bytes();
    let mut output = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let starts_line = index == 0 || bytes[index - 1] == b'\n';
        if !starts_line || !matches!(bytes[index], b'{' | b'[') {
            output.push(bytes[index]);
            index += 1;
            continue;
        }
        let region_start = index;
        let mut stack = vec![bytes[index]];
        let mut in_string = false;
        let mut escaped = false;
        while index < bytes.len() {
            let byte = bytes[index];
            if in_string {
                output.push(byte);
                if escaped {
                    escaped = false;
                } else if byte == b'\\' {
                    escaped = true;
                } else if byte == b'"' {
                    in_string = false;
                }
                index += 1;
                continue;
            }
            match byte {
                b'"' => {
                    in_string = true;
                    output.push(byte);
                }
                b'{' | b'[' => {
                    if index != region_start {
                        stack.push(byte);
                    }
                    output.push(byte);
                }
                b'}' | b']' => {
                    let expected_open = if byte == b'}' { b'{' } else { b'[' };
                    if stack.pop() != Some(expected_open) {
                        return Err(CensusError::new(
                            "Reference transcript has mismatched JSON delimiters",
                        ));
                    }
                    output.push(byte);
                    index += 1;
                    if stack.is_empty() {
                        break;
                    }
                    continue;
                }
                byte if byte.is_ascii_whitespace() => {
                    index += 1;
                    continue;
                }
                _ => output.push(byte),
            }
            index += 1;
        }
        if !stack.is_empty() || in_string {
            return Err(CensusError::new(
                "Reference transcript has an unterminated top-level JSON value",
            ));
        }
    }
    String::from_utf8(output)
        .map_err(|_| CensusError::new("JSON-region normalization did not preserve UTF-8"))
}

fn framed_hash<'a>(domain: &str, lines: impl IntoIterator<Item = &'a str>) -> String {
    let mut framed = Vec::new();
    append_frame(&mut framed, domain.as_bytes());
    for line in lines {
        append_frame(&mut framed, line.as_bytes());
    }
    format!("fnv1a64:{:016x}", fnv1a64(&framed))
}

fn append_frame(buffer: &mut Vec<u8>, bytes: &[u8]) {
    buffer.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buffer.extend_from_slice(bytes);
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum WireValueKind {
    Null,
    Boolean,
    Number,
    String,
    Array,
    Object,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObjectShape {
    pub unknown_fields: Vec<String>,
}

fn expected_wire_kind(type_expression: &str) -> Option<WireValueKind> {
    let expression = type_expression
        .strip_prefix("Option ")
        .unwrap_or(type_expression);
    if expression.starts_with("Array ") || expression.starts_with("List ") {
        Some(WireValueKind::Array)
    } else if matches!(expression, "Bool") {
        Some(WireValueKind::Boolean)
    } else if matches!(
        expression,
        "Nat" | "Int" | "UInt32" | "UInt64" | "USize" | "Float"
    ) {
        Some(WireValueKind::Number)
    } else if matches!(expression, "String" | "Name" | "DocumentUri") {
        Some(WireValueKind::String)
    } else if expression == "Json" {
        None
    } else {
        Some(WireValueKind::Object)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SessionPhase {
    Start,
    AwaitingInitialized,
    Running,
    Shutdown,
    Exited,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RequestId {
    Number(i64),
    String(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RequestStatus {
    Active,
    Cancelled,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct RpcSessionState {
    uri: String,
    expires_at_ms: u64,
    refs: BTreeMap<u64, u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProtocolState {
    phase: SessionPhase,
    documents: BTreeMap<String, i64>,
    requests: BTreeMap<RequestId, RequestStatus>,
    partial_next: BTreeMap<RequestId, u64>,
    partial_closed: BTreeSet<RequestId>,
    progress: BTreeSet<String>,
    rpc_sessions: BTreeMap<u64, RpcSessionState>,
}

impl Default for ProtocolState {
    fn default() -> Self {
        Self {
            phase: SessionPhase::Start,
            documents: BTreeMap::new(),
            requests: BTreeMap::new(),
            partial_next: BTreeMap::new(),
            partial_closed: BTreeSet::new(),
            progress: BTreeSet::new(),
            rpc_sessions: BTreeMap::new(),
        }
    }
}

impl ProtocolState {
    pub fn phase(&self) -> SessionPhase {
        self.phase
    }

    pub fn document_version(&self, uri: &str) -> Option<i64> {
        self.documents.get(uri).copied()
    }

    pub fn request_is_cancelled(&self, id: &RequestId) -> bool {
        self.requests.get(id) == Some(&RequestStatus::Cancelled)
    }

    pub fn next_partial_sequence(&self, id: &RequestId) -> Option<u64> {
        self.partial_next.get(id).copied()
    }

    pub fn progress_is_active(&self, token: &str) -> bool {
        self.progress.contains(token)
    }

    pub fn rpc_ref_count(&self, session_id: u64, reference: u64) -> Option<u32> {
        self.rpc_sessions
            .get(&session_id)?
            .refs
            .get(&reference)
            .copied()
    }

    pub fn apply(
        &mut self,
        inventory: &LspInventory,
        transition: Transition,
    ) -> Result<TransitionEffect, ProtocolFault> {
        let mut candidate = self.clone();
        let effect = candidate.apply_inner(inventory, transition)?;
        *self = candidate;
        Ok(effect)
    }

    fn apply_inner(
        &mut self,
        inventory: &LspInventory,
        transition: Transition,
    ) -> Result<TransitionEffect, ProtocolFault> {
        match &transition {
            Transition::Malformed { reason } => {
                return Err(ProtocolFault::MalformedMessage(reason.clone()));
            }
            Transition::PlatformUnavailable { surface } => {
                return Err(ProtocolFault::PlatformUnavailable(surface.clone()));
            }
            _ => {}
        }
        match self.phase {
            SessionPhase::Start => match transition {
                Transition::Initialize => {
                    self.phase = SessionPhase::AwaitingInitialized;
                    Ok(TransitionEffect::Applied)
                }
                other => Err(invalid_phase(self.phase, other)),
            },
            SessionPhase::AwaitingInitialized => match transition {
                Transition::Initialized => {
                    self.phase = SessionPhase::Running;
                    Ok(TransitionEffect::Applied)
                }
                other => Err(invalid_phase(self.phase, other)),
            },
            SessionPhase::Shutdown => match transition {
                Transition::Exit => {
                    self.phase = SessionPhase::Exited;
                    Ok(TransitionEffect::Applied)
                }
                other => Err(invalid_phase(self.phase, other)),
            },
            SessionPhase::Exited => Err(invalid_phase(self.phase, transition)),
            SessionPhase::Running => self.apply_running(inventory, transition),
        }
    }

    fn apply_running(
        &mut self,
        inventory: &LspInventory,
        transition: Transition,
    ) -> Result<TransitionEffect, ProtocolFault> {
        match transition {
            Transition::ShutdownRequest => {
                self.phase = SessionPhase::Shutdown;
                Ok(TransitionEffect::Applied)
            }
            Transition::Open { uri, version } => {
                if self.documents.contains_key(&uri) {
                    return Err(ProtocolFault::DocumentAlreadyOpen(uri));
                }
                self.documents.insert(uri, version);
                Ok(TransitionEffect::Applied)
            }
            Transition::Change { uri, version } => {
                let current = self
                    .documents
                    .get_mut(&uri)
                    .ok_or_else(|| ProtocolFault::ClosedDocument(uri.clone()))?;
                if version <= *current {
                    return Err(ProtocolFault::StaleDocumentVersion {
                        uri,
                        current: *current,
                        received: version,
                    });
                }
                *current = version;
                Ok(TransitionEffect::Applied)
            }
            Transition::Close { uri } => {
                if self.documents.remove(&uri).is_none() {
                    return Err(ProtocolFault::ClosedDocument(uri));
                }
                self.rpc_sessions.retain(|_, session| session.uri != uri);
                Ok(TransitionEffect::Applied)
            }
            Transition::Request {
                id,
                method,
                document,
            } => {
                if !inventory.accepts_client_request(&method) {
                    return Err(ProtocolFault::UnknownMethod(method));
                }
                let contract = inventory
                    .method(&method)
                    .ok_or_else(|| ProtocolFault::UnknownMethod(method.clone()))?;
                if contract.policy.lifecycle == "document" {
                    let uri = document.ok_or_else(|| {
                        ProtocolFault::MalformedMessage(format!(
                            "document-scoped request {method} has no document"
                        ))
                    })?;
                    if !self.documents.contains_key(&uri) {
                        return Err(ProtocolFault::ClosedDocument(uri));
                    }
                }
                if self.requests.contains_key(&id) {
                    return Err(ProtocolFault::DuplicateRequestId(id));
                }
                self.requests.insert(id.clone(), RequestStatus::Active);
                self.partial_next.insert(id, 0);
                Ok(TransitionEffect::Applied)
            }
            Transition::CompleteRequest { id } => {
                if self.requests.remove(&id).is_none() {
                    return Err(ProtocolFault::UnknownRequestId(id));
                }
                self.partial_next.remove(&id);
                self.partial_closed.remove(&id);
                Ok(TransitionEffect::Applied)
            }
            Transition::CancelRequest { id } => {
                let status = self
                    .requests
                    .get_mut(&id)
                    .ok_or_else(|| ProtocolFault::UnknownRequestId(id.clone()))?;
                *status = RequestStatus::Cancelled;
                Ok(TransitionEffect::Applied)
            }
            Transition::PartialResult {
                id,
                sequence,
                terminal,
            } => {
                if !self.requests.contains_key(&id) {
                    return Err(ProtocolFault::UnknownRequestId(id));
                }
                if self.partial_closed.contains(&id) {
                    return Err(ProtocolFault::PartialResultAfterFinal(id));
                }
                let expected = self
                    .partial_next
                    .get(&id)
                    .copied()
                    .ok_or_else(|| ProtocolFault::PartialResultAfterFinal(id.clone()))?;
                if sequence != expected {
                    return Err(ProtocolFault::OutOfOrderPartialResult {
                        id,
                        expected,
                        received: sequence,
                    });
                }
                self.partial_next.insert(
                    id.clone(),
                    expected
                        .checked_add(1)
                        .ok_or_else(|| ProtocolFault::PartialSequenceExhausted(id.clone()))?,
                );
                if terminal {
                    self.partial_closed.insert(id);
                }
                Ok(TransitionEffect::Applied)
            }
            Transition::BeginProgress { token } => {
                if !self.progress.insert(token.clone()) {
                    return Err(ProtocolFault::DuplicateProgressToken(token));
                }
                Ok(TransitionEffect::Applied)
            }
            Transition::EndProgress { token } => {
                if !self.progress.remove(&token) {
                    return Err(ProtocolFault::UnknownProgressToken(token));
                }
                Ok(TransitionEffect::Applied)
            }
            Transition::UnknownNotification { .. } => Ok(TransitionEffect::Ignored),
            Transition::RpcConnect {
                uri,
                session_id,
                now_ms,
            } => {
                if !self.documents.contains_key(&uri) {
                    return Err(ProtocolFault::ClosedDocument(uri));
                }
                if self.rpc_sessions.contains_key(&session_id) {
                    return Err(ProtocolFault::DuplicateRpcSession(session_id));
                }
                self.rpc_sessions.insert(
                    session_id,
                    RpcSessionState {
                        uri,
                        expires_at_ms: now_ms.saturating_add(RPC_KEEP_ALIVE_MS),
                        refs: BTreeMap::new(),
                    },
                );
                Ok(TransitionEffect::Applied)
            }
            Transition::RpcKeepAlive { session_id, now_ms } => {
                let session = self
                    .rpc_sessions
                    .get_mut(&session_id)
                    .ok_or(ProtocolFault::RpcNeedsReconnect(session_id))?;
                if now_ms >= session.expires_at_ms {
                    return Err(ProtocolFault::RpcNeedsReconnect(session_id));
                }
                session.expires_at_ms = now_ms.saturating_add(RPC_KEEP_ALIVE_MS);
                Ok(TransitionEffect::Applied)
            }
            Transition::RpcAcquireRef {
                session_id,
                reference,
            } => {
                let session = self
                    .rpc_sessions
                    .get_mut(&session_id)
                    .ok_or(ProtocolFault::RpcNeedsReconnect(session_id))?;
                let count = session.refs.entry(reference).or_default();
                *count = count
                    .checked_add(1)
                    .ok_or(ProtocolFault::ReferenceCountExhausted {
                        session_id,
                        reference,
                    })?;
                Ok(TransitionEffect::Applied)
            }
            Transition::RpcReleaseRef {
                session_id,
                reference,
            } => {
                let session = self
                    .rpc_sessions
                    .get_mut(&session_id)
                    .ok_or(ProtocolFault::RpcNeedsReconnect(session_id))?;
                let count =
                    session
                        .refs
                        .get_mut(&reference)
                        .ok_or(ProtocolFault::UnknownRpcReference {
                            session_id,
                            reference,
                        })?;
                *count -= 1;
                if *count == 0 {
                    session.refs.remove(&reference);
                }
                Ok(TransitionEffect::Applied)
            }
            Transition::RpcExpire { session_id, now_ms } => {
                let session = self
                    .rpc_sessions
                    .get(&session_id)
                    .ok_or(ProtocolFault::RpcNeedsReconnect(session_id))?;
                if now_ms < session.expires_at_ms {
                    return Err(ProtocolFault::RpcSessionNotExpired {
                        session_id,
                        expires_at_ms: session.expires_at_ms,
                        now_ms,
                    });
                }
                self.rpc_sessions.remove(&session_id);
                Ok(TransitionEffect::Applied)
            }
            Transition::Initialize
            | Transition::Initialized
            | Transition::Exit
            | Transition::Malformed { .. }
            | Transition::PlatformUnavailable { .. } => Err(invalid_phase(self.phase, transition)),
        }
    }
}

fn invalid_phase(phase: SessionPhase, transition: Transition) -> ProtocolFault {
    ProtocolFault::InvalidLifecycle {
        phase,
        transition: transition.name(),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Transition {
    Initialize,
    Initialized,
    ShutdownRequest,
    Exit,
    Open {
        uri: String,
        version: i64,
    },
    Change {
        uri: String,
        version: i64,
    },
    Close {
        uri: String,
    },
    Request {
        id: RequestId,
        method: String,
        document: Option<String>,
    },
    CompleteRequest {
        id: RequestId,
    },
    CancelRequest {
        id: RequestId,
    },
    PartialResult {
        id: RequestId,
        sequence: u64,
        terminal: bool,
    },
    BeginProgress {
        token: String,
    },
    EndProgress {
        token: String,
    },
    UnknownNotification {
        method: String,
    },
    RpcConnect {
        uri: String,
        session_id: u64,
        now_ms: u64,
    },
    RpcKeepAlive {
        session_id: u64,
        now_ms: u64,
    },
    RpcAcquireRef {
        session_id: u64,
        reference: u64,
    },
    RpcReleaseRef {
        session_id: u64,
        reference: u64,
    },
    RpcExpire {
        session_id: u64,
        now_ms: u64,
    },
    Malformed {
        reason: String,
    },
    PlatformUnavailable {
        surface: String,
    },
}

impl Transition {
    fn name(&self) -> &'static str {
        match self {
            Self::Initialize => "initialize",
            Self::Initialized => "initialized",
            Self::ShutdownRequest => "shutdown",
            Self::Exit => "exit",
            Self::Open { .. } => "open",
            Self::Change { .. } => "change",
            Self::Close { .. } => "close",
            Self::Request { .. } => "request",
            Self::CompleteRequest { .. } => "complete_request",
            Self::CancelRequest { .. } => "cancel_request",
            Self::PartialResult { .. } => "partial_result",
            Self::BeginProgress { .. } => "begin_progress",
            Self::EndProgress { .. } => "end_progress",
            Self::UnknownNotification { .. } => "unknown_notification",
            Self::RpcConnect { .. } => "rpc_connect",
            Self::RpcKeepAlive { .. } => "rpc_keep_alive",
            Self::RpcAcquireRef { .. } => "rpc_acquire_ref",
            Self::RpcReleaseRef { .. } => "rpc_release_ref",
            Self::RpcExpire { .. } => "rpc_expire",
            Self::Malformed { .. } => "malformed",
            Self::PlatformUnavailable { .. } => "platform_unavailable",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TransitionEffect {
    Applied,
    Ignored,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProtocolFault {
    InvalidLifecycle {
        phase: SessionPhase,
        transition: &'static str,
    },
    MalformedMessage(String),
    UnknownMethod(String),
    UnknownSchema(String),
    MissingField {
        schema: String,
        field: String,
    },
    WrongFieldType {
        schema: String,
        field: String,
        expected: WireValueKind,
        actual: WireValueKind,
    },
    DocumentAlreadyOpen(String),
    ClosedDocument(String),
    StaleDocumentVersion {
        uri: String,
        current: i64,
        received: i64,
    },
    DuplicateRequestId(RequestId),
    UnknownRequestId(RequestId),
    OutOfOrderPartialResult {
        id: RequestId,
        expected: u64,
        received: u64,
    },
    PartialResultAfterFinal(RequestId),
    PartialSequenceExhausted(RequestId),
    DuplicateProgressToken(String),
    UnknownProgressToken(String),
    DuplicateRpcSession(u64),
    RpcNeedsReconnect(u64),
    RpcSessionNotExpired {
        session_id: u64,
        expires_at_ms: u64,
        now_ms: u64,
    },
    UnknownRpcReference {
        session_id: u64,
        reference: u64,
    },
    ReferenceCountExhausted {
        session_id: u64,
        reference: u64,
    },
    UnsupportedRpcWireVersion(String),
    PlatformUnavailable(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RpcWireVersion {
    V0,
    V1,
}

pub fn parse_rpc_wire_version(value: &str) -> Result<RpcWireVersion, ProtocolFault> {
    match value {
        "v0" => Ok(RpcWireVersion::V0),
        "v1" => Ok(RpcWireVersion::V1),
        other => Err(ProtocolFault::UnsupportedRpcWireVersion(other.to_string())),
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct ClientCapabilityOffer {
    pub incremental_diagnostics: Option<bool>,
    pub silent_diagnostics: Option<bool>,
    pub rpc_wire_format: Option<RpcWireVersion>,
    pub widgets: Option<bool>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NegotiatedCapabilities {
    pub incremental_diagnostics: bool,
    pub silent_diagnostics: bool,
    pub rpc_wire_format: RpcWireVersion,
    pub widgets: bool,
    pub position_encoding: PositionEncoding,
}

pub fn negotiate_capabilities(offer: ClientCapabilityOffer) -> NegotiatedCapabilities {
    NegotiatedCapabilities {
        incremental_diagnostics: offer.incremental_diagnostics.unwrap_or(false),
        silent_diagnostics: offer.silent_diagnostics.unwrap_or(false),
        rpc_wire_format: offer.rpc_wire_format.unwrap_or(RpcWireVersion::V0),
        widgets: offer.widgets.unwrap_or(false),
        position_encoding: PositionEncoding::Utf16,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PositionEncoding {
    Utf16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Position {
    pub line: usize,
    pub character: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PositionError {
    LineOutOfRange {
        line: usize,
        line_count: usize,
    },
    CharacterOutOfRange {
        line: usize,
        character: usize,
        utf16_len: usize,
    },
    InsideSurrogatePair {
        line: usize,
        character: usize,
    },
}

pub fn position_to_byte(text: &str, position: Position) -> Result<usize, PositionError> {
    let lines = line_spans(text);
    let Some((start, end)) = lines.get(position.line).copied() else {
        return Err(PositionError::LineOutOfRange {
            line: position.line,
            line_count: lines.len(),
        });
    };
    let line = &text[start..end];
    let mut utf16 = 0;
    for (offset, character) in line.char_indices() {
        if utf16 == position.character {
            return Ok(start + offset);
        }
        let next = utf16 + character.len_utf16();
        if position.character > utf16 && position.character < next {
            return Err(PositionError::InsideSurrogatePair {
                line: position.line,
                character: position.character,
            });
        }
        utf16 = next;
    }
    if utf16 == position.character {
        Ok(end)
    } else {
        Err(PositionError::CharacterOutOfRange {
            line: position.line,
            character: position.character,
            utf16_len: utf16,
        })
    }
}

pub fn byte_to_position(text: &str, byte: usize) -> Option<Position> {
    if byte > text.len() || !text.is_char_boundary(byte) {
        return None;
    }
    let lines = line_spans(text);
    for (line_number, (start, end)) in lines.into_iter().enumerate() {
        if byte >= start && byte <= end {
            let prefix = &text[start..byte];
            return Some(Position {
                line: line_number,
                character: prefix.encode_utf16().count(),
            });
        }
    }
    None
}

fn line_spans(text: &str) -> Vec<(usize, usize)> {
    let mut spans = Vec::new();
    let mut start = 0;
    for (index, byte) in text.bytes().enumerate() {
        if byte == b'\n' {
            let end = if index > start && text.as_bytes()[index - 1] == b'\r' {
                index - 1
            } else {
                index
            };
            spans.push((start, end));
            start = index + 1;
        }
    }
    spans.push((start, text.len()));
    spans
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SemanticDisposition {
    Request,
    Result,
    Error,
    Cancelled,
    Notification,
}

impl SemanticDisposition {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Request => "request",
            Self::Result => "result",
            Self::Error => "error",
            Self::Cancelled => "cancelled",
            Self::Notification => "notification",
        }
    }

    fn parse(value: &str) -> Result<Self, CensusError> {
        match value {
            "request" => Ok(Self::Request),
            "result" => Ok(Self::Result),
            "error" => Ok(Self::Error),
            "cancelled" => Ok(Self::Cancelled),
            "notification" => Ok(Self::Notification),
            other => Err(CensusError::new(format!(
                "unknown semantic disposition {other:?}"
            ))),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticEvent {
    pub sequence: u64,
    pub epoch_id: String,
    pub client_id: String,
    pub capability_id: String,
    pub session_id: String,
    pub document_id: String,
    pub document_version: u64,
    pub request_id: String,
    pub fixture_id: String,
    pub comparison_id: String,
    pub direction: MessageDirection,
    pub method_id: String,
    pub parameter_schema_id: String,
    pub response_schema_id: String,
    pub expected_disposition: SemanticDisposition,
    pub actual_disposition: SemanticDisposition,
    pub expected_message_root: String,
    pub actual_message_root: String,
    pub expected_error_code: String,
    pub actual_error_code: String,
    pub authority_root: String,
    pub resource_state: String,
    pub cleanup_state: String,
    pub final_state: String,
}

impl SemanticEvent {
    fn render(&self) -> String {
        format!(
            "{{\"schema\":\"{SEMANTIC_SCHEMA}\",\"sequence\":{},\"epoch_id\":{},\
             \"client_id\":{},\"capability_id\":{},\"session_id\":{},\"document_id\":{},\
             \"document_version\":{},\"request_id\":{},\"fixture_id\":{},\
             \"comparison_id\":{},\"direction\":\"{}\",\"method_id\":{},\
             \"parameter_schema_id\":{},\"response_schema_id\":{},\
             \"expected_disposition\":\"{}\",\"actual_disposition\":\"{}\",\
             \"expected_message_root\":{},\"actual_message_root\":{},\
             \"expected_error_code\":{},\"actual_error_code\":{},\"authority_root\":{},\
             \"resource_state\":{},\"cleanup_state\":{},\"final_state\":{}}}",
            self.sequence,
            json_string(&self.epoch_id),
            json_string(&self.client_id),
            json_string(&self.capability_id),
            json_string(&self.session_id),
            json_string(&self.document_id),
            self.document_version,
            json_string(&self.request_id),
            json_string(&self.fixture_id),
            json_string(&self.comparison_id),
            self.direction.as_str(),
            json_string(&self.method_id),
            json_string(&self.parameter_schema_id),
            json_string(&self.response_schema_id),
            self.expected_disposition.as_str(),
            self.actual_disposition.as_str(),
            json_string(&self.expected_message_root),
            json_string(&self.actual_message_root),
            json_string(&self.expected_error_code),
            json_string(&self.actual_error_code),
            json_string(&self.authority_root),
            json_string(&self.resource_state),
            json_string(&self.cleanup_state),
            json_string(&self.final_state),
        )
    }

    fn parse(line: &str) -> Result<Self, CensusError> {
        let values = parse_flat_json_object(line)?;
        require_json_keys(
            &values,
            &[
                "schema",
                "sequence",
                "epoch_id",
                "client_id",
                "capability_id",
                "session_id",
                "document_id",
                "document_version",
                "request_id",
                "fixture_id",
                "comparison_id",
                "direction",
                "method_id",
                "parameter_schema_id",
                "response_schema_id",
                "expected_disposition",
                "actual_disposition",
                "expected_message_root",
                "actual_message_root",
                "expected_error_code",
                "actual_error_code",
                "authority_root",
                "resource_state",
                "cleanup_state",
                "final_state",
            ],
        )?;
        if string_json_field(&values, "schema")? != SEMANTIC_SCHEMA {
            return Err(CensusError::new("semantic NDJSON schema mismatch"));
        }
        let event = Self {
            sequence: number_json_field(&values, "sequence")?,
            epoch_id: string_json_field(&values, "epoch_id")?.to_string(),
            client_id: string_json_field(&values, "client_id")?.to_string(),
            capability_id: string_json_field(&values, "capability_id")?.to_string(),
            session_id: string_json_field(&values, "session_id")?.to_string(),
            document_id: string_json_field(&values, "document_id")?.to_string(),
            document_version: number_json_field(&values, "document_version")?,
            request_id: string_json_field(&values, "request_id")?.to_string(),
            fixture_id: string_json_field(&values, "fixture_id")?.to_string(),
            comparison_id: string_json_field(&values, "comparison_id")?.to_string(),
            direction: MessageDirection::parse(string_json_field(&values, "direction")?)?,
            method_id: string_json_field(&values, "method_id")?.to_string(),
            parameter_schema_id: string_json_field(&values, "parameter_schema_id")?.to_string(),
            response_schema_id: string_json_field(&values, "response_schema_id")?.to_string(),
            expected_disposition: SemanticDisposition::parse(string_json_field(
                &values,
                "expected_disposition",
            )?)?,
            actual_disposition: SemanticDisposition::parse(string_json_field(
                &values,
                "actual_disposition",
            )?)?,
            expected_message_root: parse_fnv(string_json_field(&values, "expected_message_root")?)?,
            actual_message_root: parse_fnv(string_json_field(&values, "actual_message_root")?)?,
            expected_error_code: string_json_field(&values, "expected_error_code")?.to_string(),
            actual_error_code: string_json_field(&values, "actual_error_code")?.to_string(),
            authority_root: parse_fnv(string_json_field(&values, "authority_root")?)?,
            resource_state: string_json_field(&values, "resource_state")?.to_string(),
            cleanup_state: string_json_field(&values, "cleanup_state")?.to_string(),
            final_state: string_json_field(&values, "final_state")?.to_string(),
        };
        if event.render() != line {
            return Err(CensusError::new(
                "semantic NDJSON line is valid-shaped but noncanonical",
            ));
        }
        Ok(event)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TelemetryEvent {
    pub sequence: u64,
    pub elapsed_micros: u64,
    pub worker: String,
    pub detail: String,
}

impl TelemetryEvent {
    fn render(&self) -> String {
        format!(
            "{{\"schema\":\"{TELEMETRY_SCHEMA}\",\"sequence\":{},\"elapsed_micros\":{},\
             \"worker\":{},\"detail\":{}}}",
            self.sequence,
            self.elapsed_micros,
            json_string(&self.worker),
            json_string(&self.detail),
        )
    }

    fn parse(line: &str) -> Result<Self, CensusError> {
        let values = parse_flat_json_object(line)?;
        require_json_keys(
            &values,
            &["schema", "sequence", "elapsed_micros", "worker", "detail"],
        )?;
        if string_json_field(&values, "schema")? != TELEMETRY_SCHEMA {
            return Err(CensusError::new("telemetry NDJSON schema mismatch"));
        }
        let event = Self {
            sequence: number_json_field(&values, "sequence")?,
            elapsed_micros: number_json_field(&values, "elapsed_micros")?,
            worker: string_json_field(&values, "worker")?.to_string(),
            detail: string_json_field(&values, "detail")?.to_string(),
        };
        if event.render() != line {
            return Err(CensusError::new(
                "telemetry NDJSON line is valid-shaped but noncanonical",
            ));
        }
        Ok(event)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TranscriptBundle {
    semantic: Vec<SemanticEvent>,
    telemetry: Vec<TelemetryEvent>,
}

impl TranscriptBundle {
    pub fn new(
        semantic: Vec<SemanticEvent>,
        telemetry: Vec<TelemetryEvent>,
    ) -> Result<Self, CensusError> {
        validate_sequences(
            semantic.iter().map(|event| event.sequence),
            "semantic transcript",
        )?;
        validate_sequences(
            telemetry.iter().map(|event| event.sequence),
            "telemetry transcript",
        )?;
        Ok(Self {
            semantic,
            telemetry,
        })
    }

    pub fn from_ndjson(semantic: &str, telemetry: &str) -> Result<Self, CensusError> {
        let semantic = parse_ndjson(semantic, SemanticEvent::parse)?;
        let telemetry = parse_ndjson(telemetry, TelemetryEvent::parse)?;
        Self::new(semantic, telemetry)
    }

    pub fn semantic_ndjson(&self) -> String {
        render_ndjson(self.semantic.iter().map(SemanticEvent::render))
    }

    pub fn telemetry_ndjson(&self) -> String {
        render_ndjson(self.telemetry.iter().map(TelemetryEvent::render))
    }

    pub fn semantic_root(&self) -> String {
        hash(Domain::Fixture, self.semantic_ndjson().as_bytes()).to_hex()
    }

    pub fn telemetry_root(&self) -> String {
        hash(Domain::OperationalMeta, self.telemetry_ndjson().as_bytes()).to_hex()
    }

    pub fn semantic_events(&self) -> &[SemanticEvent] {
        &self.semantic
    }

    pub fn telemetry_events(&self) -> &[TelemetryEvent] {
        &self.telemetry
    }
}

fn render_ndjson(lines: impl IntoIterator<Item = String>) -> String {
    let mut output = String::new();
    for line in lines {
        output.push_str(&line);
        output.push('\n');
    }
    output
}

fn parse_ndjson<T>(
    text: &str,
    parse: impl Fn(&str) -> Result<T, CensusError>,
) -> Result<Vec<T>, CensusError> {
    if !text.is_empty() && !text.ends_with('\n') {
        return Err(CensusError::new(
            "nonempty NDJSON stream lacks its canonical final newline",
        ));
    }
    text.lines().map(parse).collect()
}

fn validate_sequences(
    values: impl IntoIterator<Item = u64>,
    label: &str,
) -> Result<(), CensusError> {
    for (expected, actual) in values.into_iter().enumerate() {
        if actual != expected as u64 {
            return Err(CensusError::new(format!(
                "{label} sequence {actual} occurs at position {expected}"
            )));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum FlatJsonValue {
    String(String),
    Number(u64),
}

fn parse_flat_json_object(line: &str) -> Result<BTreeMap<String, FlatJsonValue>, CensusError> {
    let bytes = line.as_bytes();
    let mut cursor = 0;
    expect_byte(bytes, &mut cursor, b'{')?;
    let mut values = BTreeMap::new();
    if bytes.get(cursor) == Some(&b'}') {
        cursor += 1;
    } else {
        loop {
            let key = parse_json_string(bytes, &mut cursor)?;
            expect_byte(bytes, &mut cursor, b':')?;
            let value = if bytes.get(cursor) == Some(&b'"') {
                FlatJsonValue::String(parse_json_string(bytes, &mut cursor)?)
            } else {
                let start = cursor;
                while bytes.get(cursor).is_some_and(u8::is_ascii_digit) {
                    cursor += 1;
                }
                if start == cursor {
                    return Err(CensusError::new(
                        "flat NDJSON value is neither a string nor an unsigned integer",
                    ));
                }
                let number = std::str::from_utf8(&bytes[start..cursor])
                    .ok()
                    .and_then(|value| value.parse::<u64>().ok())
                    .ok_or_else(|| CensusError::new("invalid NDJSON unsigned integer"))?;
                FlatJsonValue::Number(number)
            };
            if values.insert(key.clone(), value).is_some() {
                return Err(CensusError::new(format!(
                    "duplicate NDJSON object key {key:?}"
                )));
            }
            match bytes.get(cursor) {
                Some(b',') => cursor += 1,
                Some(b'}') => {
                    cursor += 1;
                    break;
                }
                _ => {
                    return Err(CensusError::new(
                        "flat NDJSON object has malformed separator",
                    ));
                }
            }
        }
    }
    if cursor != bytes.len() {
        return Err(CensusError::new(
            "flat NDJSON object has trailing bytes or whitespace",
        ));
    }
    Ok(values)
}

fn require_json_keys(
    values: &BTreeMap<String, FlatJsonValue>,
    expected: &[&str],
) -> Result<(), CensusError> {
    let actual = values.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(CensusError::new(format!(
            "NDJSON key set is {actual:?}, expected {expected:?}"
        )));
    }
    Ok(())
}

fn string_json_field<'a>(
    values: &'a BTreeMap<String, FlatJsonValue>,
    name: &str,
) -> Result<&'a str, CensusError> {
    match values.get(name) {
        Some(FlatJsonValue::String(value)) => Ok(value),
        Some(FlatJsonValue::Number(_)) => Err(CensusError::new(format!(
            "NDJSON field {name} must be a string"
        ))),
        None => Err(CensusError::new(format!("NDJSON field {name} is absent"))),
    }
}

fn number_json_field(
    values: &BTreeMap<String, FlatJsonValue>,
    name: &str,
) -> Result<u64, CensusError> {
    match values.get(name) {
        Some(FlatJsonValue::Number(value)) => Ok(*value),
        Some(FlatJsonValue::String(_)) => Err(CensusError::new(format!(
            "NDJSON field {name} must be an unsigned integer"
        ))),
        None => Err(CensusError::new(format!("NDJSON field {name} is absent"))),
    }
}

fn expect_byte(bytes: &[u8], cursor: &mut usize, expected: u8) -> Result<(), CensusError> {
    if bytes.get(*cursor) != Some(&expected) {
        return Err(CensusError::new(format!(
            "NDJSON expected byte {:?} at offset {}",
            char::from(expected),
            *cursor
        )));
    }
    *cursor += 1;
    Ok(())
}

fn parse_json_string(bytes: &[u8], cursor: &mut usize) -> Result<String, CensusError> {
    expect_byte(bytes, cursor, b'"')?;
    let mut output = Vec::new();
    while let Some(byte) = bytes.get(*cursor).copied() {
        *cursor += 1;
        match byte {
            b'"' => {
                return String::from_utf8(output)
                    .map_err(|_| CensusError::new("NDJSON string is not UTF-8"));
            }
            b'\\' => {
                let escape = bytes
                    .get(*cursor)
                    .copied()
                    .ok_or_else(|| CensusError::new("truncated NDJSON string escape"))?;
                *cursor += 1;
                match escape {
                    b'"' | b'\\' | b'/' => output.push(escape),
                    b'b' => output.push(0x08),
                    b'f' => output.push(0x0c),
                    b'n' => output.push(b'\n'),
                    b'r' => output.push(b'\r'),
                    b't' => output.push(b'\t'),
                    b'u' => {
                        let first = parse_json_hex_quad(bytes, cursor)?;
                        let scalar = if (0xd800..=0xdbff).contains(&first) {
                            if bytes.get(*cursor) != Some(&b'\\')
                                || bytes.get(*cursor + 1) != Some(&b'u')
                            {
                                return Err(CensusError::new(
                                    "high surrogate lacks a low-surrogate NDJSON escape",
                                ));
                            }
                            *cursor += 2;
                            let second = parse_json_hex_quad(bytes, cursor)?;
                            if !(0xdc00..=0xdfff).contains(&second) {
                                return Err(CensusError::new(
                                    "high surrogate has an invalid NDJSON low surrogate",
                                ));
                            }
                            0x1_0000
                                + ((u32::from(first) - 0xd800) << 10)
                                + (u32::from(second) - 0xdc00)
                        } else if (0xdc00..=0xdfff).contains(&first) {
                            return Err(CensusError::new(
                                "unpaired low surrogate in NDJSON string",
                            ));
                        } else {
                            u32::from(first)
                        };
                        let character = char::from_u32(scalar)
                            .ok_or_else(|| CensusError::new("invalid NDJSON Unicode scalar"))?;
                        let mut encoded = [0_u8; 4];
                        output.extend_from_slice(character.encode_utf8(&mut encoded).as_bytes());
                    }
                    _ => {
                        return Err(CensusError::new(
                            "unsupported escape in canonical NDJSON string",
                        ));
                    }
                }
            }
            0x00..=0x1f => {
                return Err(CensusError::new("unescaped control byte in NDJSON string"));
            }
            other => output.push(other),
        }
    }
    Err(CensusError::new("unterminated NDJSON string"))
}

fn parse_json_hex_quad(bytes: &[u8], cursor: &mut usize) -> Result<u16, CensusError> {
    let mut value = 0_u16;
    for _ in 0..4 {
        let byte = bytes
            .get(*cursor)
            .copied()
            .ok_or_else(|| CensusError::new("truncated NDJSON Unicode escape"))?;
        *cursor += 1;
        let nibble = hex_nibble(byte)
            .ok_or_else(|| CensusError::new("invalid hexadecimal NDJSON Unicode escape"))?;
        value = (value << 4) | u16::from(nibble);
    }
    Ok(value)
}

fn json_string(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                use fmt::Write as _;
                let _ = write!(output, "\\u{:04x}", u32::from(character));
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    fn inventory() -> LspInventory {
        LspInventory::load_embedded().expect("the checked-in LSP census must parse")
    }

    fn running_state(inventory: &LspInventory) -> ProtocolState {
        let mut state = ProtocolState::default();
        assert_eq!(
            state.apply(inventory, Transition::Initialize),
            Ok(TransitionEffect::Applied)
        );
        assert_eq!(
            state.apply(inventory, Transition::Initialized),
            Ok(TransitionEffect::Applied)
        );
        state
    }

    fn semantic_event(
        sequence: u64,
        direction: MessageDirection,
        method_id: &str,
        disposition: SemanticDisposition,
        message_root: &str,
    ) -> SemanticEvent {
        SemanticEvent {
            sequence,
            epoch_id: "8c9756b28d64dab099da31a4c09229a9e6a2ef35".to_string(),
            client_id: "unit-profile".to_string(),
            capability_id: "unit-capabilities".to_string(),
            session_id: "session-0".to_string(),
            document_id: "file:///Main.lean".to_string(),
            document_version: 1,
            request_id: sequence.to_string(),
            fixture_id: "unit-fixture".to_string(),
            comparison_id: "exact".to_string(),
            direction,
            method_id: method_id.to_string(),
            parameter_schema_id: "Params".to_string(),
            response_schema_id: "Result".to_string(),
            expected_disposition: disposition,
            actual_disposition: disposition,
            expected_message_root: message_root.to_string(),
            actual_message_root: message_root.to_string(),
            expected_error_code: "none".to_string(),
            actual_error_code: "none".to_string(),
            authority_root: "fnv1a64:0000000000000000".to_string(),
            resource_state: "bounded".to_string(),
            cleanup_state: "complete".to_string(),
            final_state: "exited".to_string(),
        }
    }

    fn manifest_event(
        inventory: &LspInventory,
        method: &ProtocolMethod,
        sequence: u64,
    ) -> SemanticEvent {
        let document_bound = matches!(method.policy.lifecycle.as_str(), "document" | "rpc_session");
        SemanticEvent {
            sequence,
            epoch_id: inventory.reference.commit.clone(),
            client_id: method.policy.client.clone(),
            capability_id: "unit-complete-profile".to_string(),
            session_id: "unit-session".to_string(),
            document_id: if document_bound {
                "file:///Unit.lean"
            } else {
                "none"
            }
            .to_string(),
            document_version: u64::from(document_bound) * 2,
            request_id: sequence.to_string(),
            fixture_id: method.fixture.clone(),
            comparison_id: method.policy.comparison.clone(),
            direction: method.direction,
            method_id: method.key.clone(),
            parameter_schema_id: method.parameter_type.clone(),
            response_schema_id: method.response_type.clone(),
            expected_disposition: SemanticDisposition::Result,
            actual_disposition: SemanticDisposition::Result,
            expected_message_root: "fnv1a64:0000000000000001".to_string(),
            actual_message_root: "fnv1a64:0000000000000001".to_string(),
            expected_error_code: "none".to_string(),
            actual_error_code: "none".to_string(),
            authority_root: inventory.inventory_root.clone(),
            resource_state: format!("probe={}", method.probe),
            cleanup_state: "document=closed;rpc=released;server=exited".to_string(),
            final_state: "manifest-complete".to_string(),
        }
    }

    fn reseal_inventory(inventory_text: &str, policy_text: &str) -> String {
        let mut lines = inventory_text
            .lines()
            .map(str::to_string)
            .collect::<Vec<_>>();
        let raw_begin = lines
            .iter()
            .position(|line| line == "raw-begin")
            .expect("raw begin");
        let raw_end = lines
            .iter()
            .position(|line| line == "raw-end")
            .expect("raw end");
        lines[raw_end + 1] = format!(
            "raw-root {}",
            framed_hash(
                "fln-lsp-wire-raw/1",
                lines[raw_begin + 1..raw_end].iter().map(String::as_str),
            )
        );
        lines[raw_end + 2] = format!(
            "policy-root {}",
            framed_hash("fln-lsp-wire-policy/1", policy_text.lines())
        );
        let inventory_root = framed_hash(
            "fln-lsp-wire-inventory/1",
            lines[..lines.len() - 1].iter().map(String::as_str),
        );
        let last = lines.len() - 1;
        lines[last] = format!("inventory-root {inventory_root}");
        lines.join("\n") + "\n"
    }

    #[test]
    fn lsp_method_schema_inventory() {
        let inventory = inventory();
        assert_eq!(inventory.methods.len(), 59);
        assert_eq!(inventory.schemas.len(), 208);
        assert_eq!(inventory.fields.len(), 491);
        assert_eq!(inventory.capabilities.len(), 19);
        assert_eq!(inventory.lifecycle.len(), 21);
        assert_eq!(inventory.fixtures.len(), 8);
        assert_eq!(inventory.reference.tag, "v4.32.0");
        assert_eq!(
            inventory.reference.commit,
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
        );
        assert_eq!(
            inventory.reference.tree,
            "ba16913719a2f6a15a826918fbe6ba9dd5413e91"
        );
        assert!(inventory.method("initialize").is_some());
        assert!(inventory.method("$/lean/plainGoal").is_some());
        assert!(inventory.method("$/lean/rpc/call").is_some());
        assert!(
            inventory
                .rpc_method("Lean.Widget.getInteractiveGoals")
                .is_some()
        );
        assert!(
            inventory
                .schema_named("InitializeParams")
                .is_some_and(|schema| schema.declared_field_count == 7)
        );
        for (key, value) in [
            ("request-method-not-found", "method_not_found_error"),
            ("request-invalid-params", "invalid_params_error"),
            ("request-cancelled", "request_cancelled_error"),
            ("rpc-method-not-found", "method_not_found_error"),
            ("rpc-invalid-params", "invalid_params_error"),
            ("partial-inlay-refresh-ms", "500"),
            ("partial-semantic-refresh-ms", "2000"),
        ] {
            assert_eq!(
                inventory
                    .lifecycle_fact(key)
                    .map(|fact| fact.value.as_str()),
                Some(value)
            );
        }
        inventory
            .validate_workspace_sources(&crate::pin::workspace_root())
            .expect("every source binding must still match this checkout");

        let raw_drift = INVENTORY_TEXT.replacen("parameter=CancelParams", "parameter=Empty", 1);
        assert!(
            LspInventory::parse(&raw_drift, POLICY_TEXT)
                .expect_err("raw drift must invalidate its root")
                .to_string()
                .contains("raw root mismatch")
        );
        let policy_drift = POLICY_TEXT.replacen("lifecycle=request", "lifecycle=document", 1);
        assert!(
            LspInventory::parse(INVENTORY_TEXT, &policy_drift)
                .expect_err("reviewed policy drift must invalidate only the policy join")
                .to_string()
                .contains("policy root mismatch")
        );

        let probe_drift =
            INVENTORY_TEXT.replacen("probe=real-request-dispatch", "probe=source-only", 1);
        assert!(
            LspInventory::parse(&reseal_inventory(&probe_drift, POLICY_TEXT), POLICY_TEXT)
                .expect_err("a source-only probe cannot replace the real method matrix")
                .to_string()
                .contains("manifest-complete real probe")
        );
        let legend_drift = INVENTORY_TEXT.replacen(
            "legend-type index=0 name=keyword",
            "legend-type index=0 name=word",
            1,
        );
        assert!(
            LspInventory::parse(&reseal_inventory(&legend_drift, POLICY_TEXT), POLICY_TEXT)
                .expect_err("an altered semantic legend must be refused after resealing")
                .to_string()
                .contains("ordered legend")
        );

        let lifecycle_row = INVENTORY_TEXT
            .lines()
            .find(|line| line.starts_with("lifecycle key=request-invalid-params "))
            .expect("request-invalid-params lifecycle row");
        let missing_error = INVENTORY_TEXT
            .replace(&format!("{lifecycle_row}\n"), "")
            .replacen("lifecycle-count 21", "lifecycle-count 20", 1);
        assert!(
            LspInventory::parse(&reseal_inventory(&missing_error, POLICY_TEXT), POLICY_TEXT,)
                .expect_err("omitting a typed error row must fail after resealing")
                .to_string()
                .contains("reviewed method/schema/capability/lifecycle census")
        );

        let field_row = INVENTORY_TEXT
            .lines()
            .find(|line| {
                line.starts_with("schema-field schema=Lean.Lsp.InitializeParams%40")
                    && line.contains(" name=capabilities ")
            })
            .expect("InitializeParams.capabilities field row");
        let missing_field = INVENTORY_TEXT
            .replace(&format!("{field_row}\n"), "")
            .replacen("schema-field-count 491", "schema-field-count 490", 1)
            .replacen(
                "name=Lean.Lsp.InitializeParams kind=structure source=vendor/lean4-src/src/Lean/Data/Lsp/InitShutdown.lean:73-84 declaration=fnv1a64:dcbab86b2565b39b field-count=7",
                "name=Lean.Lsp.InitializeParams kind=structure source=vendor/lean4-src/src/Lean/Data/Lsp/InitShutdown.lean:73-84 declaration=fnv1a64:dcbab86b2565b39b field-count=6",
                1,
            );
        assert!(
            LspInventory::parse(&reseal_inventory(&missing_field, POLICY_TEXT), POLICY_TEXT,)
                .expect_err("omitting a schema field must fail after resealing")
                .to_string()
                .contains("reviewed method/schema/capability/lifecycle census")
        );

        let method_row = INVENTORY_TEXT
            .lines()
            .find(|line| line.starts_with("method key=request:initialize "))
            .expect("initialize method row");
        let policy_row = POLICY_TEXT
            .lines()
            .find(|line| line.starts_with("row request:initialize "))
            .expect("initialize policy row");
        let missing_method = INVENTORY_TEXT
            .replace(&format!("{method_row}\n"), "")
            .replacen("method-count 59", "method-count 58", 1)
            .replacen("request-count 37", "request-count 36", 1);
        let missing_method_policy = POLICY_TEXT.replace(&format!("{policy_row}\n"), "");
        assert!(
            LspInventory::parse(
                &reseal_inventory(&missing_method, &missing_method_policy),
                &missing_method_policy,
            )
            .expect_err("omitting one method and its policy row must still fail")
            .to_string()
            .contains("reviewed method/schema/capability/lifecycle census")
        );

        for policy_mutant in [
            POLICY_TEXT.replacen(
                "row request:initialize support=required comparison=exact",
                "row request:initialize support=required comparison=normalized",
                1,
            ),
            POLICY_TEXT.replacen(
                "row request:initialize support=required comparison=exact lifecycle=process client=mandatory_client",
                "row request:initialize support=required comparison=exact lifecycle=process client=hidden_client",
                1,
            ),
            POLICY_TEXT.replacen("platform=all", "platform=hidden", 1),
        ] {
            let error = LspInventory::parse(
                &reseal_inventory(INVENTORY_TEXT, &policy_mutant),
                &policy_mutant,
            )
            .expect_err("comparison, client, and platform policy cannot be hidden or weakened");
            assert!(
                error
                    .to_string()
                    .contains("disagrees with its extracted wire role")
                    || error.to_string().contains("unsupported policy vocabulary"),
                "unexpected policy refusal: {error}"
            );
        }

        let mut initialize = BTreeMap::from([
            ("capabilities".to_string(), WireValueKind::Object),
            ("processId".to_string(), WireValueKind::Null),
            ("futureClientField".to_string(), WireValueKind::Object),
        ]);
        let shape = inventory
            .validate_object_shape("InitializeParams", &initialize)
            .expect("null optional and unknown fields are accepted");
        assert_eq!(shape.unknown_fields, ["futureClientField"]);
        assert!(inventory.fields.iter().any(|field| field.defaulted));
        assert!(
            inventory
                .fields
                .iter()
                .filter(|field| field.defaulted)
                .all(|field| field.optional)
        );
        initialize.remove("capabilities");
        assert!(matches!(
            inventory.validate_object_shape("InitializeParams", &initialize),
            Err(ProtocolFault::MissingField { field, .. }) if field == "capabilities"
        ));
        initialize.insert("capabilities".to_string(), WireValueKind::Null);
        assert!(matches!(
            inventory.validate_object_shape("InitializeParams", &initialize),
            Err(ProtocolFault::WrongFieldType {
                field,
                expected: WireValueKind::Object,
                actual: WireValueKind::Null,
                ..
            }) if field == "capabilities"
        ));
        initialize.insert("capabilities".to_string(), WireValueKind::Boolean);
        assert!(matches!(
            inventory.validate_object_shape("InitializeParams", &initialize),
            Err(ProtocolFault::WrongFieldType {
                field,
                expected: WireValueKind::Object,
                actual: WireValueKind::Boolean,
                ..
            }) if field == "capabilities"
        ));
    }

    #[test]
    fn lsp_lifecycle_state_model() {
        let inventory = inventory();
        let mut state = ProtocolState::default();
        let before = state.clone();
        assert!(matches!(
            state.apply(&inventory, Transition::Initialized),
            Err(ProtocolFault::InvalidLifecycle {
                phase: SessionPhase::Start,
                ..
            })
        ));
        assert_eq!(state, before);
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Malformed {
                    reason: "truncated params".to_string(),
                },
            ),
            Err(ProtocolFault::MalformedMessage(_))
        ));
        assert_eq!(state, before);
        state
            .apply(&inventory, Transition::Initialize)
            .expect("initialize");
        assert_eq!(state.phase(), SessionPhase::AwaitingInitialized);
        state
            .apply(&inventory, Transition::Initialized)
            .expect("initialized");
        let running = state.clone();
        assert_eq!(
            state.apply(
                &inventory,
                Transition::PlatformUnavailable {
                    surface: "watched-files".to_string(),
                },
            ),
            Err(ProtocolFault::PlatformUnavailable(
                "watched-files".to_string()
            ))
        );
        assert_eq!(state, running);
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Request {
                    id: RequestId::Number(6),
                    method: "$/lean/notReal".to_string(),
                    document: None,
                },
            ),
            Err(ProtocolFault::UnknownMethod(method)) if method == "$/lean/notReal"
        ));
        assert_eq!(state, running);
        let uri = "file:///Main.lean".to_string();
        state
            .apply(
                &inventory,
                Transition::Open {
                    uri: uri.clone(),
                    version: 4,
                },
            )
            .expect("open");
        let before_stale = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Change {
                    uri: uri.clone(),
                    version: 4,
                },
            ),
            Err(ProtocolFault::StaleDocumentVersion { .. })
        ));
        assert_eq!(state, before_stale);
        state
            .apply(
                &inventory,
                Transition::Change {
                    uri: uri.clone(),
                    version: 5,
                },
            )
            .expect("newer document version");
        assert_eq!(state.document_version(&uri), Some(5));
        assert_eq!(
            state.apply(
                &inventory,
                Transition::UnknownNotification {
                    method: "$/futureNotification".to_string(),
                },
            ),
            Ok(TransitionEffect::Ignored)
        );
        state
            .apply(&inventory, Transition::Close { uri: uri.clone() })
            .expect("close");
        let closed = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Request {
                    id: RequestId::Number(7),
                    method: "textDocument/hover".to_string(),
                    document: Some(uri),
                },
            ),
            Err(ProtocolFault::ClosedDocument(_))
        ));
        assert_eq!(state, closed);
        state
            .apply(&inventory, Transition::ShutdownRequest)
            .expect("shutdown");
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Request {
                    id: RequestId::Number(8),
                    method: "workspace/symbol".to_string(),
                    document: None,
                },
            ),
            Err(ProtocolFault::InvalidLifecycle {
                phase: SessionPhase::Shutdown,
                ..
            })
        ));
        state.apply(&inventory, Transition::Exit).expect("exit");
        assert_eq!(state.phase(), SessionPhase::Exited);
    }

    #[test]
    fn capability_negotiation_matrix() {
        let inventory = inventory();
        let semantic = inventory
            .capability("semanticTokensProvider?")
            .expect("semantic token capability");
        assert!(semantic.value.contains("full := true"));
        assert!(semantic.value.contains("range := true"));
        assert!(
            inventory
                .capability("experimental?")
                .is_some_and(|capability| capability.value.contains("rpcWireFormat? := some .v1"))
        );
        assert_eq!(parse_rpc_wire_version("v0"), Ok(RpcWireVersion::V0));
        assert_eq!(parse_rpc_wire_version("v1"), Ok(RpcWireVersion::V1));
        assert_eq!(
            parse_rpc_wire_version("v2"),
            Err(ProtocolFault::UnsupportedRpcWireVersion("v2".to_string()))
        );
        for incremental in [None, Some(false), Some(true)] {
            for silent in [None, Some(false), Some(true)] {
                for rpc in [None, Some(RpcWireVersion::V0), Some(RpcWireVersion::V1)] {
                    for widgets in [None, Some(false), Some(true)] {
                        let negotiated = negotiate_capabilities(ClientCapabilityOffer {
                            incremental_diagnostics: incremental,
                            silent_diagnostics: silent,
                            rpc_wire_format: rpc,
                            widgets,
                        });
                        assert_eq!(
                            negotiated.incremental_diagnostics,
                            incremental.unwrap_or(false)
                        );
                        assert_eq!(negotiated.silent_diagnostics, silent.unwrap_or(false));
                        assert_eq!(
                            negotiated.rpc_wire_format,
                            rpc.unwrap_or(RpcWireVersion::V0)
                        );
                        assert_eq!(negotiated.widgets, widgets.unwrap_or(false));
                        assert_eq!(negotiated.position_encoding, PositionEncoding::Utf16);
                    }
                }
            }
        }
    }

    #[test]
    fn position_and_legend_contract() {
        let inventory = inventory();
        assert_eq!(
            inventory.token_types,
            [
                "keyword",
                "variable",
                "property",
                "function",
                "namespace",
                "type",
                "class",
                "enum",
                "interface",
                "struct",
                "typeParameter",
                "parameter",
                "enumMember",
                "event",
                "method",
                "macro",
                "modifier",
                "comment",
                "string",
                "number",
                "regexp",
                "operator",
                "decorator",
                "leanSorryLike",
            ]
        );
        assert_eq!(
            inventory.token_modifiers,
            [
                "declaration",
                "definition",
                "readonly",
                "static",
                "deprecated",
                "abstract",
                "async",
                "modification",
                "documentation",
                "defaultLibrary",
            ]
        );
        let text = "a😀z\r\nβ";
        assert_eq!(
            position_to_byte(
                text,
                Position {
                    line: 0,
                    character: 3,
                },
            ),
            Ok(5)
        );
        assert_eq!(
            position_to_byte(
                text,
                Position {
                    line: 0,
                    character: 2,
                },
            ),
            Err(PositionError::InsideSurrogatePair {
                line: 0,
                character: 2,
            })
        );
        assert_eq!(
            byte_to_position(text, 5),
            Some(Position {
                line: 0,
                character: 3,
            })
        );
        assert!(matches!(
            position_to_byte(
                text,
                Position {
                    line: 2,
                    character: 0,
                },
            ),
            Err(PositionError::LineOutOfRange { .. })
        ));
        for sample in [
            "",
            "ascii",
            "αβγ\n",
            "a😀z\r\nβ𝄞\nlast",
            "combining e\u{301}\n中文",
        ] {
            for byte in 0..=sample.len() {
                if !sample.is_char_boundary(byte) {
                    assert_eq!(byte_to_position(sample, byte), None);
                    continue;
                }
                if let Some(position) = byte_to_position(sample, byte) {
                    assert_eq!(
                        position_to_byte(sample, position),
                        Ok(byte),
                        "UTF-16 position round-trip failed for {sample:?} at byte {byte}"
                    );
                } else {
                    assert!(
                        byte < sample.len()
                            && sample.as_bytes()[byte] == b'\n'
                            && byte > 0
                            && sample.as_bytes()[byte - 1] == b'\r',
                        "only the interior CRLF boundary lacks an LSP position"
                    );
                }
            }
        }
    }

    #[test]
    fn cancellation_progress_model() {
        let inventory = inventory();
        let mut state = running_state(&inventory);
        let request = RequestId::String("hover-1".to_string());
        state
            .apply(
                &inventory,
                Transition::Request {
                    id: request.clone(),
                    method: "workspace/symbol".to_string(),
                    document: None,
                },
            )
            .expect("register request");
        let active = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::Request {
                    id: request.clone(),
                    method: "workspace/symbol".to_string(),
                    document: None,
                },
            ),
            Err(ProtocolFault::DuplicateRequestId(id)) if id == request
        ));
        assert_eq!(state, active);
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::PartialResult {
                    id: request.clone(),
                    sequence: 1,
                    terminal: false,
                },
            ),
            Err(ProtocolFault::OutOfOrderPartialResult {
                expected: 0,
                received: 1,
                ..
            })
        ));
        assert_eq!(state, active);
        state
            .apply(
                &inventory,
                Transition::PartialResult {
                    id: request.clone(),
                    sequence: 0,
                    terminal: false,
                },
            )
            .expect("first partial result");
        assert_eq!(state.next_partial_sequence(&request), Some(1));
        state
            .apply(
                &inventory,
                Transition::CancelRequest {
                    id: request.clone(),
                },
            )
            .expect("cancel request");
        assert!(state.request_is_cancelled(&request));
        state
            .apply(
                &inventory,
                Transition::PartialResult {
                    id: request.clone(),
                    sequence: 1,
                    terminal: true,
                },
            )
            .expect("a terminal partial result may race with cancellation");
        let partial_final = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::PartialResult {
                    id: request.clone(),
                    sequence: 2,
                    terminal: false,
                },
            ),
            Err(ProtocolFault::PartialResultAfterFinal(id)) if id == request
        ));
        assert_eq!(state, partial_final);
        let cancelled = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::CancelRequest {
                    id: RequestId::Number(99),
                },
            ),
            Err(ProtocolFault::UnknownRequestId(_))
        ));
        assert_eq!(state, cancelled);
        state
            .apply(
                &inventory,
                Transition::BeginProgress {
                    token: "elab".to_string(),
                },
            )
            .expect("begin progress");
        assert!(state.progress_is_active("elab"));
        let progress = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::BeginProgress {
                    token: "elab".to_string(),
                },
            ),
            Err(ProtocolFault::DuplicateProgressToken(_))
        ));
        assert_eq!(state, progress);
        state
            .apply(
                &inventory,
                Transition::EndProgress {
                    token: "elab".to_string(),
                },
            )
            .expect("end progress");
        assert!(!state.progress_is_active("elab"));
        state
            .apply(&inventory, Transition::CompleteRequest { id: request })
            .expect("a cancelled request may still terminate exactly once");
    }

    #[test]
    fn lean_extension_rpc_contract() {
        let inventory = inventory();
        assert_eq!(
            inventory
                .lifecycle_fact("rpc-client-default-wire")
                .map(|fact| fact.value.as_str()),
            Some("v0")
        );
        assert_eq!(
            inventory
                .lifecycle_fact("rpc-server-advertised-wire")
                .map(|fact| fact.value.as_str()),
            Some("v1")
        );
        assert_eq!(
            inventory
                .lifecycle_fact("rpc-reserved-field")
                .map(|fact| fact.value.as_str()),
            Some("__rpcref")
        );
        let mut state = running_state(&inventory);
        let uri = "file:///Rpc.lean".to_string();
        state
            .apply(
                &inventory,
                Transition::Open {
                    uri: uri.clone(),
                    version: 1,
                },
            )
            .expect("open");
        state
            .apply(
                &inventory,
                Transition::RpcConnect {
                    uri,
                    session_id: 41,
                    now_ms: 100,
                },
            )
            .expect("connect RPC session");
        state
            .apply(
                &inventory,
                Transition::RpcAcquireRef {
                    session_id: 41,
                    reference: 7,
                },
            )
            .expect("acquire reference");
        state
            .apply(
                &inventory,
                Transition::RpcAcquireRef {
                    session_id: 41,
                    reference: 7,
                },
            )
            .expect("serve same reference twice");
        assert_eq!(state.rpc_ref_count(41, 7), Some(2));
        state
            .apply(
                &inventory,
                Transition::RpcReleaseRef {
                    session_id: 41,
                    reference: 7,
                },
            )
            .expect("release one served instance");
        assert_eq!(state.rpc_ref_count(41, 7), Some(1));
        state
            .apply(
                &inventory,
                Transition::RpcKeepAlive {
                    session_id: 41,
                    now_ms: 10_000,
                },
            )
            .expect("keep alive");
        let live = state.clone();
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::RpcExpire {
                    session_id: 41,
                    now_ms: 39_999,
                },
            ),
            Err(ProtocolFault::RpcSessionNotExpired { .. })
        ));
        assert_eq!(state, live);
        state
            .apply(
                &inventory,
                Transition::RpcExpire {
                    session_id: 41,
                    now_ms: 40_000,
                },
            )
            .expect("expire session and all references");
        assert!(matches!(
            state.apply(
                &inventory,
                Transition::RpcKeepAlive {
                    session_id: 41,
                    now_ms: 40_001,
                },
            ),
            Err(ProtocolFault::RpcNeedsReconnect(41))
        ));
    }

    #[test]
    fn reference_transcript_normalization_is_path_and_layout_independent() {
        let transcript = concat!(
            "{\n",
            "  \"uri\": \"file:///opt/lean/src/lean/Init/Prelude.lean\",\n",
            "  \"goal\": \"?m.12 and ?_fresh.77\",\n",
            "  \"reference\": \"https://lean-lang.org/doc/reference/v4.32.0/terms.html\"\n",
            "}\n",
            "human-readable output stays spaced\n",
        );
        assert_eq!(
            normalize_reference_transcript(transcript, Path::new("/opt/lean")),
            Ok(concat!(
                "{\"uri\":\"file:///src/Init/Prelude.lean\",",
                "\"goal\":\"?m and ?_fresh\",",
                "\"reference\":\"REFERENCE/terms.html\"}\n",
                "human-readable output stays spaced\n",
            )
            .to_string())
        );
    }

    #[test]
    fn semantic_and_telemetry_logs_are_strictly_separate() {
        let inventory = inventory();
        let mut complete_manifest = inventory
            .methods
            .iter()
            .enumerate()
            .map(|(sequence, method)| manifest_event(&inventory, method, sequence as u64))
            .collect::<Vec<_>>();
        inventory
            .validate_semantic_manifest(&complete_manifest)
            .expect("all 59 authority-bound rows form a complete manifest");
        let omitted = complete_manifest.pop().expect("nonempty manifest");
        assert!(
            inventory
                .validate_semantic_manifest(&complete_manifest)
                .expect_err("a published partial transcript must fail")
                .to_string()
                .contains("not method-complete")
        );
        complete_manifest.push(omitted);
        complete_manifest[0].actual_message_root = "fnv1a64:0000000000000002".to_string();
        assert!(
            inventory
                .validate_semantic_manifest(&complete_manifest)
                .expect_err("expected and actual message roots cannot diverge")
                .to_string()
                .contains("non-deterministic")
        );
        complete_manifest[0].actual_message_root =
            complete_manifest[0].expected_message_root.clone();
        complete_manifest[0].authority_root = "fnv1a64:0000000000000002".to_string();
        assert!(
            inventory
                .validate_semantic_manifest(&complete_manifest)
                .expect_err("a stale authority root cannot discharge the manifest")
                .to_string()
                .contains("stale")
        );

        let semantic = vec![
            semantic_event(
                0,
                MessageDirection::ClientToServer,
                "request:initialize",
                SemanticDisposition::Result,
                "fnv1a64:0000000000000001",
            ),
            semantic_event(
                1,
                MessageDirection::ServerToClient,
                "notification:textDocument/publishDiagnostics",
                SemanticDisposition::Notification,
                "fnv1a64:0000000000000002",
            ),
        ];
        let first = TranscriptBundle::new(
            semantic.clone(),
            vec![TelemetryEvent {
                sequence: 0,
                elapsed_micros: 12,
                worker: "local".to_string(),
                detail: "cold\u{1}".to_string(),
            }],
        )
        .expect("first bundle");
        let second = TranscriptBundle::new(
            semantic,
            vec![TelemetryEvent {
                sequence: 0,
                elapsed_micros: 98_765,
                worker: "remote-7".to_string(),
                detail: "warm".to_string(),
            }],
        )
        .expect("second bundle");
        assert_eq!(first.semantic_root(), second.semantic_root());
        assert_ne!(first.telemetry_root(), second.telemetry_root());
        assert_eq!(
            TranscriptBundle::from_ndjson(&first.semantic_ndjson(), &first.telemetry_ndjson()),
            Ok(first.clone())
        );
        assert!(
            first
                .telemetry_ndjson()
                .contains("\"detail\":\"cold\\u0001\"")
        );
        let unknown_key =
            first
                .semantic_ndjson()
                .replacen("\"actual_message_root\"", "\"unexpected\"", 1);
        assert!(
            TranscriptBundle::from_ndjson(&unknown_key, &first.telemetry_ndjson())
                .expect_err("unknown semantic keys must fail closed")
                .to_string()
                .contains("key set")
        );
        let reordered = first.semantic_ndjson().replacen(
            "\"schema\":\"fln.lsp.semantic/1\",\"sequence\":0",
            "\"sequence\":0,\"schema\":\"fln.lsp.semantic/1\"",
            1,
        );
        assert!(
            TranscriptBundle::from_ndjson(&reordered, &first.telemetry_ndjson())
                .expect_err("noncanonical key order must be refused")
                .to_string()
                .contains("noncanonical")
        );
    }
}
