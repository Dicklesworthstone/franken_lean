//! Canonical join over the pinned option, CLI/Lake, and LSP census products.
//!
//! `PublicSurfaceContractV1` is a conformance authority only. It cannot implement
//! an option, frontend, package manager, or protocol method. The generated text
//! carries every public row beneath one Reference identity while retaining the
//! three input roots and their separately reviewed policy roots.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use fln_hash::domain::{Domain as HashDomain, hash};

use crate::cli_lake_census::{CliLakeInventory, EMBEDDED_INVENTORY, EMBEDDED_POLICY};
use crate::lsp_census::{
    INVENTORY_TEXT as LSP_INVENTORY, LspInventory, MessageFamily, POLICY_TEXT as LSP_POLICY,
};
use crate::options::{OptionRole, classify_role, parse_census};
use crate::public_surface_generated as generated;

pub const CONTRACT_SCHEMA: &str = "fln-public-surface-contract/1";
pub const SEMANTIC_SCHEMA: &str = "fln.public-surface.semantic/1";
pub const TELEMETRY_SCHEMA: &str = "fln.public-surface.telemetry/1";
pub const CONTRACT_TEXT: &str = include_str!("../../../contracts/PUBLIC_SURFACE_CONTRACT.txt");
pub const CONTRACT_DOCUMENT: &str = include_str!("../../../contracts/PUBLIC_SURFACE_CONTRACT.md");

const OPTION_CENSUS: &str = include_str!("../../../contracts/option_census.ndjson");
const OPTION_PROBE: &str = include_str!("../evidence/option_census/probe_v4.32.0.jsonl");
const ROOT_PLACEHOLDER: &str = "fnv1a64:PUBLIC_SURFACE_CONTRACT_ROOT";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ContractError(String);

impl ContractError {
    fn new(message: impl Into<String>) -> Self {
        Self(message.into())
    }

    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for ContractError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ContractError {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReferenceIdentity {
    pub repo: String,
    pub tag: String,
    pub commit: String,
    pub tree: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DomainBinding {
    pub name: String,
    pub schema: String,
    pub platform: String,
    pub row_count: usize,
    pub input_root: String,
    pub raw_root: String,
    pub policy_root: String,
    pub fixture_root: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicSurfaceRow {
    pub domain: String,
    pub key: String,
    pub kind: String,
    pub epoch: String,
    pub platform: String,
    pub client: String,
    pub profile: String,
    pub mode: String,
    pub fixture: String,
    pub comparison: String,
    pub authority: String,
    pub support: String,
    pub effect: String,
    pub source: String,
    pub row_root: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FixtureBinding {
    pub domain: String,
    pub key: String,
    pub kind: String,
    pub source: String,
    pub expected: String,
    pub normalizer: String,
    pub authority: String,
    pub fixture_root: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectionBinding {
    pub kind: String,
    pub path: String,
    pub template_root: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicSurfaceContract {
    pub reference: ReferenceIdentity,
    pub observation_platform: String,
    pub domains: Vec<DomainBinding>,
    pub surfaces: Vec<PublicSurfaceRow>,
    pub fixtures: Vec<FixtureBinding>,
    pub projections: Vec<ProjectionBinding>,
    pub contract_root: String,
}

impl PublicSurfaceContract {
    pub fn load_embedded() -> Result<Self, ContractError> {
        Self::parse(CONTRACT_TEXT)?
            .validate_generated_projection()?
            .validate_domain_inputs()
    }

    pub fn parse(text: &str) -> Result<Self, ContractError> {
        if !text.ends_with('\n') {
            return Err(ContractError::new(
                "PublicSurface contract lacks its canonical final newline",
            ));
        }
        let lines = text.lines().collect::<Vec<_>>();
        let fixed_header = [
            format!("schema {CONTRACT_SCHEMA}"),
            "contract PublicSurfaceContractV1".to_string(),
            "hash fnv1a64-noncryptographic framing=u64le-length-prefixed".to_string(),
            format!("semantic-schema {SEMANTIC_SCHEMA}"),
            format!("telemetry-schema {TELEMETRY_SCHEMA}"),
        ];
        if lines.len() < 20
            || lines
                .iter()
                .take(fixed_header.len())
                .copied()
                .ne(fixed_header.iter().map(String::as_str))
        {
            return Err(ContractError::new(
                "PublicSurface contract fixed header mismatch",
            ));
        }
        let root_index = unique_prefix_index(&lines, "contract-root ")?;
        if root_index + 1 != lines.len() {
            return Err(ContractError::new(
                "PublicSurface contract root is not the final row",
            ));
        }
        let contract_root = lines[root_index]
            .strip_prefix("contract-root ")
            .ok_or_else(|| ContractError::new("contract root row malformed"))?;
        require_fnv(contract_root, "contract root")?;
        let computed = framed_hash(CONTRACT_SCHEMA, lines[..root_index].iter().copied());
        if contract_root != computed {
            return Err(ContractError::new(format!(
                "PublicSurface contract root mismatch: recorded {contract_root}, \
                 computed {computed}"
            )));
        }
        let rows_begin = unique_line_index(&lines, "rows-begin")?;
        let rows_end = unique_line_index(&lines, "rows-end")?;
        if rows_begin >= rows_end || rows_end + 2 != lines.len() {
            return Err(ContractError::new(
                "PublicSurface row section is reversed or has trailing material",
            ));
        }
        if single_value(&lines[..rows_begin], "raw-policy-separation")? != "required" {
            return Err(ContractError::new(
                "PublicSurface raw facts and policy are not declared separate",
            ));
        }
        let reference_fields = one_record(&lines[..rows_begin], "reference ")?;
        require_exact_keys(
            &reference_fields,
            &["commit", "repo", "tag", "tree"],
            "Reference identity",
        )?;
        let reference = ReferenceIdentity {
            repo: field(&reference_fields, "repo")?.to_string(),
            tag: field(&reference_fields, "tag")?.to_string(),
            commit: field(&reference_fields, "commit")?.to_string(),
            tree: field(&reference_fields, "tree")?.to_string(),
        };
        require_lower_hex(&reference.commit, 40, "Reference commit")?;
        require_lower_hex(&reference.tree, 40, "Reference tree")?;
        let observation_platform =
            single_value(&lines[..rows_begin], "observation-platform")?.to_string();
        if observation_platform != "linux-x86_64" {
            return Err(ContractError::new(format!(
                "unsupported PublicSurface observation platform {observation_platform:?}"
            )));
        }
        let expected_domains = parse_usize(single_value(&lines[..rows_begin], "domain-count")?)?;
        let expected_surfaces = parse_usize(single_value(&lines[..rows_begin], "surface-count")?)?;
        let expected_fixtures = parse_usize(single_value(&lines[..rows_begin], "fixture-count")?)?;

        let mut domains = Vec::new();
        let mut surfaces = Vec::new();
        let mut fixtures = Vec::new();
        let mut projections = Vec::new();
        let mut phase = 0_u8;
        for (offset, line) in lines[rows_begin + 1..rows_end].iter().enumerate() {
            let number = rows_begin + offset + 2;
            let (kind, values) = parse_record(line, number)?;
            let row_phase = match kind.as_str() {
                "domain" => 0,
                "surface" => 1,
                "fixture" => 2,
                "projection" => 3,
                other => {
                    return Err(ContractError::new(format!(
                        "PublicSurface contract:{number}: unknown row kind {other:?}"
                    )));
                }
            };
            if row_phase < phase {
                return Err(ContractError::new(format!(
                    "PublicSurface contract:{number}: row families are not canonical"
                )));
            }
            phase = row_phase;
            match kind.as_str() {
                "domain" => domains.push(parse_domain(&values, number)?),
                "surface" => {
                    surfaces.push(parse_surface(&values, &reference, number)?);
                }
                "fixture" => fixtures.push(parse_fixture(&values, number)?),
                "projection" => projections.push(parse_projection(&values, number)?),
                _ => unreachable!(),
            }
        }
        if domains.len() != expected_domains
            || surfaces.len() != expected_surfaces
            || fixtures.len() != expected_fixtures
        {
            return Err(ContractError::new(format!(
                "PublicSurface declared population differs: domains {}/{expected_domains}, \
                 surfaces {}/{expected_surfaces}, fixtures {}/{expected_fixtures}",
                domains.len(),
                surfaces.len(),
                fixtures.len()
            )));
        }
        if expected_domains != 3 || expected_surfaces != 1_010 || expected_fixtures != 40 {
            return Err(ContractError::new(
                "PublicSurface anti-vacuity population changed without a schema revision",
            ));
        }
        require_sorted_unique(domains.iter().map(|row| row.name.as_str()), "domain names")?;
        require_pair_sorted_unique(
            surfaces
                .iter()
                .map(|row| (row.domain.as_str(), row.key.as_str())),
            "surface ids",
        )?;
        require_pair_sorted_unique(
            fixtures
                .iter()
                .map(|row| (row.domain.as_str(), row.key.as_str())),
            "fixture ids",
        )?;
        require_sorted_unique(
            projections.iter().map(|row| row.kind.as_str()),
            "projection kinds",
        )?;
        let domain_names = domains
            .iter()
            .map(|domain| domain.name.as_str())
            .collect::<BTreeSet<_>>();
        if domain_names != BTreeSet::from(["cli-lake", "lsp", "option"]) {
            return Err(ContractError::new(format!(
                "PublicSurface domain set is {domain_names:?}"
            )));
        }
        if projections
            .iter()
            .map(|projection| projection.kind.as_str())
            .collect::<BTreeSet<_>>()
            != BTreeSet::from(["markdown", "rust"])
        {
            return Err(ContractError::new(
                "PublicSurface projections are not exactly markdown and rust",
            ));
        }
        for domain in &domains {
            let rows = surfaces
                .iter()
                .filter(|surface| surface.domain == domain.name)
                .count();
            if rows != domain.row_count {
                return Err(ContractError::new(format!(
                    "domain {} declares {} rows but contains {rows}",
                    domain.name, domain.row_count
                )));
            }
        }
        for row in &surfaces {
            if !domain_names.contains(row.domain.as_str()) {
                return Err(ContractError::new(format!(
                    "surface {}:{} names an unknown domain",
                    row.domain, row.key
                )));
            }
        }
        for row in &fixtures {
            if !domain_names.contains(row.domain.as_str()) {
                return Err(ContractError::new(format!(
                    "fixture {}:{} names an unknown domain",
                    row.domain, row.key
                )));
            }
        }
        Ok(Self {
            reference,
            observation_platform,
            domains,
            surfaces,
            fixtures,
            projections,
            contract_root: contract_root.to_string(),
        })
    }

    pub fn domain(&self, name: &str) -> Option<&DomainBinding> {
        self.domains.iter().find(|domain| domain.name == name)
    }

    pub fn surface(&self, domain: &str, key: &str) -> Option<&PublicSurfaceRow> {
        self.surfaces
            .iter()
            .find(|row| row.domain == domain && row.key == key)
    }

    pub fn validate_generated_projection(self) -> Result<Self, ContractError> {
        if generated::CONTRACT_ROOT != self.contract_root
            || generated::REFERENCE_TAG != self.reference.tag
            || generated::REFERENCE_COMMIT != self.reference.commit
            || generated::REFERENCE_TREE != self.reference.tree
            || generated::SURFACE_COUNT != self.surfaces.len()
            || generated::FIXTURE_COUNT != self.fixtures.len()
        {
            return Err(ContractError::new(
                "generated Rust consumer header drifted from PublicSurfaceContractV1",
            ));
        }
        if generated::DOMAINS.len() != self.domains.len()
            || generated::SURFACES.len() != self.surfaces.len()
            || generated::FIXTURES.len() != self.fixtures.len()
        {
            return Err(ContractError::new(
                "generated Rust consumer population drifted from the contract",
            ));
        }
        for (actual, generated) in self.domains.iter().zip(generated::DOMAINS) {
            if actual.name != generated.name
                || actual.schema != generated.schema
                || actual.platform != generated.platform
                || actual.row_count != generated.row_count
                || actual.input_root != generated.input_root
                || actual.raw_root != generated.raw_root
                || actual.policy_root != generated.policy_root
                || actual.fixture_root != generated.fixture_root
            {
                return Err(ContractError::new(format!(
                    "generated Rust domain {} drifted",
                    actual.name
                )));
            }
        }
        for (actual, generated) in self.surfaces.iter().zip(generated::SURFACES) {
            if actual.domain != generated.domain
                || actual.key != generated.key
                || actual.kind != generated.kind
                || actual.row_root != generated.row_root
            {
                return Err(ContractError::new(format!(
                    "generated Rust surface {}:{} drifted",
                    actual.domain, actual.key
                )));
            }
        }
        for (actual, generated) in self.fixtures.iter().zip(generated::FIXTURES) {
            if actual.domain != generated.domain
                || actual.key != generated.key
                || actual.fixture_root != generated.fixture_root
            {
                return Err(ContractError::new(format!(
                    "generated Rust fixture {}:{} drifted",
                    actual.domain, actual.key
                )));
            }
        }
        if CONTRACT_DOCUMENT.matches(&self.contract_root).count() != 1 {
            return Err(ContractError::new(
                "generated Markdown does not bind the contract root exactly once",
            ));
        }
        for projection in &self.projections {
            let template = match projection.kind.as_str() {
                "markdown" => CONTRACT_DOCUMENT.replace(&self.contract_root, ROOT_PLACEHOLDER),
                "rust" => include_str!("public_surface_generated.rs")
                    .replace(&self.contract_root, ROOT_PLACEHOLDER),
                other => {
                    return Err(ContractError::new(format!(
                        "unknown generated projection {other}"
                    )));
                }
            };
            let computed = fnv(template.as_bytes());
            if computed != projection.template_root {
                return Err(ContractError::new(format!(
                    "{} projection template root mismatch: recorded {}, computed {computed}",
                    projection.kind, projection.template_root
                )));
            }
        }
        Ok(self)
    }

    pub fn validate_domain_inputs(self) -> Result<Self, ContractError> {
        let (expected_domains, expected_surfaces, expected_fixtures) =
            expected_domain_products(&self.reference)?;
        if self.domains != expected_domains {
            let first = self
                .domains
                .iter()
                .zip(&expected_domains)
                .find(|(actual, expected)| actual != expected)
                .map(|(actual, expected)| {
                    format!("first divergence actual={actual:?}, expected={expected:?}")
                })
                .unwrap_or_else(|| "population differs".to_string());
            return Err(ContractError::new(format!(
                "PublicSurface domain roots drifted from their canonical inputs: {first}"
            )));
        }
        if self.surfaces != expected_surfaces {
            let first = self
                .surfaces
                .iter()
                .zip(&expected_surfaces)
                .find(|(actual, expected)| actual != expected)
                .map(|(actual, expected)| {
                    format!(
                        "first divergence actual={}:{} expected={}:{}",
                        actual.domain, actual.key, expected.domain, expected.key
                    )
                })
                .unwrap_or_else(|| "population differs".to_string());
            return Err(ContractError::new(format!(
                "PublicSurface rows drifted from facts/policy: {first}"
            )));
        }
        if self.fixtures != expected_fixtures {
            return Err(ContractError::new(
                "PublicSurface fixture projection drifted from real domain evidence",
            ));
        }
        Ok(self)
    }
}

fn parse_domain(
    values: &BTreeMap<String, String>,
    line: usize,
) -> Result<DomainBinding, ContractError> {
    require_exact_keys(
        values,
        &[
            "fixture-root",
            "input-root",
            "name",
            "platform",
            "policy-root",
            "raw-root",
            "row-count",
            "schema",
        ],
        &format!("domain row {line}"),
    )?;
    for key in ["fixture-root", "input-root", "policy-root", "raw-root"] {
        require_fnv(field(values, key)?, &format!("domain row {line} {key}"))?;
    }
    let platform = field(values, "platform")?;
    if !matches!(
        platform,
        "linux-x86_64"
            | "portable-schema+linux-x86_64-oracle"
            | "portable-source+linux-x86_64-oracle"
    ) {
        return Err(ContractError::new(format!(
            "domain row {line} has unreviewed platform {platform:?}"
        )));
    }
    Ok(DomainBinding {
        name: field(values, "name")?.to_string(),
        schema: field(values, "schema")?.to_string(),
        platform: platform.to_string(),
        row_count: parse_usize(field(values, "row-count")?)?,
        input_root: field(values, "input-root")?.to_string(),
        raw_root: field(values, "raw-root")?.to_string(),
        policy_root: field(values, "policy-root")?.to_string(),
        fixture_root: field(values, "fixture-root")?.to_string(),
    })
}

fn parse_surface(
    values: &BTreeMap<String, String>,
    reference: &ReferenceIdentity,
    line: usize,
) -> Result<PublicSurfaceRow, ContractError> {
    require_exact_keys(
        values,
        &[
            "authority",
            "client",
            "comparison",
            "domain",
            "effect",
            "epoch",
            "fixture",
            "key",
            "kind",
            "mode",
            "platform",
            "profile",
            "row-root",
            "source",
            "support",
        ],
        &format!("surface row {line}"),
    )?;
    let epoch = field(values, "epoch")?;
    let expected_epoch = format!("{}@{}", reference.tag, reference.commit);
    if epoch != expected_epoch {
        return Err(ContractError::new(format!(
            "surface row {line} mixes epoch {epoch:?}; expected {expected_epoch:?}"
        )));
    }
    for key in [
        "authority",
        "client",
        "comparison",
        "effect",
        "fixture",
        "kind",
        "mode",
        "platform",
        "profile",
        "source",
        "support",
    ] {
        if field(values, key)?.contains("unknown") {
            return Err(ContractError::new(format!(
                "surface row {line} carries unreviewed {key}"
            )));
        }
    }
    if field(values, "profile")? != "faithful,sound" || field(values, "mode")? != "all" {
        return Err(ContractError::new(format!(
            "surface row {line} escaped the reviewed profile/mode projection"
        )));
    }
    require_fnv(field(values, "row-root")?, &format!("surface row {line}"))?;
    Ok(PublicSurfaceRow {
        domain: field(values, "domain")?.to_string(),
        key: field(values, "key")?.to_string(),
        kind: field(values, "kind")?.to_string(),
        epoch: epoch.to_string(),
        platform: field(values, "platform")?.to_string(),
        client: field(values, "client")?.to_string(),
        profile: field(values, "profile")?.to_string(),
        mode: field(values, "mode")?.to_string(),
        fixture: field(values, "fixture")?.to_string(),
        comparison: field(values, "comparison")?.to_string(),
        authority: field(values, "authority")?.to_string(),
        support: field(values, "support")?.to_string(),
        effect: field(values, "effect")?.to_string(),
        source: field(values, "source")?.to_string(),
        row_root: field(values, "row-root")?.to_string(),
    })
}

fn parse_fixture(
    values: &BTreeMap<String, String>,
    line: usize,
) -> Result<FixtureBinding, ContractError> {
    require_exact_keys(
        values,
        &[
            "authority",
            "domain",
            "expected",
            "fixture-root",
            "key",
            "kind",
            "normalizer",
            "source",
        ],
        &format!("fixture row {line}"),
    )?;
    require_fnv(
        field(values, "fixture-root")?,
        &format!("fixture row {line}"),
    )?;
    Ok(FixtureBinding {
        domain: field(values, "domain")?.to_string(),
        key: field(values, "key")?.to_string(),
        kind: field(values, "kind")?.to_string(),
        source: field(values, "source")?.to_string(),
        expected: field(values, "expected")?.to_string(),
        normalizer: field(values, "normalizer")?.to_string(),
        authority: field(values, "authority")?.to_string(),
        fixture_root: field(values, "fixture-root")?.to_string(),
    })
}

fn parse_projection(
    values: &BTreeMap<String, String>,
    line: usize,
) -> Result<ProjectionBinding, ContractError> {
    require_exact_keys(
        values,
        &["kind", "path", "template-root"],
        &format!("projection row {line}"),
    )?;
    require_fnv(
        field(values, "template-root")?,
        &format!("projection row {line}"),
    )?;
    let kind = field(values, "kind")?;
    let path = field(values, "path")?;
    let expected_path = match kind {
        "markdown" => "contracts/PUBLIC_SURFACE_CONTRACT.md",
        "rust" => "crates/fln-conformance/src/public_surface_generated.rs",
        _ => {
            return Err(ContractError::new(format!(
                "projection row {line} has unknown kind {kind:?}"
            )));
        }
    };
    if path != expected_path {
        return Err(ContractError::new(format!(
            "projection row {line} points {kind} at {path:?}, expected {expected_path:?}"
        )));
    }
    Ok(ProjectionBinding {
        kind: kind.to_string(),
        path: path.to_string(),
        template_root: field(values, "template-root")?.to_string(),
    })
}

type DomainProducts = (
    Vec<DomainBinding>,
    Vec<PublicSurfaceRow>,
    Vec<FixtureBinding>,
);

fn expected_domain_products(
    reference: &ReferenceIdentity,
) -> Result<DomainProducts, ContractError> {
    let cli = CliLakeInventory::load_embedded()
        .map_err(|error| ContractError::new(format!("CLI/Lake input: {error}")))?;
    let lsp = LspInventory::load_embedded()
        .map_err(|error| ContractError::new(format!("LSP input: {error}")))?;
    if cli.reference.repo != reference.repo
        || cli.reference.tag != reference.tag
        || cli.reference.commit != reference.commit
        || cli.reference.tree != reference.tree
        || lsp.reference.repository != reference.repo
        || lsp.reference.tag != reference.tag
        || lsp.reference.commit != reference.commit
        || lsp.reference.tree != reference.tree
    {
        return Err(ContractError::new(
            "domain inventories do not share the PublicSurface Reference identity",
        ));
    }

    let mut domains = Vec::new();
    let mut surfaces = Vec::new();
    let mut fixtures = Vec::new();
    let epoch = format!("{}@{}", reference.tag, reference.commit);

    let cli_raw = raw_lines(EMBEDDED_INVENTORY)?;
    let cli_raw_by_key = keyed_lines(&cli_raw, "surface ", "key")?;
    let cli_policy_by_key = policy_lines(EMBEDDED_POLICY)?;
    for surface in &cli.surfaces {
        let raw = cli_raw_by_key.get(surface.key.as_str()).ok_or_else(|| {
            ContractError::new(format!("CLI/Lake raw row {} is absent", surface.key))
        })?;
        let policy_line = cli_policy_by_key.get(surface.key.as_str()).ok_or_else(|| {
            ContractError::new(format!("CLI/Lake policy row {} is absent", surface.key))
        })?;
        surfaces.push(PublicSurfaceRow {
            domain: "cli-lake".to_string(),
            key: surface.key.clone(),
            kind: surface.kind.as_str().to_string(),
            epoch: epoch.clone(),
            platform: surface.policy.platform.clone(),
            client: surface
                .attribute("personality")
                .unwrap_or("command-line")
                .to_string(),
            profile: "faithful,sound".to_string(),
            mode: "all".to_string(),
            fixture: "cli-lake-census-no-mock-e2e".to_string(),
            comparison: surface.policy.comparison.clone(),
            authority: surface.policy.authority.clone(),
            support: surface.policy.support.clone(),
            effect: format!(
                "channel:{};precedence:{}",
                surface.policy.channel, surface.policy.precedence
            ),
            source: surface.source.clone(),
            row_root: framed_hash(
                "fln-public-surface-row/cli-lake/1",
                [raw.as_str(), policy_line.as_str()],
            ),
        });
    }
    let cli_transcript_lines = keyed_lines(&cli_raw, "transcript ", "key")?;
    for transcript in &cli.transcripts {
        let raw = cli_transcript_lines
            .get(transcript.key.as_str())
            .ok_or_else(|| {
                ContractError::new(format!(
                    "CLI/Lake transcript row {} is absent",
                    transcript.key
                ))
            })?;
        fixtures.push(FixtureBinding {
            domain: "cli-lake".to_string(),
            key: transcript.key.clone(),
            kind: "real-process-transcript".to_string(),
            source: format!("contracts/CLI_LAKE_TRANSCRIPTS.txt:{}", transcript.key),
            expected: format!(
                "exit={};stdout={};stderr={}",
                transcript.exit_code, transcript.stdout_hash, transcript.stderr_hash
            ),
            normalizer: transcript.normalizer.clone(),
            authority: "pinned-reference-binary".to_string(),
            fixture_root: framed_hash(
                "fln-public-surface-row/cli-lake-fixture/1",
                [raw.as_str(), cli.inventory_root.as_str()],
            ),
        });
    }
    let cli_fixture_root = framed_hash(
        "fln-public-surface-cli-fixtures/1",
        fixtures
            .iter()
            .filter(|fixture| fixture.domain == "cli-lake")
            .map(|fixture| fixture.fixture_root.as_str()),
    );
    domains.push(DomainBinding {
        name: "cli-lake".to_string(),
        schema: "fln-cli-lake-inventory/1".to_string(),
        platform: cli.platform.clone(),
        row_count: cli.surfaces.len(),
        input_root: cli.inventory_root.clone(),
        raw_root: cli.raw_root.clone(),
        policy_root: cli.policy_root.clone(),
        fixture_root: cli_fixture_root,
    });

    let lsp_raw = raw_lines(LSP_INVENTORY)?;
    let lsp_raw_by_key = keyed_lines(&lsp_raw, "method ", "key")?;
    let lsp_policy_by_key = policy_lines(LSP_POLICY)?;
    for method in &lsp.methods {
        let raw = lsp_raw_by_key
            .get(method.key.as_str())
            .ok_or_else(|| ContractError::new(format!("LSP raw row {} is absent", method.key)))?;
        let policy_line = lsp_policy_by_key.get(method.key.as_str()).ok_or_else(|| {
            ContractError::new(format!("LSP policy row {} is absent", method.key))
        })?;
        surfaces.push(PublicSurfaceRow {
            domain: "lsp".to_string(),
            key: method.key.clone(),
            kind: message_family(method.family).to_string(),
            epoch: epoch.clone(),
            platform: method.policy.platform.clone(),
            client: method.policy.client.clone(),
            profile: "faithful,sound".to_string(),
            mode: "all".to_string(),
            fixture: method.fixture.clone(),
            comparison: method.policy.comparison.clone(),
            authority: "pinned-source+real-server-transcript".to_string(),
            support: method.policy.support.clone(),
            effect: format!("lifecycle:{}", method.policy.lifecycle),
            source: method.source.clone(),
            row_root: framed_hash(
                "fln-public-surface-row/lsp/1",
                [raw.as_str(), policy_line.as_str()],
            ),
        });
    }
    let lsp_fixture_lines = keyed_lines(&lsp_raw, "fixture ", "name")?;
    for fixture in &lsp.fixtures {
        let raw = lsp_fixture_lines
            .get(fixture.name.as_str())
            .ok_or_else(|| {
                ContractError::new(format!("LSP fixture row {} is absent", fixture.name))
            })?;
        fixtures.push(FixtureBinding {
            domain: "lsp".to_string(),
            key: fixture.name.clone(),
            kind: "real-server-transcript".to_string(),
            source: fixture.source.clone(),
            expected: format!(
                "source={};expected={}",
                fixture.source_hash, fixture.expected_hash
            ),
            normalizer: fixture.normalizer.clone(),
            authority: "pinned-reference-server".to_string(),
            fixture_root: framed_hash(
                "fln-public-surface-row/lsp-fixture/1",
                [raw.as_str(), lsp.inventory_root.as_str()],
            ),
        });
    }
    let lsp_fixture_root = framed_hash(
        "fln-public-surface-lsp-fixtures/1",
        fixtures
            .iter()
            .filter(|fixture| fixture.domain == "lsp")
            .map(|fixture| fixture.fixture_root.as_str()),
    );
    domains.push(DomainBinding {
        name: "lsp".to_string(),
        schema: "fln-lsp-wire-inventory/1".to_string(),
        platform: "portable-schema+linux-x86_64-oracle".to_string(),
        row_count: lsp.methods.len(),
        input_root: lsp.inventory_root.clone(),
        raw_root: lsp.raw_root.clone(),
        policy_root: lsp.policy_root.clone(),
        fixture_root: lsp_fixture_root,
    });

    let option_rows = parse_census(OPTION_CENSUS)
        .map_err(|error| ContractError::new(format!("option input: {error:?}")))?;
    let option_lines = OPTION_CENSUS.lines().collect::<Vec<_>>();
    if option_rows.len() != 660 || option_lines.len() != option_rows.len() {
        return Err(ContractError::new("option census population is not 660"));
    }
    let option_raw_root = framed_hash("fln-option-public-raw/1", option_lines.iter().copied());
    let mut option_policy_lines = Vec::new();
    for (row, raw) in option_rows.iter().zip(&option_lines) {
        let key = option_key(row);
        let dynamic = row.kind == "dynamic";
        let role = if dynamic {
            "dynamic-unresolved"
        } else {
            option_role(classify_role(&row.name))
        };
        let authority = "pinned-source+real-binary-receipt";
        let comparison = if dynamic {
            "disclosed-unresolved"
        } else {
            "exact"
        };
        let support = if dynamic {
            "blocked-unresolved"
        } else {
            "required"
        };
        let policy_line = format!(
            "row {} authority={} comparison={} platform=all role={} support={}",
            percent_encode(&key),
            percent_encode(authority),
            percent_encode(comparison),
            percent_encode(role),
            percent_encode(support)
        );
        option_policy_lines.push(policy_line.clone());
        surfaces.push(PublicSurfaceRow {
            domain: "option".to_string(),
            key,
            kind: row.kind.clone(),
            epoch: epoch.clone(),
            platform: "all".to_string(),
            client: "all-consumers".to_string(),
            profile: "faithful,sound".to_string(),
            mode: "all".to_string(),
            fixture: "option-census-no-mock-e2e".to_string(),
            comparison: comparison.to_string(),
            authority: authority.to_string(),
            support: support.to_string(),
            effect: role.to_string(),
            source: row.source.clone(),
            row_root: framed_hash(
                "fln-public-surface-row/option/1",
                [*raw, policy_line.as_str()],
            ),
        });
    }
    option_policy_lines.sort();
    let option_policy_root = framed_hash(
        "fln-option-public-policy/1",
        option_policy_lines.iter().map(String::as_str),
    );
    let mut summary = 0;
    for (index, line) in OPTION_PROBE.lines().enumerate() {
        let step = flat_json_string_field(line, "step").ok_or_else(|| {
            ContractError::new(format!("option probe row {} lacks step", index + 1))
        })?;
        if step == "summary" {
            summary += 1;
            if flat_json_string_field(line, "pin").as_deref() != Some(reference.tag.as_str())
                || flat_json_string_field(line, "verdict").as_deref() != Some("all-cells-hold")
            {
                return Err(ContractError::new(
                    "option probe summary is not bound to this epoch",
                ));
            }
        }
        fixtures.push(FixtureBinding {
            domain: "option".to_string(),
            key: step,
            kind: "real-binary-probe".to_string(),
            source: format!(
                "crates/fln-conformance/evidence/option_census/\
                 probe_v4.32.0.jsonl:{}",
                index + 1
            ),
            expected: fnv(line.as_bytes()),
            normalizer: "canonical-json-v1".to_string(),
            authority: "pinned-reference-binary".to_string(),
            fixture_root: framed_hash(
                "fln-public-surface-row/option-fixture/1",
                [line, reference.commit.as_str()],
            ),
        });
    }
    if summary != 1 {
        return Err(ContractError::new(
            "option probe receipt has no unique summary",
        ));
    }
    let option_fixture_root = framed_hash("fln-option-public-fixtures/1", OPTION_PROBE.lines());
    let option_input_root = framed_hash(
        "fln-option-public-domain/1",
        [
            option_raw_root.as_str(),
            option_policy_root.as_str(),
            option_fixture_root.as_str(),
            reference.commit.as_str(),
            reference.tree.as_str(),
        ],
    );
    domains.push(DomainBinding {
        name: "option".to_string(),
        schema: "fln.option-census/1".to_string(),
        platform: "portable-source+linux-x86_64-oracle".to_string(),
        row_count: option_rows.len(),
        input_root: option_input_root,
        raw_root: option_raw_root,
        policy_root: option_policy_root,
        fixture_root: option_fixture_root,
    });

    domains.sort_by(|left, right| left.name.cmp(&right.name));
    surfaces.sort_by(|left, right| (&left.domain, &left.key).cmp(&(&right.domain, &right.key)));
    fixtures.sort_by(|left, right| (&left.domain, &left.key).cmp(&(&right.domain, &right.key)));
    Ok((domains, surfaces, fixtures))
}

fn message_family(family: MessageFamily) -> &'static str {
    match family {
        MessageFamily::Request => "request",
        MessageFamily::Notification => "notification",
        MessageFamily::RpcRequest => "rpc_request",
    }
}

fn option_key(row: &crate::options::OptionRow) -> String {
    if row.kind == "dynamic" {
        format!("dynamic:{}", row.source)
    } else {
        format!("{}:{}", row.kind, row.name)
    }
}

fn option_role(role: OptionRole) -> &'static str {
    match role {
        OptionRole::Semantic => "semantic",
        OptionRole::ResourceBudget => "resource-budget",
        OptionRole::Presentation => "presentation",
        OptionRole::Diagnostic => "diagnostic",
        OptionRole::Infrastructure => "infrastructure",
    }
}

fn raw_lines(text: &str) -> Result<Vec<String>, ContractError> {
    let lines = text.lines().collect::<Vec<_>>();
    let begin = unique_line_index(&lines, "raw-begin")?;
    let end = unique_line_index(&lines, "raw-end")?;
    if begin + 1 >= end {
        return Err(ContractError::new("embedded raw section is empty"));
    }
    Ok(lines[begin + 1..end]
        .iter()
        .map(|line| (*line).to_string())
        .collect())
}

fn keyed_lines(
    lines: &[String],
    prefix: &str,
    key_name: &str,
) -> Result<BTreeMap<String, String>, ContractError> {
    let mut result = BTreeMap::new();
    for line in lines.iter().filter(|line| line.starts_with(prefix)) {
        let values = parse_fields(line.strip_prefix(prefix).unwrap_or_default())?;
        let key = field(&values, key_name)?.to_string();
        if result.insert(key.clone(), line.clone()).is_some() {
            return Err(ContractError::new(format!(
                "duplicate embedded {prefix}{key}"
            )));
        }
    }
    Ok(result)
}

fn policy_lines(text: &str) -> Result<BTreeMap<String, String>, ContractError> {
    let mut result = BTreeMap::new();
    for line in text.lines().skip(1) {
        let rest = line
            .strip_prefix("row ")
            .ok_or_else(|| ContractError::new("embedded policy row lacks row prefix"))?;
        let (key, values) = rest
            .split_once(' ')
            .ok_or_else(|| ContractError::new("embedded policy row lacks fields"))?;
        let parsed = parse_fields(values)?;
        let canonical = parsed
            .iter()
            .map(|(name, value)| format!("{name}={value}"))
            .collect::<Vec<_>>()
            .join(" ");
        if result.insert(key.to_string(), canonical).is_some() {
            return Err(ContractError::new(format!(
                "duplicate embedded policy {key}"
            )));
        }
    }
    Ok(result)
}

fn flat_json_string_field(line: &str, key: &str) -> Option<String> {
    let tag = format!("\"{key}\":\"");
    let start = line.find(&tag)? + tag.len();
    let bytes = line.as_bytes();
    let mut index = start;
    let mut result = String::new();
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return Some(result),
            b'\\' if index + 1 < bytes.len() => {
                index += 1;
                result.push(match bytes[index] {
                    b'"' => '"',
                    b'\\' => '\\',
                    b'n' => '\n',
                    b'r' => '\r',
                    b't' => '\t',
                    _ => return None,
                });
            }
            byte if byte.is_ascii() => result.push(char::from(byte)),
            _ => return None,
        }
        index += 1;
    }
    None
}

fn parse_record(
    line: &str,
    number: usize,
) -> Result<(String, BTreeMap<String, String>), ContractError> {
    let (kind, fields) = line.split_once(' ').ok_or_else(|| {
        ContractError::new(format!("PublicSurface contract:{number}: row lacks fields"))
    })?;
    Ok((kind.to_string(), parse_fields(fields)?))
}

fn parse_fields(text: &str) -> Result<BTreeMap<String, String>, ContractError> {
    let mut values = BTreeMap::new();
    for token in text.split_ascii_whitespace() {
        let (key, value) = token
            .split_once('=')
            .ok_or_else(|| ContractError::new(format!("field {token:?} is not key=value")))?;
        if key.is_empty() || value.is_empty() {
            return Err(ContractError::new(format!(
                "field {token:?} has an empty key or value"
            )));
        }
        let decoded = percent_decode(value)?; // ubs:ignore — decoded fields never select paths or commands
        if percent_encode(&decoded) != value {
            return Err(ContractError::new(format!(
                "field {key:?} is not canonically percent-encoded"
            )));
        }
        if values.insert(key.to_string(), decoded).is_some() {
            return Err(ContractError::new(format!("duplicate field {key:?}")));
        }
    }
    Ok(values)
}

fn percent_decode(value: &str) -> Result<String, ContractError> {
    // ubs:ignore — UTF-8 checked contract data, never path authority
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
            return Err(ContractError::new(format!(
                "truncated percent escape in {value:?}"
            )));
        }
        let high = hex_nibble(bytes[index + 1])
            .ok_or_else(|| ContractError::new(format!("invalid escape in {value:?}")))?;
        let low = hex_nibble(bytes[index + 2])
            .ok_or_else(|| ContractError::new(format!("invalid escape in {value:?}")))?;
        decoded.push((high << 4) | low);
        index += 3;
    }
    String::from_utf8(decoded)
        .map_err(|_| ContractError::new(format!("percent-decoded value is not UTF-8: {value:?}")))
}

fn percent_encode(value: &str) -> String {
    let mut encoded = String::new();
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric()
            || matches!(byte, b'-' | b'.' | b'_' | b'~' | b'/' | b':' | b'$')
        {
            encoded.push(char::from(byte));
        } else {
            use std::fmt::Write as _;
            let _ = write!(encoded, "%{byte:02X}");
        }
    }
    encoded
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn one_record(lines: &[&str], prefix: &str) -> Result<BTreeMap<String, String>, ContractError> {
    let matches = lines
        .iter()
        .filter_map(|line| line.strip_prefix(prefix))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [fields] => parse_fields(fields),
        _ => Err(ContractError::new(format!(
            "expected exactly one {prefix:?} record"
        ))),
    }
}

fn field<'a>(values: &'a BTreeMap<String, String>, key: &str) -> Result<&'a str, ContractError> {
    values
        .get(key)
        .map(String::as_str)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| ContractError::new(format!("missing field {key:?}")))
}

fn require_exact_keys(
    values: &BTreeMap<String, String>,
    expected: &[&str],
    context: &str,
) -> Result<(), ContractError> {
    let actual = values.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(ContractError::new(format!(
            "{context} fields {actual:?} != {expected:?}"
        )));
    }
    Ok(())
}

fn single_value<'a>(lines: &'a [&str], key: &str) -> Result<&'a str, ContractError> {
    let prefix = format!("{key} ");
    let matches = lines
        .iter()
        .filter_map(|line| line.strip_prefix(&prefix))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [value] if !value.is_empty() && !value.contains(' ') => Ok(*value),
        _ => Err(ContractError::new(format!(
            "expected exactly one scalar {key:?}"
        ))),
    }
}

fn unique_line_index(lines: &[&str], target: &str) -> Result<usize, ContractError> {
    let matches = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| (*line == target).then_some(index))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(ContractError::new(format!(
            "expected exactly one {target:?} row"
        ))),
    }
}

fn unique_prefix_index(lines: &[&str], prefix: &str) -> Result<usize, ContractError> {
    let matches = lines
        .iter()
        .enumerate()
        .filter_map(|(index, line)| line.starts_with(prefix).then_some(index))
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [index] => Ok(*index),
        _ => Err(ContractError::new(format!(
            "expected exactly one row beginning {prefix:?}"
        ))),
    }
}

fn parse_usize(value: &str) -> Result<usize, ContractError> {
    value
        .parse()
        .map_err(|_| ContractError::new(format!("{value:?} is not a usize")))
}

fn require_lower_hex(value: &str, len: usize, context: &str) -> Result<(), ContractError> {
    if value.len() != len
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(ContractError::new(format!(
            "{context} is not {len} lowercase hexadecimal bytes: {value:?}"
        )));
    }
    Ok(())
}

fn require_fnv(value: &str, context: &str) -> Result<(), ContractError> {
    let Some(hex) = value.strip_prefix("fnv1a64:") else {
        return Err(ContractError::new(format!(
            "{context} does not use fnv1a64: {value:?}"
        )));
    };
    require_lower_hex(hex, 16, context)
}

fn require_sorted_unique<'a>(
    values: impl IntoIterator<Item = &'a str>,
    context: &str,
) -> Result<(), ContractError> {
    let values = values.into_iter().collect::<Vec<_>>();
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(ContractError::new(format!(
            "{context} are not strictly sorted and unique"
        )));
    }
    Ok(())
}

fn require_pair_sorted_unique<'a>(
    values: impl IntoIterator<Item = (&'a str, &'a str)>,
    context: &str,
) -> Result<(), ContractError> {
    let values = values.into_iter().collect::<Vec<_>>();
    if values.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(ContractError::new(format!(
            "{context} are not strictly sorted and unique"
        )));
    }
    Ok(())
}

fn fnv(bytes: &[u8]) -> String {
    let mut value = 0xcbf29ce484222325_u64;
    for byte in bytes {
        value ^= u64::from(*byte);
        value = value.wrapping_mul(0x100000001b3);
    }
    format!("fnv1a64:{value:016x}")
}

fn framed_hash<'a>(domain: &'a str, fields: impl IntoIterator<Item = &'a str>) -> String {
    let mut payload = Vec::new();
    for field in std::iter::once(domain).chain(fields) {
        payload.extend_from_slice(&(field.len() as u64).to_le_bytes());
        payload.extend_from_slice(field.as_bytes());
    }
    fnv(&payload)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScheduleEvidence {
    pub workers: usize,
    pub completed_per_worker: Vec<usize>,
    pub semantic_root: String,
}

pub fn reduce_productively(
    contract: &PublicSurfaceContract,
    workers: usize,
) -> Result<ScheduleEvidence, ContractError> {
    if workers == 0 || workers > contract.surfaces.len() {
        return Err(ContractError::new(format!(
            "worker count {workers} cannot productively partition {} rows",
            contract.surfaces.len()
        )));
    }
    let mut handles = Vec::with_capacity(workers);
    let base = contract.surfaces.len() / workers;
    let extra = contract.surfaces.len() % workers;
    let mut start = 0;
    for worker in 0..workers {
        let width = base + usize::from(worker < extra);
        let rows = &contract.surfaces[start..start + width];
        start += width;
        let owned = rows
            .iter()
            .map(|row| (row.domain.clone(), row.key.clone(), row.row_root.clone()))
            .collect::<Vec<_>>();
        handles.push(std::thread::spawn(move || {
            let completed = owned.len();
            let reduced = owned
                .into_iter()
                .map(|(domain, key, row_root)| {
                    framed_hash(
                        "fln-public-surface-reduction-row/1",
                        [domain.as_str(), key.as_str(), row_root.as_str()],
                    )
                })
                .collect::<Vec<_>>();
            (worker, completed, reduced)
        }));
    }
    if handles.len() != workers || start != contract.surfaces.len() {
        return Err(ContractError::new(
            "productive schedule did not partition every row exactly once",
        ));
    }
    let mut partitions = handles
        .into_iter()
        .map(|handle| {
            handle
                .join()
                .map_err(|_| ContractError::new("PublicSurface worker panicked"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    partitions.sort_by_key(|(worker, _, _)| *worker);
    let completed_per_worker = partitions
        .iter()
        .map(|(_, completed, _)| *completed)
        .collect::<Vec<_>>();
    if completed_per_worker.contains(&0) {
        return Err(ContractError::new(
            "PublicSurface schedule admitted an idle worker",
        ));
    }
    let reduced = partitions
        .iter()
        .flat_map(|(_, _, rows)| rows.iter().map(String::as_str));
    Ok(ScheduleEvidence {
        workers,
        completed_per_worker,
        semantic_root: framed_hash("fln-public-surface-reduction/1", reduced),
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublicationPhase {
    CandidatesValidated,
    RustProjection,
    MarkdownProjection,
    CanonicalContract,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicationState {
    pub canonical_root: String,
    pub rust_projection_root: String,
    pub markdown_projection_root: String,
}

impl PublicationState {
    pub fn complete(root: impl Into<String>) -> Self {
        let root = root.into();
        Self {
            canonical_root: root.clone(),
            rust_projection_root: root.clone(),
            markdown_projection_root: root,
        }
    }

    pub fn authoritative_root(&self) -> Option<&str> {
        (self.canonical_root == self.rust_projection_root
            && self.canonical_root == self.markdown_projection_root)
            .then_some(self.canonical_root.as_str())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PublicationDisposition {
    Complete,
    Inconclusive { interrupted_after: PublicationPhase },
}

pub fn publish_with_interruption(
    current: &PublicationState,
    candidate_root: &str,
    interrupt_after: Option<PublicationPhase>,
) -> (PublicationState, PublicationDisposition) {
    let mut next = current.clone();
    if interrupt_after == Some(PublicationPhase::CandidatesValidated) {
        return (
            next,
            PublicationDisposition::Inconclusive {
                interrupted_after: PublicationPhase::CandidatesValidated,
            },
        );
    }
    next.rust_projection_root = candidate_root.to_string();
    if interrupt_after == Some(PublicationPhase::RustProjection) {
        return (
            next,
            PublicationDisposition::Inconclusive {
                interrupted_after: PublicationPhase::RustProjection,
            },
        );
    }
    next.markdown_projection_root = candidate_root.to_string();
    if interrupt_after == Some(PublicationPhase::MarkdownProjection) {
        return (
            next,
            PublicationDisposition::Inconclusive {
                interrupted_after: PublicationPhase::MarkdownProjection,
            },
        );
    }
    next.canonical_root = candidate_root.to_string();
    if interrupt_after == Some(PublicationPhase::CanonicalContract) {
        return (
            next,
            PublicationDisposition::Inconclusive {
                interrupted_after: PublicationPhase::CanonicalContract,
            },
        );
    }
    (next, PublicationDisposition::Complete)
}

pub fn recover_publication(
    interrupted: &PublicationState,
    candidate_root: &str,
) -> Result<PublicationState, ContractError> {
    require_fnv(candidate_root, "publication candidate root")?;
    for (name, root) in [
        ("canonical", interrupted.canonical_root.as_str()),
        ("Rust projection", interrupted.rust_projection_root.as_str()),
        (
            "Markdown projection",
            interrupted.markdown_projection_root.as_str(),
        ),
    ] {
        require_fnv(root, &format!("interrupted {name} root"))?;
    }

    let prior_roots = [
        interrupted.canonical_root.as_str(),
        interrupted.rust_projection_root.as_str(),
        interrupted.markdown_projection_root.as_str(),
    ]
    .into_iter()
    .filter(|root| *root != candidate_root)
    .collect::<BTreeSet<_>>();
    if prior_roots.len() > 1 {
        return Err(ContractError::new(
            "interrupted publication contains more than one prior root",
        ));
    }

    let reachable = match prior_roots.iter().next().copied() {
        None => interrupted == &PublicationState::complete(candidate_root),
        Some(prior) => {
            interrupted == &PublicationState::complete(prior)
                || (interrupted.canonical_root == prior
                    && interrupted.rust_projection_root == candidate_root
                    && interrupted.markdown_projection_root == prior)
                || (interrupted.canonical_root == prior
                    && interrupted.rust_projection_root == candidate_root
                    && interrupted.markdown_projection_root == candidate_root)
        }
    };
    if !reachable {
        return Err(ContractError::new(
            "interrupted publication is not a reachable projections-first prefix",
        ));
    }
    Ok(PublicationState::complete(candidate_root))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProcessOutcome {
    Observed,
    Mismatch,
    Cancelled,
    TimedOut,
    OutputBudgetExceeded,
    InternalFault,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SemanticDisposition {
    Accepted,
    Rejected,
    Inconclusive,
    InternalFault,
}

impl SemanticDisposition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::Rejected => "rejected",
            Self::Inconclusive => "inconclusive",
            Self::InternalFault => "internal_fault",
        }
    }
}

pub const fn classify_outcome(outcome: ProcessOutcome) -> SemanticDisposition {
    match outcome {
        ProcessOutcome::Observed => SemanticDisposition::Accepted,
        ProcessOutcome::Mismatch => SemanticDisposition::Rejected,
        ProcessOutcome::Cancelled
        | ProcessOutcome::TimedOut
        | ProcessOutcome::OutputBudgetExceeded => SemanticDisposition::Inconclusive,
        ProcessOutcome::InternalFault => SemanticDisposition::InternalFault,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticRecord {
    pub run_id: String,
    pub sequence: usize,
    pub domain: String,
    pub row: String,
    pub epoch: String,
    pub platform: String,
    pub client: String,
    pub profile: String,
    pub mode: String,
    pub fixture: String,
    pub comparison: String,
    pub authority: String,
    pub input_root: String,
    pub output_root: String,
    pub expected: String,
    pub actual: String,
    pub resource_class: String,
    pub resource_used: u64,
    pub disposition: SemanticDisposition,
    pub decision: String,
    pub cleanup: String,
    pub final_state: String,
}

impl SemanticRecord {
    pub fn to_ndjson(&self) -> String {
        format!(
            concat!(
                "{{\"schema\":{},\"run_id\":{},\"sequence\":{},\"domain\":{},",
                "\"row\":{},\"epoch\":{},\"platform\":{},\"client\":{},",
                "\"profile\":{},\"mode\":{},\"fixture\":{},\"comparison\":{},",
                "\"authority\":{},\"input_root\":{},\"output_root\":{},",
                "\"expected\":{},\"actual\":{},\"resource_class\":{},",
                "\"resource_used\":{},\"disposition\":{},\"decision\":{},",
                "\"cleanup\":{},\"final_state\":{}}}"
            ),
            json_string(SEMANTIC_SCHEMA),
            json_string(&self.run_id),
            self.sequence,
            json_string(&self.domain),
            json_string(&self.row),
            json_string(&self.epoch),
            json_string(&self.platform),
            json_string(&self.client),
            json_string(&self.profile),
            json_string(&self.mode),
            json_string(&self.fixture),
            json_string(&self.comparison),
            json_string(&self.authority),
            json_string(&self.input_root),
            json_string(&self.output_root),
            json_string(&self.expected),
            json_string(&self.actual),
            json_string(&self.resource_class),
            self.resource_used,
            json_string(self.disposition.as_str()),
            json_string(&self.decision),
            json_string(&self.cleanup),
            json_string(&self.final_state),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TelemetryRecord {
    pub run_id: String,
    pub sequence: usize,
    pub host: String,
    pub pid: u32,
    pub worker: usize,
    pub elapsed_micros: u64,
    pub path: String,
    pub cache: String,
    pub detail: String,
}

impl TelemetryRecord {
    pub fn to_ndjson(&self) -> String {
        format!(
            concat!(
                "{{\"schema\":{},\"run_id\":{},\"sequence\":{},\"host\":{},",
                "\"pid\":{},\"worker\":{},\"elapsed_micros\":{},\"path\":{},",
                "\"cache\":{},\"detail\":{}}}"
            ),
            json_string(TELEMETRY_SCHEMA),
            json_string(&self.run_id),
            self.sequence,
            json_string(&self.host),
            self.pid,
            self.worker,
            self.elapsed_micros,
            json_string(&self.path),
            json_string(&self.cache),
            json_string(&self.detail),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvidenceBundle {
    semantic: Vec<SemanticRecord>,
    telemetry: Vec<TelemetryRecord>,
}

impl EvidenceBundle {
    pub fn new(
        semantic: Vec<SemanticRecord>,
        telemetry: Vec<TelemetryRecord>,
    ) -> Result<Self, ContractError> {
        validate_semantic_records(&semantic)?;
        validate_telemetry_records(&telemetry)?;
        let semantic_runs = semantic
            .iter()
            .map(|record| record.run_id.as_str())
            .collect::<BTreeSet<_>>();
        let telemetry_runs = telemetry
            .iter()
            .map(|record| record.run_id.as_str())
            .collect::<BTreeSet<_>>();
        if semantic_runs.len() != 1 || telemetry_runs.len() != 1 || semantic_runs != telemetry_runs
        {
            return Err(ContractError::new(
                "semantic and telemetry streams are not linked to one run id",
            ));
        }
        if semantic.len() != telemetry.len() {
            return Err(ContractError::new(
                "semantic and telemetry streams do not have one-to-one sequence linkage",
            ));
        }
        Ok(Self {
            semantic,
            telemetry,
        })
    }

    pub fn semantic_ndjson(&self) -> String {
        lines_with_newline(self.semantic.iter().map(SemanticRecord::to_ndjson))
    }

    pub fn telemetry_ndjson(&self) -> String {
        lines_with_newline(self.telemetry.iter().map(TelemetryRecord::to_ndjson))
    }

    pub fn semantic_root(&self) -> String {
        hash(HashDomain::Fixture, self.semantic_ndjson().as_bytes()).to_hex()
    }

    pub fn telemetry_root(&self) -> String {
        hash(
            HashDomain::OperationalMeta,
            self.telemetry_ndjson().as_bytes(),
        )
        .to_hex()
    }

    pub fn from_ndjson(semantic: &str, telemetry: &str) -> Result<Self, ContractError> {
        let parsed_semantic = parse_semantic_ndjson(semantic)?;
        let parsed_telemetry = parse_telemetry_ndjson(telemetry)?;
        let bundle = Self::new(parsed_semantic, parsed_telemetry)?;
        if bundle.semantic_ndjson() != semantic || bundle.telemetry_ndjson() != telemetry {
            return Err(ContractError::new(
                "evidence NDJSON is parseable but not byte-canonical",
            ));
        }
        Ok(bundle)
    }
}

fn validate_semantic_records(records: &[SemanticRecord]) -> Result<(), ContractError> {
    if records.is_empty() {
        return Err(ContractError::new("semantic evidence stream is empty"));
    }
    for (expected_sequence, record) in records.iter().enumerate() {
        if record.sequence != expected_sequence {
            return Err(ContractError::new(
                "semantic evidence sequence is not contiguous",
            ));
        }
        if [
            record.run_id.as_str(),
            record.domain.as_str(),
            record.row.as_str(),
            record.epoch.as_str(),
            record.platform.as_str(),
            record.client.as_str(),
            record.profile.as_str(),
            record.mode.as_str(),
            record.fixture.as_str(),
            record.comparison.as_str(),
            record.authority.as_str(),
            record.input_root.as_str(),
            record.output_root.as_str(),
            record.expected.as_str(),
            record.actual.as_str(),
            record.resource_class.as_str(),
            record.decision.as_str(),
            record.cleanup.as_str(),
            record.final_state.as_str(),
        ]
        .contains(&"")
        {
            return Err(ContractError::new(
                "semantic evidence has an empty required field",
            ));
        }
        require_fnv(&record.input_root, "semantic evidence input root")?;
        if matches!(
            record.disposition,
            SemanticDisposition::Inconclusive | SemanticDisposition::InternalFault
        ) && (record.decision != "no-promotion" || record.output_root != "none")
        {
            return Err(ContractError::new(
                "inconclusive/fault evidence attempted to publish authority",
            ));
        }
        if matches!(
            record.disposition,
            SemanticDisposition::Accepted | SemanticDisposition::Rejected
        ) {
            require_fnv(
                &record.output_root,
                "conclusive semantic evidence output root",
            )?;
            if record.decision == "no-promotion" {
                return Err(ContractError::new(
                    "conclusive semantic evidence was marked no-promotion",
                ));
            }
        }
    }
    Ok(())
}

fn validate_telemetry_records(records: &[TelemetryRecord]) -> Result<(), ContractError> {
    if records.is_empty() {
        return Err(ContractError::new("telemetry evidence stream is empty"));
    }
    for (expected_sequence, record) in records.iter().enumerate() {
        if record.sequence != expected_sequence
            || [
                record.run_id.as_str(),
                record.host.as_str(),
                record.path.as_str(),
                record.cache.as_str(),
                record.detail.as_str(),
            ]
            .contains(&"")
        {
            return Err(ContractError::new(
                "telemetry evidence sequence, linkage, or required field is invalid",
            ));
        }
    }
    Ok(())
}

fn lines_with_newline(lines: impl IntoIterator<Item = String>) -> String {
    let mut result = lines.into_iter().collect::<Vec<_>>().join("\n");
    result.push('\n');
    result
}

fn parse_semantic_ndjson(text: &str) -> Result<Vec<SemanticRecord>, ContractError> {
    require_canonical_stream(text, "semantic")?;
    text.lines()
        .map(|line| {
            let values = parse_flat_json(line)?;
            require_exact_keys(
                &values,
                &[
                    "actual",
                    "authority",
                    "cleanup",
                    "client",
                    "comparison",
                    "decision",
                    "disposition",
                    "domain",
                    "epoch",
                    "expected",
                    "final_state",
                    "fixture",
                    "input_root",
                    "mode",
                    "output_root",
                    "platform",
                    "profile",
                    "resource_class",
                    "resource_used",
                    "row",
                    "run_id",
                    "schema",
                    "sequence",
                ],
                "semantic evidence row",
            )?;
            if field(&values, "schema")? != SEMANTIC_SCHEMA {
                return Err(ContractError::new("semantic evidence schema mismatch"));
            }
            let disposition = match field(&values, "disposition")? {
                "accepted" => SemanticDisposition::Accepted,
                "rejected" => SemanticDisposition::Rejected,
                "inconclusive" => SemanticDisposition::Inconclusive,
                "internal_fault" => SemanticDisposition::InternalFault,
                other => {
                    return Err(ContractError::new(format!(
                        "unknown semantic disposition {other:?}"
                    )));
                }
            };
            Ok(SemanticRecord {
                run_id: field(&values, "run_id")?.to_string(),
                sequence: parse_usize(field(&values, "sequence")?)?,
                domain: field(&values, "domain")?.to_string(),
                row: field(&values, "row")?.to_string(),
                epoch: field(&values, "epoch")?.to_string(),
                platform: field(&values, "platform")?.to_string(),
                client: field(&values, "client")?.to_string(),
                profile: field(&values, "profile")?.to_string(),
                mode: field(&values, "mode")?.to_string(),
                fixture: field(&values, "fixture")?.to_string(),
                comparison: field(&values, "comparison")?.to_string(),
                authority: field(&values, "authority")?.to_string(),
                input_root: field(&values, "input_root")?.to_string(),
                output_root: field(&values, "output_root")?.to_string(),
                expected: field(&values, "expected")?.to_string(),
                actual: field(&values, "actual")?.to_string(),
                resource_class: field(&values, "resource_class")?.to_string(),
                resource_used: parse_u64(field(&values, "resource_used")?)?,
                disposition,
                decision: field(&values, "decision")?.to_string(),
                cleanup: field(&values, "cleanup")?.to_string(),
                final_state: field(&values, "final_state")?.to_string(),
            })
        })
        .collect()
}

fn parse_telemetry_ndjson(text: &str) -> Result<Vec<TelemetryRecord>, ContractError> {
    require_canonical_stream(text, "telemetry")?;
    text.lines()
        .map(|line| {
            let values = parse_flat_json(line)?;
            require_exact_keys(
                &values,
                &[
                    "cache",
                    "detail",
                    "elapsed_micros",
                    "host",
                    "path",
                    "pid",
                    "run_id",
                    "schema",
                    "sequence",
                    "worker",
                ],
                "telemetry evidence row",
            )?;
            if field(&values, "schema")? != TELEMETRY_SCHEMA {
                return Err(ContractError::new("telemetry evidence schema mismatch"));
            }
            Ok(TelemetryRecord {
                run_id: field(&values, "run_id")?.to_string(),
                sequence: parse_usize(field(&values, "sequence")?)?,
                host: field(&values, "host")?.to_string(),
                pid: parse_u64(field(&values, "pid")?)?
                    .try_into()
                    .map_err(|_| ContractError::new("telemetry pid exceeds u32"))?,
                worker: parse_usize(field(&values, "worker")?)?,
                elapsed_micros: parse_u64(field(&values, "elapsed_micros")?)?,
                path: field(&values, "path")?.to_string(),
                cache: field(&values, "cache")?.to_string(),
                detail: field(&values, "detail")?.to_string(),
            })
        })
        .collect()
}

fn require_canonical_stream(text: &str, name: &str) -> Result<(), ContractError> {
    if text.is_empty() || !text.ends_with('\n') || text.contains("\n\n") {
        return Err(ContractError::new(format!(
            "{name} NDJSON is empty or lacks canonical line framing"
        )));
    }
    Ok(())
}

fn parse_flat_json(line: &str) -> Result<BTreeMap<String, String>, ContractError> {
    if !line.starts_with('{') || !line.ends_with('}') {
        return Err(ContractError::new("evidence row is not a JSON object"));
    }
    let bytes = line.as_bytes();
    let mut index = 1;
    let mut values = BTreeMap::new();
    while index + 1 < bytes.len() {
        let (key, next) = parse_json_string(bytes, index)?;
        index = next;
        if bytes.get(index) != Some(&b':') {
            return Err(ContractError::new("JSON field lacks colon"));
        }
        index += 1;
        let (value, next) = if bytes.get(index) == Some(&b'"') {
            parse_json_string(bytes, index)?
        } else {
            let start = index;
            while index < bytes.len() && bytes[index].is_ascii_digit() {
                index += 1;
            }
            if start == index {
                return Err(ContractError::new(
                    "flat evidence JSON admits only strings and unsigned integers",
                ));
            }
            (
                std::str::from_utf8(&bytes[start..index])
                    .map_err(|_| ContractError::new("numeric JSON token is not UTF-8"))?
                    .to_string(),
                index,
            )
        };
        index = next;
        if values.insert(key.clone(), value).is_some() {
            return Err(ContractError::new(format!("duplicate JSON field {key:?}")));
        }
        match bytes.get(index) {
            Some(b',') => index += 1,
            Some(b'}') if index + 1 == bytes.len() => return Ok(values),
            _ => return Err(ContractError::new("flat JSON object framing is invalid")),
        }
    }
    Err(ContractError::new("unterminated flat JSON object"))
}

fn parse_json_string(bytes: &[u8], start: usize) -> Result<(String, usize), ContractError> {
    if bytes.get(start) != Some(&b'"') {
        return Err(ContractError::new("JSON string lacks opening quote"));
    }
    let mut index = start + 1;
    let mut result = String::new();
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return Ok((result, index + 1)),
            b'\\' => {
                index += 1;
                let escaped = match bytes.get(index).copied() {
                    Some(b'"') => '"',
                    Some(b'\\') => '\\',
                    Some(b'n') => '\n',
                    Some(b'r') => '\r',
                    Some(b't') => '\t',
                    Some(b'u') => {
                        let (unit, next) = parse_json_hex_quad(bytes, index + 1)?;
                        index = next;
                        let scalar = if (0xd800..=0xdbff).contains(&unit) {
                            if bytes.get(index..index + 2) != Some(b"\\u") {
                                return Err(ContractError::new(
                                    "JSON high surrogate lacks a low surrogate",
                                ));
                            }
                            let (low, next) = parse_json_hex_quad(bytes, index + 2)?;
                            if !(0xdc00..=0xdfff).contains(&low) {
                                return Err(ContractError::new(
                                    "JSON high surrogate is followed by a non-low surrogate",
                                ));
                            }
                            index = next;
                            0x1_0000
                                + ((u32::from(unit) - 0xd800) << 10)
                                + (u32::from(low) - 0xdc00)
                        } else if (0xdc00..=0xdfff).contains(&unit) {
                            return Err(ContractError::new(
                                "JSON low surrogate lacks a high surrogate",
                            ));
                        } else {
                            u32::from(unit)
                        };
                        result.push(char::from_u32(scalar).ok_or_else(|| {
                            ContractError::new("JSON Unicode escape is not a scalar value")
                        })?);
                        continue;
                    }
                    _ => {
                        return Err(ContractError::new("unsupported JSON string escape"));
                    }
                };
                result.push(escaped);
            }
            byte if byte.is_ascii_control() => {
                return Err(ContractError::new("unescaped control byte in JSON string"));
            }
            byte if byte.is_ascii() => result.push(char::from(byte)),
            _ => {
                let suffix = std::str::from_utf8(&bytes[index..])
                    .map_err(|_| ContractError::new("JSON string is not UTF-8"))?;
                let character = suffix
                    .chars()
                    .next()
                    .ok_or_else(|| ContractError::new("JSON string ended mid-scalar"))?;
                result.push(character);
                index += character.len_utf8();
                continue;
            }
        }
        index += 1;
    }
    Err(ContractError::new("unterminated JSON string"))
}

fn parse_json_hex_quad(bytes: &[u8], start: usize) -> Result<(u16, usize), ContractError> {
    let end = start
        .checked_add(4)
        .ok_or_else(|| ContractError::new("JSON Unicode escape overflowed"))?;
    let digits = bytes
        .get(start..end)
        .ok_or_else(|| ContractError::new("JSON Unicode escape is truncated"))?;
    let mut value = 0_u16;
    for digit in digits {
        value = value
            .checked_mul(16)
            .and_then(|value| hex_nibble(*digit).map(|nibble| value + u16::from(nibble)))
            .ok_or_else(|| ContractError::new("JSON Unicode escape is malformed"))?;
    }
    Ok((value, end))
}

fn json_string(value: &str) -> String {
    let mut result = String::with_capacity(value.len() + 2);
    result.push('"');
    for character in value.chars() {
        match character {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write as _;
                let _ = write!(result, "\\u{:04x}", u32::from(character));
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

fn parse_u64(value: &str) -> Result<u64, ContractError> {
    value
        .parse()
        .map_err(|_| ContractError::new(format!("{value:?} is not a u64")))
}
