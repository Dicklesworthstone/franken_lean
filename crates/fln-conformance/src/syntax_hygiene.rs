//! G0-4 syntax, source-information, and hygiene fidelity contract.
//!
//! This module is the join the individual Vellum slices did not provide:
//!
//! * the fixture manifest binds C0, pinned Lean C1, and pinned mathlib C2
//!   sources to the exact Reference and Corpus revisions in `SUITE.lock`;
//! * the stock Reference transcript is parsed fail-closed and compared in
//!   manifest order;
//! * the implemented C0 slice runs the real lexer, attachment builder, and
//!   Pratt engine, then serializes the resulting `Syntax` with the same
//!   source-information codec as the Reference fixture;
//! * every unsupported C1/C2 production or expansion is a named contract gap.
//!   It is never dropped, normalized away, or counted as a match;
//! * grammar epochs, macro-scope observations, quotation splices, resource
//!   budgets, and the 1/8/32 partition law are reusable model surfaces.
//!
//! G0-4 is a spike, not the downstream macro engine. Its computed decision is
//! therefore allowed to amend the production contract, but the apparatus here
//! may not pretend that a model is the production macro transaction path.

use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_hash::domain::{Domain, hash};
use fln_parse::build::Leaves;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::pratt::{Grammar, Lookup, pratt_parser, result_of};
use fln_parse::registry::{GrammarEpoch, Registry};
use fln_parse::state::{MAX_PREC, ParseError, ParserState, Production};
use fln_syntax::literal::LiteralKind;
use fln_syntax::run::{Event, LexBudget, lex_run, lex_run_bounded};
use fln_syntax::source::{BytePos, SourceInfo, SourceText};
use fln_syntax::token::{LexedToken, TokenKind, TokenTable};
use fln_syntax::tree::{Preresolved, Syntax};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Weak};

use crate::trace_replay::{
    EventFamily, TRACE_REPLAY_SCHEMA, check_elab_steps, family_root, parse_trace,
};

pub const MANIFEST_SCHEMA: &str = "fln-g04-syntax-manifest/1";
pub const REFERENCE_SCHEMA: &str = "fln-g04-reference/1";
pub const SEMANTIC_SCHEMA: &str = "fln-g04-semantic/1";
pub const TELEMETRY_SCHEMA: &str = "fln-g04-telemetry/1";
pub const REFERENCE_TAG: &str = "v4.32.0";
pub const REFERENCE_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
pub const CORPUS_COMMIT: &str = "81a5d257c8e410db227a6665ed08f64fea08e997";
pub const TRACE_CONTRACT_SCHEMA: &str = "fln-g09-trace-replay/1";

const MANIFEST_TEXT: &str = include_str!("../fixtures/g04_syntax_manifest.tsv");
const STOCK_G09_TRACE: &str = include_str!("../fixtures/g09_multi_family_trace.txt");
const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");

const HEADER: &[&str] = &[
    "id",
    "family",
    "origin",
    "origin_rev",
    "origin_path",
    "origin_lines",
    "imports",
    "options",
    "category",
    "grammar_phase",
    "grammar_epoch",
    "grammar_root",
    "observation",
    "disposition",
    "comparison",
    "source_hex",
];

const REQUIRED_FACETS: &[&str] = &[
    "tokens",
    "tree",
    "sourceinfo",
    "trivia",
    "positions",
    "diagnostic",
    "recovery",
    "grammar_epoch",
    "expansion",
    "hygiene",
    "quotation",
    "antiquotation",
    "splice",
    "generated_ids",
    "trace_elab_step",
];

const EXPECTED_GAPS: &[(&str, &str)] = &[
    (
        "c0_missing_rhs",
        "diagnostic-rendering-identity-not-yet-bound",
    ),
    (
        "c1_call_before_registration",
        "builtin-application-and-dotted-ident-slice-not-yet-in-g04-adapter",
    ),
    (
        "c1_call_parse",
        "dynamic-call-production-not-yet-in-production-parser",
    ),
    (
        "c1_call_expand",
        "macro-expansion-identity-not-yet-in-production-path",
    ),
    (
        "c1_call_malformed",
        "dynamic-call-recovery-not-yet-in-production-parser",
    ),
    (
        "c2_matrix_parse",
        "pp-separator-combinator-not-yet-in-production-parser",
    ),
    (
        "c2_matrix_expand",
        "nested-antiquotation-expansion-not-yet-in-production-path",
    ),
    (
        "c2_matrix_uneven",
        "macro-diagnostic-source-map-not-yet-in-production-path",
    ),
];

const EXPECTED_ROW_CONTRACTS: &[(
    &str,
    FixtureFamily,
    &str,
    u64,
    ObservationKind,
    Disposition,
    &str,
)] = &[
    (
        "c0_pratt_trivia",
        FixtureFamily::C0,
        "builtin",
        4,
        ObservationKind::Parse,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,trivia,positions,recovery",
    ),
    (
        "c0_unicode_positions",
        FixtureFamily::C0,
        "builtin",
        4,
        ObservationKind::Parse,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,trivia,positions,recovery",
    ),
    (
        "c0_missing_rhs",
        FixtureFamily::C0,
        "builtin",
        4,
        ObservationKind::Parse,
        Disposition::ParseError,
        "tokens,tree,sourceinfo,diagnostic,recovery",
    ),
    (
        "c1_call_before_registration",
        FixtureFamily::C1,
        "pre-call",
        4,
        ObservationKind::Parse,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,grammar_epoch,positions,trace_elab_step",
    ),
    (
        "c1_call_parse",
        FixtureFamily::C1,
        "post-call",
        5,
        ObservationKind::Parse,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,grammar_epoch,quotation,splice,positions,trace_elab_step",
    ),
    (
        "c1_call_expand",
        FixtureFamily::C1,
        "post-call",
        5,
        ObservationKind::Expand,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,grammar_epoch,expansion,hygiene,quotation,splice,generated_ids,trace_elab_step",
    ),
    (
        "c1_call_malformed",
        FixtureFamily::C1,
        "post-call",
        5,
        ObservationKind::Parse,
        Disposition::ParseError,
        "tokens,tree,sourceinfo,grammar_epoch,diagnostic,recovery,trace_elab_step",
    ),
    (
        "c2_matrix_parse",
        FixtureFamily::C2,
        "post-matrix",
        6,
        ObservationKind::Parse,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,grammar_epoch,quotation,antiquotation,splice,positions,trace_elab_step",
    ),
    (
        "c2_matrix_expand",
        FixtureFamily::C2,
        "post-matrix",
        6,
        ObservationKind::Expand,
        Disposition::Accepted,
        "tokens,tree,sourceinfo,grammar_epoch,expansion,hygiene,quotation,antiquotation,splice,generated_ids,trace_elab_step",
    ),
    (
        "c2_matrix_uneven",
        FixtureFamily::C2,
        "post-matrix",
        6,
        ObservationKind::Expand,
        Disposition::ExpansionError,
        "tokens,tree,sourceinfo,grammar_epoch,diagnostic,recovery,quotation,antiquotation,splice,trace_elab_step",
    ),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FixtureFamily {
    C0,
    C1,
    C2,
}

impl FixtureFamily {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::C0 => "C0",
            Self::C1 => "C1",
            Self::C2 => "C2",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "C0" => Some(Self::C0),
            "C1" => Some(Self::C1),
            "C2" => Some(Self::C2),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObservationKind {
    Parse,
    Expand,
}

impl ObservationKind {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Parse => "parse",
            Self::Expand => "expand",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "parse" => Some(Self::Parse),
            "expand" => Some(Self::Expand),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Disposition {
    Accepted,
    ParseError,
    ExpansionError,
}

impl Disposition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Accepted => "accepted",
            Self::ParseError => "parse-error",
            Self::ExpansionError => "expansion-error",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "accepted" => Some(Self::Accepted),
            "parse-error" => Some(Self::ParseError),
            "expansion-error" => Some(Self::ExpansionError),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureRow {
    pub id: String,
    pub family: FixtureFamily,
    pub origin: String,
    pub origin_rev: String,
    pub origin_path: String,
    pub origin_lines: String,
    pub imports: String,
    pub options: String,
    pub category: String,
    pub grammar_phase: String,
    pub grammar_epoch: GrammarEpoch,
    pub grammar_root: String,
    pub observation: ObservationKind,
    pub disposition: Disposition,
    pub comparison: BTreeSet<String>,
    pub source: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FixtureManifest {
    raw: String,
    rows: Vec<FixtureRow>,
}

impl FixtureManifest {
    pub fn load_embedded() -> Result<Self, String> {
        Self::parse(MANIFEST_TEXT)
    }

    pub fn parse(text: &str) -> Result<Self, String> {
        if !text.ends_with('\n') {
            return Err("G0-4 manifest must end with one newline".to_string());
        }
        let mut lines = text.lines();
        let schema = lines
            .next()
            .ok_or_else(|| "G0-4 manifest is empty".to_string())?;
        if schema != MANIFEST_SCHEMA {
            return Err(format!("unsupported G0-4 manifest schema {schema:?}"));
        }
        let header = lines
            .next()
            .ok_or_else(|| "G0-4 manifest has no header".to_string())?;
        if header.split('\t').collect::<Vec<_>>() != HEADER {
            return Err(format!("G0-4 manifest header drifted: {header:?}"));
        }

        let mut rows = Vec::new();
        let mut ids = BTreeSet::new();
        for (index, line) in lines.enumerate() {
            if line.is_empty() {
                return Err(format!("G0-4 manifest row {} is empty", index + 3));
            }
            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != HEADER.len() {
                return Err(format!(
                    "G0-4 manifest row {} has {} fields, expected {}",
                    index + 3,
                    fields.len(),
                    HEADER.len()
                ));
            }
            let id = fields[0].to_string();
            if !ids.insert(id.clone()) {
                return Err(format!("duplicate G0-4 fixture id {id:?}"));
            }
            if !id
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'_')
            {
                return Err(format!("malformed G0-4 fixture id {id:?}"));
            }
            let family = FixtureFamily::parse(fields[1])
                .ok_or_else(|| format!("{id}: unsupported family {:?}", fields[1]))?;
            let grammar_epoch = fields[10]
                .parse::<u64>()
                .map(GrammarEpoch)
                .map_err(|_| format!("{id}: malformed grammar epoch {:?}", fields[10]))?;
            if !is_lower_hex(fields[11], 64) {
                return Err(format!("{id}: malformed grammar root {:?}", fields[11]));
            }
            let observation = ObservationKind::parse(fields[12])
                .ok_or_else(|| format!("{id}: unsupported observation {:?}", fields[12]))?;
            let disposition = Disposition::parse(fields[13])
                .ok_or_else(|| format!("{id}: unsupported disposition {:?}", fields[13]))?;
            let comparison = fields[14]
                .split(',')
                .map(str::to_string)
                .collect::<BTreeSet<_>>();
            if comparison.is_empty() || comparison.contains("") {
                return Err(format!("{id}: comparison facet set is empty"));
            }
            if comparison.len() != fields[14].split(',').count() {
                return Err(format!("{id}: duplicate comparison facet"));
            }
            let expected_comparison = EXPECTED_ROW_CONTRACTS
                .iter()
                .find_map(|contract| (contract.0 == id).then_some(contract.6))
                .ok_or_else(|| format!("{id}: fixture is not in the closed G0-4 row contract"))?;
            if fields[14] != expected_comparison {
                return Err(format!(
                    "{id}: comparison facet order/set drifted: expected {expected_comparison:?}, \
                     got {:?}",
                    fields[14]
                ));
            }
            for facet in &comparison {
                if !REQUIRED_FACETS.contains(&facet.as_str()) {
                    return Err(format!("{id}: unsupported comparison facet {facet:?}"));
                }
            }
            let source_bytes =
                decode_hex(fields[15]).map_err(|error| format!("{id}: source_hex: {error}"))?;
            let source = String::from_utf8(source_bytes)
                .map_err(|_| format!("{id}: source_hex is not UTF-8"))?;
            if source.is_empty() {
                return Err(format!("{id}: source is empty"));
            }
            for (field_name, value) in [
                ("origin", fields[2]),
                ("origin_rev", fields[3]),
                ("origin_path", fields[4]),
                ("origin_lines", fields[5]),
                ("imports", fields[6]),
                ("options", fields[7]),
                ("category", fields[8]),
                ("grammar_phase", fields[9]),
            ] {
                if value.trim().is_empty() {
                    return Err(format!("{id}: {field_name} is empty"));
                }
            }

            rows.push(FixtureRow {
                id,
                family,
                origin: fields[2].to_string(),
                origin_rev: fields[3].to_string(),
                origin_path: fields[4].to_string(),
                origin_lines: fields[5].to_string(),
                imports: fields[6].to_string(),
                options: fields[7].to_string(),
                category: fields[8].to_string(),
                grammar_phase: fields[9].to_string(),
                grammar_epoch,
                grammar_root: fields[11].to_string(),
                observation,
                disposition,
                comparison,
                source,
            });
        }
        let manifest = Self {
            raw: text.to_string(),
            rows,
        };
        manifest.validate_closed_world()?;
        Ok(manifest)
    }

    pub fn rows(&self) -> &[FixtureRow] {
        &self.rows
    }

    pub fn row(&self, id: &str) -> Option<&FixtureRow> {
        self.rows.iter().find(|row| row.id == id)
    }

    pub fn root(&self) -> String {
        fixture_digest(self.raw.as_bytes())
    }

    pub fn validate_grammar_roots(&self) -> Result<(), String> {
        let roots = grammar_phase_roots();
        for row in &self.rows {
            let Some((epoch, root)) = roots.get(row.grammar_phase.as_str()) else {
                return Err(format!(
                    "{}: unregistered grammar phase {:?}",
                    row.id, row.grammar_phase
                ));
            };
            if *epoch != row.grammar_epoch || root != &row.grammar_root {
                return Err(format!(
                    "{}: grammar identity drift: manifest epoch={} root={}, derived epoch={} root={}",
                    row.id, row.grammar_epoch.0, row.grammar_root, epoch.0, root
                ));
            }
        }
        Ok(())
    }

    fn validate_closed_world(&self) -> Result<(), String> {
        let expected_ids = EXPECTED_ROW_CONTRACTS
            .iter()
            .map(|contract| contract.0)
            .collect::<Vec<_>>();
        let actual_ids = self
            .rows
            .iter()
            .map(|row| row.id.as_str())
            .collect::<Vec<_>>();
        if actual_ids != expected_ids {
            return Err(format!(
                "G0-4 fixture order/set drifted: expected {expected_ids:?}, got {actual_ids:?}"
            ));
        }
        let family_counts = [FixtureFamily::C0, FixtureFamily::C1, FixtureFamily::C2]
            .map(|family| self.rows.iter().filter(|row| row.family == family).count());
        if family_counts != [3, 4, 3] {
            return Err(format!(
                "G0-4 family cardinality drifted: {family_counts:?}"
            ));
        }

        let observed_facets = self
            .rows
            .iter()
            .flat_map(|row| row.comparison.iter().map(String::as_str))
            .collect::<BTreeSet<_>>();
        let required_facets = REQUIRED_FACETS.iter().copied().collect::<BTreeSet<_>>();
        if observed_facets != required_facets {
            return Err(format!(
                "G0-4 comparison facet set is not exact: required={required_facets:?} observed={observed_facets:?}"
            ));
        }
        let dispositions = self
            .rows
            .iter()
            .map(|row| row.disposition)
            .collect::<BTreeSet<_>>();
        if dispositions
            != [
                Disposition::Accepted,
                Disposition::ParseError,
                Disposition::ExpansionError,
            ]
            .into_iter()
            .collect()
        {
            return Err(format!(
                "G0-4 success/error/recovery disposition set is incomplete: {dispositions:?}"
            ));
        }
        for (row, contract) in self.rows.iter().zip(EXPECTED_ROW_CONTRACTS) {
            if row.id != contract.0
                || row.family != contract.1
                || row.grammar_phase != contract.2
                || row.grammar_epoch.0 != contract.3
                || row.observation != contract.4
                || row.disposition != contract.5
            {
                return Err(format!(
                    "{}: row contract drifted: expected family={} phase={} epoch={} \
                     observation={} disposition={}",
                    row.id,
                    contract.1.as_str(),
                    contract.2,
                    contract.3,
                    contract.4.as_str(),
                    contract.5.as_str()
                ));
            }
            if row.imports != "Lean" || row.options != "default" || row.category != "term" {
                return Err(format!(
                    "{}: fixture context drifted (imports={}, options={}, category={})",
                    row.id, row.imports, row.options, row.category
                ));
            }
            match row.family {
                FixtureFamily::C0 => {
                    if row.origin_rev != "g04-owned/1" {
                        return Err(format!("{}: C0 provenance drifted", row.id));
                    }
                }
                FixtureFamily::C1 => {
                    if row.origin_rev != REFERENCE_COMMIT {
                        return Err(format!("{}: C1 pin drifted", row.id));
                    }
                }
                FixtureFamily::C2 => {
                    if row.origin_rev != CORPUS_COMMIT {
                        return Err(format!("{}: C2 pin drifted", row.id));
                    }
                }
            }
        }
        let reference_row =
            format!("reference leanprover/lean4 tag={REFERENCE_TAG} commit={REFERENCE_COMMIT}");
        let corpus_row = format!(
            "corpus leanprover-community/mathlib4 tag={REFERENCE_TAG} commit={CORPUS_COMMIT}"
        );
        if !SUITE_LOCK.contains(&reference_row) || !SUITE_LOCK.contains(&corpus_row) {
            return Err(
                "G0-4 manifest pins do not match the authoritative SUITE.lock rows".to_string(),
            );
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceRecord {
    pub fixture: String,
    pub observation: ObservationKind,
    pub disposition: Disposition,
    pub payload: Vec<u8>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReferenceTranscript {
    raw: String,
    records: Vec<ReferenceRecord>,
}

impl ReferenceTranscript {
    pub fn parse(raw: String, manifest: &FixtureManifest) -> Result<Self, String> {
        if !raw.ends_with('\n') {
            return Err("G0-4 Reference transcript must end with one newline".to_string());
        }
        let mut records = Vec::new();
        for (index, line) in raw.lines().enumerate() {
            let fields = line.split('\t').collect::<Vec<_>>();
            if fields.len() != 5 {
                return Err(format!(
                    "G0-4 Reference row {} has {} fields, expected 5",
                    index + 1,
                    fields.len()
                ));
            }
            if fields[0] != REFERENCE_SCHEMA {
                return Err(format!(
                    "G0-4 Reference row {} has unsupported schema {:?}",
                    index + 1,
                    fields[0]
                ));
            }
            let observation = ObservationKind::parse(fields[2]).ok_or_else(|| {
                format!(
                    "G0-4 Reference row {} has unsupported observation {:?}",
                    index + 1,
                    fields[2]
                )
            })?;
            let disposition = Disposition::parse(fields[3]).ok_or_else(|| {
                format!(
                    "G0-4 Reference row {} has unsupported disposition {:?}",
                    index + 1,
                    fields[3]
                )
            })?;
            let payload = decode_hex(fields[4])
                .map_err(|error| format!("G0-4 Reference row {}: {error}", index + 1))?;
            if payload.is_empty() {
                return Err(format!(
                    "G0-4 Reference row {} has an empty payload",
                    index + 1
                ));
            }
            if disposition == Disposition::Accepted
                && !payload.starts_with(b"N(")
                && !payload.starts_with(b"A(")
                && !payload.starts_with(b"I(")
            {
                return Err(format!(
                    "G0-4 Reference row {} accepted without a structural Syntax payload",
                    index + 1
                ));
            }
            records.push(ReferenceRecord {
                fixture: fields[1].to_string(),
                observation,
                disposition,
                payload,
            });
        }
        if records.len() != manifest.rows.len() {
            return Err(format!(
                "G0-4 Reference transcript has {} rows, manifest has {}",
                records.len(),
                manifest.rows.len()
            ));
        }
        for (index, (record, row)) in records.iter().zip(&manifest.rows).enumerate() {
            if record.fixture != row.id
                || record.observation != row.observation
                || record.disposition != row.disposition
            {
                return Err(format!(
                    "G0-4 Reference row {} does not match manifest: record={record:?} manifest={row:?}",
                    index + 1
                ));
            }
        }
        let transcript = Self { raw, records };
        if transcript.to_text() != transcript.raw {
            return Err("G0-4 Reference transcript is not canonical".to_string());
        }
        Ok(transcript)
    }

    pub fn records(&self) -> &[ReferenceRecord] {
        &self.records
    }

    pub fn record(&self, fixture: &str) -> Option<&ReferenceRecord> {
        self.records.iter().find(|record| record.fixture == fixture)
    }

    pub fn root(&self) -> String {
        fixture_digest(self.raw.as_bytes())
    }

    pub fn to_text(&self) -> String {
        let mut out = String::new();
        for record in &self.records {
            out.push_str(REFERENCE_SCHEMA);
            out.push('\t');
            out.push_str(&record.fixture);
            out.push('\t');
            out.push_str(record.observation.as_str());
            out.push('\t');
            out.push_str(record.disposition.as_str());
            out.push('\t');
            push_hex(&mut out, &record.payload);
            out.push('\n');
        }
        out
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ComparisonStatus {
    Exact,
    ContractGap,
    Unclassified,
}

impl ComparisonStatus {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Exact => "exact",
            Self::ContractGap => "contract-gap",
            Self::Unclassified => "unclassified",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticObservation {
    pub sequence: usize,
    pub fixture: String,
    pub family: FixtureFamily,
    pub expected: Disposition,
    pub actual: String,
    pub status: ComparisonStatus,
    pub code: String,
    pub source_root: String,
    pub reference_root: String,
    pub local_root: String,
    pub grammar_root: String,
}

impl SemanticObservation {
    pub fn to_ndjson(&self) -> String {
        let first_divergence = if self.status == ComparisonStatus::Exact {
            "none"
        } else {
            &self.code
        };
        format!(
            "{{\"schema\":\"{SEMANTIC_SCHEMA}\",\"run_id\":\"g04-{REFERENCE_TAG}\",\
             \"scenario_id\":\"g0_4_no_mock_e2e\",\"step_id\":\"{}\",\
             \"bead\":\"franken_lean-hly\",\"claim\":\"g04-syntax-hygiene-fidelity\",\
             \"invariant\":\"FL-INV-01+FL-INV-07\",\"parity_row\":\"g04:{}\",\
             \"gate\":\"G0-4\",\"epoch\":\"{REFERENCE_TAG}\",\"mode\":\"faithful\",\
             \"profile\":\"test\",\"platform\":\"linux-x86_64\",\
             \"thread_count\":\"canonical\",\"seed\":0,\"cache_state\":\"none\",\
             \"sequence\":{},\"fixture\":\"{}\",\
             \"family\":\"{}\",\"expected\":\"{}\",\"actual\":\"{}\",\
             \"classification\":\"{}\",\"code\":\"{}\",\
             \"source_root\":\"{}\",\
             \"reference_root\":\"{}\",\"local_root\":\"{}\",\
             \"grammar_root\":\"{}\",\"trace_contract\":\"{TRACE_CONTRACT_SCHEMA}\",\
             \"first_divergence\":\"{}\",\"process_exit\":0,\"signal\":\"none\",\
             \"stdout_ref\":\"regen_{REFERENCE_TAG}.ndjson#reference_stdout\",\
             \"stderr_ref\":\"regen_{REFERENCE_TAG}.ndjson#empty\",\
             \"cleanup_state\":\"reference_children_reaped\",\
             \"final_state\":\"classified\"}}\n",
            self.fixture,
            self.fixture,
            self.sequence,
            self.fixture,
            self.family.as_str(),
            self.expected.as_str(),
            self.actual,
            self.status.as_str(),
            self.code,
            self.source_root,
            self.reference_root,
            self.local_root,
            self.grammar_root,
            first_divergence,
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TelemetryObservation {
    pub run_id: String,
    pub wall_micros: u64,
    pub peak_rss_bytes: Option<u64>,
    pub reference_processes: u64,
    pub partitions: Vec<usize>,
}

impl TelemetryObservation {
    pub fn to_ndjson(&self) -> String {
        let partitions = self
            .partitions
            .iter()
            .map(usize::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let (peak_rss_state, peak_rss_bytes) = match self.peak_rss_bytes {
            Some(bytes) => ("sampled", bytes.to_string()),
            None => ("not_sampled", "null".to_string()),
        };
        format!(
            "{{\"schema\":\"{TELEMETRY_SCHEMA}\",\"run_id\":\"{}\",\
             \"scenario_id\":\"g0_4_no_mock_e2e\",\"step_id\":\"reference_pair\",\
             \"bead\":\"franken_lean-hly\",\"claim\":\"nonsemantic-run-facts\",\
             \"gate\":\"G0-4\",\"argv\":\"lean g04_reference_fixture.lean\",\
             \"cwd\":\"<workspace>/crates/fln-conformance/fixtures\",\
             \"epoch\":\"{REFERENCE_TAG}\",\"mode\":\"faithful\",\
             \"profile\":\"test\",\"platform\":\"linux-x86_64\",\
             \"thread_count\":32,\"seed\":0,\"cache_state\":\"none\",\
             \"host\":\"redacted\",\"pid\":\"redacted\",\
             \"monotonic_start_micros\":0,\"monotonic_end_micros\":{},\
             \"wall_micros\":{},\"peak_rss_state\":\"{}\",\
             \"peak_rss_bytes\":{},\
             \"reference_processes\":{},\"partitions\":[{}],\
             \"exit_status\":0,\"signal\":\"none\",\
             \"stdout_ref\":\"regen_{REFERENCE_TAG}.ndjson#reference_stdout\",\
             \"stderr_ref\":\"regen_{REFERENCE_TAG}.ndjson#empty\",\
             \"cleanup_state\":\"reference_children_reaped\",\
             \"final_state\":\"telemetry_only\"}}\n",
            self.run_id,
            self.wall_micros,
            self.wall_micros,
            peak_rss_state,
            peak_rss_bytes,
            self.reference_processes,
            partitions,
        )
    }
}

pub fn compare_manifest(
    manifest: &FixtureManifest,
    reference: &ReferenceTranscript,
) -> Vec<SemanticObservation> {
    manifest
        .rows
        .iter()
        .enumerate()
        .map(|(sequence, row)| {
            let record = reference
                .record(&row.id)
                .expect("ReferenceTranscript::parse proved the join complete");
            let reference_root = fixture_digest(&record.payload);
            let grammar_root = row.grammar_root.clone();
            let source_root = fixture_digest(row.source.as_bytes());

            if row.id == "c0_pratt_trivia" || row.id == "c0_unicode_positions" {
                return match local_c0_payload(&row.source) {
                    Ok(encoded) => {
                        let local_root = fixture_digest(encoded.as_bytes());
                        if encoded.as_bytes() == record.payload {
                            SemanticObservation {
                                sequence,
                                fixture: row.id.clone(),
                                family: row.family,
                                expected: row.disposition,
                                actual: "accepted".to_string(),
                                status: ComparisonStatus::Exact,
                                code: "byte-identical-syntax-sourceinfo".to_string(),
                                source_root,
                                reference_root,
                                local_root,
                                grammar_root,
                            }
                        } else {
                            SemanticObservation {
                                sequence,
                                fixture: row.id.clone(),
                                family: row.family,
                                expected: row.disposition,
                                actual: "accepted".to_string(),
                                status: ComparisonStatus::Unclassified,
                                code: "c0-tree-or-sourceinfo-divergence".to_string(),
                                source_root,
                                reference_root,
                                local_root,
                                grammar_root,
                            }
                        }
                    }
                    Err(error) => SemanticObservation {
                        sequence,
                        fixture: row.id.clone(),
                        family: row.family,
                        expected: row.disposition,
                        actual: "parse-error".to_string(),
                        status: ComparisonStatus::Unclassified,
                        code: "c0-unexpected-local-refusal".to_string(),
                        source_root,
                        reference_root,
                        local_root: fixture_digest(error.as_bytes()),
                        grammar_root,
                    },
                };
            }

            let source = SourceText::from_utf8(row.source.as_bytes())
                .expect("manifest parser proved the source is UTF-8");
            let table = token_table_for_phase(&row.grammar_phase);
            let lexical = lex_run(&source, &table);
            let lex_root = lexical_root(&source, &lexical);
            let expected_gap = EXPECTED_GAPS
                .iter()
                .find_map(|(fixture, code)| (*fixture == row.id).then_some(*code));
            let (status, code) = match expected_gap {
                Some(code) if lexical.accepted() => {
                    (ComparisonStatus::ContractGap, code.to_string())
                }
                Some(_) => (
                    ComparisonStatus::Unclassified,
                    "lexer-refused-before-classified-gap".to_string(),
                ),
                None => (
                    ComparisonStatus::Unclassified,
                    "fixture-has-no-classification".to_string(),
                ),
            };
            SemanticObservation {
                sequence,
                fixture: row.id.clone(),
                family: row.family,
                expected: row.disposition,
                actual: if lexical.accepted() {
                    "lexed-production-or-expansion-unavailable".to_string()
                } else {
                    "lex-error".to_string()
                },
                status,
                code,
                source_root,
                reference_root,
                local_root: lex_root,
                grammar_root,
            }
        })
        .collect()
}

pub fn acceptance_is_green(observations: &[SemanticObservation]) -> bool {
    if observations.len() != 10
        || observations
            .iter()
            .enumerate()
            .any(|(sequence, observation)| observation.sequence != sequence)
        || observations
            .iter()
            .any(|observation| observation.status == ComparisonStatus::Unclassified)
    {
        return false;
    }
    let exact = observations
        .iter()
        .filter(|observation| observation.status == ComparisonStatus::Exact)
        .map(|observation| observation.fixture.as_str())
        .collect::<Vec<_>>();
    if exact != ["c0_pratt_trivia", "c0_unicode_positions"] {
        return false;
    }
    let gaps = observations
        .iter()
        .filter(|observation| observation.status == ComparisonStatus::ContractGap)
        .map(|observation| (observation.fixture.as_str(), observation.code.as_str()))
        .collect::<Vec<_>>();
    gaps == EXPECTED_GAPS
}

pub fn semantic_stream(observations: &[SemanticObservation]) -> String {
    observations
        .iter()
        .map(SemanticObservation::to_ndjson)
        .collect()
}

pub fn semantic_root(observations: &[SemanticObservation]) -> String {
    fixture_digest(semantic_stream(observations).as_bytes())
}

pub fn fixture_digest(bytes: &[u8]) -> String {
    hash(Domain::Fixture, bytes).to_hex()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StockTraceContract {
    pub schema: &'static str,
    pub event_count: usize,
    pub elab_step_count: usize,
    pub elab_step_family_root: String,
    pub fixture_root: String,
}

pub fn stock_trace_contract() -> Result<StockTraceContract, String> {
    let events = parse_trace(STOCK_G09_TRACE).map_err(|error| error.to_string())?;
    let elab_step_count = check_elab_steps(&events).map_err(|error| format!("{error:?}"))?;
    if elab_step_count == 0 {
        return Err("stock G0-9 trace contains no Elab.step observations".to_string());
    }
    Ok(StockTraceContract {
        schema: TRACE_REPLAY_SCHEMA,
        event_count: events.len(),
        elab_step_count,
        elab_step_family_root: format!("{:016x}", family_root(&events, EventFamily::ElabStep)),
        fixture_root: fixture_digest(STOCK_G09_TRACE.as_bytes()),
    })
}

pub fn grammar_phase_roots() -> BTreeMap<&'static str, (GrammarEpoch, String)> {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("fresh G0-4 registry category");
    for (token, kind, priority) in [
        ("+", "term_+_", 65),
        ("*", "term_*_", 70),
        ("ident", "Lean.Parser.Term.app", 0),
    ] {
        registry
            .add_trailing(
                &term,
                name(token),
                Production::new(name(kind), priority, |_| {}),
                false,
            )
            .expect("G0-4 builtin production");
    }
    let builtin_epoch = registry.epoch();
    let builtin_root = grammar_root_digest(&registry, builtin_epoch);

    registry
        .add_leading(
            &term,
            name("call"),
            Production::new(name("flnG04.call"), 0, |_| {}),
            false,
        )
        .expect("G0-4 call production");
    let call_epoch = registry.epoch();
    let call_root = grammar_root_digest(&registry, call_epoch);

    registry
        .add_leading(
            &term,
            name("!!["),
            Production::new(name("flnG04.matrixNotation"), 0, |_| {}),
            false,
        )
        .expect("G0-4 matrix production");
    let matrix_epoch = registry.epoch();
    let matrix_root = grammar_root_digest(&registry, matrix_epoch);

    BTreeMap::from([
        ("builtin", (builtin_epoch, builtin_root.clone())),
        ("pre-call", (builtin_epoch, builtin_root)),
        ("post-call", (call_epoch, call_root)),
        ("post-matrix", (matrix_epoch, matrix_root)),
    ])
}

fn grammar_root_digest(registry: &Registry, epoch: GrammarEpoch) -> String {
    fixture_digest(registry.grammar_root(epoch).0.as_bytes())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HygieneObservation {
    pub decorated: String,
    pub has_macro_scopes: bool,
    pub erased: String,
    pub simplified: String,
    pub root: String,
}

pub fn model_macro_scope_name(base: Name, context: &Name, scopes: &[u64]) -> Name {
    let mut decorated = Name::str(base, "_@").append_core(context);
    decorated = Name::str(decorated, "_hyg");
    for scope in scopes {
        decorated = Name::num(decorated, *scope);
    }
    decorated
}

pub fn observe_hygiene(name: &Name) -> HygieneObservation {
    let decorated = name.to_display_string();
    let erased = name.erase_macro_scopes().to_display_string();
    let simplified = name.simp_macro_scopes().to_display_string();
    let preimage = format!("{decorated}\0{erased}\0{simplified}");
    HygieneObservation {
        decorated,
        has_macro_scopes: name.has_macro_scopes(),
        erased,
        simplified,
        root: fixture_digest(preimage.as_bytes()),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuotationPart {
    Literal(String),
    Antiquotation(String),
    Splice(Vec<String>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuotationSpliceObservation {
    pub flattened: Vec<String>,
    pub provenance: Vec<String>,
    pub generated_ids: Vec<HygieneObservation>,
    pub root: String,
}

/// Model quotation flattening without claiming to be the production macro engine.
///
/// The model retains the origin of every emitted item, assigns a distinct hygienic
/// identifier even when two items have equal text, and hashes the ordered stream.
/// The pinned Reference fixture is the authority for actual expansion identity;
/// this bounded model makes the splice/order/capture laws independently executable.
pub fn model_quotation_splice(
    parts: &[QuotationPart],
    context: &Name,
    scope_seed: u64,
) -> QuotationSpliceObservation {
    let mut flattened = Vec::new();
    let mut provenance = Vec::new();
    for (part_index, part) in parts.iter().enumerate() {
        match part {
            QuotationPart::Literal(value) => {
                flattened.push(value.clone());
                provenance.push(format!("literal:{part_index}"));
            }
            QuotationPart::Antiquotation(value) => {
                flattened.push(value.clone());
                provenance.push(format!("antiquotation:{part_index}"));
            }
            QuotationPart::Splice(values) => {
                for (splice_index, value) in values.iter().enumerate() {
                    flattened.push(value.clone());
                    provenance.push(format!("splice:{part_index}:{splice_index}"));
                }
            }
        }
    }

    let generated_ids = flattened
        .iter()
        .enumerate()
        .map(|(index, _)| {
            let base = Name::str(Name::anonymous(), format!("quoteItem{index}"));
            let generated = model_macro_scope_name(base, context, &[scope_seed, index as u64]);
            observe_hygiene(&generated)
        })
        .collect::<Vec<_>>();
    let mut canonical = String::new();
    for ((value, origin), generated) in flattened.iter().zip(&provenance).zip(&generated_ids) {
        canonical.push_str(&format!(
            "{}:{}:{}\n",
            field(value),
            field(origin),
            field(&generated.decorated)
        ));
    }
    QuotationSpliceObservation {
        flattened,
        provenance,
        generated_ids,
        root: fixture_digest(canonical.as_bytes()),
    }
}

pub fn syntax_root(syntax: &Syntax, source: &SourceText) -> String {
    fixture_digest(encode_syntax(syntax, source).as_bytes())
}

pub fn local_c0_payload(raw: &str) -> Result<String, String> {
    let (tree, source) = parse_c0(raw)?;
    Ok(encode_syntax(&tree, &source))
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BudgetMatrix {
    pub threads: usize,
    pub partitions: Vec<usize>,
    pub sequence: Vec<usize>,
    pub stream_root: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum BudgetAxis {
    SourceBytes,
    Tokens,
    TreeNodes,
    TreeDepth,
    GrammarEpochs,
    Registrations,
    MacroSteps,
    MacroDepth,
    GeneratedNames,
    SourceMapBytes,
    DiagnosticBytes,
    OracleEvents,
    OutputBytes,
    LogBytes,
}

impl BudgetAxis {
    pub const ALL: &[Self] = &[
        Self::SourceBytes,
        Self::Tokens,
        Self::TreeNodes,
        Self::TreeDepth,
        Self::GrammarEpochs,
        Self::Registrations,
        Self::MacroSteps,
        Self::MacroDepth,
        Self::GeneratedNames,
        Self::SourceMapBytes,
        Self::DiagnosticBytes,
        Self::OracleEvents,
        Self::OutputBytes,
        Self::LogBytes,
    ];

    pub const fn as_str(self) -> &'static str {
        match self {
            Self::SourceBytes => "source_bytes",
            Self::Tokens => "tokens",
            Self::TreeNodes => "tree_nodes",
            Self::TreeDepth => "tree_depth",
            Self::GrammarEpochs => "grammar_epochs",
            Self::Registrations => "registrations",
            Self::MacroSteps => "macro_steps",
            Self::MacroDepth => "macro_depth",
            Self::GeneratedNames => "generated_names",
            Self::SourceMapBytes => "source_map_bytes",
            Self::DiagnosticBytes => "diagnostic_bytes",
            Self::OracleEvents => "oracle_events",
            Self::OutputBytes => "output_bytes",
            Self::LogBytes => "log_bytes",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxContractUsage {
    observed: BTreeMap<BudgetAxis, u64>,
}

impl SyntaxContractUsage {
    pub fn observed(&self, axis: BudgetAxis) -> u64 {
        self.observed.get(&axis).copied().unwrap_or(0)
    }

    pub fn root(&self) -> String {
        let mut canonical = String::new();
        for axis in BudgetAxis::ALL {
            canonical.push_str(&format!("{}={}\n", axis.as_str(), self.observed(*axis)));
        }
        fixture_digest(canonical.as_bytes())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SyntaxBudget {
    limits: BTreeMap<BudgetAxis, u64>,
}

impl SyntaxBudget {
    pub fn exact(usage: &SyntaxContractUsage) -> Self {
        Self {
            limits: usage.observed.clone(),
        }
    }

    pub fn with_limit(mut self, axis: BudgetAxis, limit: u64) -> Self {
        self.limits.insert(axis, limit);
        self
    }

    fn limit(&self, axis: BudgetAxis) -> u64 {
        self.limits.get(&axis).copied().unwrap_or(0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContractAttemptOutcome {
    Complete,
    Inconclusive {
        axis: BudgetAxis,
        allowed: u64,
        observed: u64,
    },
    Cancelled {
        before: BudgetAxis,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractAttempt {
    pub outcome: ContractAttemptOutcome,
    pub usage_root: String,
    pub publication_root: Option<String>,
}

impl ContractAttempt {
    pub fn publication_is_valid(&self) -> bool {
        match self.outcome {
            ContractAttemptOutcome::Complete => {
                self.publication_root.as_deref() == Some(self.usage_root.as_str())
            }
            ContractAttemptOutcome::Inconclusive { .. }
            | ContractAttemptOutcome::Cancelled { .. } => self.publication_root.is_none(),
        }
    }
}

/// Measure the bounded spike apparatus, not the not-yet-built macro transaction engine.
///
/// Tree nodes use the lexer-backed leaf/node upper bound and tree depth uses delimiter
/// nesting; the G0 decision remains `bounded_model` for precisely this reason. Every axis
/// is nevertheless driven by the complete manifest and is nonzero, so each boundary can
/// be made to fire without a vacuous fake budget.
pub fn measure_contract_usage(manifest: &FixtureManifest) -> Result<SyntaxContractUsage, String> {
    let mut source_bytes = 0u64;
    let mut tokens = 0u64;
    let mut tree_nodes = 0u64;
    let mut tree_depth = 1u64;
    let mut macro_steps = 0u64;
    let mut macro_depth = 1u64;
    let mut generated_names = 0u64;
    let mut source_map_bytes = 0u64;
    let mut diagnostic_bytes = 0u64;
    let mut output_bytes = 0u64;

    for row in &manifest.rows {
        let row_bytes = u64::try_from(row.source.len())
            .map_err(|_| format!("{}: source length does not fit u64", row.id))?;
        source_bytes = source_bytes.saturating_add(row_bytes);
        let source = SourceText::from_utf8(row.source.as_bytes())
            .map_err(|error| format!("{}: source refused: {error}", row.id))?;
        let run = lex_run(&source, &token_table_for_phase(&row.grammar_phase));
        let row_tokens = run
            .events
            .iter()
            .filter(|event| matches!(event, Event::Token(_)))
            .count() as u64;
        tokens = tokens.saturating_add(row_tokens);
        tree_nodes = tree_nodes.saturating_add(row_tokens.saturating_mul(2).saturating_add(1));
        let mut depth = 1u64;
        let mut maximum = depth;
        for byte in row.source.bytes() {
            if matches!(byte, b'(' | b'[' | b'{') {
                depth = depth.saturating_add(1);
                maximum = maximum.max(depth);
            } else if matches!(byte, b')' | b']' | b'}') {
                depth = depth.saturating_sub(1).max(1);
            }
        }
        tree_depth = tree_depth.max(maximum);
        macro_steps = macro_steps.saturating_add(u64::from(
            row.observation == ObservationKind::Expand || row.family != FixtureFamily::C0,
        ));
        let row_macro_depth = 1
            + u64::from(row.comparison.contains("quotation"))
            + u64::from(row.comparison.contains("antiquotation"))
            + u64::from(row.comparison.contains("splice"));
        macro_depth = macro_depth.max(row_macro_depth);
        generated_names =
            generated_names.saturating_add(u64::from(row.comparison.contains("generated_ids")));
        if row.comparison.contains("sourceinfo") {
            source_map_bytes = source_map_bytes.saturating_add(row_bytes);
        }
        if row.disposition != Disposition::Accepted {
            diagnostic_bytes = diagnostic_bytes.saturating_add(row_bytes);
        }
        output_bytes = output_bytes
            .saturating_add(row_bytes)
            .saturating_add(row.grammar_root.len() as u64);
    }
    let grammar_epochs = manifest
        .rows
        .iter()
        .map(|row| row.grammar_epoch)
        .collect::<BTreeSet<_>>()
        .len() as u64;
    let registrations = grammar_phase_roots()
        .values()
        .map(|(epoch, _)| epoch.0)
        .max()
        .unwrap_or(0);
    let trace = stock_trace_contract()?;
    let oracle_events = manifest.rows.len() as u64 + trace.event_count as u64;
    let log_bytes = (manifest.rows.len() as u64)
        .saturating_mul(512)
        .saturating_add(trace.fixture_root.len() as u64);
    let observed = BTreeMap::from([
        (BudgetAxis::SourceBytes, source_bytes),
        (BudgetAxis::Tokens, tokens),
        (BudgetAxis::TreeNodes, tree_nodes),
        (BudgetAxis::TreeDepth, tree_depth),
        (BudgetAxis::GrammarEpochs, grammar_epochs),
        (BudgetAxis::Registrations, registrations),
        (BudgetAxis::MacroSteps, macro_steps),
        (BudgetAxis::MacroDepth, macro_depth),
        (BudgetAxis::GeneratedNames, generated_names),
        (BudgetAxis::SourceMapBytes, source_map_bytes),
        (BudgetAxis::DiagnosticBytes, diagnostic_bytes),
        (BudgetAxis::OracleEvents, oracle_events),
        (BudgetAxis::OutputBytes, output_bytes),
        (BudgetAxis::LogBytes, log_bytes),
    ]);
    if BudgetAxis::ALL
        .iter()
        .any(|axis| observed.get(axis).copied().unwrap_or(0) == 0)
    {
        return Err("G0-4 budget apparatus has a vacuous zero-observation axis".to_string());
    }
    Ok(SyntaxContractUsage { observed })
}

pub fn run_contract_attempt(
    usage: &SyntaxContractUsage,
    budget: &SyntaxBudget,
    cancel_before: Option<BudgetAxis>,
) -> ContractAttempt {
    let usage_root = usage.root();
    for axis in BudgetAxis::ALL {
        if cancel_before == Some(*axis) {
            return ContractAttempt {
                outcome: ContractAttemptOutcome::Cancelled { before: *axis },
                usage_root,
                publication_root: None,
            };
        }
        let observed = usage.observed(*axis);
        let allowed = budget.limit(*axis);
        if observed > allowed {
            return ContractAttempt {
                outcome: ContractAttemptOutcome::Inconclusive {
                    axis: *axis,
                    allowed,
                    observed,
                },
                usage_root,
                publication_root: None,
            };
        }
    }
    ContractAttempt {
        outcome: ContractAttemptOutcome::Complete,
        publication_root: Some(usage_root.clone()),
        usage_root,
    }
}

pub fn run_budget_matrix(
    manifest: &FixtureManifest,
    threads: usize,
) -> Result<BudgetMatrix, String> {
    if ![1, 8, 32].contains(&threads) {
        return Err(format!("unsupported G0-4 thread count {threads}"));
    }
    let tasks = manifest
        .rows
        .iter()
        .enumerate()
        .flat_map(|(fixture, _)| (0..4).map(move |phase| (fixture, phase)))
        .collect::<Vec<_>>();
    if tasks.len() < threads {
        return Err(format!(
            "{} G0-4 tasks cannot make {threads} productive partitions",
            tasks.len()
        ));
    }
    let rows = Arc::new(manifest.rows.clone());
    let mut ranges = Vec::new();
    let mut start = 0usize;
    for worker in 0..threads {
        let width = tasks.len() / threads + usize::from(worker < tasks.len() % threads);
        ranges.push(start..start + width);
        start += width;
    }
    let partitions = ranges.iter().map(std::ops::Range::len).collect::<Vec<_>>();
    if partitions.contains(&0) {
        return Err("G0-4 partition matrix admitted an idle worker".to_string());
    }

    let results = std::thread::scope(|scope| {
        let handles = ranges
            .into_iter()
            .map(|range| {
                let rows = Arc::clone(&rows);
                let slice = tasks[range].to_vec();
                scope.spawn(move || {
                    slice
                        .into_iter()
                        .map(|(fixture, phase)| {
                            let sequence = fixture * 4 + phase;
                            task_root(&rows[fixture], phase).map(|root| (sequence, root))
                        })
                        .collect::<Result<Vec<_>, _>>()
                })
            })
            .collect::<Vec<_>>();
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .map_err(|_| "G0-4 budget worker panicked".to_string())?
            })
            .collect::<Result<Vec<_>, String>>()
    })?;
    let flat = results.into_iter().flatten().collect::<Vec<_>>();
    let sequence = flat
        .iter()
        .map(|(sequence, _)| *sequence)
        .collect::<Vec<_>>();
    let expected_sequence = (0..tasks.len()).collect::<Vec<_>>();
    if sequence != expected_sequence {
        return Err(format!(
            "G0-4 partitions changed within-file task order: {sequence:?}"
        ));
    }
    let mut stream = String::new();
    for (sequence, root) in &flat {
        stream.push_str(&format!("{sequence}:{root}\n"));
    }
    Ok(BudgetMatrix {
        threads,
        partitions,
        sequence,
        stream_root: fixture_digest(stream.as_bytes()),
    })
}

fn task_root(row: &FixtureRow, phase: usize) -> Result<String, String> {
    let source = SourceText::from_utf8(row.source.as_bytes())
        .map_err(|error| format!("{}: source refused: {error}", row.id))?;
    let table = token_table_for_phase(&row.grammar_phase);
    match phase {
        0 => {
            let run = lex_run_bounded(&source, &table, LexBudget::generous());
            let run = run
                .into_complete()
                .map_err(|non_authoritative| format!("{}: {non_authoritative:?}", row.id))?;
            Ok(lexical_root(&source, &run))
        }
        1 => {
            let mut positions = String::new();
            for at in 0..=source.len_bytes() {
                if source.as_str().is_char_boundary(at)
                    && let Some(position) = source.position_of(BytePos(at))
                {
                    positions.push_str(&format!(
                        "{at}:{},{},{},{};",
                        position.line,
                        position.byte_column,
                        position.scalar_column,
                        position.utf16_column
                    ));
                }
            }
            Ok(fixture_digest(positions.as_bytes()))
        }
        2 => {
            let budget = LexBudget {
                max_input_bytes: source.len_bytes().saturating_sub(1) as u64,
                max_events: u64::MAX,
            };
            match lex_run_bounded(&source, &table, budget) {
                Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                    InconclusiveCause::ResourceExhausted { usage }
                        if usage.is_genuine_exhaustion() =>
                    {
                        Ok(fixture_digest(format!("{inconclusive:?}").as_bytes()))
                    }
                    _ => Err(format!(
                        "{}: tight lexical budget was not a genuine resource exhaustion: \
                         {inconclusive:?}",
                        row.id
                    )),
                },
                other => Err(format!(
                    "{}: tight lexical budget was authoritative instead of Inconclusive: {other:?}",
                    row.id
                )),
            }
        }
        3 => Ok(fixture_digest(
            format!(
                "{}:{}:{}:{}:{}",
                row.id,
                row.family.as_str(),
                row.grammar_epoch.0,
                row.grammar_root,
                row.comparison.iter().cloned().collect::<Vec<_>>().join(",")
            )
            .as_bytes(),
        )),
        _ => Err(format!("{}: unsupported budget task phase {phase}", row.id)),
    }
}

fn token_table_for_phase(phase: &str) -> TokenTable {
    let mut tokens = vec!["+", "*", "(", ")", ",", ";", "[", "]"];
    if matches!(phase, "post-call" | "post-matrix") {
        tokens.push("call");
    }
    if phase == "post-matrix" {
        tokens.push("!![");
    }
    TokenTable::from_tokens(tokens)
}

fn lexical_root(source: &SourceText, run: &fln_syntax::run::LexRun) -> String {
    let mut canonical = String::new();
    for event in &run.events {
        match event {
            Event::Trivia(span) => canonical.push_str(&format!(
                "T:{}:{}:{};",
                span.start().0,
                span.end().0,
                source.span_str(*span).unwrap_or_default()
            )),
            Event::Token(token) => canonical.push_str(&format!(
                "K:{}:{}:{:?};",
                token.extent.start().0,
                token.extent.end().0,
                token.kind
            )),
            Event::Refused { error, skipped } => canonical.push_str(&format!(
                "R:{}:{}:{}:{};",
                error.at().0,
                skipped.start().0,
                skipped.end().0,
                error.message()
            )),
        }
    }
    fixture_digest(canonical.as_bytes())
}

fn encode_syntax(syntax: &Syntax, source: &SourceText) -> String {
    match syntax {
        Syntax::Missing => "M".to_string(),
        Syntax::Atom { info, val } => {
            format!("A({};{})", encode_info(*info, source), field(val))
        }
        Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } => {
            let raw = source.span_str(*raw_val).unwrap_or_default();
            let encoded_preresolved = preresolved
                .iter()
                .map(encode_preresolved)
                .collect::<String>();
            format!(
                "I({};{};{};{};{})",
                encode_info(*info, source),
                field(raw),
                field(&val.to_display_string()),
                preresolved.len(),
                encoded_preresolved
            )
        }
        Syntax::Node { info, kind, args } => {
            let encoded_args = args
                .iter()
                .map(|arg| encode_syntax(arg, source))
                .collect::<String>();
            let kind = reference_name_string(kind);
            format!(
                "N({};{};{};{})",
                encode_info(*info, source),
                field(&kind),
                args.len(),
                encoded_args
            )
        }
    }
}

fn reference_name_string(name: &Name) -> String {
    let display = name.to_display_string();
    match display.as_str() {
        // The C0 Pratt contract's symbolic parser kinds are quoted by Lean's
        // `Name.toString`; `Name::to_display_string` deliberately does not add
        // that surface syntax.
        "term_+_" | "term_*_" => format!("«{display}»"),
        _ => display,
    }
}

fn encode_preresolved(preresolved: &Preresolved) -> String {
    match preresolved {
        Preresolved::Namespace { ns } => format!("PNS({})", field(&ns.to_display_string())),
        Preresolved::Decl { name, fields } => format!(
            "PDECL({};{};{})",
            field(&name.to_display_string()),
            fields.len(),
            fields
                .iter()
                .map(|field_name| field(field_name))
                .collect::<String>()
        ),
    }
}

fn encode_info(info: SourceInfo, source: &SourceText) -> String {
    match info {
        SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } => format!(
            "O({};{};{};{})",
            encode_span(leading, source),
            pos.0,
            encode_span(trailing, source),
            end_pos.0
        ),
        SourceInfo::Synthetic {
            pos,
            end_pos,
            canonical,
        } => format!("S({};{};{})", pos.0, end_pos.0, usize::from(canonical)),
        SourceInfo::None => "Z".to_string(),
    }
}

fn encode_span(span: fln_syntax::source::ByteSpan, source: &SourceText) -> String {
    format!(
        "{},{},{}",
        span.start().0,
        span.end().0,
        field(source.span_str(span).unwrap_or_default())
    )
}

fn field(text: &str) -> String {
    let mut out = format!("{}:", text.len());
    push_hex(&mut out, text.as_bytes());
    out
}

fn parse_c0(raw: &str) -> Result<(Syntax, SourceText), String> {
    let grammar = C0Grammar::build(raw)?;
    let mut state = ParserState::new(0);
    pratt_parser(grammar.as_ref(), &mut state);
    if let Some(error) = state.error() {
        return Err(format!(
            "parser refused at byte {}: {}",
            error.at.0,
            error.message()
        ));
    }
    if let Some(index) = grammar.next_token_index(state.pos()) {
        return Err(format!(
            "parser left token {:?} at byte {}",
            grammar.tokens[index].kind,
            grammar.tokens[index].extent.start().0
        ));
    }
    let tree = result_of(&state)
        .cloned()
        .ok_or_else(|| "parser produced no tree".to_string())?;
    Ok((tree, grammar.source.clone()))
}

struct IndexedProduction {
    token_index: usize,
    production: Production,
}

struct C0Grammar {
    source: SourceText,
    tokens: Vec<LexedToken>,
    leading: Vec<IndexedProduction>,
    trailing: Vec<IndexedProduction>,
}

impl C0Grammar {
    fn build(raw: &str) -> Result<Arc<Self>, String> {
        let source = SourceText::from_utf8(raw.as_bytes())
            .map_err(|error| format!("source is not UTF-8: {error}"))?;
        let run = lex_run(&source, &TokenTable::from_tokens(["+", "*"]));
        if !run.accepted() {
            return Err(format!("lexer refused: {:?}", run.diagnostics()));
        }
        let tokens = run
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Token(token) => Some(token.clone()),
                Event::Trivia(_) | Event::Refused { .. } => None,
            })
            .collect::<Vec<_>>();
        let leaves = Leaves::build(&source, &tokens)
            .map_err(|error| format!("attachment refused: {error:?}"))?;
        Ok(Arc::new_cyclic(move |grammar| {
            let mut leading = Vec::new();
            let mut trailing = Vec::new();
            for (token_index, token) in tokens.iter().enumerate() {
                let leaf = leaves.leaf(token_index).unwrap_or(Syntax::Missing);
                match &token.kind {
                    TokenKind::Literal(kind) => leading.push(IndexedProduction {
                        token_index,
                        production: literal_production(*kind, leaf, token.extent.end()),
                    }),
                    TokenKind::Ident(_) => leading.push(IndexedProduction {
                        token_index,
                        production: ident_production(leaf, token.extent.end()),
                    }),
                    TokenKind::Symbol(symbol) => {
                        let precedence = match symbol.as_str() {
                            "+" => Some(65),
                            "*" => Some(70),
                            _ => None,
                        };
                        if let Some(precedence) = precedence {
                            trailing.push(IndexedProduction {
                                token_index,
                                production: operator_production(
                                    grammar.clone(),
                                    symbol.clone(),
                                    precedence,
                                    leaf,
                                    token.extent.end(),
                                ),
                            });
                        }
                    }
                }
            }
            Self {
                source,
                tokens,
                leading,
                trailing,
            }
        }))
    }

    fn next_token_index(&self, from: BytePos) -> Option<usize> {
        self.tokens
            .iter()
            .position(|token| token.extent.start().0 >= from.0)
    }

    fn lookup<'a>(&'a self, entries: &'a [IndexedProduction], state: &ParserState) -> Lookup<'a> {
        let Some(index) = self.next_token_index(state.pos()) else {
            return Lookup::TokenError(ParseError::new("unexpected end of input", state.pos()));
        };
        Lookup::Productions(
            entries
                .iter()
                .filter(|entry| entry.token_index == index)
                .map(|entry| &entry.production)
                .collect(),
        )
    }
}

impl Grammar for C0Grammar {
    fn kind(&self) -> Name {
        name("term")
    }

    fn leading_at(&self, state: &ParserState) -> Lookup<'_> {
        self.lookup(&self.leading, state)
    }

    fn trailing_at(&self, state: &ParserState) -> Lookup<'_> {
        self.lookup(&self.trailing, state)
    }

    fn consume_token(&self, state: &mut ParserState) -> Result<String, ParseError> {
        let Some(index) = self.next_token_index(state.pos()) else {
            return Err(ParseError::new("unexpected end of input", state.pos()));
        };
        let token = &self.tokens[index];
        state.set_pos(token.extent.end());
        Ok(self
            .source
            .span_str(token.extent)
            .unwrap_or_default()
            .to_string())
    }
}

fn literal_production(kind: LiteralKind, leaf: Syntax, end: BytePos) -> Production {
    let node_kind = match kind {
        LiteralKind::Nat => "num",
        LiteralKind::Scientific => "scientific",
        LiteralKind::Str => "str",
        LiteralKind::Char => "char",
        LiteralKind::Name => "name",
    };
    Production::new(name(node_kind), 0, move |state| {
        state.set_pos(end);
        state.set_lhs_prec(MAX_PREC);
        state.push(Syntax::node(name(node_kind), vec![leaf.clone()]));
    })
}

fn ident_production(leaf: Syntax, end: BytePos) -> Production {
    Production::new(name("ident"), 0, move |state| {
        state.set_pos(end);
        state.set_lhs_prec(MAX_PREC);
        state.push(leaf.clone());
    })
}

fn operator_production(
    grammar: Weak<C0Grammar>,
    symbol: String,
    precedence: u32,
    operator_leaf: Syntax,
    operator_end: BytePos,
) -> Production {
    let kind = name(&format!("term_{symbol}_"));
    let production_kind = kind.clone();
    Production::new(production_kind, 0, move |state| {
        if !state.check_lhs_prec(precedence) || !state.check_prec(precedence) {
            return;
        }
        let Some(left) = state.pop() else {
            state.set_error(ParseError::new(
                "operator production has no left operand",
                state.pos(),
            ));
            return;
        };
        state.set_pos(operator_end);
        let outer = state.prec();
        state.set_prec(precedence + 1);
        let Some(grammar) = grammar.upgrade() else {
            state.set_error(ParseError::new(
                "G0-4 grammar expired during parse",
                state.pos(),
            ));
            return;
        };
        pratt_parser(grammar.as_ref(), state);
        state.set_prec(outer);
        if state.has_error() {
            return;
        }
        let Some(right) = state.pop() else {
            state.set_error(ParseError::new(
                "operator production has no right operand",
                state.pos(),
            ));
            return;
        };
        state.push(Syntax::node(
            kind.clone(),
            vec![left, operator_leaf.clone(), right],
        ));
        state.set_lhs_prec(precedence);
    })
}

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn is_lower_hex(text: &str, len: usize) -> bool {
    text.len() == len
        && text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub fn decode_hex(text: &str) -> Result<Vec<u8>, String> {
    if !text.len().is_multiple_of(2) {
        return Err("hex payload has odd length".to_string());
    }
    let mut bytes = Vec::with_capacity(text.len() / 2);
    let (pairs, remainder) = text.as_bytes().as_chunks::<2>();
    debug_assert!(remainder.is_empty());
    for pair in pairs {
        let high = hex_nibble(pair[0]).ok_or_else(|| {
            format!(
                "hex payload contains non-lowercase-hex byte {:?}",
                pair[0] as char
            )
        })?;
        let low = hex_nibble(pair[1]).ok_or_else(|| {
            format!(
                "hex payload contains non-lowercase-hex byte {:?}",
                pair[1] as char
            )
        })?;
        bytes.push((high << 4) | low);
    }
    Ok(bytes)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn push_hex(out: &mut String, bytes: &[u8]) {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
}
