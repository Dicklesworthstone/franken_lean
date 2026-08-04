//! W1's deliberate suite-upgrade model (plan §2.10–2.11, R16).
//!
//! The current lock is authoritative until every candidate join is present. This
//! small model is intentionally independent of the concrete extractor and
//! Tribunal runners: those runners produce the identities it requires, while it
//! decides whether publication is legal.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

pub const REQUIRED_LEDGER_IDS: [&str; 6] = [
    "asupersync-ordered-merge",
    "franken-networkx-incremental-dominators",
    "frankensearch-transaction-commit-hooks",
    "franken-markdown-lean-lexer-profile",
    "frankensqlite-cas-blob-access",
    "fln-bignum-second-suite-consumer",
];

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum LedgerState {
    Proposed,
    Investigated,
    UpstreamRequested,
    AcceptedUpstream,
    Released,
    PinnedInSuiteLock,
    AcceptanceEvidenced,
    LoadBearing,
    Rejected,
    Superseded,
}

impl LedgerState {
    pub fn parse(value: &str) -> Result<Self, String> {
        match value {
            "proposed" => Ok(Self::Proposed),
            "investigated" => Ok(Self::Investigated),
            "upstream-requested" => Ok(Self::UpstreamRequested),
            "accepted-upstream" => Ok(Self::AcceptedUpstream),
            "released" => Ok(Self::Released),
            "pinned-in-SUITE.lock" => Ok(Self::PinnedInSuiteLock),
            "acceptance-evidenced" => Ok(Self::AcceptanceEvidenced),
            "load-bearing" => Ok(Self::LoadBearing),
            "rejected" => Ok(Self::Rejected),
            "superseded" => Ok(Self::Superseded),
            _ => Err(format!("unknown upstream-ledger state `{value}`")),
        }
    }

    pub fn can_transition_to(self, next: Self) -> bool {
        use LedgerState::*;
        matches!(
            (self, next),
            (Proposed, Investigated | Rejected | Superseded)
                | (Investigated, UpstreamRequested | Rejected | Superseded)
                | (UpstreamRequested, AcceptedUpstream | Rejected | Superseded)
                | (AcceptedUpstream, Released | Rejected | Superseded)
                | (Released, PinnedInSuiteLock | Rejected | Superseded)
                | (
                    PinnedInSuiteLock,
                    AcceptanceEvidenced | Rejected | Superseded
                )
                | (AcceptanceEvidenced, LoadBearing | Rejected | Superseded)
        )
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct LedgerRow {
    pub id: String,
    pub state: LedgerState,
    pub fields: BTreeMap<String, String>,
}

pub fn parse_ledger(text: &str) -> Result<Vec<LedgerRow>, String> {
    let mut rows = Vec::new();
    let mut schema = false;
    for (line_number, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line == "schema upstream-ledger/1" {
            schema = true;
            continue;
        }
        let Some(payload) = line.strip_prefix("entry ") else {
            continue;
        };
        let mut fields = BTreeMap::new();
        for field in payload.split('|') {
            let Some((key, value)) = field.split_once('=') else {
                return Err(format!(
                    "UPSTREAM_LEDGER.md:{}: malformed field `{field}`",
                    line_number + 1
                ));
            };
            if key.is_empty()
                || value.is_empty()
                || fields.insert(key.to_string(), value.to_string()).is_some()
            {
                return Err(format!(
                    "UPSTREAM_LEDGER.md:{}: duplicate or empty `{key}`",
                    line_number + 1
                ));
            }
        }
        let id = fields
            .remove("id")
            .ok_or_else(|| format!("UPSTREAM_LEDGER.md:{}: missing id", line_number + 1))?;
        let state =
            LedgerState::parse(&fields.remove("state").ok_or_else(|| {
                format!("UPSTREAM_LEDGER.md:{}: missing state", line_number + 1)
            })?)?;
        rows.push(LedgerRow { id, state, fields });
    }
    if !schema {
        return Err("UPSTREAM_LEDGER.md: missing `schema upstream-ledger/1`".to_string());
    }
    Ok(rows)
}

pub fn validate_ledger(rows: &[LedgerRow]) -> Result<(), String> {
    let mut seen = BTreeMap::new();
    for row in rows {
        if seen.insert(row.id.clone(), ()).is_some() {
            return Err(format!("duplicate upstream-ledger id `{}`", row.id));
        }
        for required in [
            "owner",
            "repository",
            "link",
            "rationale",
            "gate",
            "consumer",
            "fallback",
            "revisit",
        ] {
            if row.fields.get(required).is_none_or(String::is_empty) {
                return Err(format!("upstream-ledger `{}` missing `{required}`", row.id));
            }
        }
        if row.state == LedgerState::LoadBearing
            && row.fields.get("acceptance").is_none_or(String::is_empty)
        {
            return Err(format!(
                "upstream-ledger `{}` is load-bearing without an attached candidate acceptance record",
                row.id
            ));
        }
    }
    for id in REQUIRED_LEDGER_IDS {
        if !seen.contains_key(id) {
            return Err(format!("upstream-ledger missing seed `{id}`"));
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LockChange {
    Addition,
    Removal,
    Upgrade,
    Downgrade,
    Retarget,
    Nightly,
    TargetFeature,
    Profile,
    Reference,
    Corpus,
    PathCommitTreeChecksum,
}

impl LockChange {
    pub const fn label(self) -> &'static str {
        match self {
            Self::Addition => "addition",
            Self::Removal => "removal",
            Self::Upgrade => "upgrade",
            Self::Downgrade => "downgrade",
            Self::Retarget => "retarget",
            Self::Nightly => "nightly",
            Self::TargetFeature => "target-feature",
            Self::Profile => "profile",
            Self::Reference => "reference",
            Self::Corpus => "corpus",
            Self::PathCommitTreeChecksum => "path-commit-tree-checksum",
        }
    }

    fn parse_label(value: &str) -> Result<Self, String> {
        match value {
            "addition" => Ok(Self::Addition),
            "removal" => Ok(Self::Removal),
            "upgrade" => Ok(Self::Upgrade),
            "downgrade" => Ok(Self::Downgrade),
            "retarget" => Ok(Self::Retarget),
            "nightly" => Ok(Self::Nightly),
            "target-feature" => Ok(Self::TargetFeature),
            "profile" => Ok(Self::Profile),
            "reference" => Ok(Self::Reference),
            "corpus" => Ok(Self::Corpus),
            "path-commit-tree-checksum" => Ok(Self::PathCommitTreeChecksum),
            _ => Err(format!("unknown candidate receipt change kind `{value}`")),
        }
    }
}

/// The identity-bearing half of a candidate's retained evidence. A `true`
/// stage flag alone is not publication evidence: every producer must name the
/// same candidate and its exact old/proposed lock roots.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CandidateReceipt {
    pub candidate_id: String,
    pub change: LockChange,
    pub old_lock_root: String,
    pub candidate_lock_root: String,
    pub closure_root: String,
    pub contract_and_census_root: String,
    pub tribunal_root: String,
    pub migration_root: String,
    pub rollback_root: String,
    pub external_evidence_root: String,
    pub final_current_lock_root: String,
}

impl CandidateReceipt {
    pub fn validate(&self) -> Result<(), String> {
        if self.candidate_id.is_empty()
            || !self
                .candidate_id
                .bytes()
                .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
        {
            return Err("candidate receipt needs a canonical candidate id".to_string());
        }
        if self.old_lock_root == self.candidate_lock_root {
            return Err("candidate receipt does not change the lock root".to_string());
        }
        if self.final_current_lock_root != self.old_lock_root {
            return Err(
                "candidate receipt observed an authoritative lock root different from its old root"
                    .to_string(),
            );
        }
        for (name, root) in [
            ("old_lock_root", &self.old_lock_root),
            ("candidate_lock_root", &self.candidate_lock_root),
            ("closure_root", &self.closure_root),
            ("contract_and_census_root", &self.contract_and_census_root),
            ("tribunal_root", &self.tribunal_root),
            ("migration_root", &self.migration_root),
            ("rollback_root", &self.rollback_root),
            ("external_evidence_root", &self.external_evidence_root),
            ("final_current_lock_root", &self.final_current_lock_root),
        ] {
            if !is_canonical_root(root) {
                return Err(format!(
                    "candidate receipt `{name}` is not a canonical SHA-256 root"
                ));
            }
        }
        Ok(())
    }

    /// One canonical, schema-versioned NDJSON record. The eventual shared E2E
    /// emits this receipt alongside its richer run log; parsing it back makes a
    /// reordered or partial record non-authoritative before its identities can
    /// join the candidate.
    pub fn to_ndjson(&self) -> Result<String, String> {
        self.validate()?;
        Ok(format!(
            concat!(
                r#"{{"schema":"fln-suite-upgrade-candidate/1","candidate_id":"{}","change":"{}","old_lock_root":"{}","candidate_lock_root":"{}","closure_root":"{}","contract_and_census_root":"{}","tribunal_root":"{}","migration_root":"{}","rollback_root":"{}","external_evidence_root":"{}","final_current_lock_root":"{}"}}"#,
                "\n"
            ),
            self.candidate_id,
            self.change.label(),
            self.old_lock_root,
            self.candidate_lock_root,
            self.closure_root,
            self.contract_and_census_root,
            self.tribunal_root,
            self.migration_root,
            self.rollback_root,
            self.external_evidence_root,
            self.final_current_lock_root,
        ))
    }

    pub fn from_ndjson(text: &str) -> Result<Self, String> {
        let values = parse_canonical_receipt_ndjson(text)?;
        let change = LockChange::parse_label(&values[2])?;
        let receipt = Self {
            candidate_id: values[1].clone(),
            change,
            old_lock_root: values[3].clone(),
            candidate_lock_root: values[4].clone(),
            closure_root: values[5].clone(),
            contract_and_census_root: values[6].clone(),
            tribunal_root: values[7].clone(),
            migration_root: values[8].clone(),
            rollback_root: values[9].clone(),
            external_evidence_root: values[10].clone(),
            final_current_lock_root: values[11].clone(),
        };
        receipt.validate()?;
        if receipt.to_ndjson()? != text {
            return Err("candidate receipt NDJSON is parseable but not canonical".to_string());
        }
        Ok(receipt)
    }
}

fn is_canonical_root(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || matches!(byte, b'a'..=b'f'))
}

fn parse_canonical_receipt_ndjson(text: &str) -> Result<Vec<String>, String> {
    const KEYS: [&str; 12] = [
        "schema",
        "candidate_id",
        "change",
        "old_lock_root",
        "candidate_lock_root",
        "closure_root",
        "contract_and_census_root",
        "tribunal_root",
        "migration_root",
        "rollback_root",
        "external_evidence_root",
        "final_current_lock_root",
    ];
    if !text.ends_with('\n') || text[..text.len() - 1].contains('\n') {
        return Err(
            "candidate receipt must be exactly one newline-terminated NDJSON row".to_string(),
        );
    }
    let mut remaining = &text[..text.len() - 1];
    remaining = remaining
        .strip_prefix('{')
        .ok_or_else(|| "candidate receipt row must start with `{`".to_string())?;
    let mut values = Vec::with_capacity(KEYS.len());
    for (index, expected_key) in KEYS.iter().enumerate() {
        let (key, after_key) = take_json_string(remaining)?;
        if key != *expected_key {
            return Err(format!(
                "candidate receipt field {index} is `{key}`, expected `{expected_key}`"
            ));
        }
        let after_colon = after_key
            .strip_prefix(':')
            .ok_or_else(|| format!("candidate receipt field `{expected_key}` lacks `:`"))?;
        let (value, after_value) = take_json_string(after_colon)?;
        values.push(value);
        remaining = if index + 1 == KEYS.len() {
            after_value
                .strip_prefix('}')
                .ok_or_else(|| "candidate receipt row lacks closing `}`".to_string())?
        } else {
            after_value
                .strip_prefix(',')
                .ok_or_else(|| format!("candidate receipt field `{expected_key}` lacks `,`"))?
        };
    }
    if !remaining.is_empty() {
        return Err("candidate receipt row has trailing bytes".to_string());
    }
    if values[0] != "fln-suite-upgrade-candidate/1" {
        return Err(format!("unknown candidate receipt schema `{}`", values[0]));
    }
    Ok(values)
}

fn take_json_string(input: &str) -> Result<(String, &str), String> {
    let input = input
        .strip_prefix('"')
        .ok_or_else(|| "candidate receipt field is not a JSON string".to_string())?;
    let Some(end) = input.find('"') else {
        return Err("candidate receipt has an unterminated JSON string".to_string());
    };
    let value = &input[..end];
    if value.contains('\\') || value.bytes().any(|byte| byte.is_ascii_control()) {
        return Err("candidate receipt strings must be unescaped canonical ASCII".to_string());
    }
    Ok((value.to_string(), &input[end + 1..]))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Candidate {
    pub change: LockChange,
    pub current_lock_root: String,
    pub candidate_lock_root: String,
    pub isolated: bool,
    pub closure_delta: bool,
    pub canonical_contract_and_census_diff: bool,
    pub tribunal_diff: bool,
    pub component_migration: bool,
    pub rollback_proven: bool,
    pub current_root_unchanged: bool,
    pub external_evidence_identity: bool,
    pub cancelled: bool,
}

impl Candidate {
    pub fn publication_error(&self) -> Option<&'static str> {
        if self.cancelled {
            return Some("candidate was cancelled");
        }
        if !self.isolated {
            return Some("candidate is not isolated");
        }
        if self.current_lock_root == self.candidate_lock_root {
            return Some("candidate does not change the lock root");
        }
        if !self.closure_delta {
            return Some("closure delta is absent");
        }
        if !self.canonical_contract_and_census_diff {
            return Some("canonical contract/census diff is absent");
        }
        if !self.tribunal_diff {
            return Some("Tribunal comparison is absent");
        }
        if !self.component_migration {
            return Some("component migration is absent");
        }
        if !self.rollback_proven {
            return Some("rollback proof is absent");
        }
        if !self.current_root_unchanged {
            return Some("current authoritative root changed during candidate validation");
        }
        if !self.external_evidence_identity {
            return Some("external evidence identity is absent");
        }
        None
    }

    pub fn may_publish(&self, waiver: Option<&Waiver>) -> bool {
        self.publication_error().is_none() && waiver.is_none()
    }

    /// Binds the model's stage completion claims to the retained receipt. The
    /// receipt is deliberately separate so E2E runners can supply exact
    /// identities without treating an in-memory model as evidence.
    pub fn publication_error_with_receipt(&self, receipt: &CandidateReceipt) -> Option<String> {
        if let Some(error) = self.publication_error() {
            return Some(error.to_string());
        }
        if let Err(error) = receipt.validate() {
            return Some(error);
        }
        if self.change != receipt.change {
            return Some(format!(
                "candidate change kind `{}` does not match receipt change kind `{}`",
                self.change.label(),
                receipt.change.label()
            ));
        }
        if self.current_lock_root != receipt.old_lock_root
            || self.candidate_lock_root != receipt.candidate_lock_root
        {
            return Some(
                "candidate lock roots do not match the receipt's exact old/proposed roots"
                    .to_string(),
            );
        }
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Waiver {
    pub owner: String,
    pub scope: String,
    pub rationale: String,
    pub expiry: String,
    pub review_date: String,
    pub defers_only: bool,
    pub constitutional_or_load_bearing: bool,
}

impl Waiver {
    pub fn validate(&self) -> Result<(), String> {
        if [
            self.owner.as_str(),
            self.scope.as_str(),
            self.rationale.as_str(),
            self.expiry.as_str(),
            self.review_date.as_str(),
        ]
        .iter()
        .any(|field| field.is_empty())
        {
            return Err(
                "waiver needs owner, exact scope, rationale, expiry, and review date".to_string(),
            );
        }
        if !self.defers_only || self.constitutional_or_load_bearing {
            return Err("waiver may defer or block only; it cannot authorize constitutional or load-bearing obligations".to_string());
        }
        for (name, value) in [("expiry", &self.expiry), ("review date", &self.review_date)] {
            let bytes = value.as_bytes();
            if bytes.len() != 10
                || bytes[4] != b'-'
                || bytes[7] != b'-'
                || !bytes
                    .iter()
                    .enumerate()
                    .all(|(index, byte)| matches!(index, 4 | 7) || byte.is_ascii_digit())
            {
                return Err(format!("waiver {name} must be a bounded YYYY-MM-DD date"));
            }
        }
        Ok(())
    }
}
