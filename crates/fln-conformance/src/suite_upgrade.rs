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
