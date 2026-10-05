//! **The stdlib frontier coverage ratchet** (bead `franken_lean-z8j.1.16`, criterion 3):
//! a fresh `fln check-olean --continue --json` frontier is compared with the retained
//! receipt at `crates/fln-conformance/evidence/stdlib_frontier/<pin>.json`, and coverage
//! may only rise.
//!
//! A **drop** fails, and every drop is named:
//! * a module the receipt has that the fresh run does not ([`CoverageComparison::lost`]);
//! * a module the receipt accepts that the fresh run does not accept, whatever its new
//!   verdict ([`CoverageComparison::no_longer_accepted`]);
//! * a module accepted in both whose accepted declaration count changed, in either
//!   direction ([`CoverageComparison::count_changed`]). At one pin a module's declarations
//!   are fixed, so a different count means the decode or the admission changed what it
//!   covers, and that needs a human before it is called coverage.
//!
//! An **improvement** is reported and never fails: a module the receipt did not accept that
//! the fresh run accepts, or a module the fresh run has that the receipt does not.
//!
//! A **non-acceptance that changed shape** — a module not accepted on either side whose
//! verdict or `blockedBy` differs — is reported for a human and never fails: it moves no
//! coverage ([`CoverageComparison::changed`]).
//!
//! **Only format-independent fields are read.** A row's coverage is its module, verdict,
//! declaration count and `blockedBy`. Declaration digests, logical roots and any other
//! field whose value depends on a hashing or encoding format (for example a new
//! `decl-content-dag/1` digest tag) are ignored on both sides, and `detail` text — which can
//! quote such values — is reported but never compared. So a run of a later binary with new
//! digests and identical verdicts passes against a receipt bound to an older binary.
//!
//! Timings (`elapsedMs`) are measurements, never compared. Before either document is
//! compared it must be **self-consistent** — its summary counts are recomputed from its
//! rows and must agree, module names are unique, and the schema is the frontier schema —
//! so a truncated or hand-edited file is refused rather than compared as if it were clean.
//!
//! Driven from the command line by the `stdlib-frontier-ratchet` binary.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// The frontier document schema this ratchet understands.
pub const FRONTIER_SCHEMA: &str = "fln.check-olean-frontier/1";

/// The retained receipt for the pinned Reference, relative to the workspace root.
pub const RETAINED_RECEIPT: &str = "crates/fln-conformance/evidence/stdlib_frontier/v4.32.0.json";

/// Nesting and size bounds for the reader: a frontier document is one object holding one
/// array of flat objects, so anything deeper is not one.
const MAX_DEPTH: usize = 8;
const MAX_BYTES: usize = 64 * 1024 * 1024;

/// One module's row, as far as coverage is concerned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontierRow {
    pub module: String,
    pub verdict: String,
    pub declarations: u64,
    pub detail: String,
    /// The import a `blocked` module waits on; `None` for every other verdict.
    pub blocked_by: Option<String>,
}

/// A parsed, self-consistent frontier document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Frontier {
    pub outcome: String,
    pub authority: bool,
    pub rows: Vec<FrontierRow>,
    pub accepted_declarations: u64,
}

/// Why a document could not be compared.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrontierError {
    /// Not JSON this reader accepts, with the byte where it stopped.
    Syntax { at: usize, reason: &'static str },
    /// Valid JSON that is not a frontier document.
    Shape(String),
    /// A frontier document whose summary disagrees with its own rows.
    Inconsistent(String),
}

impl fmt::Display for FrontierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FrontierError::Syntax { at, reason } => write!(f, "not JSON at byte {at}: {reason}"),
            FrontierError::Shape(detail) => write!(f, "not a frontier document: {detail}"),
            FrontierError::Inconsistent(detail) => {
                write!(f, "frontier document disagrees with itself: {detail}")
            }
        }
    }
}

impl std::error::Error for FrontierError {}

/// The comparison of a fresh frontier with the retained receipt.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CoverageComparison {
    /// Modules in the receipt and absent from the fresh run.
    pub lost: Vec<String>,
    /// Modules the receipt accepts and the fresh run does not: (module, new verdict, detail).
    pub no_longer_accepted: Vec<(String, String, String)>,
    /// Modules accepted in both whose declaration count changed: (module, receipt, now).
    pub count_changed: Vec<(String, u64, u64)>,
    /// Modules the receipt did not accept that the fresh run accepts: (module, old verdict).
    pub newly_accepted: Vec<(String, String)>,
    /// Modules the fresh run has that the receipt does not: (module, verdict).
    pub added: Vec<(String, String)>,
    /// Modules not accepted on either side whose verdict or `blockedBy` differs:
    /// (module, (receipt verdict, receipt blockedBy), (now verdict, now blockedBy)).
    #[allow(clippy::type_complexity)]
    pub changed: Vec<(String, (String, Option<String>), (String, Option<String>))>,
    pub receipt_accepted: usize,
    pub current_accepted: usize,
    pub receipt_modules: usize,
    pub current_modules: usize,
}

impl CoverageComparison {
    /// Whether coverage dropped: any lost module, lost acceptance or changed count.
    pub fn dropped(&self) -> bool {
        !self.lost.is_empty()
            || !self.no_longer_accepted.is_empty()
            || !self.count_changed.is_empty()
    }

    /// Whether anything improved.
    pub fn improved(&self) -> bool {
        !self.newly_accepted.is_empty() || !self.added.is_empty()
    }

    /// A human report, one finding per line, drops first.
    pub fn render(&self) -> String {
        let mut out = format!(
            "stdlib frontier coverage: receipt {}/{} accepted, now {}/{} accepted\n",
            self.receipt_accepted,
            self.receipt_modules,
            self.current_accepted,
            self.current_modules
        );
        for module in &self.lost {
            out.push_str(&format!(
                "DROP lost module: {module} is in the receipt and not in this run\n"
            ));
        }
        for (module, verdict, detail) in &self.no_longer_accepted {
            out.push_str(&format!(
                "DROP no longer accepted: {module} is {verdict} ({detail})\n"
            ));
        }
        for (module, before, after) in &self.count_changed {
            out.push_str(&format!(
                "DROP declaration count changed: {module} {before} -> {after}\n"
            ));
        }
        for (module, before) in &self.newly_accepted {
            out.push_str(&format!(
                "IMPROVEMENT newly accepted: {module} (was {before})\n"
            ));
        }
        for (module, verdict) in &self.added {
            out.push_str(&format!("IMPROVEMENT added module: {module} ({verdict})\n"));
        }
        let shown = |(verdict, by): &(String, Option<String>)| match by {
            Some(by) => format!("{verdict} by {by}"),
            None => verdict.clone(),
        };
        for (module, before, now) in &self.changed {
            out.push_str(&format!(
                "CHANGED non-acceptance (no coverage moved): {module} {} -> {}\n",
                shown(before),
                shown(now)
            ));
        }
        out.push_str(if self.dropped() {
            "verdict: COVERAGE DROPPED\n"
        } else if self.improved() {
            "verdict: no coverage drop; coverage improved\n"
        } else {
            "verdict: no coverage drop\n"
        });
        out
    }
}

/// Compare a fresh frontier with the retained receipt.
pub fn compare(receipt: &Frontier, current: &Frontier) -> CoverageComparison {
    let now: BTreeMap<&str, &FrontierRow> = current
        .rows
        .iter()
        .map(|row| (row.module.as_str(), row))
        .collect();
    let before: BTreeSet<&str> = receipt.rows.iter().map(|row| row.module.as_str()).collect();
    let mut comparison = CoverageComparison {
        receipt_accepted: receipt
            .rows
            .iter()
            .filter(|row| row.verdict == "accepted")
            .count(),
        current_accepted: current
            .rows
            .iter()
            .filter(|row| row.verdict == "accepted")
            .count(),
        receipt_modules: receipt.rows.len(),
        current_modules: current.rows.len(),
        ..CoverageComparison::default()
    };
    for old in &receipt.rows {
        let Some(new) = now.get(old.module.as_str()) else {
            comparison.lost.push(old.module.clone());
            continue;
        };
        match (old.verdict == "accepted", new.verdict == "accepted") {
            (true, false) => comparison.no_longer_accepted.push((
                old.module.clone(),
                new.verdict.clone(),
                new.detail.clone(),
            )),
            (true, true) if old.declarations != new.declarations => comparison
                .count_changed
                .push((old.module.clone(), old.declarations, new.declarations)),
            (false, true) => comparison
                .newly_accepted
                .push((old.module.clone(), old.verdict.clone())),
            (false, false) if old.verdict != new.verdict || old.blocked_by != new.blocked_by => {
                comparison.changed.push((
                    old.module.clone(),
                    (old.verdict.clone(), old.blocked_by.clone()),
                    (new.verdict.clone(), new.blocked_by.clone()),
                ));
            }
            _ => {}
        }
    }
    for row in &current.rows {
        if !before.contains(row.module.as_str()) {
            comparison
                .added
                .push((row.module.clone(), row.verdict.clone()));
        }
    }
    comparison
}

/// Parse and validate one frontier document.
pub fn parse(text: &str) -> Result<Frontier, FrontierError> {
    if text.len() > MAX_BYTES {
        return Err(FrontierError::Shape(format!(
            "{} bytes is over the {MAX_BYTES}-byte reader bound",
            text.len()
        )));
    }
    let mut reader = Reader {
        bytes: text.as_bytes(),
        at: 0,
    };
    reader.skip_ws();
    let value = reader.value(0)?;
    reader.skip_ws();
    if reader.at != reader.bytes.len() {
        return Err(reader.error("trailing bytes after the document"));
    }
    let top = object(&value, "the document")?;
    let schema = string(top, "schema")?;
    if schema != FRONTIER_SCHEMA {
        return Err(FrontierError::Shape(format!(
            "schema is {schema:?}, not {FRONTIER_SCHEMA:?}"
        )));
    }
    let outcome = string(top, "outcome")?.to_owned();
    let authority = match field(top, "authority")? {
        Value::Bool(value) => *value,
        _ => {
            return Err(FrontierError::Shape(
                "authority is not a boolean".to_owned(),
            ));
        }
    };
    let Value::Array(items) = field(top, "rows")? else {
        return Err(FrontierError::Shape("rows is not an array".to_owned()));
    };
    let mut rows = Vec::with_capacity(items.len());
    let mut names = BTreeSet::new();
    let mut tally: BTreeMap<String, u64> = BTreeMap::new();
    let mut declarations = 0u64;
    for (index, item) in items.iter().enumerate() {
        let row = object(item, &format!("row {index}"))?;
        let verdict = string(row, "verdict")?.to_owned();
        if !matches!(
            verdict.as_str(),
            "accepted" | "failed" | "inconclusive" | "internal-fault" | "blocked"
        ) {
            return Err(FrontierError::Shape(format!(
                "row {index} has the unknown verdict {verdict:?}"
            )));
        }
        let module = string(row, "module")?.to_owned();
        if !names.insert(module.clone()) {
            return Err(FrontierError::Inconsistent(format!(
                "module {module} has two rows"
            )));
        }
        let count = number(row, "declarations")?;
        if verdict == "accepted" {
            declarations = declarations.saturating_add(count);
        }
        *tally.entry(verdict.clone()).or_default() += 1;
        rows.push(FrontierRow {
            module,
            verdict,
            declarations: count,
            detail: string(row, "detail")?.to_owned(),
            blocked_by: match field(row, "blockedBy")? {
                Value::Null => None,
                Value::String(module) => Some(module.clone()),
                _ => {
                    return Err(FrontierError::Shape(format!(
                        "row {index} has a blockedBy that is neither null nor a string"
                    )));
                }
            },
        });
    }
    let summary = [
        ("modules", rows.len() as u64),
        ("accepted", tally.get("accepted").copied().unwrap_or(0)),
        ("failed", tally.get("failed").copied().unwrap_or(0)),
        (
            "inconclusive",
            tally.get("inconclusive").copied().unwrap_or(0),
        ),
        (
            "internalFault",
            tally.get("internal-fault").copied().unwrap_or(0),
        ),
        ("blocked", tally.get("blocked").copied().unwrap_or(0)),
        ("acceptedDeclarations", declarations),
    ];
    for (key, measured) in summary {
        let stated = number(top, key)?;
        if stated != measured {
            return Err(FrontierError::Inconsistent(format!(
                "{key} says {stated}, the rows give {measured}"
            )));
        }
    }
    if rows.is_empty() {
        return Err(FrontierError::Inconsistent(
            "no rows: an empty frontier is a broken run, not a clean one".to_owned(),
        ));
    }
    Ok(Frontier {
        outcome,
        authority,
        rows,
        accepted_declarations: declarations,
    })
}

impl Frontier {
    /// Render this frontier in the document form [`parse`] reads, recomputing every
    /// summary count from the rows. Synthetic variants for tests are built this way, so
    /// a planted drop is a consistent document and is caught by the comparison, not by
    /// the consistency check.
    pub fn to_json(&self) -> String {
        let count = |verdict: &str| {
            self.rows
                .iter()
                .filter(|row| row.verdict == verdict)
                .count()
        };
        let declarations: u64 = self
            .rows
            .iter()
            .filter(|row| row.verdict == "accepted")
            .map(|row| row.declarations)
            .sum();
        let rows = self
            .rows
            .iter()
            .map(|row| {
                format!(
                    "{{\"module\":{},\"verdict\":{},\"declarations\":{},\"elapsedMs\":0,\"detail\":{},\"detailTruncated\":false,\"blockedBy\":{}}}",
                    quote(&row.module),
                    quote(&row.verdict),
                    row.declarations,
                    quote(&row.detail),
                    row.blocked_by.as_deref().map_or_else(|| "null".to_owned(), quote)
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "{{\"schema\":{},\"outcome\":{},\"authority\":{},\"trust\":\"recheck\",\"modules\":{},\"accepted\":{},\"failed\":{},\"inconclusive\":{},\"internalFault\":{},\"blocked\":{},\"acceptedDeclarations\":{},\"rows\":[{}]}}\n",
            quote(FRONTIER_SCHEMA),
            quote(&self.outcome),
            self.authority,
            self.rows.len(),
            count("accepted"),
            count("failed"),
            count("inconclusive"),
            count("internal-fault"),
            count("blocked"),
            declarations,
            rows
        )
    }
}

fn quote(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ---------------------------------------------------------------------------
// A small strict JSON reader: objects refuse duplicate keys, numbers must be
// non-negative integers, nesting is bounded.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value {
    Null,
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<Value>),
    Object(Vec<(String, Value)>),
}

fn object<'a>(value: &'a Value, what: &str) -> Result<&'a [(String, Value)], FrontierError> {
    match value {
        Value::Object(fields) => Ok(fields),
        _ => Err(FrontierError::Shape(format!("{what} is not an object"))),
    }
}

fn field<'a>(fields: &'a [(String, Value)], key: &str) -> Result<&'a Value, FrontierError> {
    fields
        .iter()
        .find(|(name, _)| name == key)
        .map(|(_, value)| value)
        .ok_or_else(|| FrontierError::Shape(format!("missing field {key:?}")))
}

fn string<'a>(fields: &'a [(String, Value)], key: &str) -> Result<&'a str, FrontierError> {
    match field(fields, key)? {
        Value::String(text) => Ok(text),
        _ => Err(FrontierError::Shape(format!("{key:?} is not a string"))),
    }
}

fn number(fields: &[(String, Value)], key: &str) -> Result<u64, FrontierError> {
    match field(fields, key)? {
        Value::Number(value) => Ok(*value),
        _ => Err(FrontierError::Shape(format!(
            "{key:?} is not a non-negative integer"
        ))),
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn error(&self, reason: &'static str) -> FrontierError {
        FrontierError::Syntax {
            at: self.at,
            reason,
        }
    }

    fn skip_ws(&mut self) {
        while matches!(self.bytes.get(self.at), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.at += 1;
        }
    }

    fn literal(&mut self, word: &'static [u8], value: Value) -> Result<Value, FrontierError> {
        if self.bytes.get(self.at..self.at + word.len()) == Some(word) {
            self.at += word.len();
            Ok(value)
        } else {
            Err(self.error("unknown literal"))
        }
    }

    fn value(&mut self, depth: usize) -> Result<Value, FrontierError> {
        if depth > MAX_DEPTH {
            return Err(self.error("nested too deeply for a frontier document"));
        }
        match self.bytes.get(self.at) {
            Some(b'{') => self.object(depth),
            Some(b'[') => self.array(depth),
            Some(b'"') => self.string().map(Value::String),
            Some(b't') => self.literal(b"true", Value::Bool(true)),
            Some(b'f') => self.literal(b"false", Value::Bool(false)),
            Some(b'n') => self.literal(b"null", Value::Null),
            Some(b'0'..=b'9') => self.number(),
            Some(_) => Err(self.error("unexpected byte")),
            None => Err(self.error("unexpected end of input")),
        }
    }

    fn number(&mut self) -> Result<Value, FrontierError> {
        let start = self.at;
        while matches!(self.bytes.get(self.at), Some(b'0'..=b'9')) {
            self.at += 1;
        }
        if matches!(self.bytes.get(self.at), Some(b'.' | b'e' | b'E')) {
            return Err(self.error("only non-negative integers are expected"));
        }
        let digits = self
            .bytes
            .get(start..self.at)
            .and_then(|digits| std::str::from_utf8(digits).ok())
            .ok_or_else(|| self.error("number is not ASCII"))?;
        if digits.len() > 1 && digits.starts_with('0') {
            return Err(self.error("leading zero"));
        }
        digits
            .parse::<u64>()
            .map(Value::Number)
            .map_err(|_| self.error("integer out of range"))
    }

    fn string(&mut self) -> Result<String, FrontierError> {
        self.at += 1;
        let mut out = String::new();
        loop {
            let Some(&byte) = self.bytes.get(self.at) else {
                return Err(self.error("unterminated string"));
            };
            match byte {
                b'"' => {
                    self.at += 1;
                    return Ok(out);
                }
                b'\\' => {
                    self.at += 1;
                    let Some(&escape) = self.bytes.get(self.at) else {
                        return Err(self.error("unterminated escape"));
                    };
                    self.at += 1;
                    match escape {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let high = self.hex4()?;
                            let ch = if (0xD800..0xDC00).contains(&high) {
                                if self.bytes.get(self.at..self.at + 2) != Some(b"\\u") {
                                    return Err(self.error("lone high surrogate"));
                                }
                                self.at += 2;
                                let low = self.hex4()?;
                                if !(0xDC00..0xE000).contains(&low) {
                                    return Err(self.error("bad low surrogate"));
                                }
                                char::from_u32(0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00))
                            } else {
                                char::from_u32(high)
                            };
                            out.push(ch.ok_or_else(|| self.error("invalid code point"))?);
                        }
                        _ => return Err(self.error("unknown escape")),
                    }
                }
                0x00..=0x1f => return Err(self.error("control byte in string")),
                _ => {
                    let width = match byte {
                        0x00..=0x7f => 1,
                        0xc0..=0xdf => 2,
                        0xe0..=0xef => 3,
                        0xf0..=0xf7 => 4,
                        _ => return Err(self.error("string is not UTF-8")),
                    };
                    let ch = self
                        .bytes
                        .get(self.at..self.at + width)
                        .and_then(|bytes| std::str::from_utf8(bytes).ok())
                        .and_then(|text| text.chars().next())
                        .ok_or_else(|| self.error("string is not UTF-8"))?;
                    out.push(ch);
                    self.at += ch.len_utf8();
                }
            }
        }
    }

    fn hex4(&mut self) -> Result<u32, FrontierError> {
        let digits = self
            .bytes
            .get(self.at..self.at + 4)
            .and_then(|digits| std::str::from_utf8(digits).ok())
            .ok_or_else(|| self.error("short \\u escape"))?;
        let value = u32::from_str_radix(digits, 16).map_err(|_| self.error("bad \\u escape"))?;
        self.at += 4;
        Ok(value)
    }

    fn array(&mut self, depth: usize) -> Result<Value, FrontierError> {
        self.at += 1;
        let mut items = Vec::new();
        self.skip_ws();
        if self.bytes.get(self.at) == Some(&b']') {
            self.at += 1;
            return Ok(Value::Array(items));
        }
        loop {
            self.skip_ws();
            items.push(self.value(depth + 1)?);
            self.skip_ws();
            match self.bytes.get(self.at) {
                Some(b',') => self.at += 1,
                Some(b']') => {
                    self.at += 1;
                    return Ok(Value::Array(items));
                }
                _ => return Err(self.error("expected , or ] in array")),
            }
        }
    }

    fn object(&mut self, depth: usize) -> Result<Value, FrontierError> {
        self.at += 1;
        let mut fields: Vec<(String, Value)> = Vec::new();
        self.skip_ws();
        if self.bytes.get(self.at) == Some(&b'}') {
            self.at += 1;
            return Ok(Value::Object(fields));
        }
        loop {
            self.skip_ws();
            if self.bytes.get(self.at) != Some(&b'"') {
                return Err(self.error("expected a key"));
            }
            let key = self.string()?;
            if fields.iter().any(|(name, _)| *name == key) {
                return Err(self.error("duplicate key"));
            }
            self.skip_ws();
            if self.bytes.get(self.at) != Some(&b':') {
                return Err(self.error("expected :"));
            }
            self.at += 1;
            self.skip_ws();
            let value = self.value(depth + 1)?;
            fields.push((key, value));
            self.skip_ws();
            match self.bytes.get(self.at) {
                Some(b',') => self.at += 1,
                Some(b'}') => {
                    self.at += 1;
                    return Ok(Value::Object(fields));
                }
                _ => return Err(self.error("expected , or } in object")),
            }
        }
    }
}
