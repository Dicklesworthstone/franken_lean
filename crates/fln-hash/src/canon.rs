//! Canonical serialization (bead franken_lean-rps, requirements b/c).
//!
//! One versioned schema per durable value shape; exactly one valid byte encoding per
//! value (no encoder freedom: fixed-width little-endian integers, u64 length prefixes,
//! u8 enum tags in declaration order). The semantic-hash / byte-hash distinction of
//! plan §7.3 is structural here: a *semantic* digest is a domain hash over THIS
//! canonical encoding, while a *byte* digest covers whatever artifact bytes exist on
//! disk — re-encoding or compression can change the latter without pretending to
//! change the former.
//!
//! Decoding is total over arbitrary bytes: every failure is a typed [`CanonError`],
//! never a panic (D8 taxonomy).

use fln_core::diag::{Diagnostic, ErrorValue, ResourceReason, Severity, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_core::pos::Position;

/// A frozen schema identity: name + version. Bumping the version is the only legal
/// way to change an encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemaId {
    pub name: &'static str,
    pub version: u16,
}

pub const SCHEMA_NAME: SchemaId = SchemaId {
    name: "fln.canon.name",
    version: 1,
};
pub const SCHEMA_LEVEL: SchemaId = SchemaId {
    name: "fln.canon.level",
    version: 1,
};
pub const SCHEMA_EXPR: SchemaId = SchemaId {
    name: "fln.canon.expr",
    version: 1,
};
pub const SCHEMA_KVMAP: SchemaId = SchemaId {
    name: "fln.canon.kvmap",
    version: 1,
};
/// The order-independent projection of a `KVMap` — a *set* view, distinct from the
/// ordered encoding above. See [`kvmap_canonical_set_bytes`].
pub const SCHEMA_KVMAP_SET: SchemaId = SchemaId {
    name: "fln.canon.kvmap-set",
    version: 1,
};
/// Durable snapshot of one generic shadow-run promotion cell.
pub const SCHEMA_SHADOW_CELL: SchemaId = SchemaId {
    name: "fln.canon.shadow-cell",
    version: 1,
};
/// Canonical semantic NDJSON projection of a shadow publication.
pub const SCHEMA_SHADOW_SEMANTIC_NDJSON: SchemaId = SchemaId {
    name: "fln.canon.shadow-semantic-ndjson",
    version: 1,
};
/// Canonical operational NDJSON projection carried beside, never inside, semantic
/// shadow authority.
pub const SCHEMA_SHADOW_TELEMETRY_NDJSON: SchemaId = SchemaId {
    name: "fln.canon.shadow-telemetry-ndjson",
    version: 1,
};

/// The crate that defines a durable format's codec.
///
/// Formats live in the crate that encodes them — the registry does not centralize the
/// *codecs*, only the *identities*. That is forced by the crate map (§21): dependency
/// edges point strictly downward and fln-hash sits below fln-env and fln-verdict, so
/// this crate cannot import their constants even to compare them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SchemaOwner {
    /// `fln-hash` — the term plane and the diagnostic taxonomy (this module).
    Hash,
    /// `fln-env` — Grimoire's module and provenance identities.
    Env,
    /// `fln-verdict` — the CNF / model / proof wire formats.
    Verdict,
}

impl SchemaOwner {
    pub const fn crate_name(self) -> &'static str {
        match self {
            SchemaOwner::Hash => "fln-hash",
            SchemaOwner::Env => "fln-env",
            SchemaOwner::Verdict => "fln-verdict",
        }
    }

    /// The source file whose `SchemaId` constants define this owner's formats. This is
    /// the join target: the registry is checked against these files in both directions,
    /// so a format cannot be added, moved, or version-bumped without the registry
    /// agreeing.
    pub const fn declaration_file(self) -> &'static str {
        match self {
            SchemaOwner::Hash => "crates/fln-hash/src/canon.rs",
            SchemaOwner::Env => "crates/fln-env/src/provenance.rs",
            SchemaOwner::Verdict => "crates/fln-verdict/src/lib.rs",
        }
    }

    pub const ALL: [SchemaOwner; 3] = [SchemaOwner::Hash, SchemaOwner::Env, SchemaOwner::Verdict];
}

/// One durable format of the program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SchemaRow {
    pub id: SchemaId,
    pub owner: SchemaOwner,
    /// What the format serializes — the reviewable half of the row.
    pub covers: &'static str,
}

/// **The registry of every durable format in the program** (bead franken_lean-rps
/// requirement b; plan §7.3 and Appendix B: "every durable format specified once").
///
/// Before this existed, three crates declared `SchemaId` constants independently and
/// nothing joined them: two formats could claim one name, a version could move on one
/// side of a codec, or a format could be introduced with no published identity, and no
/// artifact would disagree. Prose in a module header cannot be joined against a
/// decoder; a table can.
///
/// The rows are checked, not asserted:
/// * names are unique and shaped `fln.<subsystem>.<format>`, lowercase (`schema_names_
///   are_unique_and_well_shaped`);
/// * fln-hash's own rows are joined against the real constants at compile time, so this
///   table and the codec cannot drift (`registry_rows_match_the_constants_they_name`);
/// * every owner's declaration file is scanned and joined **in both directions** — an
///   unregistered format and a row whose codec has vanished both fail
///   (`tests/schema_registry.rs`).
///
/// Adding a durable format means adding a row here. That is the point: the registry is
/// the reviewed inventory the conformance corpus is meant to be a projection of.
pub const SCHEMA_REGISTRY: [SchemaRow; 14] = [
    SchemaRow {
        id: SCHEMA_NAME,
        owner: SchemaOwner::Hash,
        covers: "a hierarchical Lean name (string/numeric components)",
    },
    SchemaRow {
        id: SCHEMA_LEVEL,
        owner: SchemaOwner::Hash,
        covers: "a universe level term",
    },
    SchemaRow {
        id: SCHEMA_EXPR,
        owner: SchemaOwner::Hash,
        covers: "a term-plane expression",
    },
    SchemaRow {
        id: SCHEMA_KVMAP,
        owner: SchemaOwner::Hash,
        covers: "an options / key-value map, insertion order significant",
    },
    SchemaRow {
        id: SCHEMA_KVMAP_SET,
        owner: SchemaOwner::Hash,
        covers: "the same map as an order-independent set (logical-root input)",
    },
    SchemaRow {
        id: SCHEMA_DIAG,
        owner: SchemaOwner::Hash,
        covers: "a diagnostic under the D8 typed error taxonomy",
    },
    SchemaRow {
        id: SCHEMA_SHADOW_CELL,
        owner: SchemaOwner::Hash,
        covers: "one versioned generic shadow-run promotion authority cell",
    },
    SchemaRow {
        id: SCHEMA_SHADOW_SEMANTIC_NDJSON,
        owner: SchemaOwner::Hash,
        covers: "the canonical semantic NDJSON projection of a shadow publication",
    },
    SchemaRow {
        id: SCHEMA_SHADOW_TELEMETRY_NDJSON,
        owner: SchemaOwner::Hash,
        covers: "the separate canonical operational NDJSON projection of a shadow publication",
    },
    SchemaRow {
        id: SchemaId {
            name: "fln.env.module-provenance",
            version: 1,
        },
        owner: SchemaOwner::Env,
        covers: "the module topology + contribution provenance manifest",
    },
    SchemaRow {
        id: SchemaId {
            name: "fln.env.module-provenance.entry-id",
            version: 1,
        },
        owner: SchemaOwner::Env,
        covers: "content identity of one extension journal entry",
    },
    SchemaRow {
        id: SchemaId {
            name: "fln.verdict.cnf",
            version: 1,
        },
        owner: SchemaOwner::Verdict,
        covers: "a CNF formula on the wire",
    },
    SchemaRow {
        id: SchemaId {
            name: "fln.verdict.sat-model",
            version: 1,
        },
        owner: SchemaOwner::Verdict,
        covers: "a satisfying assignment on the wire",
    },
    SchemaRow {
        id: SchemaId {
            name: "fln.verdict.unsat-proof",
            version: 1,
        },
        owner: SchemaOwner::Verdict,
        covers: "an unsatisfiability proof on the wire",
    },
];

/// The registry row for a schema, if it is registered.
pub fn registered(name: &str) -> Option<&'static SchemaRow> {
    SCHEMA_REGISTRY.iter().find(|row| row.id.name == name)
}

/// Typed decode failure. `at` is the byte offset of the failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonError {
    pub at: usize,
    pub what: &'static str,
}

impl std::fmt::Display for CanonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "canonical decode failed at byte {}: {}",
            self.at, self.what
        )
    }
}

/// Canonical byte writer.
#[derive(Debug, Default)]
pub struct CanonWriter {
    buf: Vec<u8>,
}

impl CanonWriter {
    pub fn new() -> CanonWriter {
        CanonWriter::default()
    }

    pub fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    pub fn u8(&mut self, v: u8) {
        self.buf.push(v);
    }

    pub fn u16(&mut self, v: u16) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn u32(&mut self, v: u32) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn u64(&mut self, v: u64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn i64(&mut self, v: i64) {
        self.buf.extend_from_slice(&v.to_le_bytes());
    }

    pub fn bool(&mut self, v: bool) {
        self.buf.push(u8::from(v));
    }

    /// Length-prefixed bytes (u64 LE length).
    pub fn bytes(&mut self, v: &[u8]) {
        self.u64(v.len() as u64);
        self.buf.extend_from_slice(v);
    }

    pub fn str(&mut self, v: &str) {
        self.bytes(v.as_bytes());
    }

    /// The schema header every top-level encoding starts with.
    pub fn schema(&mut self, id: SchemaId) {
        self.str(id.name);
        self.u16(id.version);
    }
}

/// Which caller-supplied limit stopped a decode (bead fln-4zk8).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetLimit {
    /// Bytes consumed from the input.
    InputBytes,
    /// Values built from it — `Expr` and `Level` nodes, `Name` components, `KVMap`
    /// entries. Deliberately a count of *work*, not of nesting: a depth cap would
    /// refuse legitimately deep terms, which is exactly what the decoder contract
    /// forbids (bead franken_lean-fnj).
    ProducedNodes,
}

/// The limits a caller is willing to spend on one decode.
///
/// Caller-supplied and passed by value into the decode call — not a global, not a
/// compile-time constant, and not a property of the artifact. Two callers with
/// different appetites decode the same bytes under different budgets in the same
/// process, and neither can change the other's.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecodeBudget {
    max_input_bytes: u64,
    max_produced_nodes: u64,
}

impl DecodeBudget {
    pub const fn new(max_input_bytes: u64, max_produced_nodes: u64) -> DecodeBudget {
        DecodeBudget {
            max_input_bytes,
            max_produced_nodes,
        }
    }

    /// The budget the unbudgeted entry point runs under, so that
    /// [`Canonical::from_canonical_bytes`] and
    /// [`Canonical::from_canonical_bytes_budgeted`] are the same code path.
    pub const fn unlimited() -> DecodeBudget {
        DecodeBudget::new(u64::MAX, u64::MAX)
    }

    pub const fn max_input_bytes(self) -> u64 {
        self.max_input_bytes
    }

    pub const fn max_produced_nodes(self) -> u64 {
        self.max_produced_nodes
    }
}

/// A decode that stopped because the caller's budget ran out.
///
/// It records which limit fired, what the caller allowed, and what had been spent
/// when the meter tripped — enough to raise the budget and retry deliberately
/// rather than by guesswork.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Exhausted {
    pub limit: BudgetLimit,
    pub allowed: u64,
    pub observed: u64,
    /// Byte offset the decode had reached.
    pub at: usize,
}

/// The outcome of a budgeted decode: `Outcome<Result<T, CanonError>>` (bead fln-8gz3).
///
/// This replaces the hand-rolled three-valued `Decoded` enum that lived here. The shape
/// is the same three claims, said in the program's one vocabulary
/// ([`fln_core::outcome`]) instead of a fourth private lattice:
///
/// | was | is | why |
/// |---|---|---|
/// | `Value(v)` | `Complete(Ok(v))` | ran to completion, domain answer is "these bytes are this value" |
/// | `Malformed(e)` | `Complete(Err(e))` | ran to completion; "not a well-formed artifact" is a real verdict ABOUT the bytes, so it belongs inside the authoritative arm |
/// | `Inconclusive(Exhausted)` | `Inconclusive(ResourceExhausted{..})` | did not complete; nothing was learned |
///
/// The property the old type was protecting is preserved and now enforced further out:
/// `Outcome` has no `From<Outcome<T>> for Result<T, E>`, no `Option` accessor and no
/// `unwrap_or`, so a caller still cannot `?` a resource stop into a rejection. What it
/// gains is a fourth claim the old enum could not make — see
/// [`Canonical::from_canonical_bytes_budgeted`] on the accounting fault.
pub type DecodeOutcome<T> = Outcome<Result<T, CanonError>>;

impl Exhausted {
    /// The structural unit this stop bounded.
    ///
    /// Total and injective, and asserted so in
    /// `every_decode_budget_limit_maps_to_exactly_one_structural_unit`: two limits must
    /// never collapse onto one unit, or a caller cannot tell which allowance to raise.
    pub const fn unit(self) -> StructuralUnit {
        match self.limit {
            BudgetLimit::InputBytes => StructuralUnit::InputBytes,
            BudgetLimit::ProducedNodes => StructuralUnit::ProducedNodes,
        }
    }

    /// This stop as the program's typed non-answer (bead franken_lean-vui8's axis).
    ///
    /// `allowed`/`observed` become the [`ResourceUsage`] a caller sizes a retry from, and
    /// `at` — which has no field in `ResourceUsage`, deliberately — is recorded through
    /// `with_progress`, where it is diagnostic only and cannot be mistaken for a budget.
    ///
    /// This is the reusable half for any adopter with a structural budget: build a
    /// `ResourceUsage` naming the unit, put the numbers in it, and localize with
    /// `with_progress`. The term store (bead fln-49c) wants the same shape with
    /// [`StructuralUnit::ExpandedWeight`].
    pub fn into_inconclusive(self) -> Inconclusive {
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit: self.unit() },
            allowed: self.allowed,
            observed: self.observed,
        })
        .with_progress(format!("byte {}", self.at))
    }
}

/// Canonical byte reader.
#[derive(Debug)]
pub struct CanonReader<'a> {
    bytes: &'a [u8],
    at: usize,
    budget: DecodeBudget,
    produced_nodes: u64,
    /// Set by the first trip, and never cleared: once the meter has fired, the rest
    /// of this decode is unwinding, and whatever `CanonError` surfaces from that
    /// unwinding describes the stop, not the bytes.
    exhausted: Option<Exhausted>,
}

impl<'a> CanonReader<'a> {
    pub fn new(bytes: &'a [u8]) -> CanonReader<'a> {
        CanonReader::with_budget(bytes, DecodeBudget::unlimited())
    }

    pub fn with_budget(bytes: &'a [u8], budget: DecodeBudget) -> CanonReader<'a> {
        CanonReader {
            bytes,
            at: 0,
            budget,
            produced_nodes: 0,
            exhausted: None,
        }
    }

    /// The stop record, if this reader's budget ran out.
    pub fn exhausted(&self) -> Option<Exhausted> {
        self.exhausted
    }

    fn err(&self, what: &'static str) -> CanonError {
        CanonError { at: self.at, what }
    }

    /// Record the first trip and return the sentinel that unwinds the decode. The
    /// caller-facing outcome is decided from [`CanonReader::exhausted`], never from
    /// this error — it exists only to stop the readers through the same `?` path
    /// they already use, without threading a second error type through every
    /// signature.
    fn trip(&mut self, limit: BudgetLimit, allowed: u64, observed: u64) -> CanonError {
        if self.exhausted.is_none() {
            self.exhausted = Some(Exhausted {
                limit,
                allowed,
                observed,
                at: self.at,
            });
        }
        self.err("decode budget exhausted")
    }

    /// Charge one produced value against the budget. Called where values are built,
    /// so the count is work actually done rather than bytes that might be skipped.
    pub(crate) fn charge_node(&mut self) -> Result<(), CanonError> {
        // Saturating rather than `+ 1`: reaching `u64::MAX` nodes would need more
        // input bytes than an address space holds, but a counter that can only
        // saturate cannot overflow into a wrap on any build profile.
        let produced = self.produced_nodes.saturating_add(1);
        if produced > self.budget.max_produced_nodes {
            return Err(self.trip(
                BudgetLimit::ProducedNodes,
                self.budget.max_produced_nodes,
                produced,
            ));
        }
        self.produced_nodes = produced;
        Ok(())
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], CanonError> {
        let end = self
            .at
            .checked_add(n)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| self.err("input truncated"))?;
        // Charged on consumption, not on the artifact's total size: bytes never read
        // are never spent, so a malformed prefix under a small budget still gets its
        // rejection instead of being reported as "too expensive to judge".
        if end as u64 > self.budget.max_input_bytes {
            return Err(self.trip(
                BudgetLimit::InputBytes,
                self.budget.max_input_bytes,
                end as u64,
            ));
        }
        let slice = &self.bytes[self.at..end];
        self.at = end;
        Ok(slice)
    }

    pub fn u8(&mut self) -> Result<u8, CanonError> {
        Ok(self.take(1)?[0])
    }

    pub fn u16(&mut self) -> Result<u16, CanonError> {
        Ok(u16::from_le_bytes(self.take(2)?.try_into().expect("len 2")))
    }

    pub fn u32(&mut self) -> Result<u32, CanonError> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().expect("len 4")))
    }

    pub fn u64(&mut self) -> Result<u64, CanonError> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().expect("len 8")))
    }

    pub fn i64(&mut self) -> Result<i64, CanonError> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().expect("len 8")))
    }

    pub fn bool(&mut self) -> Result<bool, CanonError> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(self.err("non-canonical bool")),
        }
    }

    pub fn bytes(&mut self) -> Result<&'a [u8], CanonError> {
        let len = self.u64()?;
        let len = usize::try_from(len).map_err(|_| self.err("length exceeds address space"))?;
        self.take(len)
    }

    pub fn str(&mut self) -> Result<&'a str, CanonError> {
        let raw = self.bytes()?;
        std::str::from_utf8(raw).map_err(|_| self.err("invalid UTF-8"))
    }

    pub fn expect_schema(&mut self, id: SchemaId) -> Result<(), CanonError> {
        let name = self.str()?;
        if name != id.name {
            return Err(self.err("schema name mismatch"));
        }
        let version = self.u16()?;
        if version != id.version {
            return Err(self.err("schema version mismatch"));
        }
        Ok(())
    }

    /// Decoding must consume every byte — trailing garbage is non-canonical.
    pub fn finish(self) -> Result<(), CanonError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(self.err("trailing bytes after value"))
        }
    }
}

/// A value with exactly one canonical encoding under a frozen schema.
pub trait Canonical: Sized {
    const SCHEMA: SchemaId;

    fn write_body(&self, w: &mut CanonWriter);
    fn read_body(r: &mut CanonReader<'_>) -> Result<Self, CanonError>;

    /// Schema-headed encoding of one top-level value.
    fn to_canonical_bytes(&self) -> Vec<u8> {
        let mut w = CanonWriter::new();
        w.schema(Self::SCHEMA);
        self.write_body(&mut w);
        w.into_bytes()
    }

    /// Total inverse of [`Canonical::to_canonical_bytes`].
    ///
    /// Runs under [`DecodeBudget::unlimited`], so it is two-valued by construction:
    /// an unlimited budget cannot trip, and this signature therefore never has to
    /// represent an inconclusive outcome. Callers decoding untrusted artifacts under
    /// a resource contract want [`Canonical::from_canonical_bytes_budgeted`].
    fn from_canonical_bytes(bytes: &[u8]) -> Result<Self, CanonError> {
        match Self::from_canonical_bytes_budgeted(bytes, DecodeBudget::unlimited()) {
            Outcome::Complete(result) => result,
            // Both non-answers are unreachable under an unlimited budget: nothing can
            // trip, so no stop can be recorded and no accounting fault can be detected.
            // A panic is the right encoding rather than a lie: this signature cannot
            // carry a non-answer, and reaching here would mean an invariant broke, which
            // is never a user diagnostic (FL-INV-07). Budgeted callers get the typed
            // outcome instead.
            Outcome::Inconclusive(inconclusive) => unreachable!(
                "an unlimited budget cannot be exhausted, yet a stop was reported: {:?}",
                inconclusive.cause
            ),
            Outcome::InternalFault(fault) => unreachable!(
                "an unlimited budget cannot record a stop, so no accounting fault is \
                 possible, yet one was reported: {fault:?}"
            ),
        }
    }

    /// Decode under a caller-supplied budget (bead fln-4zk8).
    ///
    /// Exhaustion is reported as [`Outcome::Inconclusive`] and is never rendered as
    /// acceptance or rejection: the meter is consulted *before* the error that
    /// unwound the decode is interpreted, so a stop can never be mistaken for a
    /// well-formedness verdict about the bytes (FL-INV-07). Decoding an artifact
    /// that fits inside the budget is byte-for-byte the same computation as the
    /// unbudgeted call.
    ///
    /// **Budget and malformedness are not conflated, and the fold is what made that
    /// checkable rather than argued.** A trip records itself in the reader and returns a
    /// sentinel error purely to unwind through the `?` path the readers already use, so
    /// every failure arrives through one channel and is separated afterwards by consulting
    /// the meter. That separation was correct but rested on a *non-local* property — that
    /// no reader anywhere swallows an error — and the old three-arm enum had no way to say
    /// otherwise: with a stop recorded and a successful parse it could only return
    /// `Value`, silently accepting an over-budget decode. There is no such swallow today
    /// (checked, not assumed: every read path uses `?`), which is exactly why the case
    /// deserves a typed refusal rather than a comment. `Outcome::InternalFault` is that
    /// refusal — our accounting contradicting itself is an invariant failure, not a
    /// verdict about anyone's bytes, and it is never cacheable.
    fn from_canonical_bytes_budgeted(bytes: &[u8], budget: DecodeBudget) -> DecodeOutcome<Self> {
        let mut r = CanonReader::with_budget(bytes, budget);
        // Every step is checked the same way: if the meter tripped, the outcome is
        // inconclusive regardless of which error surfaced.
        macro_rules! step {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => {
                        return match r.exhausted() {
                            Some(exhausted) => Outcome::Inconclusive(exhausted.into_inconclusive()),
                            // A completed run whose domain answer is "not a well-formed
                            // artifact" — a real verdict about the bytes, so it belongs
                            // inside the authoritative arm.
                            None => Outcome::Complete(Err(error)),
                        };
                    }
                }
            };
        }
        step!(r.expect_schema(Self::SCHEMA));
        let value = step!(Self::read_body(&mut r));
        // `finish` consumes the reader and reads nothing, so it cannot trip the
        // meter; the stop record is captured first and stays authoritative.
        let exhausted = r.exhausted();
        match r.finish() {
            Ok(()) => match exhausted {
                None => Outcome::Complete(Ok(value)),
                // Parsed cleanly *and* a stop was recorded. Unreachable while no reader
                // swallows a trip, and refused rather than trusted precisely because that
                // premise lives in every reader rather than here.
                Some(exhausted) => Outcome::InternalFault(
                    InternalFault::new(
                        "FL-INV-07",
                        format!(
                            "decode completed while a {} budget stop was recorded at byte {}: \
                             allowed={}, observed={}",
                            exhausted.unit().as_str(),
                            exhausted.at,
                            exhausted.allowed,
                            exhausted.observed
                        ),
                    )
                    .with_evidence("fln_hash::canon::from_canonical_bytes_budgeted"),
                ),
            },
            Err(error) => match exhausted {
                Some(exhausted) => Outcome::Inconclusive(exhausted.into_inconclusive()),
                None => Outcome::Complete(Err(error)),
            },
        }
    }
}

// ---- Name ------------------------------------------------------------------------------

const NAME_ANON: u8 = 0;
const NAME_STR: u8 = 1;
const NAME_NUM: u8 = 2;
const NAME_NUM_OVERFLOW: u8 = 3;

impl Canonical for Name {
    const SCHEMA: SchemaId = SCHEMA_NAME;

    fn write_body(&self, w: &mut CanonWriter) {
        // Components root-to-leaf so decoding is a single forward fold.
        let mut chain = Vec::new();
        let mut cursor = self.clone();
        while !cursor.is_anonymous() {
            chain.push(cursor.clone());
            cursor = cursor.parent();
        }
        w.u64(chain.len() as u64);
        for link in chain.iter().rev() {
            match link.leaf() {
                NameLeaf::Str(s) => {
                    w.u8(NAME_STR);
                    w.str(s);
                }
                NameLeaf::Num(v, false) => {
                    w.u8(NAME_NUM);
                    w.u64(v);
                }
                NameLeaf::Num(v, true) => {
                    w.u8(NAME_NUM_OVERFLOW);
                    w.u64(v);
                }
                NameLeaf::Anonymous => w.u8(NAME_ANON),
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Name, CanonError> {
        let count = r.u64()?;
        let mut name = Name::anonymous();
        for _ in 0..count {
            // One component is one produced value: a hostile count field spends the
            // caller's budget rather than the machine's memory.
            r.charge_node()?;
            name = match r.u8()? {
                NAME_STR => Name::str(name, r.str()?),
                NAME_NUM => Name::num(name, r.u64()?),
                NAME_NUM_OVERFLOW => Name::num_overflowing(name, r.u64()?),
                NAME_ANON => return Err(r.err_public("anonymous inside a component chain")),
                _ => return Err(r.err_public("unknown name component tag")),
            };
        }
        Ok(name)
    }
}

/// Leaf view used by the canonical encoder (kept here so fln-core's API stays small).
enum NameLeaf<'a> {
    Anonymous,
    Str(&'a str),
    Num(u64, bool),
}

trait NameLeafExt {
    fn leaf(&self) -> NameLeaf<'_>;
}

impl NameLeafExt for Name {
    fn leaf(&self) -> NameLeaf<'_> {
        match self.leaf_view() {
            fln_core::name::LeafView::Anonymous => NameLeaf::Anonymous,
            fln_core::name::LeafView::Str(s) => NameLeaf::Str(s),
            fln_core::name::LeafView::Num(v) => NameLeaf::Num(v, self.component_overflowed()),
        }
    }
}

impl CanonReader<'_> {
    fn err_public(&self, what: &'static str) -> CanonError {
        CanonError { at: self.at, what }
    }
}

// ---- Level -----------------------------------------------------------------------------

const LEVEL_ZERO: u8 = 0;
const LEVEL_SUCC: u8 = 1;
const LEVEL_MAX: u8 = 2;
const LEVEL_IMAX: u8 = 3;
const LEVEL_PARAM: u8 = 4;
const LEVEL_MVAR: u8 = 5;

impl Canonical for Level {
    const SCHEMA: SchemaId = SCHEMA_LEVEL;

    fn write_body(&self, w: &mut CanonWriter) {
        use fln_core::level::LevelView;
        let mut pending = vec![self];
        while let Some(level) = pending.pop() {
            match level.view() {
                LevelView::Zero => w.u8(LEVEL_ZERO),
                LevelView::Succ(inner) => {
                    w.u8(LEVEL_SUCC);
                    pending.push(inner);
                }
                LevelView::Max(a, b) => {
                    w.u8(LEVEL_MAX);
                    pending.push(b);
                    pending.push(a);
                }
                LevelView::IMax(a, b) => {
                    w.u8(LEVEL_IMAX);
                    pending.push(b);
                    pending.push(a);
                }
                LevelView::Param(name) => {
                    w.u8(LEVEL_PARAM);
                    name.write_body(w);
                }
                LevelView::MVar(id) => {
                    w.u8(LEVEL_MVAR);
                    id.0.write_body(w);
                }
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
        // Iterative, not recursive: decode depth is bounded by the heap work-stack
        // (input size), never by the call stack. A recursive descent here would
        // overflow the stack — an uncatchable SIGABRT, worse than a panic — on a
        // deeply nested but tiny hostile encoding (franken_lean-fnj, D8/FL-INV-07).
        read_level_iter(r)
    }
}

/// One pending step of the iterative [`Level`] decoder.
enum LevelTask {
    /// Read one node (tag + any leaf fields); recursive nodes push their build
    /// step plus a `Read` per child.
    Read,
    BuildSucc,
    BuildMax,
    BuildIMax,
}

/// Decode one `Level` with an explicit heap work-stack (see [`Level::read_body`]).
/// The byte grammar is identical to the recursive form; only the control stack
/// moved off the call stack.
fn read_level_iter(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
    let underflow = |r: &CanonReader<'_>| r.err_public("level value-stack underflow");
    let too_deep = |r: &CanonReader<'_>| r.err_public("level depth exceeds the 24-bit covenant");
    let mut tasks = vec![LevelTask::Read];
    let mut values: Vec<Level> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            LevelTask::Read => {
                r.charge_node()?;
                match r.u8()? {
                    LEVEL_ZERO => values.push(Level::zero()),
                    LEVEL_SUCC => {
                        tasks.push(LevelTask::BuildSucc);
                        tasks.push(LevelTask::Read);
                    }
                    LEVEL_MAX => {
                        // Push the builder first (runs last), then the two child reads;
                        // the LIFO order reads child `a` before child `b`, matching the
                        // encoder's left-to-right emission.
                        tasks.push(LevelTask::BuildMax);
                        tasks.push(LevelTask::Read);
                        tasks.push(LevelTask::Read);
                    }
                    LEVEL_IMAX => {
                        tasks.push(LevelTask::BuildIMax);
                        tasks.push(LevelTask::Read);
                        tasks.push(LevelTask::Read);
                    }
                    LEVEL_PARAM => values.push(Level::param(Name::read_body(r)?)),
                    LEVEL_MVAR => values.push(Level::mvar(LMVarId(Name::read_body(r)?))),
                    _ => return Err(r.err_public("unknown level tag")),
                }
            }
            LevelTask::BuildSucc => {
                let u = values.pop().ok_or_else(|| underflow(r))?;
                values.push(u.succ().map_err(|_| too_deep(r))?);
            }
            LevelTask::BuildMax => {
                let b = values.pop().ok_or_else(|| underflow(r))?;
                let a = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Level::max(a, b).map_err(|_| too_deep(r))?);
            }
            LevelTask::BuildIMax => {
                let b = values.pop().ok_or_else(|| underflow(r))?;
                let a = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Level::imax(a, b).map_err(|_| too_deep(r))?);
            }
        }
    }
    // A well-formed single-value stream reduces to exactly one root.
    match values.len() {
        1 => Ok(values.pop().expect("length checked")),
        _ => Err(r.err_public("level value-stack did not reduce to a single root")),
    }
}

// ---- KVMap / DataValue -----------------------------------------------------------------

const DV_STRING: u8 = 0;
const DV_BOOL: u8 = 1;
const DV_NAME: u8 = 2;
const DV_NAT: u8 = 3;
const DV_INT: u8 = 4;
const DV_SYNTAX: u8 = 5;

/// The one `DataValue` byte grammar, shared by the ordered encoding and the
/// order-independent projection so the two can never disagree about a value.
fn write_data_value(value: &DataValue, w: &mut CanonWriter) {
    match value {
        DataValue::OfString(v) => {
            w.u8(DV_STRING);
            w.str(v);
        }
        DataValue::OfBool(v) => {
            w.u8(DV_BOOL);
            w.bool(*v);
        }
        DataValue::OfName(v) => {
            w.u8(DV_NAME);
            v.write_body(w);
        }
        DataValue::OfNat(v) => {
            w.u8(DV_NAT);
            w.u64(*v);
        }
        DataValue::OfInt(v) => {
            w.u8(DV_INT);
            w.i64(*v);
        }
        DataValue::OfSyntax(v) => {
            w.u8(DV_SYNTAX);
            w.u64(v.0);
        }
    }
}

/// The **order-independent** view of a `KVMap`: entries sorted by canonical key bytes.
///
/// Two encodings of one map exist on purpose, and conflating them was a real defect.
/// The [`Canonical`] impl is order-*sensitive*, correctly: upstream `KVMap` is an
/// ordered assoc list, so insertion order is part of the value and the encoding must be
/// injective on it. But a *set* consumer — the logical root of plan §7.1 — needs the
/// opposite property. `KVMap::insert` replaces a key in place and `find` returns the
/// first match, so with the unique keys the type guarantees, insertion order is not
/// observable through any lookup: two differently-ordered maps with the same pairs agree
/// on every `find`, `contains`, and `get_*`. Digesting the ordered bytes therefore gave
/// one environment two logical roots depending on the order options happened to be set
/// in — spurious cache misses, and two identities for one environment in receipts and
/// the transparency log.
///
/// Sorting by canonical key bytes rather than by `Name`'s `Ord` keeps the order fixed by
/// the wire format instead of by a trait impl that could be changed, and matches how
/// [`LogicalRootBuilder`](crate::root::LogicalRootBuilder) already keys declarations.
///
/// This is a distinct schema, so its preimages can never be confused with the ordered
/// encoding's — order-independence is a property of the projection, never something the
/// canonical encoding quietly acquired.
///
/// **Returns `None` for a map with duplicate keys**, which are representable and
/// preserved since bead franken_lean-l84f. A set view of something that is not a set has
/// no honest definition: sorting by key alone would leave the order of two same-key
/// entries unpinned, and any first-match-wins rule would drop the shadowed value, so two
/// maps upstream separates (its own `eqv` does) would project to identical bytes. That is
/// a collision in a function whose entire purpose is identity — the defect class of bead
/// franken_lean-f6br, where a lossy projection of `Name` made distinct finding sets share
/// a witness. Refusing is the only answer that cannot lie; a caller that wants a set out
/// of a duplicate-keyed map has to say which value wins, and that is its decision to
/// make and to record, not this function's to guess.
pub fn kvmap_canonical_set_bytes(map: &KVMap) -> Option<Vec<u8>> {
    let mut sorted: Vec<(Vec<u8>, &DataValue)> = map
        .entries()
        .iter()
        .map(|(key, value)| (key.to_canonical_bytes(), value))
        .collect();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    // Sorted, so duplicates are adjacent.
    if sorted.windows(2).any(|pair| pair[0].0 == pair[1].0) {
        return None;
    }
    let mut w = CanonWriter::new();
    w.schema(SCHEMA_KVMAP_SET);
    w.u64(sorted.len() as u64);
    for (key_bytes, value) in sorted {
        // Length-prefixed, so a key's bytes can never run into the next field.
        w.bytes(&key_bytes);
        write_data_value(value, &mut w);
    }
    Some(w.into_bytes())
}

impl Canonical for KVMap {
    const SCHEMA: SchemaId = SCHEMA_KVMAP;

    fn write_body(&self, w: &mut CanonWriter) {
        // Insertion order IS the value (upstream KVMap is an ordered assoc list), so
        // this encoding is deliberately order-SENSITIVE and a test asserts that
        // permuting entries changes the bytes. The order-independent view a *set*
        // consumer needs is a separate projection — see [`kvmap_canonical_set_bytes`].
        w.u64(self.entries().len() as u64);
        for (key, value) in self.entries() {
            key.write_body(w);
            write_data_value(value, w);
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<KVMap, CanonError> {
        let count = r.u64()?;
        // Entries are collected POSITIONALLY and handed to `KVMap::from_entries`, never
        // replayed through `KVMap::insert` (bead franken_lean-l84f).
        //
        // The distinction is the whole bug that used to live here. `insert` mirrors
        // `insertCore` and replaces the first match, so building the map with it FOLDS a
        // duplicate-keyed stream: two distinct encodings collapsed onto one value, and
        // that value re-encoded shorter than the bytes it came from. Bead fln-1f8v caught
        // that and refused duplicate keys outright, which was right about the symptom —
        // one value may have exactly one encoding, or every decl hash, logical root and
        // cache key is built on sand — and wrong about the cause. The folding was the
        // defect. Appending keeps the value/encoding correspondence injective over the
        // larger value space, so canonicality holds *and* the input is representable.
        //
        // Refusing them was also a parity divergence on the artifact path, which is why
        // it had to change rather than stay a convenient narrowing: `MData` *is* `KVMap`
        // (`Lean/Expr.lean:116`), so a duplicate-keyed map rides inside any
        // `Expr::MData`; the pin's module codec has no key-aware normalization anywhere,
        // so upstream's loader materializes such a value from such bytes without
        // complaint. We were rejecting an artifact the Reference can produce and read
        // back — exactly the drift the Oracle-Only Law forbids.
        let mut entries = Vec::with_capacity(count.min(1024) as usize);
        for _ in 0..count {
            r.charge_node()?;
            let key = Name::read_body(r)?;
            let value = match r.u8()? {
                DV_STRING => DataValue::OfString(r.str()?.to_string()),
                DV_BOOL => DataValue::OfBool(r.bool()?),
                DV_NAME => DataValue::OfName(Name::read_body(r)?),
                DV_NAT => DataValue::OfNat(r.u64()?),
                DV_INT => DataValue::OfInt(r.i64()?),
                DV_SYNTAX => DataValue::OfSyntax(SyntaxHandle(r.u64()?)),
                _ => return Err(r.err_public("unknown data-value tag")),
            };
            entries.push((key, value));
        }
        Ok(KVMap::from_entries(entries))
    }
}

// ---- Expr ------------------------------------------------------------------------------

const EXPR_BVAR: u8 = 0;
const EXPR_FVAR: u8 = 1;
const EXPR_MVAR: u8 = 2;
const EXPR_SORT: u8 = 3;
const EXPR_CONST: u8 = 4;
const EXPR_APP: u8 = 5;
const EXPR_LAM: u8 = 6;
const EXPR_FORALL: u8 = 7;
const EXPR_LET: u8 = 8;
const EXPR_LIT_NAT: u8 = 9;
const EXPR_LIT_STR: u8 = 10;
const EXPR_MDATA: u8 = 11;
const EXPR_PROJ: u8 = 12;

fn binder_info_tag(bi: BinderInfo) -> u8 {
    // The upstream toUInt64 encodings (Expr.lean:163-168).
    bi.to_u64() as u8
}

fn binder_info_from_tag(tag: u8) -> Option<BinderInfo> {
    Some(match tag {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => return None,
    })
}

impl Canonical for Expr {
    const SCHEMA: SchemaId = SCHEMA_EXPR;

    fn write_body(&self, w: &mut CanonWriter) {
        enum WriteTask<'a> {
            Expr(&'a Expr),
            BinderInfo(BinderInfo),
            NonDep(bool),
        }

        let mut pending = vec![WriteTask::Expr(self)];
        while let Some(task) = pending.pop() {
            let WriteTask::Expr(expr) = task else {
                match task {
                    WriteTask::BinderInfo(info) => w.u8(binder_info_tag(info)),
                    WriteTask::NonDep(value) => w.bool(value),
                    WriteTask::Expr(_) => unreachable!("matched above"),
                }
                continue;
            };

            match expr.node() {
                ExprNode::BVar { idx } => {
                    w.u8(EXPR_BVAR);
                    w.u32(*idx);
                }
                ExprNode::FVar { id } => {
                    w.u8(EXPR_FVAR);
                    id.0.write_body(w);
                }
                ExprNode::MVar { id } => {
                    w.u8(EXPR_MVAR);
                    id.0.write_body(w);
                }
                ExprNode::Sort { level } => {
                    w.u8(EXPR_SORT);
                    level.write_body(w);
                }
                ExprNode::Const { name, levels } => {
                    w.u8(EXPR_CONST);
                    name.write_body(w);
                    w.u64(levels.len() as u64);
                    for level in levels {
                        level.write_body(w);
                    }
                }
                ExprNode::App { f, a } => {
                    w.u8(EXPR_APP);
                    pending.push(WriteTask::Expr(a));
                    pending.push(WriteTask::Expr(f));
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    w.u8(EXPR_LAM);
                    binder_name.write_body(w);
                    pending.push(WriteTask::BinderInfo(*binder_info));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(binder_type));
                }
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    w.u8(EXPR_FORALL);
                    binder_name.write_body(w);
                    pending.push(WriteTask::BinderInfo(*binder_info));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(binder_type));
                }
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => {
                    w.u8(EXPR_LET);
                    decl_name.write_body(w);
                    pending.push(WriteTask::NonDep(*non_dep));
                    pending.push(WriteTask::Expr(body));
                    pending.push(WriteTask::Expr(value));
                    pending.push(WriteTask::Expr(type_));
                }
                ExprNode::Lit { literal } => match literal {
                    Literal::Nat(n) => {
                        w.u8(EXPR_LIT_NAT);
                        w.u64(n.limbs_le().len() as u64);
                        for limb in n.limbs_le() {
                            w.u64(*limb);
                        }
                    }
                    Literal::Str(s) => {
                        w.u8(EXPR_LIT_STR);
                        w.str(s);
                    }
                },
                ExprNode::MData { data, expr } => {
                    w.u8(EXPR_MDATA);
                    data.write_body(w);
                    pending.push(WriteTask::Expr(expr));
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => {
                    w.u8(EXPR_PROJ);
                    struct_name.write_body(w);
                    w.u64(*idx);
                    pending.push(WriteTask::Expr(expr));
                }
            }
        }
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
        // Iterative, not recursive: see [`Level::read_body`]. A recursive descent
        // here overflows the call stack (SIGABRT, not a typed error) on a deeply
        // nested but tiny hostile encoding — e.g. a chain of `App` tags
        // (franken_lean-fnj, D8/FL-INV-07).
        read_expr_iter(r)
    }
}

/// One pending step of the iterative [`Expr`] decoder. Post-order scalar fields
/// (a binder's `BinderInfo`, a `let`'s `nonDep` flag) are read when the builder
/// runs — by then the child reads have advanced the cursor to exactly that field.
enum ExprTask {
    /// Read one node (tag + leaf fields); recursive nodes push their builder plus
    /// a `Read` per `Expr` child.
    Read,
    BuildApp,
    BuildLam(Name),
    BuildForall(Name),
    BuildLet(Name),
    BuildMData(KVMap),
    BuildProj(Name, u64),
}

/// Decode one `Expr` with an explicit heap work-stack (see [`Expr::read_body`]).
/// Byte-for-byte the same grammar as the recursive form; `Level`, `Name`, and
/// `KVMap` children decode through their own bounded readers, so total call-stack
/// depth is a small constant regardless of the term's nesting.
fn read_expr_iter(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
    let underflow = |r: &CanonReader<'_>| r.err_public("expr value-stack underflow");
    let mut tasks = vec![ExprTask::Read];
    let mut values: Vec<Expr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            ExprTask::Read => {
                r.charge_node()?;
                match r.u8()? {
                    EXPR_BVAR => values.push(
                        Expr::bvar(r.u32()?)
                            .map_err(|_| r.err_public("bvar exceeds the 20-bit range covenant"))?,
                    ),
                    EXPR_FVAR => values.push(Expr::fvar(FVarId(Name::read_body(r)?))),
                    EXPR_MVAR => values.push(Expr::mvar(MVarId(Name::read_body(r)?))),
                    EXPR_SORT => values.push(Expr::sort(read_level_iter(r)?)),
                    EXPR_CONST => {
                        let name = Name::read_body(r)?;
                        let count = r.u64()?;
                        let mut levels = Vec::new();
                        for _ in 0..count {
                            levels.push(read_level_iter(r)?);
                        }
                        values.push(Expr::const_(name, levels));
                    }
                    EXPR_APP => {
                        // Builder first (runs last); the two child reads follow so LIFO
                        // reads `f` before `a`, matching the encoder.
                        tasks.push(ExprTask::BuildApp);
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                    }
                    EXPR_LAM => {
                        let binder_name = Name::read_body(r)?;
                        tasks.push(ExprTask::BuildLam(binder_name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                    }
                    EXPR_FORALL => {
                        let binder_name = Name::read_body(r)?;
                        tasks.push(ExprTask::BuildForall(binder_name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                    }
                    EXPR_LET => {
                        let decl_name = Name::read_body(r)?;
                        tasks.push(ExprTask::BuildLet(decl_name));
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                        tasks.push(ExprTask::Read);
                    }
                    EXPR_LIT_NAT => {
                        let count = r.u64()?;
                        let mut limbs = Vec::new();
                        for _ in 0..count {
                            limbs.push(r.u64()?);
                        }
                        let lit = NatLit::from_limbs_le(limbs.clone());
                        if lit.limbs_le() != limbs.as_slice() {
                            // Trailing zero limbs would give two encodings of one value.
                            return Err(r.err_public("non-normalized nat literal limbs"));
                        }
                        values.push(Expr::lit(Literal::Nat(lit)));
                    }
                    EXPR_LIT_STR => values.push(Expr::lit(Literal::Str(r.str()?.to_string()))),
                    EXPR_MDATA => {
                        let data = KVMap::read_body(r)?;
                        tasks.push(ExprTask::BuildMData(data));
                        tasks.push(ExprTask::Read);
                    }
                    EXPR_PROJ => {
                        let struct_name = Name::read_body(r)?;
                        let idx = r.u64()?;
                        tasks.push(ExprTask::BuildProj(struct_name, idx));
                        tasks.push(ExprTask::Read);
                    }
                    _ => return Err(r.err_public("unknown expr tag")),
                }
            }
            ExprTask::BuildApp => {
                let a = values.pop().ok_or_else(|| underflow(r))?;
                let f = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::app(f, a));
            }
            ExprTask::BuildLam(binder_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let binder_type = values.pop().ok_or_else(|| underflow(r))?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                values.push(Expr::lam(binder_name, binder_type, body, bi));
            }
            ExprTask::BuildForall(binder_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let binder_type = values.pop().ok_or_else(|| underflow(r))?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                values.push(Expr::forall_e(binder_name, binder_type, body, bi));
            }
            ExprTask::BuildLet(decl_name) => {
                let body = values.pop().ok_or_else(|| underflow(r))?;
                let value = values.pop().ok_or_else(|| underflow(r))?;
                let type_ = values.pop().ok_or_else(|| underflow(r))?;
                let non_dep = r.bool()?;
                values.push(Expr::let_e(decl_name, type_, value, body, non_dep));
            }
            ExprTask::BuildMData(data) => {
                let expr = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::mdata(data, expr));
            }
            ExprTask::BuildProj(struct_name, idx) => {
                let expr = values.pop().ok_or_else(|| underflow(r))?;
                values.push(Expr::proj(struct_name, idx, expr));
            }
        }
    }
    match values.len() {
        1 => Ok(values.pop().expect("length checked")),
        _ => Err(r.err_public("expr value-stack did not reduce to a single root")),
    }
}

// ---- Diagnostic (the D8 typed error taxonomy, versioned on the wire) -------------------

/// **Version 2** since bead franken_lean-vui8 added `ResourceReason::StructuralBudget`
/// (wire tag `RES_STRUCTURAL`).
///
/// Bumped even though no existing value's bytes moved and no golden was re-pinned. The
/// reason is skew, not layout: a v1 reader meeting tag 4 fails closed with "unknown
/// resource-reason tag", so if the version had stayed at 1 then two artifacts both
/// labelled `fln.canon.diag/1` would exist — one every reader can decode and one only new
/// readers can. A version whose value does not identify the language it names is worse
/// than useless, because it invites exactly the confident misread it is supposed to
/// prevent. The bump was free here: nothing persists a diagnostic encoding yet and no
/// fixture or digest pins one, which was checked rather than assumed.
pub const SCHEMA_DIAG: SchemaId = SchemaId {
    name: "fln.canon.diag",
    version: 2,
};

const SEV_INFO: u8 = 0;
const SEV_WARN: u8 = 1;
const SEV_ERROR: u8 = 2;

const RES_HEARTBEATS: u8 = 0;
const RES_REC_DEPTH: u8 = 1;
const RES_CANCELLED: u8 = 2;
const RES_MEMORY: u8 = 3;
/// Added with the structural budget axis (bead franken_lean-vui8). Tags are permanent
/// once published; a new reason takes the next free value and never reuses one.
const RES_STRUCTURAL: u8 = 4;

const SU_INPUT_BYTES: u8 = 0;
const SU_PRODUCED_NODES: u8 = 1;
const SU_EXPANDED_WEIGHT: u8 = 2;

fn write_structural_unit(w: &mut CanonWriter, unit: StructuralUnit) {
    w.u8(match unit {
        StructuralUnit::InputBytes => SU_INPUT_BYTES,
        StructuralUnit::ProducedNodes => SU_PRODUCED_NODES,
        StructuralUnit::ExpandedWeight => SU_EXPANDED_WEIGHT,
    });
}

fn read_structural_unit(r: &mut CanonReader<'_>) -> Result<StructuralUnit, CanonError> {
    Ok(match r.u8()? {
        SU_INPUT_BYTES => StructuralUnit::InputBytes,
        SU_PRODUCED_NODES => StructuralUnit::ProducedNodes,
        SU_EXPANDED_WEIGHT => StructuralUnit::ExpandedWeight,
        _ => return Err(r.err_public("unknown structural-unit tag")),
    })
}

fn write_resource(w: &mut CanonWriter, resource: &ResourceReason) {
    match resource {
        ResourceReason::Heartbeats { consumed, limit } => {
            w.u8(RES_HEARTBEATS);
            w.u64(*consumed);
            w.u64(*limit);
        }
        ResourceReason::RecursionDepth { limit } => {
            w.u8(RES_REC_DEPTH);
            w.u64(*limit);
        }
        ResourceReason::Cancelled => w.u8(RES_CANCELLED),
        ResourceReason::Memory { limit_bytes } => {
            w.u8(RES_MEMORY);
            w.u64(*limit_bytes);
        }
        // No numbers: the variant carries only which quantity was bounded, because
        // `allowed`/`observed` live in `ResourceUsage`.
        ResourceReason::StructuralBudget { unit } => {
            w.u8(RES_STRUCTURAL);
            write_structural_unit(w, *unit);
        }
    }
}

fn read_resource(r: &mut CanonReader<'_>) -> Result<ResourceReason, CanonError> {
    Ok(match r.u8()? {
        RES_HEARTBEATS => ResourceReason::Heartbeats {
            consumed: r.u64()?,
            limit: r.u64()?,
        },
        RES_REC_DEPTH => ResourceReason::RecursionDepth { limit: r.u64()? },
        RES_CANCELLED => ResourceReason::Cancelled,
        RES_MEMORY => ResourceReason::Memory {
            limit_bytes: r.u64()?,
        },
        RES_STRUCTURAL => ResourceReason::StructuralBudget {
            unit: read_structural_unit(r)?,
        },
        _ => return Err(r.err_public("unknown resource-reason tag")),
    })
}

// Variant tags in taxonomy declaration order — frozen; a new variant appends.
const EV_SYNTAX: u8 = 0;
const EV_MACRO: u8 = 1;
const EV_ELAB: u8 = 2;
const EV_KERNEL_REJECT: u8 = 3;
const EV_KERNEL_INCONCLUSIVE: u8 = 4;
const EV_ARTIFACT_CORRUPT: u8 = 5;
const EV_ARTIFACT_EPOCH: u8 = 6;
const EV_ABI: u8 = 7;
const EV_CAPABILITY: u8 = 8;
const EV_PLUGIN: u8 = 9;
const EV_BUILD: u8 = 10;
const EV_PROTOCOL: u8 = 11;
const EV_REPLAY: u8 = 12;
const EV_INTERNAL: u8 = 13;

fn write_error_value(w: &mut CanonWriter, value: &ErrorValue) {
    match value {
        ErrorValue::SyntaxFailure { message } => {
            w.u8(EV_SYNTAX);
            w.str(message);
        }
        ErrorValue::MacroFailure {
            macro_name,
            message,
        } => {
            w.u8(EV_MACRO);
            macro_name.write_body(w);
            w.str(message);
        }
        ErrorValue::ElaborationFailure { message } => {
            w.u8(EV_ELAB);
            w.str(message);
        }
        ErrorValue::KernelRejection {
            decl,
            stable_error_class,
            message,
        } => {
            w.u8(EV_KERNEL_REJECT);
            decl.write_body(w);
            w.str(stable_error_class);
            w.str(message);
        }
        ErrorValue::KernelInconclusive { decl, resource } => {
            w.u8(EV_KERNEL_INCONCLUSIVE);
            decl.write_body(w);
            write_resource(w, resource);
        }
        ErrorValue::ArtifactCorrupt { path, detail } => {
            w.u8(EV_ARTIFACT_CORRUPT);
            w.str(path);
            w.str(detail);
        }
        ErrorValue::ArtifactEpochMismatch {
            path,
            expected_epoch,
            found_epoch,
        } => {
            w.u8(EV_ARTIFACT_EPOCH);
            w.str(path);
            w.str(expected_epoch);
            w.str(found_epoch);
        }
        ErrorValue::AbiViolation { symbol, detail } => {
            w.u8(EV_ABI);
            w.str(symbol);
            w.str(detail);
        }
        ErrorValue::CapabilityDenied { capability, detail } => {
            w.u8(EV_CAPABILITY);
            w.str(capability);
            w.str(detail);
        }
        ErrorValue::PluginCrashed { plugin, detail } => {
            w.u8(EV_PLUGIN);
            w.str(plugin);
            w.str(detail);
        }
        ErrorValue::BuildFailure { job, detail } => {
            w.u8(EV_BUILD);
            w.str(job);
            w.str(detail);
        }
        ErrorValue::ProtocolFailure { detail } => {
            w.u8(EV_PROTOCOL);
            w.str(detail);
        }
        ErrorValue::ReplayDivergence { detail } => {
            w.u8(EV_REPLAY);
            w.str(detail);
        }
        ErrorValue::InternalInvariantViolation { invariant, detail } => {
            w.u8(EV_INTERNAL);
            w.str(invariant);
            w.str(detail);
        }
    }
}

fn read_error_value(r: &mut CanonReader<'_>) -> Result<ErrorValue, CanonError> {
    Ok(match r.u8()? {
        EV_SYNTAX => ErrorValue::SyntaxFailure {
            message: r.str()?.to_string(),
        },
        EV_MACRO => ErrorValue::MacroFailure {
            macro_name: Name::read_body(r)?,
            message: r.str()?.to_string(),
        },
        EV_ELAB => ErrorValue::ElaborationFailure {
            message: r.str()?.to_string(),
        },
        EV_KERNEL_REJECT => ErrorValue::KernelRejection {
            decl: Name::read_body(r)?,
            stable_error_class: r.str()?.to_string(),
            message: r.str()?.to_string(),
        },
        EV_KERNEL_INCONCLUSIVE => ErrorValue::KernelInconclusive {
            decl: Name::read_body(r)?,
            resource: read_resource(r)?,
        },
        EV_ARTIFACT_CORRUPT => ErrorValue::ArtifactCorrupt {
            path: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_ARTIFACT_EPOCH => ErrorValue::ArtifactEpochMismatch {
            path: r.str()?.to_string(),
            expected_epoch: r.str()?.to_string(),
            found_epoch: r.str()?.to_string(),
        },
        EV_ABI => ErrorValue::AbiViolation {
            symbol: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_CAPABILITY => ErrorValue::CapabilityDenied {
            capability: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_PLUGIN => ErrorValue::PluginCrashed {
            plugin: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_BUILD => ErrorValue::BuildFailure {
            job: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        EV_PROTOCOL => ErrorValue::ProtocolFailure {
            detail: r.str()?.to_string(),
        },
        EV_REPLAY => ErrorValue::ReplayDivergence {
            detail: r.str()?.to_string(),
        },
        EV_INTERNAL => ErrorValue::InternalInvariantViolation {
            invariant: r.str()?.to_string(),
            detail: r.str()?.to_string(),
        },
        _ => return Err(r.err_public("unknown error-value tag (newer taxonomy version?)")),
    })
}

impl Canonical for Diagnostic {
    const SCHEMA: SchemaId = SCHEMA_DIAG;

    fn write_body(&self, w: &mut CanonWriter) {
        w.str(&self.file_name);
        w.u64(self.pos.line as u64);
        w.u64(self.pos.column as u64);
        match &self.end_pos {
            Some(end) => {
                w.u8(1);
                w.u64(end.line as u64);
                w.u64(end.column as u64);
            }
            None => w.u8(0),
        }
        w.u8(match self.severity {
            Severity::Information => SEV_INFO,
            Severity::Warning => SEV_WARN,
            Severity::Error => SEV_ERROR,
        });
        match &self.error_name {
            Some(name) => {
                w.u8(1);
                name.write_body(w);
            }
            None => w.u8(0),
        }
        w.str(&self.caption);
        write_error_value(w, &self.value);
    }

    fn read_body(r: &mut CanonReader<'_>) -> Result<Diagnostic, CanonError> {
        let file_name = r.str()?.to_string();
        let line = usize::try_from(r.u64()?).map_err(|_| r.err_public("line overflow"))?;
        let column = usize::try_from(r.u64()?).map_err(|_| r.err_public("column overflow"))?;
        let end_pos = match r.u8()? {
            0 => None,
            1 => Some(Position {
                line: usize::try_from(r.u64()?).map_err(|_| r.err_public("line overflow"))?,
                column: usize::try_from(r.u64()?).map_err(|_| r.err_public("column overflow"))?,
            }),
            _ => return Err(r.err_public("non-canonical option tag")),
        };
        let severity = match r.u8()? {
            SEV_INFO => Severity::Information,
            SEV_WARN => Severity::Warning,
            SEV_ERROR => Severity::Error,
            _ => return Err(r.err_public("unknown severity tag")),
        };
        let error_name = match r.u8()? {
            0 => None,
            1 => Some(Name::read_body(r)?),
            _ => return Err(r.err_public("non-canonical option tag")),
        };
        let caption = r.str()?.to_string();
        let value = read_error_value(r)?;
        Ok(Diagnostic {
            file_name,
            pos: Position { line, column },
            end_pos,
            severity,
            error_name,
            caption,
            value,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::level::Level;

    use fln_core::outcome::{Authority, CacheAdmission, InconclusiveCause};

    macro_rules! fixture_panic {
        ($($arg:tt)*) => {
            panic!(/* ubs:ignore — test-only diagnostic. */ $($arg)*)
        };
    }

    /// The stop facts a budgeted decode records, so assertions that used to read
    /// `Exhausted` fields directly keep asserting exactly the same things after the fold
    /// to `Outcome` (bead fln-8gz3). Panics loudly on any other outcome shape, so a test
    /// cannot pass by silently getting a different arm than it meant.
    fn stop_of<T: std::fmt::Debug>(outcome: &DecodeOutcome<T>) -> (StructuralUnit, u64, u64) {
        match outcome {
            Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
                InconclusiveCause::ResourceExhausted { usage } => match usage.reason {
                    ResourceReason::StructuralBudget { unit } => {
                        (unit, usage.allowed, usage.observed)
                    }
                    ref other => fixture_panic!("expected a structural budget, got {other:?}"),
                },
                other => fixture_panic!("expected resource exhaustion, got {other:?}"),
            },
            other => fixture_panic!("expected an inconclusive outcome, got {other:?}"),
        }
    }

    /// Where the stop was localized — the `at` offset the pre-fold `Exhausted` carried.
    fn stop_progress<T: std::fmt::Debug>(outcome: &DecodeOutcome<T>) -> String {
        match outcome {
            Outcome::Inconclusive(inconclusive) => inconclusive
                .progress
                .as_deref()
                .map(|text| text.text().to_string())
                .expect("a budget stop records where it stopped"),
            other => fixture_panic!("expected an inconclusive outcome, got {other:?}"),
        }
    }

    fn is_inconclusive<T>(outcome: &DecodeOutcome<T>) -> bool {
        matches!(outcome, Outcome::Inconclusive(_))
    }

    /// The decoded value if the run completed AND accepted — the pre-fold
    /// `Decoded::value()`. Deliberately collapses only the two arms that were already
    /// collapsed: a non-answer and a rejection both yield `None`, and callers that need to
    /// tell them apart match the `Outcome` directly.
    fn decoded_value<T>(outcome: DecodeOutcome<T>) -> Option<T> {
        match outcome {
            Outcome::Complete(Ok(value)) => Some(value),
            _ => None,
        }
    }

    #[test]
    fn schema_names_are_unique_and_well_shaped() {
        let mut seen = std::collections::BTreeSet::new();
        for row in SCHEMA_REGISTRY {
            assert!(
                seen.insert(row.id.name),
                "two durable formats claim the schema name `{}` — a name is an identity, \
                 and a collision means one decoder can be handed the other's bytes and \
                 accept them",
                row.id.name
            );
            assert!(
                row.id.version >= 1,
                "`{}` has no version; version 0 is not a published format",
                row.id.name
            );
            assert!(
                row.id.name.starts_with("fln."),
                "`{}` is outside the `fln.` namespace",
                row.id.name
            );
            // `fln.<subsystem>.<format>` at minimum, so a name says who owns it.
            assert!(
                row.id.name.split('.').count() >= 3,
                "`{}` must be shaped fln.<subsystem>.<format>",
                row.id.name
            );
            assert!(
                row.id.name.bytes().all(|b| b.is_ascii_lowercase()
                    || b.is_ascii_digit()
                    || b == b'.'
                    || b == b'-'),
                "`{}` must be lowercase ascii with `.`/`-` separators; a name that varies \
                 by case is two names to a byte comparison",
                row.id.name
            );
            assert!(
                !row.covers.is_empty(),
                "`{}` has no description; an unreviewable row is not a registration",
                row.id.name
            );
        }
        assert_eq!(seen.len(), SCHEMA_REGISTRY.len());
    }

    #[test]
    fn registry_rows_match_the_constants_they_name() {
        // fln-hash's own rows are joined against the real constants rather than
        // transcribed beside them, so this table cannot drift from the codec it
        // describes. The other owners' rows are joined against their sources in
        // tests/schema_registry.rs, which is the closest this crate can get to the
        // same check without depending upward.
        for (constant, expected) in [
            (SCHEMA_NAME, "fln.canon.name"),
            (SCHEMA_LEVEL, "fln.canon.level"),
            (SCHEMA_EXPR, "fln.canon.expr"),
            (SCHEMA_KVMAP, "fln.canon.kvmap"),
            (SCHEMA_KVMAP_SET, "fln.canon.kvmap-set"),
            (SCHEMA_DIAG, "fln.canon.diag"),
            (SCHEMA_SHADOW_CELL, "fln.canon.shadow-cell"),
            (
                SCHEMA_SHADOW_SEMANTIC_NDJSON,
                "fln.canon.shadow-semantic-ndjson",
            ),
            (
                SCHEMA_SHADOW_TELEMETRY_NDJSON,
                "fln.canon.shadow-telemetry-ndjson",
            ),
        ] {
            assert_eq!(constant.name, expected);
            let row = registered(constant.name)
                .unwrap_or_else(|| fixture_panic!("{expected} is not in SCHEMA_REGISTRY"));
            assert_eq!(
                row.id, constant,
                "the row for {expected} is not the constant"
            );
            assert_eq!(row.owner, SchemaOwner::Hash);
        }
        // And every Hash-owned row is one of those constants: a row added here without a
        // constant would otherwise pass the loop above by never being visited.
        let hash_rows = SCHEMA_REGISTRY
            .iter()
            .filter(|row| row.owner == SchemaOwner::Hash)
            .count();
        assert_eq!(
            hash_rows, 9,
            "fln-hash owns a schema the constant join above does not cover"
        );
    }

    #[test]
    fn every_owner_is_represented_and_names_a_real_declaration_file() {
        for owner in SchemaOwner::ALL {
            let rows = SCHEMA_REGISTRY
                .iter()
                .filter(|row| row.owner == owner)
                .count();
            assert!(
                rows > 0,
                "{} is a registered owner with no formats — remove the owner or the \
                 registry is incomplete",
                owner.crate_name()
            );
            assert!(
                owner
                    .declaration_file()
                    .starts_with(&format!("crates/{}/", owner.crate_name())),
                "{}'s declaration file must live in its own crate, not {}",
                owner.crate_name(),
                owner.declaration_file()
            );
            // Every row's name must name its own subsystem, so the owner column and the
            // name cannot disagree about who defines a format.
            let subsystem = owner.crate_name().trim_start_matches("fln-");
            let prefix = match owner {
                // The term-plane formats predate the crate split and are named for the
                // module (`canon`) rather than the crate; recorded here rather than
                // renamed, because a schema name is frozen once published.
                SchemaOwner::Hash => "fln.canon.".to_string(),
                _ => format!("fln.{subsystem}."),
            };
            for row in SCHEMA_REGISTRY.iter().filter(|row| row.owner == owner) {
                assert!(
                    row.id.name.starts_with(&prefix),
                    "`{}` is owned by {} but is not named `{prefix}*`",
                    row.id.name,
                    owner.crate_name()
                );
            }
        }
    }

    // Test-only mutations used by the no-mock E2E lane. They deliberately restore
    // the exact bug class: syntax-depth recursion on a bounded worker stack. The
    // parent process must observe their fatal exit instead of accepting them.
    #[derive(Clone, Copy)]
    struct RecursiveLevelEncoder(fn(&Level, &mut CanonWriter, RecursiveLevelEncoder));

    impl RecursiveLevelEncoder {
        fn encode(self, level: &Level, w: &mut CanonWriter) {
            (self.0)(level, w, self);
        }
    }

    fn recursive_level_encoder_step(
        level: &Level,
        w: &mut CanonWriter,
        recurse: RecursiveLevelEncoder,
    ) {
        use fln_core::level::LevelView;
        match level.view() {
            LevelView::Zero => w.u8(LEVEL_ZERO),
            LevelView::Succ(inner) => {
                w.u8(LEVEL_SUCC);
                recurse.encode(inner, w);
                std::hint::black_box(w.buf.len());
            }
            _ => fixture_panic!("the level mutation probe expects a Succ chain"),
        }
    }

    fn recursive_level_encoder_mutant(level: &Level, w: &mut CanonWriter) {
        RecursiveLevelEncoder(recursive_level_encoder_step).encode(level, w);
    }

    #[derive(Clone, Copy)]
    struct RecursiveExprEncoder(fn(&Expr, &mut CanonWriter, RecursiveExprEncoder));

    impl RecursiveExprEncoder {
        fn encode(self, expr: &Expr, w: &mut CanonWriter) {
            (self.0)(expr, w, self);
        }
    }

    fn recursive_expr_encoder_step(
        expr: &Expr,
        w: &mut CanonWriter,
        recurse: RecursiveExprEncoder,
    ) {
        match expr.node() {
            ExprNode::BVar { idx } => {
                w.u8(EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::App { f, a } => {
                w.u8(EXPR_APP);
                recurse.encode(f, w);
                recurse.encode(a, w);
                std::hint::black_box(w.buf.len());
            }
            _ => fixture_panic!("the expression mutation probe expects an App chain"),
        }
    }

    fn recursive_expr_encoder_mutant(expr: &Expr, w: &mut CanonWriter) {
        RecursiveExprEncoder(recursive_expr_encoder_step).encode(expr, w);
    }

    // Frozen test oracle for the recursive writer grammar that preceded 265f260.
    // Keep this deliberately shallow-only: its purpose is byte compatibility, not
    // lifecycle safety. Every nested canonical payload routes through the matching
    // pre-change helper so the iterative implementation never acts as its own oracle.
    fn prechange_name_body(name: &Name, w: &mut CanonWriter) {
        fn components(name: &Name, out: &mut Vec<Name>) {
            if name.is_anonymous() {
                return;
            }
            components(&name.parent(), out);
            out.push(name.clone());
        }

        let mut chain = Vec::new();
        components(name, &mut chain);
        w.u64(chain.len() as u64);
        for link in chain {
            match link.leaf() {
                NameLeaf::Str(value) => {
                    w.u8(NAME_STR);
                    w.str(value);
                }
                NameLeaf::Num(value, false) => {
                    w.u8(NAME_NUM);
                    w.u64(value);
                }
                NameLeaf::Num(value, true) => {
                    w.u8(NAME_NUM_OVERFLOW);
                    w.u64(value);
                }
                NameLeaf::Anonymous => w.u8(NAME_ANON),
            }
        }
    }

    fn prechange_level_body(level: &Level, w: &mut CanonWriter) {
        use fln_core::level::LevelView;

        match level.view() {
            LevelView::Zero => w.u8(LEVEL_ZERO),
            LevelView::Succ(inner) => {
                w.u8(LEVEL_SUCC);
                prechange_level_body(inner, w);
            }
            LevelView::Max(left, right) => {
                w.u8(LEVEL_MAX);
                prechange_level_body(left, w);
                prechange_level_body(right, w);
            }
            LevelView::IMax(left, right) => {
                w.u8(LEVEL_IMAX);
                prechange_level_body(left, w);
                prechange_level_body(right, w);
            }
            LevelView::Param(name) => {
                w.u8(LEVEL_PARAM);
                prechange_name_body(name, w);
            }
            LevelView::MVar(id) => {
                w.u8(LEVEL_MVAR);
                prechange_name_body(&id.0, w);
            }
        }
    }

    fn prechange_kvmap_body(map: &KVMap, w: &mut CanonWriter) {
        w.u64(map.entries().len() as u64);
        for (key, value) in map.entries() {
            prechange_name_body(key, w);
            match value {
                DataValue::OfString(value) => {
                    w.u8(DV_STRING);
                    w.str(value);
                }
                DataValue::OfBool(value) => {
                    w.u8(DV_BOOL);
                    w.bool(*value);
                }
                DataValue::OfName(value) => {
                    w.u8(DV_NAME);
                    prechange_name_body(value, w);
                }
                DataValue::OfNat(value) => {
                    w.u8(DV_NAT);
                    w.u64(*value);
                }
                DataValue::OfInt(value) => {
                    w.u8(DV_INT);
                    w.i64(*value);
                }
                DataValue::OfSyntax(value) => {
                    w.u8(DV_SYNTAX);
                    w.u64(value.0);
                }
            }
        }
    }

    fn prechange_expr_body(expr: &Expr, w: &mut CanonWriter) {
        match expr.node() {
            ExprNode::BVar { idx } => {
                w.u8(EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::FVar { id } => {
                w.u8(EXPR_FVAR);
                prechange_name_body(&id.0, w);
            }
            ExprNode::MVar { id } => {
                w.u8(EXPR_MVAR);
                prechange_name_body(&id.0, w);
            }
            ExprNode::Sort { level } => {
                w.u8(EXPR_SORT);
                prechange_level_body(level, w);
            }
            ExprNode::Const { name, levels } => {
                w.u8(EXPR_CONST);
                prechange_name_body(name, w);
                w.u64(levels.len() as u64);
                for level in levels {
                    prechange_level_body(level, w);
                }
            }
            ExprNode::App { f, a } => {
                w.u8(EXPR_APP);
                prechange_expr_body(f, w);
                prechange_expr_body(a, w);
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_LAM);
                prechange_name_body(binder_name, w);
                prechange_expr_body(binder_type, w);
                prechange_expr_body(body, w);
                w.u8(binder_info_tag(*binder_info));
            }
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(EXPR_FORALL);
                prechange_name_body(binder_name, w);
                prechange_expr_body(binder_type, w);
                prechange_expr_body(body, w);
                w.u8(binder_info_tag(*binder_info));
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                w.u8(EXPR_LET);
                prechange_name_body(decl_name, w);
                prechange_expr_body(type_, w);
                prechange_expr_body(value, w);
                prechange_expr_body(body, w);
                w.bool(*non_dep);
            }
            ExprNode::Lit { literal } => match literal {
                Literal::Nat(value) => {
                    w.u8(EXPR_LIT_NAT);
                    w.u64(value.limbs_le().len() as u64);
                    for limb in value.limbs_le() {
                        w.u64(*limb);
                    }
                }
                Literal::Str(value) => {
                    w.u8(EXPR_LIT_STR);
                    w.str(value);
                }
            },
            ExprNode::MData { data, expr } => {
                w.u8(EXPR_MDATA);
                prechange_kvmap_body(data, w);
                prechange_expr_body(expr, w);
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                w.u8(EXPR_PROJ);
                prechange_name_body(struct_name, w);
                w.u64(*idx);
                prechange_expr_body(expr, w);
            }
        }
    }

    fn prechange_bytes(schema: SchemaId, write: impl FnOnce(&mut CanonWriter)) -> Vec<u8> {
        let mut writer = CanonWriter::new();
        writer.schema(schema);
        write(&mut writer);
        writer.into_bytes()
    }

    fn drop_pair_concurrently<T: Send + 'static>(left: T, right: T) {
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(3));
        let spawn = |value, barrier: std::sync::Arc<std::sync::Barrier>| {
            std::thread::Builder::new()
                .stack_size(1024 * 1024)
                .spawn(move || {
                    barrier.wait();
                    drop(value);
                })
                .expect("spawn concurrent dropper")
        };
        let left_thread = spawn(left, barrier.clone());
        let right_thread = spawn(right, barrier.clone());
        barrier.wait();
        left_thread.join().expect("left dropper completes");
        right_thread.join().expect("right dropper completes");
    }

    /// The recursive descent that [`read_level_iter`] replaced (bead
    /// franken_lean-fnj). Test-only, and it exists for exactly one reason: a
    /// bounded-stack decode test that passes proves nothing unless the same test
    /// is known to FAIL against a recursive reader. The byte grammar is identical,
    /// so the only difference under test is where the control stack lives.
    fn recursive_level_decoder_mutant(r: &mut CanonReader<'_>) -> Result<Level, CanonError> {
        match r.u8()? {
            LEVEL_ZERO => Ok(Level::zero()),
            LEVEL_SUCC => {
                let u = recursive_level_decoder_mutant(r)?;
                u.succ()
                    .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))
            }
            LEVEL_MAX => {
                let a = recursive_level_decoder_mutant(r)?;
                let b = recursive_level_decoder_mutant(r)?;
                Level::max(a, b)
                    .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))
            }
            LEVEL_IMAX => {
                let a = recursive_level_decoder_mutant(r)?;
                let b = recursive_level_decoder_mutant(r)?;
                Level::imax(a, b)
                    .map_err(|_| r.err_public("level depth exceeds the 24-bit covenant"))
            }
            LEVEL_PARAM => Ok(Level::param(Name::read_body(r)?)),
            LEVEL_MVAR => Ok(Level::mvar(LMVarId(Name::read_body(r)?))),
            _ => Err(r.err_public("unknown level tag")),
        }
    }

    /// The recursive descent that [`read_expr_iter`] replaced (bead
    /// franken_lean-fnj); see [`recursive_level_decoder_mutant`].
    fn recursive_expr_decoder_mutant(r: &mut CanonReader<'_>) -> Result<Expr, CanonError> {
        match r.u8()? {
            EXPR_BVAR => Expr::bvar(r.u32()?)
                .map_err(|_| r.err_public("bvar exceeds the 20-bit range covenant")),
            EXPR_FVAR => Ok(Expr::fvar(FVarId(Name::read_body(r)?))),
            EXPR_MVAR => Ok(Expr::mvar(MVarId(Name::read_body(r)?))),
            EXPR_SORT => Ok(Expr::sort(recursive_level_decoder_mutant(r)?)),
            EXPR_CONST => {
                let name = Name::read_body(r)?;
                let count = r.u64()?;
                let mut levels = Vec::new();
                for _ in 0..count {
                    levels.push(recursive_level_decoder_mutant(r)?);
                }
                Ok(Expr::const_(name, levels))
            }
            EXPR_APP => {
                let f = recursive_expr_decoder_mutant(r)?;
                let a = recursive_expr_decoder_mutant(r)?;
                Ok(Expr::app(f, a))
            }
            EXPR_LAM => {
                let binder_name = Name::read_body(r)?;
                let binder_type = recursive_expr_decoder_mutant(r)?;
                let body = recursive_expr_decoder_mutant(r)?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                Ok(Expr::lam(binder_name, binder_type, body, bi))
            }
            EXPR_FORALL => {
                let binder_name = Name::read_body(r)?;
                let binder_type = recursive_expr_decoder_mutant(r)?;
                let body = recursive_expr_decoder_mutant(r)?;
                let bi = binder_info_from_tag(r.u8()?)
                    .ok_or_else(|| r.err_public("unknown binder-info tag"))?;
                Ok(Expr::forall_e(binder_name, binder_type, body, bi))
            }
            EXPR_LET => {
                let decl_name = Name::read_body(r)?;
                let type_ = recursive_expr_decoder_mutant(r)?;
                let value = recursive_expr_decoder_mutant(r)?;
                let body = recursive_expr_decoder_mutant(r)?;
                let non_dep = r.bool()?;
                Ok(Expr::let_e(decl_name, type_, value, body, non_dep))
            }
            EXPR_LIT_NAT => {
                let count = r.u64()?;
                let mut limbs = Vec::new();
                for _ in 0..count {
                    limbs.push(r.u64()?);
                }
                let lit = NatLit::from_limbs_le(limbs.clone());
                if lit.limbs_le() != limbs.as_slice() {
                    return Err(r.err_public("non-normalized nat literal limbs"));
                }
                Ok(Expr::lit(Literal::Nat(lit)))
            }
            EXPR_LIT_STR => Ok(Expr::lit(Literal::Str(r.str()?.to_string()))),
            EXPR_MDATA => {
                let data = KVMap::read_body(r)?;
                let expr = recursive_expr_decoder_mutant(r)?;
                Ok(Expr::mdata(data, expr))
            }
            EXPR_PROJ => {
                let struct_name = Name::read_body(r)?;
                let idx = r.u64()?;
                let expr = recursive_expr_decoder_mutant(r)?;
                Ok(Expr::proj(struct_name, idx, expr))
            }
            _ => Err(r.err_public("unknown expr tag")),
        }
    }

    /// Decode a schema-headed artifact with one of the recursive mutants, mirroring
    /// [`Canonical::from_canonical_bytes`] exactly apart from the reader it calls.
    fn decode_with_mutant_level(bytes: &[u8]) -> Result<Level, CanonError> {
        let mut r = CanonReader::new(bytes);
        r.expect_schema(SCHEMA_LEVEL)?;
        let value = recursive_level_decoder_mutant(&mut r)?;
        r.finish()?;
        Ok(value)
    }

    fn decode_with_mutant_expr(bytes: &[u8]) -> Result<Expr, CanonError> {
        let mut r = CanonReader::new(bytes);
        r.expect_schema(SCHEMA_EXPR)?;
        let value = recursive_expr_decoder_mutant(&mut r)?;
        r.finish()?;
        Ok(value)
    }

    /// Deterministic value generator (LCG — no external randomness, D1).
    struct Gen(u64);

    impl Gen {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            self.0
        }

        fn range(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }

        fn name(&mut self, depth: u32) -> Name {
            if depth == 0 || self.range(4) == 0 {
                return Name::anonymous();
            }
            let pre = self.name(depth - 1);
            if self.range(2) == 0 {
                Name::str(pre, format!("c{}", self.range(20)))
            } else {
                Name::num(pre, self.range(1000))
            }
        }

        fn level(&mut self, depth: u32) -> Level {
            if depth == 0 {
                return match self.range(3) {
                    0 => Level::zero(),
                    1 => Level::param(self.name(2)),
                    _ => Level::mvar(LMVarId(self.name(2))),
                };
            }
            match self.range(4) {
                0 => self.level(depth - 1).succ().expect("shallow"),
                1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                2 => Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
                _ => self.level(0),
            }
        }

        fn expr(&mut self, depth: u32) -> Expr {
            if depth == 0 {
                return match self.range(5) {
                    0 => Expr::bvar(self.range(64) as u32).expect("small"),
                    1 => Expr::fvar(FVarId(self.name(2))),
                    2 => Expr::sort(self.level(1)),
                    3 => Expr::lit(Literal::Nat(NatLit::from_u64(self.next()))),
                    _ => Expr::const_(self.name(2), vec![self.level(1)]),
                };
            }
            match self.range(6) {
                0 => Expr::app(self.expr(depth - 1), self.expr(depth - 1)),
                1 => Expr::lam(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    BinderInfo::Implicit,
                ),
                2 => Expr::forall_e(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    BinderInfo::Default,
                ),
                3 => Expr::let_e(
                    self.name(1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    self.expr(depth - 1),
                    self.range(2) == 0,
                ),
                4 => Expr::proj(self.name(2), self.range(8), self.expr(depth - 1)),
                _ => Expr::mdata(KVMap::new(), self.expr(depth - 1)),
            }
        }
    }

    #[test]
    fn name_round_trip_property() {
        let mut generator = Gen(1);
        for _ in 0..200 {
            let name = generator.name(6);
            let bytes = name.to_canonical_bytes();
            assert_eq!(
                Name::from_canonical_bytes(&bytes).expect("round-trip"),
                name
            );
        }
    }

    #[test]
    fn level_round_trip_property() {
        let mut generator = Gen(2);
        for _ in 0..200 {
            let level = generator.level(4);
            let bytes = level.to_canonical_bytes();
            assert_eq!(
                Level::from_canonical_bytes(&bytes).expect("round-trip"),
                level
            );
        }
    }

    #[test]
    fn expr_round_trip_property() {
        let mut generator = Gen(3);
        for _ in 0..100 {
            let expr = generator.expr(4);
            let bytes = expr.to_canonical_bytes();
            let back = Expr::from_canonical_bytes(&bytes).expect("round-trip");
            assert_eq!(back, expr);
            assert_eq!(back.data(), expr.data(), "observables survive the trip");
        }
    }

    #[test]
    fn iterative_encoders_cover_every_level_and_expr_constructor() {
        let n = Name::str(Name::anonymous(), "n");
        let zero = Level::zero();
        let param = Level::param(n.clone());
        let mvar_level = Level::mvar(LMVarId(n.clone()));
        let levels = vec![
            zero.clone(),
            zero.clone().succ().expect("packs"),
            Level::max(param.clone(), zero.clone()).expect("packs"),
            Level::imax(mvar_level.clone(), param.clone()).expect("packs"),
            param.clone(),
            mvar_level.clone(),
        ];
        for level in levels {
            let bytes = level.to_canonical_bytes();
            let decoded = Level::from_canonical_bytes(&bytes).expect("level round-trip");
            assert_eq!(decoded.to_canonical_bytes(), bytes);
        }

        let leaf = Expr::bvar(0).expect("small");
        let mut metadata = KVMap::new();
        metadata.insert(n.clone(), DataValue::OfBool(true));
        let mut expressions = vec![
            leaf.clone(),
            Expr::fvar(FVarId(n.clone())),
            Expr::mvar(MVarId(n.clone())),
            Expr::sort(param.clone()),
            Expr::const_(n.clone(), vec![param.clone(), mvar_level]),
            Expr::app(leaf.clone(), leaf.clone()),
            Expr::let_e(n.clone(), leaf.clone(), leaf.clone(), leaf.clone(), true),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 2]))),
            Expr::lit(Literal::Str("value".to_string())),
            Expr::mdata(metadata, leaf.clone()),
            Expr::proj(n.clone(), 3, leaf.clone()),
        ];
        for info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            expressions.push(Expr::lam(n.clone(), leaf.clone(), leaf.clone(), info));
            expressions.push(Expr::forall_e(n.clone(), leaf.clone(), leaf.clone(), info));
        }
        for expr in expressions {
            let bytes = expr.to_canonical_bytes();
            let decoded = Expr::from_canonical_bytes(&bytes).expect("expr round-trip");
            assert_eq!(decoded.to_canonical_bytes(), bytes);
            assert_eq!(decoded.data(), expr.data());
        }
    }

    #[test]
    fn iterative_encoders_match_the_prechange_recursive_grammar() {
        let base = Name::str(Name::anonymous(), "Lean");
        let names = [
            Name::anonymous(),
            base.clone(),
            Name::num(base.clone(), 17),
            Name::num_overflowing(base.clone(), u64::MAX),
        ];
        for name in &names {
            assert_eq!(
                name.to_canonical_bytes(),
                prechange_bytes(SCHEMA_NAME, |writer| prechange_name_body(name, writer))
            );
        }

        let zero = Level::zero();
        let param = Level::param(base.clone());
        let mvar_level = Level::mvar(LMVarId(Name::num(base.clone(), 3)));
        let levels = [
            zero.clone(),
            zero.clone().succ().expect("shallow level"),
            Level::max(param.clone(), mvar_level.clone()).expect("shallow level"),
            Level::imax(mvar_level.clone(), param.clone()).expect("shallow level"),
            param.clone(),
            mvar_level.clone(),
        ];
        for level in &levels {
            assert_eq!(
                level.to_canonical_bytes(),
                prechange_bytes(SCHEMA_LEVEL, |writer| prechange_level_body(level, writer))
            );
        }

        let leaf = Expr::bvar(7).expect("small bvar");
        let mut metadata = KVMap::new();
        metadata.insert(base.clone(), DataValue::OfString("value".to_string()));
        metadata.insert(Name::num(base.clone(), 1), DataValue::OfBool(true));
        metadata.insert(
            Name::num(base.clone(), 2),
            DataValue::OfName(Name::str(base.clone(), "Meta")),
        );
        metadata.insert(Name::num(base.clone(), 3), DataValue::OfNat(42));
        metadata.insert(Name::num(base.clone(), 4), DataValue::OfInt(-7));
        metadata.insert(
            Name::num(base.clone(), 5),
            DataValue::OfSyntax(SyntaxHandle(9)),
        );

        let mut expressions = vec![
            leaf.clone(),
            Expr::fvar(FVarId(base.clone())),
            Expr::mvar(MVarId(Name::num(base.clone(), 6))),
            Expr::sort(param.clone()),
            Expr::const_(base.clone(), vec![param.clone(), mvar_level]),
            Expr::app(leaf.clone(), Expr::sort(zero)),
            Expr::let_e(base.clone(), leaf.clone(), leaf.clone(), leaf.clone(), true),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![1, 2]))),
            Expr::lit(Literal::Str("text".to_string())),
            Expr::mdata(metadata, leaf.clone()),
            Expr::proj(base.clone(), 3, leaf.clone()),
        ];
        for binder_info in [
            BinderInfo::Default,
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            expressions.push(Expr::lam(
                base.clone(),
                leaf.clone(),
                leaf.clone(),
                binder_info,
            ));
            expressions.push(Expr::forall_e(
                base.clone(),
                leaf.clone(),
                leaf.clone(),
                binder_info,
            ));
        }
        for expr in &expressions {
            assert_eq!(
                expr.to_canonical_bytes(),
                prechange_bytes(SCHEMA_EXPR, |writer| prechange_expr_body(expr, writer))
            );
        }

        let mut generator = Gen(0x6a09_e667_f3bc_c909);
        for sample in 0..256 {
            let name = generator.name(6);
            assert_eq!(
                name.to_canonical_bytes(),
                prechange_bytes(SCHEMA_NAME, |writer| prechange_name_body(&name, writer)),
                "Name sample {sample}"
            );

            let level = generator.level(5);
            assert_eq!(
                level.to_canonical_bytes(),
                prechange_bytes(SCHEMA_LEVEL, |writer| prechange_level_body(&level, writer)),
                "Level sample {sample}"
            );

            let expr = generator.expr(4);
            assert_eq!(
                expr.to_canonical_bytes(),
                prechange_bytes(SCHEMA_EXPR, |writer| prechange_expr_body(&expr, writer)),
                "Expr sample {sample}"
            );
        }
    }

    #[test]
    fn kvmap_round_trip_preserves_order() {
        let mut map = KVMap::new();
        map.insert(Name::str(Name::anonymous(), "b"), DataValue::OfNat(2));
        map.insert(Name::str(Name::anonymous(), "a"), DataValue::OfBool(true));
        map.insert(
            Name::str(Name::anonymous(), "s"),
            DataValue::OfSyntax(SyntaxHandle(7)),
        );
        let bytes = map.to_canonical_bytes();
        let back = KVMap::from_canonical_bytes(&bytes).expect("round-trip");
        assert_eq!(back, map);
        // Exact order, every position — not just the first entry.
        assert_eq!(
            back.entries()
                .iter()
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>(),
            map.entries()
                .iter()
                .map(|(k, _)| k.clone())
                .collect::<Vec<_>>(),
        );
    }

    /// The two KVMap views, asserted in **both** directions. Checking only the
    /// permissive side of an ordering claim proves nothing: a codec that sorted its
    /// entries would still round-trip, and a "set" digest that ignored content would
    /// still be order-independent.
    #[test]
    fn the_ordered_encoding_is_order_sensitive_and_the_set_projection_is_not() {
        let pairs = [
            (Name::str(Name::anonymous(), "b"), DataValue::OfNat(2)),
            (Name::str(Name::anonymous(), "a"), DataValue::OfBool(true)),
            (
                Name::str(Name::anonymous(), "s"),
                DataValue::OfSyntax(SyntaxHandle(7)),
            ),
        ];
        let build = |order: [usize; 3]| {
            let mut map = KVMap::new();
            for i in order {
                map.insert(pairs[i].0.clone(), pairs[i].1.clone());
            }
            map
        };
        let forward = build([0, 1, 2]);
        let permutations = [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];

        for order in permutations {
            let other = build(order);
            // Same options by every observable lookup — this is what makes the two
            // requirements below a genuine tension rather than a distinction on paper.
            for (key, _) in &pairs {
                assert_eq!(
                    forward.find(key),
                    other.find(key),
                    "{order:?} changed a lookup"
                );
            }

            // SEQUENCE DIRECTION: insertion order IS the value for an ordered assoc
            // list, so the canonical encoding must separate permutations. If this ever
            // passes by accident, someone has "canonicalized" the codec by sorting and
            // silently merged two distinct upstream KVMap values into one encoding.
            assert_ne!(
                forward.to_canonical_bytes(),
                other.to_canonical_bytes(),
                "the ordered encoding lost order under {order:?}"
            );

            // SET DIRECTION: the projection must NOT separate them.
            assert_eq!(
                kvmap_canonical_set_bytes(&forward),
                kvmap_canonical_set_bytes(&other),
                "the set projection kept order under {order:?}"
            );
        }

        // The projection still separates genuinely different sets — order-independence
        // must not be bought by dropping content.
        let mut different_value = KVMap::new();
        different_value.insert(pairs[0].0.clone(), DataValue::OfNat(3));
        different_value.insert(pairs[1].0.clone(), pairs[1].1.clone());
        different_value.insert(pairs[2].0.clone(), pairs[2].1.clone());
        assert_ne!(
            kvmap_canonical_set_bytes(&forward),
            kvmap_canonical_set_bytes(&different_value)
        );

        // And the two views are never the same bytes, so a preimage under one can never
        // be replayed as a preimage under the other.
        let projected = kvmap_canonical_set_bytes(&forward).expect("unique keys project");
        assert_ne!(forward.to_canonical_bytes(), projected);
        assert!(
            projected.starts_with(&{
                let mut w = CanonWriter::new();
                w.schema(SCHEMA_KVMAP_SET);
                w.into_bytes()
            }),
            "the projection must carry its own schema header"
        );

        // A DUPLICATE-KEYED MAP HAS NO SET VIEW, and the projection must say so rather
        // than answer. Two maps that upstream's own `eqv` separates would otherwise land
        // on identical bytes under any first-match-wins rule — a collision inside an
        // identity function, which is the franken_lean-f6br defect class.
        let shadowed = KVMap::from_entries(vec![
            (pairs[0].0.clone(), pairs[0].1.clone()),
            (pairs[0].0.clone(), DataValue::OfNat(99)),
        ]);
        let visible_only = KVMap::from_entries(vec![(pairs[0].0.clone(), pairs[0].1.clone())]);
        assert_eq!(
            shadowed.find(&pairs[0].0),
            visible_only.find(&pairs[0].0),
            "the two differ only in an entry that lookup cannot reach"
        );
        assert_ne!(
            shadowed.to_canonical_bytes(),
            visible_only.to_canonical_bytes(),
            "the ordered encoding must keep them apart"
        );
        assert_eq!(
            kvmap_canonical_set_bytes(&shadowed),
            None,
            "a map with duplicate keys must be refused a set view, not silently collapsed \
             onto the projection of the map without the shadowed entry"
        );
        assert!(kvmap_canonical_set_bytes(&visible_only).is_some());
    }

    /// Duplicate keys are representable, preserved, and round-trip exactly (bead
    /// franken_lean-l84f). This replaces the old refusal from bead fln-1f8v rather than
    /// deleting its case: fln-1f8v was right that one value may have exactly one
    /// encoding, and wrong that duplicates were the cause — the decoder folding them
    /// through `insert` was. So the canonicality law it defended is asserted here on the
    /// larger value space, which is the part that must not regress.
    #[test]
    fn duplicate_kvmap_keys_round_trip_exactly_and_stay_canonical() {
        let key = Name::str(Name::anonymous(), "k");
        let other = Name::str(Name::anonymous(), "other");
        // The exact fixture measured against the pinned toolchain, so our behaviour is
        // pinned to observed Reference behaviour rather than to my reading of it.
        let dup = KVMap::from_entries(vec![
            (key.clone(), DataValue::OfNat(1)),
            (key.clone(), DataValue::OfNat(2)),
            (other.clone(), DataValue::OfBool(true)),
        ]);

        // Round-trip preserves both entries, in order, byte-for-byte.
        let bytes = dup.to_canonical_bytes();
        let back = KVMap::from_canonical_bytes(&bytes).expect("duplicates are legal input");
        assert_eq!(back, dup, "the shadowed entry did not survive the decode");
        assert_eq!(back.entries(), dup.entries());
        assert_eq!(back.to_canonical_bytes(), bytes, "re-encode drifted");

        // Reference-observed semantics (pin v4.32.0): first match wins, size counts
        // entries, erase removes every entry for the key, insert replaces the FIRST match
        // in place and leaves the shadowed one.
        assert_eq!(back.find(&key), Some(&DataValue::OfNat(1)));
        assert_eq!(back.len(), 3);
        let mut erased = back.clone();
        erased.erase(&key);
        assert_eq!(erased.entries(), &[(other, DataValue::OfBool(true))]);
        let mut inserted = back.clone();
        inserted.insert(key.clone(), DataValue::OfNat(9));
        assert_eq!(
            inserted.entries()[0].1,
            DataValue::OfNat(9),
            "insert must replace the first match"
        );
        assert_eq!(
            inserted.entries()[1].1,
            DataValue::OfNat(2),
            "insert must not fold the shadowed entry"
        );

        // CANONICALITY ON THE LARGER SPACE — the law fln-1f8v was protecting. Distinct
        // entry lists must not share an encoding, including lists that differ only in a
        // shadowed value or in the order of two same-key entries.
        let variants = [
            vec![
                (key.clone(), DataValue::OfNat(1)),
                (key.clone(), DataValue::OfNat(2)),
            ],
            vec![
                (key.clone(), DataValue::OfNat(2)),
                (key.clone(), DataValue::OfNat(1)),
            ],
            vec![
                (key.clone(), DataValue::OfNat(1)),
                (key.clone(), DataValue::OfNat(3)),
            ],
            vec![(key.clone(), DataValue::OfNat(1))],
        ];
        let mut seen = std::collections::BTreeMap::new();
        for entries in variants {
            let map = KVMap::from_entries(entries);
            let encoded = map.to_canonical_bytes();
            assert_eq!(
                KVMap::from_canonical_bytes(&encoded).expect("round-trip"),
                map
            );
            if let Some(previous) = seen.insert(encoded, map.clone()) {
                fixture_panic!("two distinct maps share an encoding: {previous:?} and {map:?}");
            }
        }
    }

    #[test]
    fn encoding_is_injective_on_a_corpus() {
        // One encoding per value, one value per encoding: no two distinct generated
        // values share bytes.
        let mut generator = Gen(4);
        let mut seen = std::collections::BTreeMap::new();
        for _ in 0..200 {
            let expr = generator.expr(3);
            let bytes = expr.to_canonical_bytes();
            if let Some(previous) = seen.insert(bytes, expr.clone()) {
                assert_eq!(previous, expr, "distinct values shared an encoding");
            }
        }
    }

    #[test]
    fn malformed_inputs_are_typed_errors_never_panics() {
        let cases: [&[u8]; 5] = [
            b"",
            b"\x01",
            b"\xff\xff\xff\xff\xff\xff\xff\xff",
            // Valid schema header for Name, then garbage.
            &{
                let mut w = CanonWriter::new();
                w.schema(SCHEMA_NAME);
                w.u64(1);
                w.u8(9); // unknown component tag
                w.into_bytes()
            },
            // Huge declared length with no bytes behind it.
            &{
                let mut w = CanonWriter::new();
                w.schema(SCHEMA_NAME);
                w.u64(u64::MAX);
                w.into_bytes()
            },
        ];
        for bytes in cases {
            assert!(Name::from_canonical_bytes(bytes).is_err());
            assert!(Expr::from_canonical_bytes(bytes).is_err());
        }
        // Trailing garbage after a valid value is non-canonical.
        let mut bytes = Name::anonymous().to_canonical_bytes();
        bytes.push(0);
        assert!(matches!(
            Name::from_canonical_bytes(&bytes),
            Err(CanonError {
                what: "trailing bytes after value",
                ..
            })
        ));
        // Non-normalized nat limbs are rejected (two encodings of one value).
        let mut w = CanonWriter::new();
        w.schema(SCHEMA_EXPR);
        w.u8(super::EXPR_LIT_NAT);
        w.u64(2);
        w.u64(5);
        w.u64(0); // trailing zero limb
        assert!(Expr::from_canonical_bytes(&w.into_bytes()).is_err());
    }

    #[test]
    fn schema_headers_are_checked() {
        let name_bytes = Name::anonymous().to_canonical_bytes();
        assert!(Level::from_canonical_bytes(&name_bytes).is_err());
    }

    /// franken_lean-fnj: a deeply nested hostile encoding must decode to a TYPED
    /// error, never a stack-overflow abort. Run on a deliberately small (1 MiB)
    /// stack — a recursive decoder would `SIGABRT` here; the iterative one returns
    /// `Err`. Two properties in one safe check: (a) `.join()` returning `Ok` proves
    /// no abort occurred; (b) the error is `input truncated`, not a depth cap,
    /// proving the decoder walked all 2,000,000 tags rather than bailing at some
    /// artificial limit that would false-reject a legitimately deep olean. The tag
    /// chains carry no operands, so no deep tree is ever built (that would recurse
    /// on `Drop` — a separate concern tracked in franken_lean-fnj).
    #[test]
    fn deeply_nested_input_is_a_typed_error_not_a_stack_overflow() {
        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                let mut expr_bytes = CanonWriter::new();
                expr_bytes.schema(SCHEMA_EXPR);
                let mut expr_bytes = expr_bytes.into_bytes();
                expr_bytes.extend(std::iter::repeat_n(super::EXPR_APP, 2_000_000));
                let expr_err = Expr::from_canonical_bytes(&expr_bytes)
                    .expect_err("truncated deep App chain must be a typed error");
                assert_eq!(expr_err.what, "input truncated", "no artificial depth cap");

                let mut level_bytes = CanonWriter::new();
                level_bytes.schema(SCHEMA_LEVEL);
                let mut level_bytes = level_bytes.into_bytes();
                level_bytes.extend(std::iter::repeat_n(super::LEVEL_MAX, 2_000_000));
                let level_err = Level::from_canonical_bytes(&level_bytes)
                    .expect_err("truncated deep Max chain must be a typed error");
                assert_eq!(level_err.what, "input truncated", "no artificial depth cap");
            })
            .expect("spawn decoder thread")
            .join();
        assert!(
            outcome.is_ok(),
            "decoding deep hostile input aborted the thread (stack overflow) instead of erroring"
        );
    }

    /// franken_lean-canon-stack-safe-drop-6gy: exercise valid deep decode,
    /// byte-identical re-encoding, shared-root release, and partial-error cleanup
    /// in a sacrificial process whose worker has a 1 MiB stack.  The outer test
    /// remains alive if a recursive mutation aborts the child.
    #[test]
    fn deep_valid_lifecycle_is_stack_safe_in_subprocess() {
        const CHILD: &str = "FLN_CANON_LIFECYCLE_CHILD";
        const DEPTH: &str = "FLN_CANON_LIFECYCLE_DEPTH";
        const RUNS: &str = "FLN_CANON_LIFECYCLE_RUNS";
        const ITERATION: &str = "FLN_CANON_LIFECYCLE_ITERATION";
        const MUTANT: &str = "FLN_CANON_LIFECYCLE_MUTANT";
        const NAME_DEPTH: &str = "FLN_CANON_LIFECYCLE_NAME_DEPTH";

        if std::env::var_os(CHILD).is_some() {
            let depth = std::env::var(DEPTH)
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(100_000);
            let iteration = std::env::var(ITERATION).unwrap_or_else(|_| "0".to_string());
            let mutant = std::env::var(MUTANT).ok();
            let name_depth = std::env::var(NAME_DEPTH)
                .ok()
                .and_then(|value| value.parse::<usize>().ok())
                .unwrap_or(depth.min(100_000));
            let outcome = std::thread::Builder::new()
                .name("canon-lifecycle-probe".to_string())
                .stack_size(1024 * 1024)
                .spawn(move || {
                    let mut level = Level::zero();
                    for _ in 0..depth {
                        level = level.succ().expect("depth is below the level covenant");
                    }
                    if mutant.as_deref() == Some("recursive-level-encoder") {
                        recursive_level_encoder_mutant(&level, &mut CanonWriter::new());
                        fixture_panic!("recursive Level encoder mutation unexpectedly survived");
                    }
                    let level_bytes = level.to_canonical_bytes();
                    if mutant.as_deref() == Some("recursive-level-decoder") {
                        let _ = decode_with_mutant_level(&level_bytes);
                        fixture_panic!("recursive Level decoder mutation unexpectedly survived");
                    }
                    let decoded_level = Level::from_canonical_bytes(&level_bytes)
                        .expect("deep valid level decodes");
                    assert_eq!(decoded_level.to_canonical_bytes(), level_bytes);

                    let level_clone = decoded_level.clone();
                    drop_pair_concurrently(decoded_level, level_clone);

                    let leaf = Expr::bvar(0).expect("small bvar");
                    let mut expr = leaf.clone();
                    for _ in 0..depth {
                        expr = Expr::app(expr, leaf.clone());
                    }
                    if mutant.as_deref() == Some("recursive-expr-encoder") {
                        recursive_expr_encoder_mutant(&expr, &mut CanonWriter::new());
                        fixture_panic!("recursive Expr encoder mutation unexpectedly survived");
                    }
                    let expr_bytes = expr.to_canonical_bytes();
                    if mutant.as_deref() == Some("recursive-expr-decoder") {
                        let _ = decode_with_mutant_expr(&expr_bytes);
                        fixture_panic!("recursive Expr decoder mutation unexpectedly survived");
                    }
                    let decoded_expr = Expr::from_canonical_bytes(&expr_bytes)
                        .expect("deep valid expression decodes");
                    assert_eq!(decoded_expr.to_canonical_bytes(), expr_bytes);

                    let expr_clone = decoded_expr.clone();
                    drop_pair_concurrently(decoded_expr, expr_clone);

                    // Deep names are recursive payloads of multiple Expr/Level
                    // constructors. Their encoding and final Arc release must not
                    // punch a hidden recursive hole through the outer lifecycle.
                    let mut deep_name = Name::anonymous();
                    for _ in 0..name_depth {
                        deep_name = Name::str(deep_name, "n");
                    }
                    let name_bytes = deep_name.to_canonical_bytes();
                    let decoded_name = Name::from_canonical_bytes(&name_bytes)
                        .expect("deep valid name decodes");
                    assert_eq!(decoded_name.to_canonical_bytes(), name_bytes);
                    let named_expr = Expr::const_(deep_name.clone(), Vec::new());
                    let named_expr_bytes = named_expr.to_canonical_bytes();
                    assert_eq!(
                        Expr::from_canonical_bytes(&named_expr_bytes)
                            .expect("deep name in Expr decodes")
                            .to_canonical_bytes(),
                        named_expr_bytes
                    );
                    let named_level = Level::param(deep_name.clone());
                    let named_level_bytes = named_level.to_canonical_bytes();
                    assert_eq!(
                        Level::from_canonical_bytes(&named_level_bytes)
                            .expect("deep name in Level decodes")
                            .to_canonical_bytes(),
                        named_level_bytes
                    );
                    drop(named_expr);
                    drop(named_level);
                    let decoded_name_clone = decoded_name.clone();
                    drop_pair_concurrently(decoded_name, decoded_name_clone);
                    drop(deep_name);

                    // A later missing child must clean up the already-built deep
                    // first child without recursively unwinding its Arc chain.
                    let mut partial_level = CanonWriter::new();
                    partial_level.schema(SCHEMA_LEVEL);
                    partial_level.u8(LEVEL_MAX);
                    level.write_body(&mut partial_level);
                    assert_eq!(
                        Level::from_canonical_bytes(&partial_level.into_bytes())
                            .expect_err("second Max child is absent")
                            .what,
                        "input truncated"
                    );

                    let mut partial_expr = CanonWriter::new();
                    partial_expr.schema(SCHEMA_EXPR);
                    partial_expr.u8(EXPR_APP);
                    expr.write_body(&mut partial_expr);
                    assert_eq!(
                        Expr::from_canonical_bytes(&partial_expr.into_bytes())
                            .expect_err("second App child is absent")
                            .what,
                        "input truncated"
                    );

                    let level_hash = crate::domain::hash(
                        crate::domain::Domain::Fixture,
                        &level_bytes,
                    );
                    let expr_hash =
                        crate::domain::hash(crate::domain::Domain::Fixture, &expr_bytes);
                    drop(expr);
                    drop(level);
                    drop(leaf);

                    // Recovery after both partial failures uses the same real codec.
                    let recovery = Expr::bvar(7).expect("small").to_canonical_bytes();
                    Expr::from_canonical_bytes(&recovery).expect("shallow recovery decode");

                    println!(
                        "{{\"schema\":\"fln.e2e.canon-lifecycle\",\"version\":1,\"bead\":\"franken_lean-canon-stack-safe-drop-6gy\",\"invariant\":\"FL-INV-07\",\"scenario\":\"deep-valid-lifecycle\",\"iteration\":{iteration},\"depth\":{depth},\"name_depth\":{name_depth},\"stack_bytes\":1048576,\"level_bytes\":{},\"expr_bytes\":{},\"level_hash\":\"{}\",\"expr_hash\":\"{}\",\"expected\":\"pass\",\"actual\":\"pass\",\"cleanup\":\"complete\",\"final_state\":\"recovery-decoded\"}}",
                        level_bytes.len(),
                        expr_bytes.len(),
                        level_hash,
                        expr_hash,
                    );
                })
                .expect("spawn bounded-stack probe")
                .join();
            assert!(outcome.is_ok(), "bounded-stack lifecycle worker panicked");
            return;
        }

        let runs = std::env::var(RUNS)
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(1);
        let executable = std::env::current_exe().expect("locate current test binary");
        for iteration in 0..runs {
            let output = std::process::Command::new(&executable)
                .arg("--exact")
                .arg("canon::tests::deep_valid_lifecycle_is_stack_safe_in_subprocess")
                .arg("--nocapture")
                .env(CHILD, "1")
                .env(ITERATION, iteration.to_string())
                .output()
                .expect("launch sacrificial lifecycle process");
            assert!(
                output.status.success(),
                "lifecycle child {iteration} failed: status={:?}\nstdout={}\nstderr={}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            print!("{}", String::from_utf8_lossy(&output.stdout));
        }
    }

    /// Mutation kill for the DECODE side (bead franken_lean-fnj).
    ///
    /// `deeply_nested_input_is_a_typed_error_not_a_stack_overflow` and the deep
    /// valid-lifecycle probe both pass today, but a passing test proves nothing
    /// about a hazard unless it is known to fail when the hazard returns. These
    /// children run the byte-identical RECURSIVE readers over the same deep valid
    /// artifacts; each must die of a stack overflow in its own process. A control
    /// child with no mutation must succeed on identical input, so a failure here
    /// cannot be blamed on the harness.
    ///
    /// The encoder mutants (`recursive-{level,expr}-encoder`) are killed by
    /// `scripts/e2e/canon_lifecycle.sh`; these decoder mutants are killed here as
    /// well so the guard is part of the `cargo test` gate rather than only the lane.
    #[test]
    fn recursive_decoder_mutants_die_where_the_iterative_readers_survive() {
        // Deep enough that a recursive reader cannot fit in the probe's 1 MiB
        // worker stack, small enough to keep three child processes quick.
        const DEPTH: &str = "50000";
        let executable = std::env::current_exe().expect("locate current test binary");
        let run = |mutant: Option<&str>| {
            let mut command = std::process::Command::new(&executable);
            command
                .arg("--exact")
                .arg("canon::tests::deep_valid_lifecycle_is_stack_safe_in_subprocess")
                .arg("--nocapture")
                .env("FLN_CANON_LIFECYCLE_CHILD", "1")
                .env("FLN_CANON_LIFECYCLE_DEPTH", DEPTH)
                .env("FLN_CANON_LIFECYCLE_NAME_DEPTH", "1024");
            if let Some(mutant) = mutant {
                command.env("FLN_CANON_LIFECYCLE_MUTANT", mutant);
            }
            command
                .output()
                .expect("launch sacrificial decoder process")
        };

        let control = run(None);
        assert!(
            control.status.success(),
            "control child failed on unmutated input: status={:?}\nstderr={}",
            control.status,
            String::from_utf8_lossy(&control.stderr),
        );

        for mutant in ["recursive-level-decoder", "recursive-expr-decoder"] {
            let killed = run(Some(mutant));
            assert!(
                !killed.status.success(),
                "{mutant} survived: a recursive decoder must not decode a deep artifact"
            );
            // The kill must be the intended one. A panic from the "unexpectedly
            // survived" guard, an unrelated assertion, or an early exit would also
            // be non-success, and none of those prove stack exhaustion.
            let stderr = String::from_utf8_lossy(&killed.stderr);
            assert!(
                stderr.contains("stack overflow"),
                "{mutant} died for the wrong reason: status={:?}\nstderr={stderr}",
                killed.status,
            );
        }
    }

    /// Every prefix of a valid artifact is malformed input, and malformed input is
    /// a typed error — never a panic, an abort, or a silent success (D8, FL-INV-07,
    /// bead franken_lean-fnj). A panic anywhere in the sweep fails this test by
    /// propagating, so "does not panic" needs no separate assertion.
    #[test]
    fn every_truncation_of_a_valid_artifact_is_a_typed_error() {
        let mut generator = Gen(0x5eed_1234);
        let mut checked = 0usize;
        for _ in 0..24 {
            let name = generator.name(4);
            let level = generator.level(3);
            let expr = generator.expr(3);

            for (label, bytes, decode_artifact) in [
                (
                    "name",
                    name.to_canonical_bytes(),
                    (|b: &[u8]| Name::from_canonical_bytes(b).map(|_| ()))
                        as fn(&[u8]) -> Result<(), CanonError>,
                ),
                (
                    "level",
                    level.to_canonical_bytes(),
                    (|b: &[u8]| Level::from_canonical_bytes(b).map(|_| ()))
                        as fn(&[u8]) -> Result<(), CanonError>,
                ),
                (
                    "expr",
                    expr.to_canonical_bytes(),
                    (|b: &[u8]| Expr::from_canonical_bytes(b).map(|_| ()))
                        as fn(&[u8]) -> Result<(), CanonError>,
                ),
            ] {
                assert!(
                    decode_artifact(&bytes).is_ok(),
                    "{label} fixture must decode intact"
                );
                for cut in 0..bytes.len() {
                    let error = decode_artifact(&bytes[..cut])
                        .expect_err("a truncated artifact must never decode as a value");
                    assert!(
                        !error.what.is_empty(),
                        "{label} truncated at {cut} produced an unlabelled error"
                    );
                    checked += 1;
                }
            }
        }
        assert!(checked > 1_000, "the sweep must cover every field boundary");
    }

    /// Build a well-formed artifact big enough to outrun a small budget: a right
    /// spine of `depth` applications over a shared leaf.
    fn app_spine(depth: usize) -> Expr {
        let leaf = Expr::bvar(0).expect("small");
        let mut expr = leaf.clone();
        for _ in 0..depth {
            expr = Expr::app(expr, leaf.clone());
        }
        expr
    }

    /// The criterion franken_lean-fnj could not close until fln-4zk8 existed:
    /// resource exhaustion surfaces through the typed inconclusive path, and never
    /// as acceptance or rejection (FL-INV-07).
    ///
    /// The artifact here is **valid** — the same bytes decode cleanly with room to
    /// work — so an outcome of `Malformed` would be a lie about the bytes, and an
    /// outcome of `Value` would mean the budget was not honoured.
    #[test]
    fn budget_exhaustion_on_a_valid_artifact_is_inconclusive_never_a_verdict() {
        let bytes = app_spine(5_000).to_canonical_bytes();

        let stopped = Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::new(u64::MAX, 64));
        match stopped {
            Outcome::Inconclusive(_) => {
                assert_eq!(
                    stop_of(&stopped),
                    (StructuralUnit::ProducedNodes, 64, 65),
                    "the trip reports its unit and what was spent"
                );
                assert_ne!(
                    stop_progress(&stopped),
                    "byte 0",
                    "the stop records where decoding reached"
                );
            }
            Outcome::Complete(Err(error)) => {
                fixture_panic!(
                    "a budget stop was rendered as a rejection about the bytes: {error:?}"
                )
            }
            Outcome::Complete(Ok(_)) => fixture_panic!("the budget was not honoured"),
            Outcome::InternalFault(fault) => {
                fixture_panic!("the decoder's own budget accounting broke: {fault:?}")
            }
        }

        // Same bytes, room to work: a real acceptance. The inconclusive outcome
        // above therefore said nothing about the artifact, which is the point.
        let allowed = decoded_value(Expr::from_canonical_bytes_budgeted(
            &bytes,
            DecodeBudget::unlimited(),
        ));
        assert_eq!(
            allowed.expect("the artifact is valid").to_canonical_bytes(),
            bytes
        );
    }

    /// The byte limit is charged on consumption, so it stops a large artifact part
    /// way through rather than pre-judging it by its length.
    #[test]
    fn the_input_byte_limit_stops_consumption_and_reports_the_offset() {
        let bytes = app_spine(2_000).to_canonical_bytes();
        let cap = 128;
        match Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::new(cap, u64::MAX)) {
            ref stopped @ Outcome::Inconclusive(_) => {
                let (unit, allowed, observed) = stop_of(stopped);
                assert_eq!(unit, StructuralUnit::InputBytes);
                assert_eq!(allowed, cap);
                assert!(observed > cap);
                let at: u64 = stop_progress(stopped)
                    .trim_start_matches("byte ")
                    .parse()
                    .expect("progress localizes to a byte offset");
                assert!(at <= cap, "no byte beyond the cap was consumed");
            }
            other => fixture_panic!("expected an inconclusive stop, got {other:?}"),
        }
    }

    /// The two outcomes must not collapse into each other. Malformed input under a
    /// generous budget is a rejection — a real verdict — and stays one.
    #[test]
    fn malformed_input_under_a_generous_budget_is_still_a_rejection() {
        let mut truncated = app_spine(4).to_canonical_bytes();
        truncated.truncate(truncated.len() - 1);
        match Expr::from_canonical_bytes_budgeted(&truncated, DecodeBudget::unlimited()) {
            Outcome::Complete(Err(error)) => assert_eq!(error.what, "input truncated"),
            other => fixture_panic!("a malformed artifact must be rejected, got {other:?}"),
        }

        // And a malformed prefix under a *tiny* byte budget is still a rejection if
        // the malformation is reached first: bytes never read are never spent.
        let mut w = CanonWriter::new();
        w.schema(SCHEMA_EXPR);
        w.u8(0xfe);
        let unknown_tag = w.into_bytes();
        match Expr::from_canonical_bytes_budgeted(&unknown_tag, DecodeBudget::new(u64::MAX, 8)) {
            Outcome::Complete(Err(error)) => assert_eq!(error.what, "unknown expr tag"),
            other => fixture_panic!("the malformation is reached first, got {other:?}"),
        }
    }

    /// A budget that fits changes nothing: same value, same bytes, same hash, same
    /// code path as the unbudgeted call.
    #[test]
    fn a_fitting_budget_decodes_identically_to_no_budget() {
        for depth in [0usize, 1, 7, 64] {
            let bytes = app_spine(depth).to_canonical_bytes();
            let unbudgeted = Expr::from_canonical_bytes(&bytes).expect("valid artifact");
            let budgeted = decoded_value(Expr::from_canonical_bytes_budgeted(
                &bytes,
                DecodeBudget::new(u64::MAX, u64::MAX),
            ))
            .expect("a fitting budget accepts");
            assert_eq!(unbudgeted, budgeted);
            assert_eq!(unbudgeted.hash(), budgeted.hash());
            assert_eq!(budgeted.to_canonical_bytes(), bytes);
        }
    }

    /// The budget reaches the payloads decoded by their own readers, not just the
    /// top-level term walk — otherwise a hostile `Name` chain or `KVMap` inside an
    /// otherwise small artifact would be unmetered.
    /// **The fln-8gz3 blocker is CLEARED** — this is the positive statement of the
    /// mapping it was waiting for (bead franken_lean-vui8).
    ///
    /// This test used to be a trigger: it matched `ResourceReason` and `BudgetLimit`
    /// exhaustively so that adding a variant to either would fail to compile here, with
    /// the reasoning attached, and tell whoever did it whether the blocker was cleared.
    /// It fired exactly as designed when `StructuralBudget` landed. What replaces it is
    /// the correspondence itself, kept as a total function so the taxonomy and the
    /// decoder's limits cannot drift apart again in either direction.
    ///
    /// The fold `Decoded<T>` -> `Outcome<Result<T, CanonError>>` is now expressible:
    /// `Value` to `Complete(Ok(..))`, `Malformed` to `Complete(Err(..))` — a real domain
    /// verdict about bytes, so it belongs inside the authoritative arm — and
    /// `Inconclusive(Exhausted)` to `Inconclusive(ResourceExhausted{ usage })` with the
    /// reason below, `allowed`/`observed` from the `Exhausted`, and `at` recorded through
    /// `Inconclusive::with_progress`. fln-8gz3 does that adoption; this only proves the
    /// vocabulary is there and says exactly one thing per limit.
    #[test]
    fn every_decode_budget_limit_maps_to_exactly_one_structural_unit() {
        // Total and exhaustive both ways: a new BudgetLimit must be given a unit here, and
        // a StructuralUnit that stops being reachable shows up in the coverage check below.
        fn unit_for(limit: BudgetLimit) -> StructuralUnit {
            match limit {
                BudgetLimit::InputBytes => StructuralUnit::InputBytes,
                BudgetLimit::ProducedNodes => StructuralUnit::ProducedNodes,
            }
        }

        let limits = [BudgetLimit::InputBytes, BudgetLimit::ProducedNodes];

        // Injective: two limits must never collapse onto one unit, or a caller cannot tell
        // which allowance to raise.
        let mut mapped = std::collections::BTreeSet::new();
        for limit in limits {
            let unit = unit_for(limit);
            assert!(
                mapped.insert(unit.as_str()),
                "two decode limits map onto {} — the distinction a retry needs is gone",
                unit.as_str()
            );
        }
        assert_eq!(mapped.len(), limits.len());

        // The units a decoder uses are a strict subset of the axis: ExpandedWeight belongs
        // to the term store (fln-49c), not to a byte decoder, and must NOT be reachable
        // from a BudgetLimit. Asserting the gap keeps the two adopters from quietly
        // borrowing each other's unit.
        assert!(!mapped.contains(StructuralUnit::ExpandedWeight.as_str()));
        assert_eq!(StructuralUnit::ALL.len(), 3);

        // Each unit renders as itself and nothing else, so a diagnostic cannot say
        // "memory" or "heartbeats" for a structural stop — the false-diagnostic problem
        // that made this bead necessary.
        for unit in StructuralUnit::ALL {
            let rendered = ResourceReason::StructuralBudget { unit };
            let mut writer = CanonWriter::new();
            write_resource(&mut writer, &rendered);
            let encoded = writer.into_bytes();
            let mut reader = CanonReader::new(&encoded);
            assert_eq!(
                read_resource(&mut reader).expect("round-trip"),
                rendered,
                "the {} reason did not survive the wire",
                unit.as_str()
            );
            assert!(!unit.as_str().contains("memory"));
            assert!(!unit.as_str().contains("heartbeat"));
        }

        // And the arm that never needed a taxonomy change still behaves: a malformed
        // decode is an authoritative domain rejection, not an inconclusive.
        let malformed: DecodeOutcome<Level> = Level::from_canonical_bytes_budgeted(
            b"not a canonical level",
            DecodeBudget::unlimited(),
        );
        assert!(matches!(malformed, Outcome::Complete(Err(_))));
        assert!(!is_inconclusive(&malformed));
    }

    #[test]
    fn the_budget_is_honoured_inside_nested_name_and_kvmap_payloads() {
        let mut deep_name = Name::anonymous();
        for index in 0..512 {
            deep_name = Name::num(deep_name, index);
        }
        let named = Expr::const_(deep_name.clone(), Vec::new()).to_canonical_bytes();
        assert!(
            is_inconclusive(&Expr::from_canonical_bytes_budgeted(
                &named,
                DecodeBudget::new(u64::MAX, 16)
            )),
            "a deep Name payload must be charged"
        );

        let mut map = KVMap::new();
        for index in 0..64 {
            map.insert(Name::num(Name::anonymous(), index), DataValue::OfNat(index));
        }
        let mdata = Expr::mdata(map, Expr::bvar(0).expect("small")).to_canonical_bytes();
        assert!(
            is_inconclusive(&Expr::from_canonical_bytes_budgeted(
                &mdata,
                DecodeBudget::new(u64::MAX, 16)
            )),
            "a KVMap payload must be charged"
        );

        // Both artifacts are valid: with room, they decode.
        assert!(Expr::from_canonical_bytes(&named).is_ok());
        assert!(Expr::from_canonical_bytes(&mdata).is_ok());
    }

    /// **The fold is behaviour-preserving at the boundary** (bead fln-8gz3): each of the
    /// three outcomes the old `Decoded` enum could report maps to exactly one `Outcome`
    /// arm with the same observable meaning, and the FL-INV-07 properties are now
    /// enforced by the shared type rather than restated here.
    ///
    /// What the fold *adds* is the cacheability axis, which `Decoded` had no way to
    /// express: a completed run is admissible whether its domain answer was acceptance or
    /// rejection, because "these bytes are not a well-formed artifact" is a durable fact
    /// about those bytes; a stop is refused, because nothing was learned.
    #[test]
    fn each_decoded_outcome_folds_to_one_outcome_arm_with_the_same_meaning() {
        let bytes = app_spine(200).to_canonical_bytes();

        // ACCEPTANCE -> Complete(Ok): authoritative, and cacheable.
        let accepted = Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::unlimited());
        assert!(matches!(accepted, Outcome::Complete(Ok(_))));
        assert_eq!(accepted.authority(), Authority::Authoritative);
        assert_eq!(accepted.cache_admission(), CacheAdmission::Admissible);

        // REJECTION -> Complete(Err): also authoritative and cacheable. A malformed
        // verdict is a real answer about the bytes, which is exactly why it belongs
        // inside the Complete arm rather than beside it.
        let rejected =
            Expr::from_canonical_bytes_budgeted(b"not an expr", DecodeBudget::unlimited());
        assert!(matches!(rejected, Outcome::Complete(Err(_))));
        assert_eq!(rejected.authority(), Authority::Authoritative);
        assert_eq!(rejected.cache_admission(), CacheAdmission::Admissible);

        // STOP -> Inconclusive: non-authoritative, NEVER cacheable, and unable to
        // masquerade as either of the two above.
        let stopped = Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::new(u64::MAX, 32));
        assert!(matches!(stopped, Outcome::Inconclusive(_)));
        assert_eq!(stopped.authority(), Authority::NonAuthoritative);
        assert_eq!(
            stopped.cache_admission(),
            CacheAdmission::Refused {
                authority: Authority::NonAuthoritative
            }
        );
        assert!(
            stopped.as_complete().is_none(),
            "a stop must not yield a domain result of either polarity"
        );
        assert_eq!(stop_of(&stopped).0, StructuralUnit::ProducedNodes);

        // The three are genuinely distinct outcomes over the SAME artifact, separated
        // only by the budget — so a caller can tell "invalid" from "too expensive to
        // judge", which is the distinction the whole three-valued design exists for.
        assert_ne!(
            std::mem::discriminant(&accepted),
            std::mem::discriminant(&stopped)
        );
        assert!(matches!(
            (&accepted, &rejected),
            (Outcome::Complete(Ok(_)), Outcome::Complete(Err(_)))
        ));
    }

    /// An exhausted decode must not be retryable into a verdict by accident: the
    /// stop carries what it cost, so a caller raises the budget deliberately.
    #[test]
    fn a_stop_reports_enough_to_retry_deliberately() {
        let bytes = app_spine(200).to_canonical_bytes();
        let first = Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::new(u64::MAX, 32));
        let (_, first_allowed, first_observed) = stop_of(&first);
        assert!(first_observed > first_allowed);

        // Raising the limit past what the first attempt reported is not enough by
        // itself — the stop reports the point of the trip, not the total cost — but
        // the artifact must eventually decode as the limit grows, and never flip to
        // a rejection on the way.
        let mut limit = first_allowed;
        let mut attempts = 0;
        loop {
            limit = limit.saturating_mul(4).max(4);
            attempts += 1;
            match Expr::from_canonical_bytes_budgeted(&bytes, DecodeBudget::new(u64::MAX, limit)) {
                Outcome::Complete(Ok(value)) => {
                    assert_eq!(value.to_canonical_bytes(), bytes);
                    break;
                }
                Outcome::Inconclusive(_) => {
                    assert!(attempts < 32, "budget growth did not converge")
                }
                Outcome::Complete(Err(error)) => {
                    fixture_panic!(
                        "raising a budget turned a valid artifact into a rejection: {error:?}"
                    )
                }
                Outcome::InternalFault(fault) => {
                    fixture_panic!("raising a budget broke the decoder's own accounting: {fault:?}")
                }
            }
        }
    }

    /// The last criterion of franken_lean-fnj, discharged against the budget surface
    /// built under fln-4zk8: **resource exhaustion on deep untrusted input surfaces
    /// only through the typed inconclusive path.**
    ///
    /// This could not be tested when fnj was written, because there was nothing to
    /// exhaust — every refusal the decoders could produce was a well-formedness
    /// rejection. All four prohibitions are checked, not just the happy one:
    ///
    /// * never a SIGABRT — the whole thing runs on a 1 MiB worker, and `.join()`
    ///   returning `Ok` is what proves no abort happened;
    /// * never a panic — a panic inside the worker fails the join;
    /// * never a rejection — the outcome is `Inconclusive`, and the SAME bytes under
    ///   an unlimited budget produce `Malformed` instead, so the two are genuinely
    ///   different answers rather than one relabelled;
    /// * never cacheable — an inconclusive outcome yields no value to cache, and
    ///   there is no conversion that could turn it into a verdict.
    ///
    /// And the constraint fnj sets: **no hard nesting cap**. A budget is a resource
    /// contract, not a depth limit, so a legitimately deep artifact still decodes
    /// when the caller is willing to pay for it — asserted here at depth 100_000,
    /// which a cap would have refused.
    #[test]
    fn deep_hostile_input_over_budget_is_inconclusive_never_a_verdict() {
        let outcome = std::thread::Builder::new()
            .stack_size(1024 * 1024)
            .spawn(|| {
                // The hostile shape: a compact stream of nesting tags with no
                // operands. 1e6 tags is far past any recursive decoder's stack and
                // far past a small budget.
                let mut hostile = CanonWriter::new();
                hostile.schema(SCHEMA_EXPR);
                let mut hostile = hostile.into_bytes();
                hostile.extend(std::iter::repeat_n(EXPR_APP, 1_000_000));

                // Under a tight budget the caller's limit is reached first.
                let stopped = Expr::from_canonical_bytes_budgeted(
                    &hostile,
                    DecodeBudget::new(u64::MAX, 1_000),
                );
                match stopped {
                    Outcome::Inconclusive(_) => {
                        let (unit, allowed, observed) = stop_of(&stopped);
                        assert_eq!(unit, StructuralUnit::ProducedNodes);
                        assert_eq!(allowed, 1_000);
                        assert!(observed > allowed, "a stop reports what it cost");
                    }
                    Outcome::Complete(Err(error)) => fixture_panic!(
                        "budget exhaustion was reported as a claim about the bytes: {error:?}"
                    ),
                    Outcome::Complete(Ok(_)) => fixture_panic!("the budget was not honoured"),
                    Outcome::InternalFault(fault) => {
                        fixture_panic!("the decoder's own budget accounting broke: {fault:?}")
                    }
                }

                // Nothing to cache: an inconclusive outcome carries no value, so a
                // caller cannot store it as either verdict.
                let stopped = Expr::from_canonical_bytes_budgeted(
                    &hostile,
                    DecodeBudget::new(u64::MAX, 1_000),
                );
                assert!(is_inconclusive(&stopped));
                assert!(
                    stopped.as_complete().is_none(),
                    "an inconclusive decode must not yield a value"
                );

                // The SAME bytes with room to work are a rejection — a real verdict
                // about the input, and a different answer from the stop above.
                match Expr::from_canonical_bytes_budgeted(&hostile, DecodeBudget::unlimited()) {
                    Outcome::Complete(Err(error)) => assert_eq!(
                        error.what, "input truncated",
                        "the operands never arrive, and that is a well-formedness fact"
                    ),
                    other => fixture_panic!("expected a typed rejection, got {other:?}"),
                }

                // The byte limit is the other half of the contract, on the same input.
                match Expr::from_canonical_bytes_budgeted(
                    &hostile,
                    DecodeBudget::new(512, u64::MAX),
                ) {
                    ref stopped @ Outcome::Inconclusive(_) => {
                        assert_eq!(stop_of(stopped).0, StructuralUnit::InputBytes);
                        let at: u64 = stop_progress(stopped)
                            .trim_start_matches("byte ")
                            .parse()
                            .expect("progress localizes to a byte offset");
                        assert!(at <= 512);
                    }
                    other => fixture_panic!("expected a byte-budget stop, got {other:?}"),
                }

                // NO NESTING CAP: a legitimately deep VALID artifact still decodes
                // when the caller pays for it. A depth limit would refuse this, and
                // refusing valid deep mathlib terms is what fnj rules out.
                let leaf = Expr::bvar(0).expect("small");
                let mut deep = leaf.clone();
                for _ in 0..100_000 {
                    deep = Expr::app(deep, leaf.clone());
                }
                let deep_bytes = deep.to_canonical_bytes();
                let decoded = decoded_value(Expr::from_canonical_bytes_budgeted(
                    &deep_bytes,
                    DecodeBudget::new(u64::MAX, u64::MAX),
                ))
                .expect("a valid deep artifact decodes when the budget allows it");
                assert_eq!(decoded.to_canonical_bytes(), deep_bytes);

                // And the same artifact under a budget it does not fit is a stop, not
                // a rejection: the artifact is fine, the caller was not willing to pay.
                assert!(
                    is_inconclusive(&Expr::from_canonical_bytes_budgeted(
                        &deep_bytes,
                        DecodeBudget::new(u64::MAX, 64)
                    )),
                    "a valid artifact over budget is inconclusive, never rejected"
                );
            })
            .expect("spawn bounded-stack budget worker")
            .join();
        assert!(
            outcome.is_ok(),
            "decoding deep hostile input under a budget aborted or panicked instead of \
             producing a typed outcome"
        );
    }

    /// Regression for the first finding of the seeded codec campaign (bead
    /// fln-1f8v, found at `flip/KVMap/seed=452821e638d01377/iter=6669`,
    /// minimized to the two-entry shape below).
    ///
    /// A bit flip made one key equal to an earlier key. `KVMap::insert` replaced in
    /// place, so a 2-entry stream decoded to a 1-entry map that re-encoded 27 bytes
    /// shorter: **one value, two encodings.**
    ///
    /// fln-1f8v fixed that by refusing duplicate keys, which cured the symptom and
    /// misplaced the cause: the folding was the defect. Bead franken_lean-l84f showed the
    /// refusal was also a parity divergence — `MData` is `KVMap`, so the Reference can
    /// build and serialize exactly this value — so the decoder now appends positionally
    /// and the input is accepted.
    ///
    /// This test is therefore **retargeted, not deleted**, and it is the more direct
    /// statement of what fln-1f8v was protecting: the original stream must now decode to
    /// a 2-entry map that re-encodes to the *same* bytes. If anyone reintroduces folding,
    /// the re-encode shortens and this fails on the exact fixture that found it.
    #[test]
    fn the_fln_1f8v_duplicate_stream_round_trips_instead_of_folding() {
        let key = Name::str(Name::anonymous(), "a");

        let mut honest = CanonWriter::new();
        honest.schema(SCHEMA_KVMAP);
        honest.u64(2);
        key.write_body(&mut honest);
        honest.u8(DV_NAT);
        honest.u64(1);
        Name::str(Name::anonymous(), "b").write_body(&mut honest);
        honest.u8(DV_NAT);
        honest.u64(2);
        let honest = honest.into_bytes();
        let decoded = KVMap::from_canonical_bytes(&honest).expect("distinct keys decode");
        assert_eq!(decoded.entries().len(), 2);
        assert_eq!(decoded.to_canonical_bytes(), honest, "canonical round trip");

        let mut duplicate = CanonWriter::new();
        duplicate.schema(SCHEMA_KVMAP);
        duplicate.u64(2);
        key.write_body(&mut duplicate);
        duplicate.u8(DV_NAT);
        duplicate.u64(1);
        key.write_body(&mut duplicate);
        duplicate.u8(DV_NAT);
        duplicate.u64(2);
        let duplicate = duplicate.into_bytes();
        let decoded = KVMap::from_canonical_bytes(&duplicate)
            .expect("a duplicate-keyed stream is legal input the Reference can produce");
        // THE ANTI-FOLD ASSERTION: two entries in, two entries out, same bytes back. The
        // original defect was exactly the failure of this equality.
        assert_eq!(
            decoded.entries().len(),
            2,
            "the decoder folded the duplicate"
        );
        assert_eq!(
            decoded.to_canonical_bytes(),
            duplicate,
            "re-encode drifted from the bytes that were decoded — the fln-1f8v defect"
        );
        assert_eq!(
            decoded.find(&key),
            Some(&DataValue::OfNat(1)),
            "first match"
        );
        // Distinct from the folded value it used to decode to, so the two are not
        // confusable by any consumer that hashes the canonical bytes.
        let folded = KVMap::from_entries(vec![(key.clone(), DataValue::OfNat(2))]);
        assert_ne!(decoded.to_canonical_bytes(), folded.to_canonical_bytes());

        // MData embeds a KVMap, so the same stream must decode inside an Expr too —
        // that is the artifact path a decl hash travels, and the reason refusing it was
        // a parity divergence rather than a safe narrowing.
        let mut mdata = CanonWriter::new();
        mdata.schema(SCHEMA_EXPR);
        mdata.u8(EXPR_MDATA);
        mdata.u64(2);
        key.write_body(&mut mdata);
        mdata.u8(DV_NAT);
        mdata.u64(1);
        key.write_body(&mut mdata);
        mdata.u8(DV_NAT);
        mdata.u64(2);
        mdata.u8(EXPR_BVAR);
        mdata.u32(0);
        let mdata = mdata.into_bytes();
        let expr = Expr::from_canonical_bytes(&mdata)
            .expect("a duplicate key inside MData is a value the Reference can serialize");
        assert_eq!(
            expr.to_canonical_bytes(),
            mdata,
            "the Expr round trip must be byte-exact through a duplicate-keyed MData"
        );
        match expr.node() {
            ExprNode::MData { data, .. } => {
                assert_eq!(data.entries().len(), 2, "MData folded the duplicate");
                assert_eq!(data.find(&key), Some(&DataValue::OfNat(1)));
            }
            other => fixture_panic!("expected an MData node, got {other:?}"),
        }
    }

    /// Arbitrary bytes are not a crash: corrupting a valid artifact may decode to
    /// some other value, or fail with a typed error, and nothing else. Seeded, so a
    /// failure replays exactly.
    #[test]
    fn corrupted_artifacts_never_panic_and_always_type_their_errors() {
        let mut generator = Gen(0xc0ff_ee01);
        for _ in 0..400 {
            let expr = generator.expr(3);
            let mut bytes = expr.to_canonical_bytes();
            if bytes.is_empty() {
                continue;
            }
            let flips = 1 + generator.range(3) as usize;
            for _ in 0..flips {
                let index = generator.range(bytes.len() as u64) as usize;
                bytes[index] = generator.range(256) as u8;
            }
            // Either outcome is legal; the point is that neither aborts, and that a
            // refusal is always a labelled, public error rather than a bare panic.
            if let Err(error) = Expr::from_canonical_bytes(&bytes) {
                assert!(
                    !error.what.is_empty(),
                    "corruption produced an empty reason"
                );
            }
        }
    }
}
