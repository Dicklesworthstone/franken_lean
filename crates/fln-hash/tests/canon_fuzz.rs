//! Corrupted-input fuzzing for the canonical decoders (AGENTS.md testing policy,
//! "codec rigs … corrupted-input fuzzing under resource budgets"; beads
//! franken_lean-fnj and franken_lean-canon-stack-safe-drop-6gy).
//!
//! D1 closes the dependency universe, so there is no `cargo-fuzz`, `libfuzzer`,
//! `arbitrary` or `proptest` here: the generator, the mutators, and the corpus are
//! all `std`-only and **seeded**, which buys something the usual tooling does not —
//! every run of this file executes the identical input sequence, so a finding is
//! reproducible from the seed alone and CI cannot go green by drawing luckier bytes.
//!
//! The harness is structure-aware (skill rule: structure-aware beats random bytes
//! ~10:1 on framed formats). Random bytes almost always die at the schema header,
//! which exercises nothing; here every input starts as a *valid* artifact and is
//! then damaged in one named way, so mutants reach the value grammar underneath.
//!
//! ## The oracle
//!
//! For every input, exactly one of these must hold:
//!
//! * `Err(CanonError)` carrying a non-empty public reason — a typed refusal, or
//! * `Ok(value)` whose re-encoding is **byte-identical to the input**.
//!
//! The second clause is what makes this more than a crash harness. The codec's
//! contract is that each value has exactly one encoding, so a mutated stream that
//! decodes but re-encodes differently was *silently accepted in a non-canonical
//! form* — two byte strings for one value, which breaks content addressing (every
//! cache key, decl hash, and logical root in the program). That is a finding here,
//! not a curiosity.
//!
//! A panic or an abort fails the test by propagating. An input that takes longer
//! than [`PER_INPUT_BUDGET`] is a resource finding: decoding must be linear in the
//! consumed input, so a hostile length field must fail fast rather than allocate or
//! spin (FL-INV-07 — resource exhaustion is a typed outcome, never a hang).

#![forbid(unsafe_code)]

use std::time::{Duration, Instant};

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_core::outcome::{InconclusiveCause, Outcome as CoreOutcome};
use fln_hash::canon::{CanonError, Canonical, DecodeBudget, DecodeOutcome};

/// No single decode of these inputs may take longer than this. Generous enough to
/// absorb a loaded CI box, tight enough that an unbounded allocation or a spin on a
/// hostile count field cannot hide inside it.
const PER_INPUT_BUDGET: Duration = Duration::from_secs(5);

/// Inputs never exceed this. A larger stream tests the allocator, not the decoder.
const MAX_INPUT: usize = 1 << 20;

/// Deterministic generator (LCG). No `rand`, no clock, no hash-map iteration: the
/// sequence is a pure function of the seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn below(&mut self, bound: u64) -> u64 {
        if bound == 0 { 0 } else { self.next() % bound }
    }

    fn name(&mut self, depth: u32) -> Name {
        let mut name = Name::anonymous();
        for _ in 0..depth {
            name = match self.below(3) {
                0 => Name::str(name, format!("c{}", self.below(16))),
                1 => Name::num(name, self.below(4096)),
                _ => return name,
            };
        }
        name
    }

    fn level(&mut self, depth: u32) -> Level {
        if depth == 0 {
            return match self.below(3) {
                0 => Level::zero(),
                1 => Level::param(self.name(2)),
                _ => Level::mvar(LMVarId(self.name(2))),
            };
        }
        match self.below(5) {
            0 => self.level(depth - 1).succ().expect("shallow"),
            1 => Level::max(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
            2 => Level::imax(self.level(depth - 1), self.level(depth - 1)).expect("shallow"),
            _ => self.level(0),
        }
    }

    fn kvmap(&mut self) -> KVMap {
        let mut map = KVMap::new();
        for _ in 0..self.below(4) {
            let key = self.name(2);
            let value = match self.below(6) {
                0 => DataValue::OfString(format!("s{}", self.below(32))),
                1 => DataValue::OfBool(self.below(2) == 0),
                2 => DataValue::OfName(self.name(2)),
                3 => DataValue::OfNat(self.next()),
                4 => DataValue::OfInt(self.next() as i64),
                _ => DataValue::OfNat(0),
            };
            map.insert(key, value);
        }
        map
    }

    fn expr(&mut self, depth: u32) -> Expr {
        if depth == 0 {
            return match self.below(7) {
                0 => Expr::bvar(self.below(1 << 19) as u32).expect("inside the range covenant"),
                1 => Expr::fvar(FVarId(self.name(2))),
                2 => Expr::mvar(MVarId(self.name(2))),
                3 => Expr::sort(self.level(1)),
                4 => Expr::lit(Literal::Nat(NatLit::from_u64(self.next()))),
                5 => Expr::lit(Literal::Str(format!("l{}", self.below(64)))),
                _ => Expr::const_(self.name(2), vec![self.level(1), self.level(0)]),
            };
        }
        match self.below(7) {
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
                BinderInfo::StrictImplicit,
            ),
            3 => Expr::let_e(
                self.name(1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                self.expr(depth - 1),
                self.below(2) == 0,
            ),
            4 => Expr::proj(self.name(2), self.below(64), self.expr(depth - 1)),
            5 => Expr::mdata(self.kvmap(), self.expr(depth - 1)),
            _ => self.expr(0),
        }
    }
}

/// One named way to damage a valid artifact: takes the generator (so the damage is
/// seeded and replayable) and the artifact, and returns the mutant.
type Mutator = fn(&mut Rng, &[u8]) -> Vec<u8>;

/// Which decoder an input is aimed at. The schema header is part of the artifact,
/// so a mutant is always fed back to the decoder its header names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Target {
    Name,
    Level,
    Expr,
    KVMap,
}

/// The budgeted outcome, flattened across the four artifact kinds so the sweep can
/// reason about it without naming a type per target.
enum Outcome {
    Accepted,
    NonCanonical {
        input: usize,
        canonical: usize,
    },
    Refused,
    Inconclusive {
        unit: StructuralUnit,
        allowed: u64,
        observed: u64,
    },
    /// The decoder's own budget accounting contradicted itself. Its own arm because a
    /// fuzz run that produces one has found a defect in us, not in the input, and it must
    /// not be absorbed into any of the arms above (bead fln-8gz3).
    Fault(String),
}

impl Target {
    /// Decode, then (on success) re-encode. `Ok(bytes)` is the canonical form the
    /// codec produced for whatever it accepted.
    fn round_trip(self, bytes: &[u8]) -> Result<Vec<u8>, CanonError> {
        match self {
            Target::Name => Name::from_canonical_bytes(bytes).map(|v| v.to_canonical_bytes()),
            Target::Level => Level::from_canonical_bytes(bytes).map(|v| v.to_canonical_bytes()),
            Target::Expr => Expr::from_canonical_bytes(bytes).map(|v| v.to_canonical_bytes()),
            Target::KVMap => KVMap::from_canonical_bytes(bytes).map(|v| v.to_canonical_bytes()),
        }
    }

    fn round_trip_budgeted(self, bytes: &[u8], budget: DecodeBudget) -> Outcome {
        fn classify<T: Canonical>(decoded: DecodeOutcome<T>, input: &[u8]) -> Outcome {
            match decoded {
                CoreOutcome::Complete(Ok(value)) => {
                    let canonical = value.to_canonical_bytes();
                    if canonical == input {
                        Outcome::Accepted
                    } else {
                        Outcome::NonCanonical {
                            input: input.len(),
                            canonical: canonical.len(),
                        }
                    }
                }
                CoreOutcome::Complete(Err(_)) => Outcome::Refused,
                CoreOutcome::Inconclusive(inconclusive) => match inconclusive.cause {
                    InconclusiveCause::ResourceExhausted { usage } => match usage.reason {
                        ResourceReason::StructuralBudget { unit } => Outcome::Inconclusive {
                            unit,
                            allowed: usage.allowed,
                            observed: usage.observed,
                        },
                        other => Outcome::Fault(format!(
                            "a decode stop named a non-structural resource: {other:?}"
                        )),
                    },
                    other => Outcome::Fault(format!(
                        "a decode stop was not a resource exhaustion: {other:?}"
                    )),
                },
                CoreOutcome::InternalFault(fault) => Outcome::Fault(format!("{fault:?}")),
            }
        }
        match self {
            Target::Name => classify(Name::from_canonical_bytes_budgeted(bytes, budget), bytes),
            Target::Level => classify(Level::from_canonical_bytes_budgeted(bytes, budget), bytes),
            Target::Expr => classify(Expr::from_canonical_bytes_budgeted(bytes, budget), bytes),
            Target::KVMap => classify(KVMap::from_canonical_bytes_budgeted(bytes, budget), bytes),
        }
    }
}

/// What the campaign actually exercised. A fuzz run that never gets past the
/// schema header proves nothing while looking identical to a thorough one, so the
/// profile is asserted at the end rather than merely printed.
#[derive(Default)]
struct Profile {
    executed: usize,
    accepted: usize,
    refused: usize,
    reasons: std::collections::BTreeMap<&'static str, usize>,
}

impl Profile {
    fn record(&mut self, outcome: &Result<Vec<u8>, CanonError>) {
        self.executed += 1;
        match outcome {
            Ok(_) => self.accepted += 1,
            Err(error) => {
                self.refused += 1;
                *self.reasons.entry(error.what).or_insert(0) += 1;
            }
        }
    }

    fn report(&self) -> String {
        let mut reasons: Vec<_> = self.reasons.iter().collect();
        reasons.sort_by(|a, b| b.1.cmp(a.1));
        let lines: Vec<String> = reasons
            .iter()
            .map(|(reason, count)| format!("  {count:>7}  {reason}"))
            .collect();
        format!(
            "executed={} accepted={} refused={} distinct_reasons={}\n{}",
            self.executed,
            self.accepted,
            self.refused,
            self.reasons.len(),
            lines.join("\n")
        )
    }
}

/// The single oracle every input in this file goes through.
///
/// Returns `Some(reason)` when the input is a finding, `None` when the decoder
/// behaved. Keeping this in one place means a new mutator cannot accidentally ship
/// with a weaker check than the others.
fn check(target: Target, label: &str, bytes: &[u8], profile: &mut Profile) -> Option<String> {
    assert!(
        bytes.len() <= MAX_INPUT,
        "{label}: harness produced an oversized input ({} bytes)",
        bytes.len()
    );
    let started = Instant::now();
    let outcome = target.round_trip(bytes);
    let elapsed = started.elapsed();
    profile.record(&outcome);

    if elapsed > PER_INPUT_BUDGET {
        return Some(format!(
            "{label}: decode took {elapsed:?}, over the {PER_INPUT_BUDGET:?} budget — \
             resource exhaustion must be a fast typed refusal, not a stall"
        ));
    }
    match outcome {
        Err(error) => {
            if error.what.is_empty() {
                Some(format!("{label}: refusal carried an empty public reason"))
            } else {
                None
            }
        }
        Ok(reencoded) => {
            if reencoded == bytes {
                None
            } else {
                Some(format!(
                    "{label}: input was ACCEPTED in a non-canonical form — \
                     re-encoding differs ({} input bytes, {} canonical bytes). \
                     Two encodings of one value breaks content addressing.",
                    bytes.len(),
                    reencoded.len()
                ))
            }
        }
    }
}

/// Budget-boundary sweep (bead fln-4zk8). The same bytes are decoded under a range
/// of caller budgets, and the three-valued outcome is checked for properties that
/// must hold whatever the budget was:
///
/// * an unlimited budget can never report exhaustion — if it does, the meter is
///   charging something the caller never asked to limit;
/// * an acceptance is canonical no matter how tight the budget was, so the meter
///   cannot be a path to a sloppier accept;
/// * a stop always reports spending more than it was allowed, so the record a
///   caller would retry from is never nonsense;
/// * decoding is monotone in the budget: what a small budget accepted, a bigger one
///   must accept too. A meter that mutates decoder state would break this and
///   nothing else would notice.
fn check_budgets(target: Target, label: &str, bytes: &[u8]) -> Vec<String> {
    let mut findings = Vec::new();
    let unlimited = target.round_trip_budgeted(bytes, DecodeBudget::unlimited());
    if let Outcome::Inconclusive {
        unit,
        allowed,
        observed,
    } = &unlimited
    {
        findings.push(format!(
            "{label}: an unlimited budget reported exhaustion ({} allowed={allowed} \
             observed={observed})",
            unit.as_str()
        ));
    }
    if let Outcome::Fault(detail) = &unlimited {
        findings.push(format!("{label}: unlimited decode faulted: {detail}"));
    }
    let accepted_unlimited = matches!(unlimited, Outcome::Accepted);

    let ceilings = [
        DecodeBudget::new(u64::MAX, 0),
        DecodeBudget::new(u64::MAX, 1),
        DecodeBudget::new(u64::MAX, 8),
        DecodeBudget::new(u64::MAX, 4096),
        DecodeBudget::new(0, u64::MAX),
        DecodeBudget::new(16, u64::MAX),
        DecodeBudget::new(bytes.len() as u64, u64::MAX),
    ];
    for budget in ceilings {
        match target.round_trip_budgeted(bytes, budget) {
            Outcome::Accepted => {
                if !accepted_unlimited {
                    findings.push(format!(
                        "{label}: budget {budget:?} accepted what an unlimited budget did not — \
                         decoding is not monotone in the budget"
                    ));
                }
            }
            Outcome::NonCanonical { input, canonical } => findings.push(format!(
                "{label}: budget {budget:?} accepted a non-canonical form \
                 ({input} input bytes, {canonical} canonical)"
            )),
            Outcome::Refused => {}
            Outcome::Inconclusive {
                allowed, observed, ..
            } => {
                if observed <= allowed {
                    findings.push(format!(
                        "{label}: budget {budget:?} tripped at observed={observed} \
                         allowed={allowed} — a stop must report spending past its limit"
                    ));
                }
            }
            Outcome::Fault(detail) => findings.push(format!(
                "{label}: budget {budget:?} broke the decoder's own accounting: {detail}"
            )),
        }
    }
    findings
}

/// A valid artifact of each shape, from one seed.
fn artifacts(rng: &mut Rng) -> Vec<(Target, Vec<u8>)> {
    vec![
        (Target::Name, rng.name(5).to_canonical_bytes()),
        (Target::Level, rng.level(3).to_canonical_bytes()),
        (Target::Expr, rng.expr(3).to_canonical_bytes()),
        (Target::KVMap, rng.kvmap().to_canonical_bytes()),
    ]
}

/// Seeds are part of the committed corpus: the sequence below is the corpus.
const SEEDS: [u64; 8] = [
    0x0000_0000_0000_0001,
    0x243f_6a88_85a3_08d3,
    0x1319_8a2e_0370_7344,
    0xa409_3822_299f_31d0,
    0x082e_fa98_ec4e_6c89,
    0x4528_21e6_38d0_1377,
    0xbe54_66cf_34e9_0c6c,
    0xffff_ffff_ffff_ffff,
];

/// Hand-written adversarial artifacts, kept as hex so they survive in the corpus
/// exactly as they were when a decoder last saw them. These are the shapes a
/// generator is unlikely to reach: empty input, header-only, a header with a
/// truncated body, and a length field claiming the whole address space.
const HOSTILE_HEX: [(&str, &str); 6] = [
    ("empty", ""),
    ("one-byte", "00"),
    ("header-fragment", "01020304"),
    ("name-count-max", "%NAME%ffffffffffffffff"),
    ("kvmap-count-max", "%KVMAP%ffffffffffffffff"),
    (
        "expr-const-level-count-max",
        "%EXPR%%CONST%0000000000000000ffffffffffffffff",
    ),
];

fn decode_hex(hex: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(hex.len() / 2);
    let bytes = hex.as_bytes();
    let mut index = 0;
    while index + 1 < bytes.len() {
        let hi = (bytes[index] as char).to_digit(16).expect("hex digit");
        let lo = (bytes[index + 1] as char).to_digit(16).expect("hex digit");
        out.push((hi * 16 + lo) as u8);
        index += 2;
    }
    out
}

/// The schema header of each artifact kind, learned from a real encoding rather
/// than hard-coded — the header layout is the codec's business, not this file's.
fn header(target: Target) -> Vec<u8> {
    let bytes = match target {
        Target::Name => Name::anonymous().to_canonical_bytes(),
        Target::Level => Level::zero().to_canonical_bytes(),
        Target::Expr => Expr::bvar(0).expect("small").to_canonical_bytes(),
        Target::KVMap => KVMap::new().to_canonical_bytes(),
    };
    // Every body here is a single tag or count, so the header is everything before
    // the final byte(s) of the shortest artifact: recover it by comparing two
    // artifacts of the same kind, which share exactly the header.
    let other = match target {
        Target::Name => Name::str(Name::anonymous(), "x").to_canonical_bytes(),
        Target::Level => Level::param(Name::anonymous()).to_canonical_bytes(),
        Target::Expr => Expr::bvar(1).expect("small").to_canonical_bytes(),
        Target::KVMap => {
            let mut map = KVMap::new();
            map.insert(Name::anonymous(), DataValue::OfBool(true));
            map.to_canonical_bytes()
        }
    };
    let shared = bytes
        .iter()
        .zip(other.iter())
        .take_while(|(a, b)| a == b)
        .count();
    bytes[..shared].to_vec()
}

/// The first body byte of an artifact — its constructor tag. Recovered the same
/// way, so renumbering a tag in the codec cannot silently invalidate this file.
fn tag_of(target: Target, bytes: &[u8]) -> u8 {
    let head = header(target).len();
    bytes.get(head).copied().unwrap_or(0)
}

#[test]
fn hostile_and_generated_mutants_are_typed_refusals_or_canonical_accepts() {
    let expr_head = header(Target::Expr);
    let app_tag = {
        let app = Expr::app(Expr::bvar(0).expect("small"), Expr::bvar(0).expect("small"))
            .to_canonical_bytes();
        tag_of(Target::Expr, &app)
    };
    let level_head = header(Target::Level);
    let max_tag = {
        let max = Level::max(Level::zero(), Level::zero())
            .expect("shallow")
            .to_canonical_bytes();
        tag_of(Target::Level, &max)
    };

    let mut findings: Vec<String> = Vec::new();
    let mut profile = Profile::default();

    // ---- hand-written hostile inputs ---------------------------------------------
    for (label, hex) in HOSTILE_HEX {
        let resolved = hex
            .replace("%NAME%", &hex_of(&header(Target::Name)))
            .replace("%LEVEL%", &hex_of(&header(Target::Level)))
            .replace("%EXPR%", &hex_of(&header(Target::Expr)))
            .replace("%KVMAP%", &hex_of(&header(Target::KVMap)))
            .replace("%CONST%", &hex_of(&[const_tag()]));
        let bytes = decode_hex(&resolved);
        for target in [Target::Name, Target::Level, Target::Expr, Target::KVMap] {
            if let Some(finding) = check(
                target,
                &format!("hostile/{label}/{target:?}"),
                &bytes,
                &mut profile,
            ) {
                findings.push(finding);
            }
        }
    }

    // ---- adversarially deep tag chains -------------------------------------------
    // Compact input, enormous nesting: the classic decoder-stack kill. It must be a
    // typed refusal (the operands never arrive), never an abort.
    for depth in [1_000usize, 100_000, 1_000_000] {
        let mut deep_expr = expr_head.clone();
        deep_expr.extend(std::iter::repeat_n(app_tag, depth));
        if let Some(finding) = check(
            Target::Expr,
            &format!("deep-app/{depth}"),
            &deep_expr,
            &mut profile,
        ) {
            findings.push(finding);
        }

        let mut deep_level = level_head.clone();
        deep_level.extend(std::iter::repeat_n(max_tag, depth));
        if let Some(finding) = check(
            Target::Level,
            &format!("deep-max/{depth}"),
            &deep_level,
            &mut profile,
        ) {
            findings.push(finding);
        }
    }

    // ---- seeded structure-aware mutation ------------------------------------------
    let iterations: usize = std::env::var("FLN_CANON_FUZZ_ITERS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(48);

    for seed in SEEDS {
        let mut rng = Rng(seed);
        for iteration in 0..iterations {
            for (target, valid) in artifacts(&mut rng) {
                // The unmutated artifact must always survive its own round trip.
                if let Some(finding) = check(
                    target,
                    &format!("valid/{target:?}/{seed:x}"),
                    &valid,
                    &mut profile,
                ) {
                    findings.push(finding);
                }

                let mutators: [(&str, Mutator); 6] = [
                    ("truncate", mutate_truncate),
                    ("extend", mutate_extend),
                    ("flip", mutate_flip),
                    ("tag-substitute", mutate_tag),
                    ("splice", mutate_splice),
                    ("inflate-length", mutate_inflate_length),
                ];
                // Budget-boundary sweep on the intact artifact (bead fln-4zk8).
                findings.extend(check_budgets(
                    target,
                    &format!("budget/valid/{target:?}/seed={seed:x}/iter={iteration}"),
                    &valid,
                ));

                for (name, mutator) in mutators {
                    let mutant = mutator(&mut rng, &valid);
                    if mutant.len() > MAX_INPUT {
                        continue;
                    }
                    let label = format!("{name}/{target:?}/seed={seed:x}/iter={iteration}");
                    if let Some(finding) = check(target, &label, &mutant, &mut profile) {
                        findings.push(finding);
                    }
                    // Damaged bytes under a tight budget: the outcome must still be
                    // one of the three, and a stop must never masquerade as a verdict.
                    if iteration % 8 == 0 {
                        findings.extend(check_budgets(
                            target,
                            &format!("budget/{name}/{target:?}/seed={seed:x}/iter={iteration}"),
                            &mutant,
                        ));
                    }
                }
            }
        }
    }

    if std::env::var_os("FLN_CANON_FUZZ_PROFILE").is_some() {
        println!("{}", profile.report());
    }

    assert!(
        findings.is_empty(),
        "canonical decoding findings ({} inputs):\n{}\nprofile:\n{}",
        findings.len(),
        findings.join("\n"),
        profile.report()
    );

    // Campaign validators. Each of these has failed at least once during
    // development, which is the only reason to trust them: a harness whose inputs
    // all die at the schema header, or that never reaches an accept, is vacuous
    // while looking exactly like a thorough run.
    assert!(
        profile.executed > 1_000,
        "campaign executed only {} inputs — the harness is not running\n{}",
        profile.executed,
        profile.report()
    );
    assert!(
        profile.accepted > 100,
        "mutants never reached a successful decode; they are dying at the header, \
         so the value grammar is untested\n{}",
        profile.report()
    );
    assert!(
        profile.reasons.len() >= 6,
        "only {} distinct refusal reasons — the mutators are not reaching diverse \
         code paths\n{}",
        profile.reasons.len(),
        profile.report()
    );
}

fn const_tag() -> u8 {
    let const_expr = Expr::const_(Name::anonymous(), Vec::new()).to_canonical_bytes();
    tag_of(Target::Expr, &const_expr)
}

fn hex_of(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Every prefix is malformed input; pick one.
fn mutate_truncate(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let cut = rng.below(bytes.len().max(1) as u64) as usize;
    bytes[..cut].to_vec()
}

/// Trailing garbage after a complete value: the decoder must reject it rather than
/// stop early and ignore the rest (that would give a value two encodings).
fn mutate_extend(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    for _ in 0..1 + rng.below(8) {
        out.push(rng.below(256) as u8);
    }
    out
}

fn mutate_flip(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    if out.is_empty() {
        return out;
    }
    for _ in 0..1 + rng.below(3) {
        let index = rng.below(out.len() as u64) as usize;
        out[index] ^= 1 << rng.below(8);
    }
    out
}

/// Replace a body byte with a value far outside any tag range.
fn mutate_tag(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    if out.len() < 2 {
        return out;
    }
    let index = 1 + rng.below(out.len() as u64 - 1) as usize;
    out[index] = 0x80u8.wrapping_add(rng.below(128) as u8);
    out
}

/// Graft a chunk of one artifact into another: structurally plausible, semantically
/// wrong — the shape byte-level mutation rarely reaches.
fn mutate_splice(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let donor =
        Expr::app(Expr::bvar(3).expect("small"), Expr::sort(Level::zero())).to_canonical_bytes();
    let mut out = bytes.to_vec();
    if out.is_empty() {
        return donor;
    }
    let at = rng.below(out.len() as u64) as usize;
    let take = rng.below(donor.len() as u64) as usize;
    out.splice(at..at, donor[..take].iter().copied());
    out
}

/// Overwrite eight consecutive bytes with `u64::MAX`, which lands on a count or
/// length field often enough to matter. A decoder that trusts it will try to
/// allocate or iterate 2^64 times; it must fail fast instead.
fn mutate_inflate_length(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    if out.len() < 9 {
        return out;
    }
    let at = 1 + rng.below(out.len() as u64 - 8) as usize;
    for byte in out.iter_mut().skip(at).take(8) {
        *byte = 0xff;
    }
    out
}
