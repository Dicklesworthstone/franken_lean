//! **fln-wasm** — the WASM-clean offline sealed-capsule Judge (plan §16.4b).
//!
//! Decodes real `fln.capsule.olean-replay/1` `.flnpack` archives
//! (`CartridgeArchiveV1`) and standalone `.olean` artifact chains in pure
//! `#![forbid(unsafe_code)]` Rust with zero filesystem, network, or unsafe
//! dependencies, then independently checks every declaration through
//! `fln-checker`'s own `.olean` reader and verification seat.
//!
//! Resource exhaustion and checker deferrals always yield `Verdict::Inconclusive`
//! (FL-INV-07) and are never promoted to acceptance or rejection. Browser shell
//! packaging and full OQ-12 transparency-log verification remain tracked under
//! `fln-wasm-judge-browser-kvj` and `franken_lean-wasm-judge-packaging-contract-xte`.

#![forbid(unsafe_code)]

mod declaration_plan;
mod import_repeats;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use declaration_plan::{PlanError, UnitKind, plan_declarations};
use fln_checker::admit::{
    AdmissionBudget, BlockVerdict, InductiveVerdict, QuotientVerdict, Verdict as CheckerVerdict,
    admit, admit_block, admit_inductive, admit_quotient,
};
use fln_checker::environment::{
    ConstantEntry, ConstantEnvironment, ConstantKind, EnvironmentBudget, EnvironmentOutcome,
};
use fln_checker::olean::{OleanReadError, OleanReader, OleanReading};
use fln_checker::wire::{NamePart, WireName};
use fln_core::mode::{EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_hash::canon::{CanonReader, CanonWriter, Canonical, DecodeBudget, SchemaId};
use fln_hash::cartridge::{
    CartridgeArchiveV1, CartridgeDecodeBudgetsV1, CartridgeObjectIdV1, CartridgeObjectKindV1,
    CartridgeTransportStateV1, ObjectPortabilityV1, ObjectRequirementV1,
};
use fln_hash::domain::Digest;

// ---------------------------------------------------------------------------
// §16.4b — capsule format & pinned replay schema
// ---------------------------------------------------------------------------

/// Magic bytes at the start of a `.flnproof` capsule.
pub const CAPSULE_MAGIC: &[u8; 8] = b"FLNPRF\x00\x01";

/// Numeric epoch of the pinned v4.32.0 toolchain artifacts.
pub const PINNED_EPOCH: EpochId = EpochId::new(4_032_000);

/// Pinned Reference tag and commit bound into `fln.capsule.olean-replay/1`.
pub const PIN_TAG: &str = "v4.32.0";
pub const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

/// Canonical schema of the semantic `.olean` replay profile inside `.flnpack`.
pub const SCHEMA_OLEAN_CAPSULE: SchemaId = SchemaId {
    name: "fln.capsule.olean-replay",
    version: 1,
};

/// A sealed proof capsule ready for verification.
#[derive(Debug, Clone)]
pub struct SealedCapsule {
    /// Content hash of the capsule (for integrity check).
    pub content_hash: [u8; 32],
    /// Number of declarations in the capsule.
    pub declaration_count: u32,
    /// Axiom set fingerprint (must match the verifier's expected axiom set).
    pub axiom_fingerprint: [u8; 16],
    /// Compressed declaration payload size in bytes.
    pub payload_bytes: u64,
}

/// Capsule format error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapsuleError {
    /// Magic bytes do not match or archive framing is invalid.
    BadMagic,
    /// Integrity check failed.
    IntegrityMismatch {
        expected: [u8; 32],
        observed: [u8; 32],
    },
    /// Unsupported capsule or semantic-profile version.
    UnsupportedVersion(u8),
    /// Payload exceeds the verification budget.
    PayloadTooLarge { observed: u64, limit: u64 },
    /// Axiom fingerprint or pin/epoch binding does not match.
    AxiomMismatch,
    /// Truncated, incomplete, legacy-only, or malformed capsule.
    Truncated,
    /// A missing import, cycle, or conflicting declaration prevents closed replay.
    ModuleGraph(String),
}

impl fmt::Display for CapsuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BadMagic => write!(f, "not a valid .flnpack/.flnproof capsule"),
            Self::IntegrityMismatch { .. } => write!(f, "capsule integrity check failed"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported capsule version {v}"),
            Self::PayloadTooLarge { observed, limit } => {
                write!(f, "payload {observed} bytes exceeds limit {limit}")
            }
            Self::AxiomMismatch => write!(f, "axiom or epoch/pin binding mismatch"),
            Self::Truncated => write!(f, "truncated, legacy-only, or malformed capsule"),
            Self::ModuleGraph(detail) => write!(f, "invalid module closure: {detail}"),
        }
    }
}

// ---------------------------------------------------------------------------
// §16.4b — verification verdict
// ---------------------------------------------------------------------------

/// The outcome of capsule verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Every declaration in the capsule was independently admitted.
    Accepted {
        /// Number of declarations verified.
        declarations: u32,
    },
    /// One or more declarations were rejected by the independent checker.
    Rejected {
        /// Name of the first rejected declaration.
        first_rejection: Name,
        /// Total rejections found before stopping.
        rejection_count: u32,
    },
    /// Verification could not complete within the budget or hit a non-decision
    /// (FL-INV-07: never promoted to acceptance or rejection).
    Inconclusive {
        /// Declarations verified before stopping.
        verified_so_far: u32,
        /// Reason for early termination.
        reason: String,
    },
    /// The capsule itself is malformed, corrupt, legacy-only, or unsupported.
    Malformed(CapsuleError),
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Accepted { declarations } => {
                write!(f, "accepted: {declarations} declarations verified")
            }
            Self::Rejected {
                first_rejection,
                rejection_count,
            } => {
                write!(
                    f,
                    "rejected: {rejection_count} rejections (first: {first_rejection:?})"
                )
            }
            Self::Inconclusive {
                verified_so_far,
                reason,
            } => {
                write!(
                    f,
                    "inconclusive: {verified_so_far} verified, stopped: {reason}"
                )
            }
            Self::Malformed(error) => write!(f, "malformed capsule: {error}"),
        }
    }
}

// ---------------------------------------------------------------------------
// §16.4b — verification budget
// ---------------------------------------------------------------------------

/// Resource budget for WASM verification.
#[derive(Debug, Clone, Copy)]
pub struct VerificationBudget {
    /// Maximum declarations to verify.
    pub max_declarations: u32,
    /// Maximum payload bytes to decode/expand.
    pub max_payload_bytes: u64,
    /// Maximum checker reduction/inference steps per declaration. Also bounds
    /// each planning/import-comparison pass per module and scratch-name
    /// preparation per repeated theorem.
    pub max_steps: u64,
}

impl Default for VerificationBudget {
    fn default() -> Self {
        Self {
            max_declarations: 100_000,
            max_payload_bytes: 256 * 1024 * 1024,
            max_steps: 100_000_000,
        }
    }
}

// ---------------------------------------------------------------------------
// Real offline verification over CartridgeArchiveV1 + fln-checker
// ---------------------------------------------------------------------------

struct ModuleRow {
    name: Name,
    public: CartridgeObjectIdV1,
    companions: Option<(CartridgeObjectIdV1, CartridgeObjectIdV1)>,
    declarations: u64,
}

struct DecodedModule {
    name: Name,
    imports: Vec<Name>,
    constants: Vec<ConstantEntry>,
}

impl ModuleRow {
    fn objects(&self) -> impl Iterator<Item = CartridgeObjectIdV1> {
        std::iter::once(self.public).chain(
            self.companions
                .into_iter()
                .flat_map(|(server, private)| [server, private]),
        )
    }
}

fn wire_name_to_core(wire: &WireName) -> Name {
    let mut name = Name::anonymous();
    for part in wire.parts() {
        match part {
            NamePart::Text(s) => name = Name::str(name, s.as_str()),
            NamePart::Numeric { value, .. } => name = Name::num(name, *value),
        }
    }
    name
}

fn checker_budgets(budget: VerificationBudget) -> (AdmissionBudget, EnvironmentBudget) {
    let steps = budget.max_steps;
    let mut admission = AdmissionBudget::unlimited();
    admission.inference.max_steps = steps;
    admission.inference.whnf.max_steps = steps;
    admission.inference.defeq.max_slow_comparisons = steps;
    admission.inference.defeq.quick.max_comparisons = steps;
    admission.inference.defeq.whnf.max_steps = steps;
    admission.sort_whnf.max_steps = steps;
    admission.conversion.max_slow_comparisons = steps;
    admission.conversion.quick.max_comparisons = steps;
    admission.conversion.whnf.max_steps = steps;

    let mut env_budget = EnvironmentBudget::unlimited();
    env_budget.max_constants = u64::from(budget.max_declarations).max(1);
    env_budget.max_owned_units = budget.max_payload_bytes.max(1_048_576);
    (admission, env_budget)
}

fn decode_semantic_profile(
    bytes: &[u8],
    max_profile_bytes: u64,
) -> Result<Vec<ModuleRow>, Verdict> {
    let decode_nodes = max_profile_bytes.saturating_mul(2).max(4_096);
    let mut reader =
        CanonReader::with_budget(bytes, DecodeBudget::new(max_profile_bytes, decode_nodes));

    let read_err = |reader: &CanonReader<'_>| -> Verdict {
        if reader.exhausted().is_some() {
            Verdict::Inconclusive {
                verified_so_far: 0,
                reason: "semantic profile decode budget exhausted".to_string(),
            }
        } else {
            Verdict::Malformed(CapsuleError::Truncated)
        }
    };

    let schema_name = reader.str().map_err(|_| read_err(&reader))?;
    if schema_name != SCHEMA_OLEAN_CAPSULE.name {
        return Err(Verdict::Malformed(CapsuleError::BadMagic));
    }
    let version = reader.u16().map_err(|_| read_err(&reader))?;
    if version != SCHEMA_OLEAN_CAPSULE.version {
        let clamped = u8::try_from(version).unwrap_or(u8::MAX);
        return Err(Verdict::Malformed(CapsuleError::UnsupportedVersion(
            clamped,
        )));
    }
    let low = u128::from(reader.u64().map_err(|_| read_err(&reader))?);
    let high = u128::from(reader.u64().map_err(|_| read_err(&reader))?);
    let epoch = EpochId::new(low | (high << 64));
    if epoch != PINNED_EPOCH {
        return Err(Verdict::Malformed(CapsuleError::AxiomMismatch));
    }
    let mode_tag = reader.u8().map_err(|_| read_err(&reader))?;
    let repro_tag = reader.u8().map_err(|_| read_err(&reader))?;
    if mode_tag != Mode::Sound.tag() || repro_tag != ReproducibilityProfile::Standard.tag() {
        return Err(Verdict::Malformed(CapsuleError::AxiomMismatch));
    }
    let pin_tag = reader.str().map_err(|_| read_err(&reader))?;
    let pin_commit = reader.str().map_err(|_| read_err(&reader))?;
    if pin_tag != PIN_TAG || pin_commit != PIN_COMMIT {
        return Err(Verdict::Malformed(CapsuleError::AxiomMismatch));
    }
    let _options = KVMap::read_body(&mut reader).map_err(|_| read_err(&reader))?;
    let _base_root = read_digest(&mut reader).map_err(|_| read_err(&reader))?;
    let _result_root = read_digest(&mut reader).map_err(|_| read_err(&reader))?;
    let count = reader.u64().map_err(|_| read_err(&reader))?;
    if count == 0 || count > (bytes.len() / 113) as u64 {
        return Err(Verdict::Malformed(CapsuleError::Truncated));
    }
    let mut modules: Vec<ModuleRow> = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let name = Name::read_body(&mut reader).map_err(|_| read_err(&reader))?;
        if name.is_anonymous() || modules.last().is_some_and(|row| row.name >= name) {
            return Err(Verdict::Malformed(CapsuleError::Truncated));
        }
        let public =
            CartridgeObjectIdV1::new(read_digest(&mut reader).map_err(|_| read_err(&reader))?);
        let has_companions = reader.bool().map_err(|_| read_err(&reader))?;
        let companions = if has_companions {
            let server =
                CartridgeObjectIdV1::new(read_digest(&mut reader).map_err(|_| read_err(&reader))?);
            let private =
                CartridgeObjectIdV1::new(read_digest(&mut reader).map_err(|_| read_err(&reader))?);
            Some((server, private))
        } else {
            None
        };
        let _mod_base = read_digest(&mut reader).map_err(|_| read_err(&reader))?;
        let _mod_result = read_digest(&mut reader).map_err(|_| read_err(&reader))?;
        let declarations = reader.u64().map_err(|_| read_err(&reader))?;
        modules.push(ModuleRow {
            name,
            public,
            companions,
            declarations,
        });
    }
    let exhausted = reader.exhausted().is_some();
    if reader.finish().is_err() {
        return Err(if exhausted {
            Verdict::Inconclusive {
                verified_so_far: 0,
                reason: "semantic profile decode budget exhausted".to_string(),
            }
        } else {
            Verdict::Malformed(CapsuleError::Truncated)
        });
    }
    Ok(modules)
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, ()> {
    let mut bytes = [0u8; 32];
    for b in &mut bytes {
        *b = reader.u8().map_err(|_| ())?;
    }
    Ok(Digest(bytes))
}

fn object_starts_with(
    archive: &CartridgeArchiveV1,
    object: &fln_hash::cartridge::CartridgeObjectV1,
    prefix: &[u8],
) -> bool {
    let mut matched = 0usize;
    for chunk_ref in &object.chunks {
        let Some(frame) = archive.frames.iter().find(|f| f.id == chunk_ref.id) else {
            return false;
        };
        let need = prefix.len() - matched;
        let take = frame.bytes.len().min(need);
        if frame.bytes[..take] != prefix[matched..matched + take] {
            return false;
        }
        matched += take;
        if matched == prefix.len() {
            return true;
        }
    }
    false
}

fn decode_module_parts(parts: &[&[u8]], max_objects: u64) -> Result<OleanReading, Verdict> {
    if !matches!(parts.len(), 1 | 3) {
        return Err(Verdict::Malformed(CapsuleError::Truncated));
    }
    let decode = |parts: &[&[u8]]| -> Result<OleanReading, Verdict> {
        let read_error = |error| match error {
            OleanReadError::Budget { visited } => Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!("olean decode object budget exhausted after {visited} objects"),
            },
            _ => Verdict::Malformed(CapsuleError::Truncated),
        };
        let reader = OleanReader::new(parts, max_objects).map_err(read_error)?;
        // The generated pin uses GMP and no reserved flags. The profile's pin
        // is a claim; every artifact part must independently carry that pin.
        if !reader.headers_match(1, PIN_TAG.trim_start_matches('v'), PIN_COMMIT) {
            return Err(Verdict::Malformed(CapsuleError::AxiomMismatch));
        }
        reader.constants().map_err(read_error)
    };
    let public = decode(&parts[..1])?;
    if public.is_module != (parts.len() == 3) {
        return Err(Verdict::Malformed(CapsuleError::Truncated));
    }
    if parts.len() == 1 {
        return Ok(public);
    }
    // All three parts must decode. Public metadata supplies the import graph;
    // the private array supplies the bodies checked by the Judge.
    let server = decode(&parts[..2])?;
    let mut private = decode(parts)?;
    if !server.is_module || !private.is_module {
        return Err(Verdict::Malformed(CapsuleError::Truncated));
    }
    let private_by_name: BTreeMap<_, _> = private
        .constants
        .iter()
        .map(|entry| (entry.name(), entry))
        .collect();
    for exported in &public.constants {
        let Some(counterpart) = private_by_name.get(exported.name()) else {
            return Err(Verdict::Malformed(CapsuleError::Truncated));
        };
        // Public declarations may erase a body to an axiom. Replacing a
        // public body by a private axiom would silently evade proof checking.
        if counterpart.declaration().kind() == ConstantKind::Axiom
            && exported.declaration().kind() != ConstantKind::Axiom
        {
            return Err(Verdict::Malformed(CapsuleError::Truncated));
        }
    }
    private.imports = public.imports;
    Ok(private)
}

/// Verify a sealed `.flnpack` capsule (`fln.capsule.olean-replay/1`) offline
/// using `fln-checker`'s WASM-clean independent `.olean` reader and checker seat.
///
/// Requires a valid semantic profile; legacy integrity-only capsules return
/// `Verdict::Malformed(CapsuleError::Truncated)`.
/// Compatible theorem repeats are independently rechecked without replacing
/// their imported binding. Nonidentical axiom/axiom subsumption remains unsupported.
pub fn verify_flnpack_capsule(bytes: &[u8], budget: VerificationBudget) -> Verdict {
    if bytes.len() as u64 > budget.max_payload_bytes {
        return Verdict::Inconclusive {
            verified_so_far: 0,
            reason: format!(
                "archive size {} exceeds byte budget {}",
                bytes.len(),
                budget.max_payload_bytes
            ),
        };
    }
    let decode_nodes = budget.max_payload_bytes.saturating_mul(2).max(4_096);
    let decode_budget = DecodeBudget::new(budget.max_payload_bytes, decode_nodes);
    let archive = match CartridgeArchiveV1::from_canonical_bytes_budgeted(
        bytes,
        CartridgeDecodeBudgetsV1 {
            archive: decode_budget,
            manifest: decode_budget,
        },
    ) {
        Outcome::Complete(Ok(archive)) => archive,
        Outcome::Complete(Err(_)) => return Verdict::Malformed(CapsuleError::BadMagic),
        Outcome::Inconclusive(stop) => {
            return Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!("archive decode budget exhausted: {stop:?}"),
            };
        }
        Outcome::InternalFault(fault) => {
            return Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!("archive decode internal fault: {fault:?}"),
            };
        }
    };

    if !matches!(
        archive.transport_state(),
        CartridgeTransportStateV1::Complete | CartridgeTransportStateV1::Sealed { .. }
    ) {
        return Verdict::Malformed(CapsuleError::Truncated);
    }

    let expanded: u64 = archive
        .manifest
        .objects
        .iter()
        .fold(0u64, |acc, obj| acc.saturating_add(obj.len));
    if expanded > budget.max_payload_bytes {
        return Verdict::Inconclusive {
            verified_so_far: 0,
            reason: format!(
                "expanded capsule size {expanded} exceeds budget {}",
                budget.max_payload_bytes
            ),
        };
    }

    // Locate the unique semantic receipt marker.
    let mut marker = CanonWriter::new();
    marker.str(SCHEMA_OLEAN_CAPSULE.name);
    let marker = marker.into_bytes();
    let mut candidate = None;
    for object in &archive.manifest.objects {
        if object_starts_with(&archive, object, &marker) && candidate.replace(object.id).is_some() {
            return Verdict::Malformed(CapsuleError::Truncated);
        }
    }
    let Some(receipt_id) = candidate else {
        // Legacy integrity-only archive without a semantic profile.
        return Verdict::Malformed(CapsuleError::Truncated);
    };

    let max_profile_bytes = budget.max_payload_bytes.min(8 * 1024 * 1024);
    let profile_bytes = match archive.assemble_object(receipt_id, max_profile_bytes) {
        Outcome::Complete(Ok(Some(b))) => b,
        Outcome::Complete(Ok(None)) => return Verdict::Malformed(CapsuleError::Truncated),
        Outcome::Complete(Err(_)) => return Verdict::Malformed(CapsuleError::BadMagic),
        Outcome::Inconclusive(stop) => {
            return Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!("profile assembly budget exhausted: {stop:?}"),
            };
        }
        Outcome::InternalFault(fault) => {
            return Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!("profile assembly fault: {fault:?}"),
            };
        }
    };

    let modules = match decode_semantic_profile(&profile_bytes, max_profile_bytes) {
        Ok(m) => m,
        Err(verdict) => return verdict,
    };

    if archive.manifest.epoch != PINNED_EPOCH {
        return Verdict::Malformed(CapsuleError::AxiomMismatch);
    }
    if archive.manifest.root_receipts.as_slice() != [receipt_id] {
        return Verdict::Malformed(CapsuleError::Truncated);
    }
    let Some(receipt) = archive.manifest.object(receipt_id) else {
        return Verdict::Malformed(CapsuleError::Truncated);
    };
    if receipt.kind != CartridgeObjectKindV1::Receipt
        || receipt.requirement != ObjectRequirementV1::Required
        || receipt.portability != ObjectPortabilityV1::EpochBound
    {
        return Verdict::Malformed(CapsuleError::Truncated);
    }

    let mut bound = BTreeSet::from([receipt_id]);
    let mut presented_bytes = 0u64;
    let mut declared_count = 0u64;
    for row in &modules {
        declared_count = declared_count.saturating_add(row.declarations);
        if declared_count > u64::from(budget.max_declarations) {
            return Verdict::Inconclusive {
                verified_so_far: 0,
                reason: format!(
                    "declaration count {declared_count} exceeds budget {}",
                    budget.max_declarations
                ),
            };
        }
        for obj_id in row.objects() {
            let Some(meta) = archive.manifest.object(obj_id) else {
                return Verdict::Malformed(CapsuleError::Truncated);
            };
            if meta.kind != CartridgeObjectKindV1::Declaration
                || meta.requirement != ObjectRequirementV1::Required
                || meta.portability != ObjectPortabilityV1::EpochBound
            {
                return Verdict::Malformed(CapsuleError::Truncated);
            }
            // A shared object may be decoded under many module names. Bound
            // that presentation cost as well as the unique transport bytes.
            presented_bytes = presented_bytes.saturating_add(meta.len);
            if presented_bytes > budget.max_payload_bytes {
                return Verdict::Inconclusive {
                    verified_so_far: 0,
                    reason: format!(
                        "module input size {presented_bytes} exceeds byte budget {}",
                        budget.max_payload_bytes
                    ),
                };
            }
            bound.insert(obj_id);
        }
    }

    let mut assembled_objects: BTreeMap<CartridgeObjectIdV1, Vec<u8>> = BTreeMap::new();
    for object in &archive.manifest.objects {
        if !bound.contains(&object.id)
            && (object.requirement == ObjectRequirementV1::Required
                || matches!(
                    object.kind,
                    CartridgeObjectKindV1::Declaration
                        | CartridgeObjectKindV1::Dependency
                        | CartridgeObjectKindV1::Receipt
                ))
        {
            return Verdict::Malformed(CapsuleError::Truncated);
        }
        if object.id == receipt_id {
            continue;
        }
        match archive.assemble_object(object.id, budget.max_payload_bytes) {
            Outcome::Complete(Ok(Some(data))) => {
                if bound.contains(&object.id) {
                    assembled_objects.insert(object.id, data);
                }
            }
            Outcome::Complete(Ok(None)) => return Verdict::Malformed(CapsuleError::Truncated),
            Outcome::Complete(Err(_)) => {
                return Verdict::Malformed(CapsuleError::IntegrityMismatch {
                    expected: object.id.digest().0,
                    observed: [0u8; 32],
                });
            }
            Outcome::Inconclusive(stop) => {
                return Verdict::Inconclusive {
                    verified_so_far: 0,
                    reason: format!("object assembly budget exhausted: {stop:?}"),
                };
            }
            Outcome::InternalFault(fault) => {
                return Verdict::Inconclusive {
                    verified_so_far: 0,
                    reason: format!("object assembly fault: {fault:?}"),
                };
            }
        }
    }

    let max_objects = budget.max_payload_bytes.max(65_536);
    let mut decoded = Vec::with_capacity(modules.len());
    for row in &modules {
        let Some(public_bytes) = assembled_objects.get(&row.public) else {
            return Verdict::Malformed(CapsuleError::Truncated);
        };
        let mut parts: Vec<&[u8]> = vec![public_bytes.as_slice()];
        if let Some((server_id, private_id)) = row.companions {
            let (Some(s), Some(p)) = (
                assembled_objects.get(&server_id),
                assembled_objects.get(&private_id),
            ) else {
                return Verdict::Malformed(CapsuleError::Truncated);
            };
            parts.push(s.as_slice());
            parts.push(p.as_slice());
        }
        match decode_module_parts(&parts, max_objects) {
            Ok(reading) => {
                if row.declarations != reading.constants.len() as u64 {
                    return Verdict::Malformed(CapsuleError::Truncated);
                }
                decoded.push(DecodedModule {
                    name: row.name.clone(),
                    imports: reading
                        .imports
                        .iter()
                        .map(|import| wire_name_to_core(&import.module))
                        .collect(),
                    constants: reading.constants,
                });
            }
            Err(verdict) => return verdict,
        }
    }

    check_module_closure(&decoded, budget)
}

/// Verify a standalone `.olean` part chain (`[X.olean]` or
/// `[X.olean, X.olean.server, X.olean.private]`) offline through
/// `fln-checker`'s WASM-clean independent reader and checker seat.
pub fn verify_olean_parts(parts: &[&[u8]], budget: VerificationBudget) -> Verdict {
    let total_bytes: u64 = parts
        .iter()
        .fold(0u64, |acc, part| acc.saturating_add(part.len() as u64));
    if total_bytes > budget.max_payload_bytes {
        return Verdict::Inconclusive {
            verified_so_far: 0,
            reason: format!(
                "olean input size {total_bytes} exceeds byte budget {}",
                budget.max_payload_bytes
            ),
        };
    }
    let max_objects = budget.max_payload_bytes.max(65_536);
    let reading = match decode_module_parts(parts, max_objects) {
        Ok(r) => r,
        Err(verdict) => return verdict,
    };
    if let Some(import) = reading.imports.first() {
        return Verdict::Malformed(CapsuleError::ModuleGraph(format!(
            "standalone artifact requires import {}",
            wire_name_to_core(&import.module).to_display_string()
        )));
    }
    check_constant_stream(&reading.constants, budget)
}

/// The profile sorts module names for canonical encoding; that is not their
/// dependency order. Resolve the independently decoded imports before checking,
/// then give each module exactly its own transitive import environment.
fn check_module_closure(modules: &[DecodedModule], budget: VerificationBudget) -> Verdict {
    // A capsule claims one final environment. Exact repeats and compatible
    // theorem/erased-axiom signatures may coexist, but every new proof must
    // still be admitted in its own module's actual import closure below.
    let mut global_names: BTreeMap<_, (&ConstantEntry, Digest)> = BTreeMap::new();
    for module in modules {
        let mut comparison_work = budget.max_steps;
        for entry in &module.constants {
            let digest = entry.reading_digest();
            if let Some((previous, previous_digest)) = global_names.get(entry.name()) {
                if *previous_digest != digest {
                    match import_repeats::compatible(previous, entry, &mut comparison_work) {
                        Ok(true) => {}
                        Ok(false) => return conflicting_declaration(entry),
                        Err(reason) => {
                            return Verdict::Inconclusive {
                                verified_so_far: 0,
                                reason: reason.to_owned(),
                            };
                        }
                    }
                }
            } else {
                global_names.insert(entry.name(), (entry, digest));
            }
        }
    }
    let by_name: BTreeMap<_, _> = modules
        .iter()
        .enumerate()
        .map(|(index, module)| (&module.name, index))
        .collect();
    let mut dependencies = Vec::with_capacity(modules.len());
    let mut dependants = vec![Vec::new(); modules.len()];
    let mut pending = Vec::with_capacity(modules.len());
    let mut ready = BTreeSet::new();
    for (index, module) in modules.iter().enumerate() {
        let mut imports = BTreeSet::new();
        for name in &module.imports {
            let Some(&dependency) = by_name.get(name) else {
                return Verdict::Malformed(CapsuleError::ModuleGraph(format!(
                    "{} imports missing module {}",
                    module.name.to_display_string(),
                    name.to_display_string()
                )));
            };
            if imports.insert(dependency) {
                dependants[dependency].push(index);
            }
        }
        pending.push(imports.len());
        if imports.is_empty() {
            ready.insert(index);
        }
        dependencies.push(imports);
    }
    let mut order = Vec::with_capacity(modules.len());
    while let Some(index) = ready.pop_first() {
        order.push(index);
        for &dependent in &dependants[index] {
            pending[dependent] -= 1;
            if pending[dependent] == 0 {
                ready.insert(dependent);
            }
        }
    }
    if order.len() != modules.len() {
        return Verdict::Malformed(CapsuleError::ModuleGraph("import cycle".to_owned()));
    }

    let (_, env_budget) = checker_budgets(budget);
    let mut verified = 0;
    let mut import_work = 0u64;
    let mut admitted: Vec<Option<ConstantEnvironment>> = vec![None; modules.len()];
    for index in order {
        let mut comparison_work = budget.max_steps;
        // Start from the largest already checked direct import. Persistent
        // snapshots make a single-parent chain an O(1) clone per module, not
        // repeated validation of its entire transitive closure. Other direct
        // imports contribute only constants absent from that snapshot.
        let base = dependencies[index]
            .iter()
            .copied()
            .max_by_key(|&dependency| {
                admitted[dependency]
                    .as_ref()
                    .map_or(0, ConstantEnvironment::len)
            });
        let mut env = match base {
            Some(dependency) => match &admitted[dependency] {
                Some(environment) => environment.clone(),
                None => return missing_import_snapshot(verified),
            },
            None => ConstantEnvironment::empty(),
        };
        for &dependency in &dependencies[index] {
            if Some(dependency) == base {
                continue;
            }
            let Some(imported) = &admitted[dependency] else {
                return missing_import_snapshot(verified);
            };
            for (name, declaration) in imported.constants() {
                import_work = import_work.saturating_add(1);
                if import_work > budget.max_payload_bytes {
                    return Verdict::Inconclusive {
                        verified_so_far: verified,
                        reason: "import environment presentation budget exhausted".to_owned(),
                    };
                }
                if let Some(existing) = env.find(name) {
                    // Shared import snapshots have shared term/name storage.
                    // Preserve their equality shortcut before cloning or
                    // hashing a common ancestor's complete proof reading.
                    if existing != declaration {
                        let previous = ConstantEntry::new(name.clone(), existing.clone());
                        let entry = ConstantEntry::new(name.clone(), declaration.clone());
                        if previous.reading_digest() != entry.reading_digest() {
                            match import_repeats::compatible(
                                &previous,
                                &entry,
                                &mut comparison_work,
                            ) {
                                Ok(true) => {}
                                Ok(false) => return conflicting_declaration(&entry),
                                Err(reason) => {
                                    return Verdict::Inconclusive {
                                        verified_so_far: verified,
                                        reason: reason.to_owned(),
                                    };
                                }
                            }
                        }
                    }
                    // Both imported variants were independently admitted in
                    // their original closures. Retain the deterministic first
                    // representative, as native import merging does.
                } else {
                    let entry = ConstantEntry::new(name.clone(), declaration.clone());
                    env = match extend_env(&env, &entry, env_budget, verified) {
                        Ok(next) => next,
                        Err(verdict) => return verdict,
                    };
                }
            }
        }
        match check_constant_stream_in(&modules[index].constants, budget, &mut env, verified) {
            Verdict::Accepted { declarations } => {
                verified = declarations;
                admitted[index] = Some(env);
            }
            other => return other,
        }
    }
    Verdict::Accepted {
        declarations: verified,
    }
}

fn conflicting_declaration(entry: &ConstantEntry) -> Verdict {
    Verdict::Malformed(CapsuleError::ModuleGraph(format!(
        "conflicting declaration {} across capsule modules",
        wire_name_to_core(entry.name()).to_display_string()
    )))
}

fn missing_import_snapshot(verified: u32) -> Verdict {
    Verdict::Inconclusive {
        verified_so_far: verified,
        reason: "internal fault: topological import has no checked snapshot".to_owned(),
    }
}

fn extend_env(
    env: &ConstantEnvironment,
    item: &ConstantEntry,
    env_budget: EnvironmentBudget,
    verified: u32,
) -> Result<ConstantEnvironment, Verdict> {
    match env.extend(item.clone(), env_budget) {
        EnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        EnvironmentOutcome::Inconclusive(stop) => Err(Verdict::Inconclusive {
            verified_so_far: verified,
            reason: format!("environment budget exhausted: {stop:?}"),
        }),
        EnvironmentOutcome::Refused { .. } => Err(Verdict::Rejected {
            first_rejection: wire_name_to_core(item.name()),
            rejection_count: 1,
        }),
        EnvironmentOutcome::InternalFault { fault, .. } => Err(Verdict::Inconclusive {
            verified_so_far: verified,
            reason: format!("environment fault: {fault:?}"),
        }),
    }
}

/// Reconstruct atomic declaration units and dependency order from decoded
/// constants, then independently admit every unit under `budget`.
fn check_constant_stream(entries: &[ConstantEntry], budget: VerificationBudget) -> Verdict {
    check_constant_stream_in(entries, budget, &mut ConstantEnvironment::empty(), 0)
}

fn check_constant_stream_in(
    entries: &[ConstantEntry],
    budget: VerificationBudget,
    env: &mut ConstantEnvironment,
    already_verified: u32,
) -> Verdict {
    if (entries.len() as u64).saturating_add(u64::from(already_verified))
        > u64::from(budget.max_declarations)
    {
        return Verdict::Inconclusive {
            verified_so_far: already_verified,
            reason: format!(
                "declaration count {} exceeds budget {}",
                entries.len(),
                budget.max_declarations
            ),
        };
    }

    let plan = match plan_declarations(entries, env, budget.max_steps) {
        Ok(plan) => plan,
        Err(PlanError::Rejected(name)) => {
            return Verdict::Rejected {
                first_rejection: wire_name_to_core(&name),
                rejection_count: 1,
            };
        }
        Err(PlanError::Inconclusive(reason)) => {
            return Verdict::Inconclusive {
                verified_so_far: already_verified,
                reason: reason.to_owned(),
            };
        }
    };
    let (admission_budget, env_budget) = checker_budgets(budget);
    let mut verified = already_verified.saturating_add(plan.already_present);
    for index in plan.order {
        let unit = &plan.units[index];
        let entry = &entries[unit.members[0]];
        let rejection = || Verdict::Rejected {
            first_rejection: wire_name_to_core(entry.name()),
            rejection_count: 1,
        };
        let stopped = |reason| Verdict::Inconclusive {
            verified_so_far: verified,
            reason,
        };
        let mut grouped = Vec::new();
        let members = if unit.kind == UnitKind::Single {
            std::slice::from_ref(entry)
        } else {
            if grouped.try_reserve_exact(unit.members.len()).is_err() {
                return stopped("declaration unit allocation failed".to_owned());
            }
            grouped.extend(unit.members.iter().map(|&index| entries[index].clone()));
            grouped.as_slice()
        };
        match unit.kind {
            UnitKind::Quotient => match admit_quotient(env, members, admission_budget) {
                QuotientVerdict::Admitted(_) => {}
                QuotientVerdict::Rejected(_) => return rejection(),
                QuotientVerdict::Inconclusive(stop) => {
                    return stopped(format!("quotient admission budget exhausted: {stop:?}"));
                }
                QuotientVerdict::InternalFault(fault) => {
                    return stopped(format!("quotient admission fault: {fault:?}"));
                }
            },
            UnitKind::Inductive => {
                match admit_inductive(env, members, admission_budget, env_budget) {
                    InductiveVerdict::Admitted(_) => {}
                    InductiveVerdict::Rejected(_) => return rejection(),
                    InductiveVerdict::Deferred(reason) => {
                        return stopped(format!("inductive block deferred: {reason:?}"));
                    }
                    InductiveVerdict::Inconclusive(stop) => {
                        return stopped(format!("inductive admission budget exhausted: {stop:?}"));
                    }
                    InductiveVerdict::InternalFault(fault) => {
                        return stopped(format!("inductive admission fault: {fault:?}"));
                    }
                }
            }
            UnitKind::Mutual => match admit_block(env, members, admission_budget) {
                BlockVerdict::Admitted(_) => {}
                BlockVerdict::Rejected(_) => return rejection(),
                BlockVerdict::MemberRejected { member, .. } => {
                    return Verdict::Rejected {
                        first_rejection: wire_name_to_core(&member),
                        rejection_count: 1,
                    };
                }
                BlockVerdict::MemberDeferred { deferred, .. } => {
                    return stopped(format!("mutual block deferred: {deferred:?}"));
                }
                BlockVerdict::MemberInconclusive { stop, .. } => {
                    return stopped(format!("mutual admission budget exhausted: {stop:?}"));
                }
                BlockVerdict::MemberFault { fault, .. } => {
                    return stopped(format!("mutual admission fault: {fault:?}"));
                }
            },
            UnitKind::Single => match admit(env, entry, admission_budget) {
                CheckerVerdict::Admitted(_) => {}
                CheckerVerdict::Rejected(_) => return rejection(),
                CheckerVerdict::Deferred(reason) => {
                    return stopped(format!("declaration deferred: {reason:?}"));
                }
                CheckerVerdict::Inconclusive(stop) => {
                    return stopped(format!("admission budget exhausted: {stop:?}"));
                }
                CheckerVerdict::InternalFault(fault) => {
                    return stopped(format!("admission internal fault: {fault:?}"));
                }
            },
        }
        for item in members {
            match extend_env(env, item, env_budget, verified) {
                Ok(next) => *env = next,
                Err(verdict) => return verdict,
            }
            verified = verified.saturating_add(1);
        }
    }

    // Repeats are intentionally absent from the local dependency owners. A
    // helper can refer to the already checked imported theorem, while a new
    // proof of that theorem can refer to the helper without a false cycle.
    for index in plan.repeats {
        let entry = &entries[index];
        if entry.declaration().kind() == ConstantKind::Theorem {
            let fresh = match import_repeats::fresh_theorem(entry, env, budget.max_steps) {
                Ok(fresh) => fresh,
                Err(reason) => {
                    return Verdict::Inconclusive {
                        verified_so_far: verified,
                        reason: reason.to_owned(),
                    };
                }
            };
            let stopped = |reason| Verdict::Inconclusive {
                verified_so_far: verified,
                reason,
            };
            match admit(env, &fresh, admission_budget) {
                CheckerVerdict::Admitted(_) => {}
                CheckerVerdict::Rejected(_) => {
                    return Verdict::Rejected {
                        first_rejection: wire_name_to_core(entry.name()),
                        rejection_count: 1,
                    };
                }
                CheckerVerdict::Deferred(reason) => {
                    return stopped(format!("repeated theorem deferred: {reason:?}"));
                }
                CheckerVerdict::Inconclusive(stop) => {
                    return stopped(format!(
                        "repeated theorem admission budget exhausted: {stop:?}"
                    ));
                }
                CheckerVerdict::InternalFault(fault) => {
                    return stopped(format!("repeated theorem admission fault: {fault:?}"));
                }
            }
        }
        // Compatible erased axioms carry no body to recheck. Neither kind
        // replaces the imported binding or publishes a scratch declaration.
        verified = verified.saturating_add(1);
    }

    Verdict::Accepted {
        declarations: verified,
    }
}
