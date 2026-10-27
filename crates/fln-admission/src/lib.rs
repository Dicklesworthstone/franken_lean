//! **fln-admission** — the `.olean` import-admission council, behind a crate
//! boundary (bead `fln-import-reuse-composes-4ngt`).
//!
//! This crate holds the code that decides whether an imported `.olean`
//! declaration enters an environment: the pinned `.olean` read path, the
//! independent checker's own reading of the same bytes, the declaration
//! planner, the per-module frontier scheduler, and the K1-plus-independent-checker
//! council that admits each declaration. It was moved out of `fln` verbatim; `fln`
//! re-exports every public name it had and wraps each council method on
//! `fln::Engine`.
//!
//! The boundary is the point. The crate depends only on `fln-kernel`,
//! `fln-checker`, `fln-olean`, `fln-env`, `fln-core` and `fln-hash`, so the
//! compiler keeps the council from naming the elaborator, the compiler, the VM,
//! the server or `fln` itself. `fln-rt` (the Marrow object model) is reachable
//! only through `fln-olean`'s reader. A later step keys import-reuse records by a
//! build-time digest of this crate's sources and its dependency closure, which is
//! sound only because of that boundary.
//!
//! [`Admitted`] is the state the council reads and writes: the part of
//! `fln::Engine` that admission touches. Every other `Engine` field is carried
//! through unchanged by `fln`.
//!
//! [`AUTHORITY`] is that digest: `build.rs` reads this crate's dependency closure from
//! the `Cargo.toml` files and hashes every file of every crate in it, with the
//! workspace manifest, lock and toolchain file and the compiler's own `-vV` report.
//! `reuse::CheckerIdentity::admission_authority` keys import-reuse records by it, so a
//! rebuild that changes no code an admission depends on keeps its records.

#![forbid(unsafe_code)]
// Allocation failure unwinds to the import frontier's per-module guard.
#![feature(alloc_error_hook)]

pub mod olean_imports;
pub mod reuse;

/// The admission authority: a SHA-256 digest, made by `build.rs`, over every crate in this
/// crate's dependency closure and the toolchain that compiles them.
pub const AUTHORITY: &str = env!("FLN_ADMISSION_AUTHORITY");

/// The crates [`AUTHORITY`] digests, by directory name, comma separated.
pub const AUTHORITY_CLOSURE: &str = env!("FLN_ADMISSION_CLOSURE");

pub use fln_checker::admit::{
    AdmissionBudget as CheckerAdmissionBudget, AdmissionGround as CheckerAdmissionGround,
};
use fln_checker::admit::{
    BlockVerdict as CheckerBlockVerdict, InductiveVerdict as CheckerInductiveVerdict,
    QuotientVerdict as CheckerQuotientVerdict, Verdict as CheckerVerdict,
};
pub use fln_checker::environment::EnvironmentBudget as CheckerEnvironmentBudget;
use fln_checker::environment::{
    ConstantDeclaration as CheckerConstantDeclaration, ConstantEntry as CheckerConstantEntry,
    ConstantEnvironment as CheckerConstantEnvironment, ConstantKind as CheckerConstantKind,
    ConstantSafety as CheckerConstantSafety,
    ConstructorDeclaration as CheckerConstructorDeclaration,
    DefinitionBody as CheckerDefinitionBody, DefinitionSafety as CheckerDefinitionSafety,
    EnvironmentOutcome as CheckerEnvironmentOutcome,
    InductiveDeclaration as CheckerInductiveDeclaration, QuotientKind as CheckerQuotientKind,
    RecursorDeclaration as CheckerRecursorDeclaration, RecursorRule as CheckerRecursorRule,
    ReducibilityHint as CheckerReducibilityHint,
};
pub use fln_checker::wire::DecodeBudget as CheckerDecodeBudget;
use fln_checker::wire::{
    DecodeOutcome as CheckerDecodeOutcome, WireExpr as CheckerExpr, WireName as CheckerName,
    decode_expr_dag as checker_decode_expr_dag, decode_name as checker_decode_name,
};
use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_env::constants::{
    ConstantInfo, DefinitionSafety, DefinitionVal, QuotKind, QuotVal, ReducibilityHints,
};
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::environment::{DeclarationCommitted, EnvironmentEntry};
use fln_env::modules::CancellationProbe;
use fln_env::pmap::CollisionBudget;
use fln_hash::canon::{CanonWriter, Canonical};
use fln_hash::root::LogicalRoot;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{
    Council, CouncilOutcome, Seat, SeatBounds, SeatOrigin, SeatVerdict, convene,
};
use fln_kernel::verdict::{Budget, RejectClass};
use fln_olean::decl::DeclError as OleanDeclarationError;
use fln_olean::decl::{DeclDecoder, verify_private_superset};
use fln_olean::region::OleanView;
use fln_olean::region::{
    ModuleDataView as OleanModuleData, OleanHeader, RegionError as OleanRegionError,
    WalkBudget as OleanWalkBudget, WalkReport as OleanWalkReport,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// The part of an engine snapshot the admission council reads and writes.
///
/// `fln::Engine` keeps its own fields; it hands the council these, by value, and
/// takes them back. The persistent environments and the `Arc`-shared sets make
/// that a reference-count copy, not a deep one. `options` is here because a
/// council successor records the options it was admitted under,
/// `executable_opaques` because admitting a handed opaque marks its value
/// executable, and `runtime_initializers` because a rebuilt import closure
/// ([`reuse`]) starts it empty while a council successor carries it on.
#[derive(Debug, Clone)]
pub struct Admitted {
    pub environment: Environment,
    pub checker_environment: Option<CheckerConstantEnvironment>,
    /// Modules whose `.olean` declarations this environment admitted through
    /// [`Admitted::check_olean_modules`].
    pub imported_modules: std::sync::Arc<BTreeSet<Name>>,
    /// Exact environment produced solely by independently checked, named imports.
    pub imported_environment: Option<Environment>,
    /// Direct import edges retained from each checked module's decoded header.
    pub imported_module_dependencies: std::sync::Arc<BTreeMap<Name, Vec<Name>>>,
    /// Admitted opaques whose stored values have executable meaning.
    pub executable_opaques: std::sync::Arc<BTreeSet<Name>>,
    /// Imported globals whose initializer supplies the runtime value.
    pub runtime_initializers: std::sync::Arc<BTreeSet<Name>>,
    pub options: KVMap,
}

impl Admitted {
    /// The deterministic identity of this snapshot under the caller's exact
    /// elaboration-relevant options, as `fln::Engine::logical_root` computes it.
    pub fn logical_root(&self, options: &KVMap) -> LogicalRoot {
        self.environment.logical_root(options)
    }
}

/// Independent resource ceilings for pinned-format `.olean` inspection.
///
/// The byte ceiling is checked before any parsing or whole-file auditing.
/// Each object budget applies to its named pass rather than being silently
/// shared across passes.
#[derive(Debug, Clone, Copy)]
pub struct OleanDecodeLimits {
    pub max_bytes: usize,
    pub graph: OleanWalkBudget,
    pub module: OleanWalkBudget,
    pub declarations: OleanWalkBudget,
}

impl OleanDecodeLimits {
    /// Construct limits with an explicit whole-artifact ceiling and the
    /// codec's conservative default object budgets.
    pub fn new(max_bytes: usize) -> Self {
        let objects = OleanWalkBudget::default();
        Self {
            max_bytes,
            graph: objects,
            module: objects,
            declarations: objects,
        }
    }
}

/// A fully decoded, by-value view of one pinned-format `.olean` artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecodedOlean {
    pub header: OleanHeader,
    pub walk: OleanWalkReport,
    pub module: OleanModuleData,
    pub constants: Vec<ConstantInfo>,
    /// The independent checker's own reading of the same bytes (bead
    /// `franken_lean-z8j.1.14`): what the checker seat compares every declaration
    /// it is asked to judge against.
    pub independent: IndependentReading,
    /// Whether the authoritative module-system server and private parts were
    /// loaded in addition to the exported public part.
    pub companion_parts_loaded: bool,
}

/// The independent checker's own reading of an artifact (bead
/// `franken_lean-z8j.1.14`), made by `fln_checker::olean` from the bytes, never from
/// `fln-olean`'s decoded values: each constant's name and reading digest in table
/// order, or why the checker could not read the artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndependentReading {
    Read(Vec<(CheckerName, fln_hash::domain::Digest)>),
    Unread(String),
}

/// The checker's reading of `parts` (`[X.olean]`, or the module-system chain
/// `[X.olean, X.olean.server, X.olean.private]`), from their bytes alone.
///
/// This is the whole of the checker's `.olean` input path, and it is public so the
/// linker can measure that: `fln-conformance`'s `checker-reader-probe` references
/// nothing else, and its test refuses any `fln-core`, `fln-olean`, `fln-env`,
/// `fln-rt` or `fln-kernel` function the linker keeps reachable from here.
pub fn independent_reading(parts: &[&[u8]], limits: OleanDecodeLimits) -> IndependentReading {
    match fln_checker::olean::read_constants(parts, limits.declarations.max_objects) {
        Ok(reading) => IndependentReading::Read(
            reading
                .constants
                .iter()
                .map(|constant| (constant.name().clone(), constant.reading_digest()))
                .collect(),
        ),
        Err(error) => IndependentReading::Unread(error.to_string()),
    }
}

/// The checker's own reading of one artifact, by name, as its seat consults it.
pub struct ArtifactReadings(pub std::collections::HashMap<CheckerName, fln_hash::domain::Digest>);

/// An unread artifact and a refused allocation both leave the checker without
/// an answer, but only the allocation can recover when sibling workers stop.
#[derive(Debug)]
pub enum ArtifactReadingsError {
    Unavailable(String),
    AllocationFailure { requested: usize },
}

impl fmt::Display for ArtifactReadingsError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unavailable(reason) => formatter.write_str(reason),
            Self::AllocationFailure { requested } => {
                write!(formatter, "could not reserve {requested} checker readings")
            }
        }
    }
}

impl ArtifactReadingsError {
    pub fn into_nonanswer<T>(self) -> Result<Outcome<T>, OleanCheckError> {
        match self {
            Self::Unavailable(reason) => Ok(Outcome::Inconclusive(
                Inconclusive::dependency_unavailable(reason),
            )),
            Self::AllocationFailure { requested } => Err(OleanCheckError::AllocationFailure {
                resource: ".olean independent checker readings",
                requested,
            }),
        }
    }
}

/// Why the checker seat will not vouch for a declaration as the artifact's.
pub enum ReadingObjection {
    /// Its reading of the artifact says something else: one decoder is wrong, and
    /// a council must not agree on either reading.
    Differs(String),
    /// The declaration under review could not be projected for comparison.
    Unprojected(String),
}

impl ReadingObjection {
    fn review(&self) -> CheckerReview {
        match self {
            Self::Differs(detail) => CheckerReview::from_seat(
                SeatVerdict::Disagrees {
                    detail: detail.clone(),
                },
                None,
                None,
            ),
            Self::Unprojected(reason) => CheckerReview::no_answer(reason.clone()),
        }
    }
}

pub fn checker_name_text(name: &CheckerName) -> String {
    let parts: Vec<String> = name
        .parts()
        .iter()
        .map(|part| match part {
            fln_checker::wire::NamePart::Text(text) => text.clone(),
            fln_checker::wire::NamePart::Numeric { value, .. } => value.to_string(),
        })
        .collect();
    parts.join(".")
}

impl ArtifactReadings {
    /// Index a reading, or say why there is none to consult. An artifact the
    /// checker could not read, or that names one constant twice, gives it no
    /// independent answer about any of its declarations.
    pub fn new(reading: &IndependentReading) -> Result<Self, ArtifactReadingsError> {
        Self::new_with_reserve(reading, |index, count| index.try_reserve(count))
    }

    /// Fault tests refuse this allocation through the same typed constructor
    /// used by the council, without changing the global allocator.
    pub fn new_with_reserve(
        reading: &IndependentReading,
        reserve: impl FnOnce(
            &mut std::collections::HashMap<CheckerName, fln_hash::domain::Digest>,
            usize,
        ) -> Result<(), std::collections::TryReserveError>,
    ) -> Result<Self, ArtifactReadingsError> {
        let entries = match reading {
            IndependentReading::Read(entries) => entries,
            IndependentReading::Unread(reason) => {
                return Err(ArtifactReadingsError::Unavailable(format!(
                    "fln-checker could not read the .olean itself: {reason}"
                )));
            }
        };
        let mut readings = std::collections::HashMap::new();
        reserve(&mut readings, entries.len()).map_err(|_| {
            ArtifactReadingsError::AllocationFailure {
                requested: entries.len(),
            }
        })?;
        for (name, digest) in entries {
            if readings.insert(name.clone(), *digest).is_some() {
                return Err(ArtifactReadingsError::Unavailable(format!(
                    "fln-checker read `{}` twice in one .olean",
                    checker_name_text(name)
                )));
            }
        }
        Ok(Self(readings))
    }

    /// The objection to judging `candidate` as the artifact's declaration of its name.
    fn objection_to(&self, candidate: &CheckerConstantEntry) -> Option<ReadingObjection> {
        let name = checker_name_text(candidate.name());
        match self.0.get(candidate.name()) {
            Some(digest) if *digest == candidate.reading_digest() => None,
            Some(_) => Some(ReadingObjection::Differs(format!(
                "fln-checker's own reading of the .olean declares `{name}` differently from the \
                 declaration under review"
            ))),
            None => Some(ReadingObjection::Differs(format!(
                "fln-checker's own reading of the .olean declares no `{name}`"
            ))),
        }
    }

    /// [`Self::objection_to`] for a primary-decoded constant.
    pub fn objection(
        &self,
        info: &ConstantInfo,
        budget: CheckerDecodeBudget,
    ) -> Option<ReadingObjection> {
        match checker_entry(info, budget) {
            Ok(candidate) => self.objection_to(&candidate),
            Err(detail) => Some(ReadingObjection::Unprojected(format!(
                "projection of `{}` into fln-checker failed: {detail}",
                info.name().to_display_string()
            ))),
        }
    }
}

/// A reading objection to a declaration no council reviews: a difference refuses
/// the module as a seat's disagreement would, and a failed projection leaves it
/// without an independent answer.
fn unreviewed_reading_refusal<T>(
    name: &Name,
    objection: ReadingObjection,
) -> Result<Outcome<T>, OleanCheckError> {
    match objection {
        ReadingObjection::Differs(detail) => Err(OleanCheckError::IndependentReadingDiffers {
            name: name.clone(),
            detail,
        }),
        ReadingObjection::Unprojected(reason) => Ok(Outcome::Inconclusive(
            Inconclusive::dependency_unavailable(reason),
        )),
    }
}

/// What the checker seat compares the declaration under review against (bead
/// `franken_lean-z8j.1.14`).
#[derive(Clone, Copy)]
pub enum ReadingCheck<'a> {
    /// A source declaration: no artifact was read, so there is nothing to compare.
    Unread,
    /// An `.olean` declaration: every candidate must be the artifact's declaration
    /// of its name in the checker's own reading.
    Artifact(&'a ArtifactReadings),
    /// Already compared by the caller, as the artifact states the declaration: a
    /// subsumed repeat is renamed before its council sees it.
    Settled(Option<&'a ReadingObjection>),
}

/// The seat's review when a candidate is not what its own reading says, else
/// `None` and the seat goes on to judge.
fn reading_review(
    candidates: &[CheckerConstantEntry],
    reading: ReadingCheck<'_>,
) -> Option<CheckerReview> {
    match reading {
        ReadingCheck::Unread => None,
        ReadingCheck::Settled(objection) => objection.map(ReadingObjection::review),
        ReadingCheck::Artifact(readings) => candidates
            .iter()
            .find_map(|candidate| readings.objection_to(candidate))
            .map(|objection| objection.review()),
    }
}

/// One non-public compacted region in a module-system `.olean` chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OleanCompanionPart {
    Server,
    Private,
}

impl fmt::Display for OleanCompanionPart {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Server => ".olean.server",
            Self::Private => ".olean.private",
        })
    }
}

/// Typed refusal from the public `.olean` read path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanDecodeError {
    ArtifactTooLarge {
        bytes: usize,
        limit: usize,
    },
    UnexpectedCompanionParts,
    CompanionHeaderMismatch {
        part: OleanCompanionPart,
    },
    CompanionRegion {
        part: OleanCompanionPart,
        error: OleanRegionError,
    },
    CompanionDeclaration {
        part: OleanCompanionPart,
        error: OleanDeclarationError,
    },
    Region(OleanRegionError),
    Declaration(OleanDeclarationError),
    /// A part's fixed header is not the pinned toolchain's: its `flags`, `githash`
    /// or `lean_version` differ (bead `fln-fur.1`). `part` is `None` for the
    /// exported `.olean`.
    HeaderNotPinned {
        part: Option<OleanCompanionPart>,
        mismatch: fln_olean::pin::HeaderPinMismatch,
    },
}

/// Refuse a part whose header is not the pinned toolchain's, before any further
/// decoding: the pinned loader refuses such a file as an "incompatible header".
fn require_pinned_header(
    file: &[u8],
    part: Option<OleanCompanionPart>,
) -> Result<(), OleanDecodeError> {
    fln_olean::pin::check_pinned_header(file)
        .map_err(|mismatch| OleanDecodeError::HeaderNotPinned { part, mismatch })
}

impl fmt::Display for OleanDecodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ArtifactTooLarge { bytes, limit } => {
                write!(f, ".olean artifact has {bytes} bytes; limit is {limit}")
            }
            Self::UnexpectedCompanionParts => write!(
                f,
                "standalone .olean artifact must not have module-system companion parts"
            ),
            Self::CompanionHeaderMismatch { part } => write!(
                f,
                "{part} identity fields do not match the exported .olean part"
            ),
            Self::CompanionRegion { part, error } => {
                write!(f, "{part} region: {error}")
            }
            Self::CompanionDeclaration { part, error } => {
                write!(f, "{part} declaration: {error}")
            }
            Self::Region(error) => write!(f, ".olean region: {error}"),
            Self::Declaration(error) => write!(f, ".olean declaration: {error}"),
            Self::HeaderNotPinned {
                part: None,
                mismatch,
            } => write!(f, "incompatible .olean header: {mismatch}"),
            Self::HeaderNotPinned {
                part: Some(part),
                mismatch,
            } => write!(f, "incompatible {part} header: {mismatch}"),
        }
    }
}

impl std::error::Error for OleanDecodeError {}

impl OleanDecodeError {
    /// Whether this refusal is solely an explicit byte/object budget, or the host
    /// refusing a decode reservation, rather than malformed input or a
    /// companion-chain identity failure.
    ///
    /// A host refusal was reported as a decode `Budget` until fln-s97y gave it its
    /// own variant; it stays in this class so the CLI's non-answer exit is unchanged.
    pub const fn is_resource_exhaustion(&self) -> bool {
        self.is_host_allocation_refusal()
            || matches!(
                self,
                Self::ArtifactTooLarge { .. }
                    | Self::Region(
                        OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. }
                    )
                    | Self::Declaration(OleanDeclarationError::Budget { .. })
                    | Self::Declaration(OleanDeclarationError::Region(
                        OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. }
                    ))
                    | Self::CompanionRegion {
                        error: OleanRegionError::BudgetExhausted { .. }
                            | OleanRegionError::PayloadBudgetExhausted { .. },
                        ..
                    }
                    | Self::Declaration(OleanDeclarationError::ChainTooLarge { .. })
                    | Self::CompanionDeclaration {
                        error: OleanDeclarationError::Budget { .. }
                            | OleanDeclarationError::ChainTooLarge { .. },
                        ..
                    }
                    | Self::CompanionDeclaration {
                        error: OleanDeclarationError::Region(
                            OleanRegionError::BudgetExhausted { .. }
                                | OleanRegionError::PayloadBudgetExhausted { .. }
                        ),
                        ..
                    }
            )
    }

    /// The construct the decoder stopped at because it does not interpret it yet,
    /// when that is the whole reason: a limit of this implementation, not a fault in
    /// the input (FL-INV-07). Today that is a `Name.num` whose component needs an
    /// `mpz`.
    pub fn unsupported_construct(&self) -> Option<&'static str> {
        match self {
            Self::Declaration(OleanDeclarationError::Unsupported { what, .. })
            | Self::CompanionDeclaration {
                error: OleanDeclarationError::Unsupported { what, .. },
                ..
            } => Some(what),
            _ => None,
        }
    }

    /// Whether the host refused a reservation the decoder needed: a non-answer
    /// about this host, never a property of the input.
    pub const fn is_host_allocation_refusal(&self) -> bool {
        matches!(
            self,
            Self::Declaration(OleanDeclarationError::AllocationRefused { .. })
                | Self::CompanionDeclaration {
                    error: OleanDeclarationError::AllocationRefused { .. },
                    ..
                }
        )
    }

    /// The allowance this decode stop exceeded and what had been spent, when it is an
    /// explicit byte or object budget whose own numbers show it was exceeded
    /// (bead fln-s97y). The frontier reports such a stop as a typed resource
    /// exhaustion instead of a failed module. `None` for every other refusal, and
    /// for a budget error whose numbers do not show an overrun: a stop that cannot
    /// show its allowance is not reported as one.
    pub fn resource_usage(&self) -> Option<fln_core::outcome::ResourceUsage> {
        use fln_core::diag::{ResourceReason, StructuralUnit};
        let to_u64 = |value: usize| u64::try_from(value).unwrap_or(u64::MAX);
        let usage = |unit, allowed: u64, observed: u64| fln_core::outcome::ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit },
            allowed,
            observed,
        };
        let region = |error: &OleanRegionError| match error {
            OleanRegionError::BudgetExhausted { visited, budget } => {
                Some(usage(StructuralUnit::ProducedNodes, *budget, *visited))
            }
            OleanRegionError::PayloadBudgetExhausted { required, budget } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*budget),
                to_u64(*required),
            )),
            _ => None,
        };
        let declaration = |error: &OleanDeclarationError| match error {
            OleanDeclarationError::Budget { visited, budget } => {
                Some(usage(StructuralUnit::ProducedNodes, *budget, *visited))
            }
            OleanDeclarationError::ChainTooLarge { bytes, limit } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*limit),
                to_u64(*bytes),
            )),
            OleanDeclarationError::Region(error) => region(error),
            _ => None,
        };
        let usage = match self {
            Self::ArtifactTooLarge { bytes, limit } => Some(usage(
                StructuralUnit::InputBytes,
                to_u64(*limit),
                to_u64(*bytes),
            )),
            Self::Region(error) | Self::CompanionRegion { error, .. } => region(error),
            Self::Declaration(error) | Self::CompanionDeclaration { error, .. } => {
                declaration(error)
            }
            _ => None,
        };
        usage.filter(fln_core::outcome::ResourceUsage::is_genuine_exhaustion)
    }
}

impl From<OleanRegionError> for OleanDecodeError {
    fn from(error: OleanRegionError) -> Self {
        Self::Region(error)
    }
}

impl From<OleanDeclarationError> for OleanDecodeError {
    fn from(error: OleanDeclarationError) -> Self {
        Self::Declaration(error)
    }
}

/// One physical part of a module image, in the Reference's load order: the
/// exported `.olean`, then `.olean.server`, then `.olean.private`
/// (`saveModuleDataParts` writes them in that order, and each later part is
/// compacted against the earlier ones).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OleanModulePart {
    Exported,
    Server,
    Private,
}

impl OleanModulePart {
    /// Every part, in load order.
    pub const LOAD_ORDER: [Self; 3] = [Self::Exported, Self::Server, Self::Private];

    /// What the Reference appends to the exported file name to name this part
    /// (`OLeanLevel.adjustFileName`): nothing, `.server`, or `.private`.
    pub const fn file_suffix(self) -> &'static str {
        match self {
            Self::Exported => "",
            Self::Server => ".server",
            Self::Private => ".private",
        }
    }
}

impl fmt::Display for OleanModulePart {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Exported => ".olean",
            Self::Server => ".olean.server",
            Self::Private => ".olean.private",
        })
    }
}

/// Audit and decode one `.olean` produced by the pinned Reference epoch.
///
/// This is the existing Grimoire reader behind the embeddable facade: it
/// validates the entire compacted region through the shared runtime audit,
/// walks the reachable object graph, decodes `ModuleData`, and cross-checks
/// every decoded declaration's stored computed fields. The returned values
/// own their data and do not borrow the artifact.
///
/// This function does not resolve imports, admit or kernel-check declarations,
/// advance an [`Engine`], or write/re-emit `.olean` bytes.
pub fn decode_olean_artifact(
    artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<DecodedOlean, OleanDecodeError> {
    decode_olean_artifact_with(artifact, limits, CheckerReading::Read)
}

/// Whether a decode also produces the independent checker's own reading of the
/// bytes ([`independent_reading`]).
///
/// Only a council consults that reading. The `reuse-verified` rebuild admits no
/// declaration through the checker in its run, so making it would be a second
/// full decode of every module whose result is discarded; for the pinned `Init`
/// closure it was a quarter of a warm import. A decode that skips it records
/// [`IndependentReading::Unread`] with this reason, so a later attempt to consult
/// it is refused by [`ArtifactReadings::new`] rather than silently satisfied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckerReading {
    Read,
    Skip,
}

const CHECKER_READING_SKIPPED: &str =
    "not read: this decode serves a reuse-verified rebuild, which consults no checker reading";

fn checker_reading(
    parts: &[&[u8]],
    limits: OleanDecodeLimits,
    mode: CheckerReading,
) -> IndependentReading {
    match mode {
        CheckerReading::Read => independent_reading(parts, limits),
        CheckerReading::Skip => IndependentReading::Unread(CHECKER_READING_SKIPPED.to_owned()),
    }
}

fn decode_olean_artifact_with(
    artifact: &[u8],
    limits: OleanDecodeLimits,
    reading: CheckerReading,
) -> Result<DecodedOlean, OleanDecodeError> {
    if artifact.len() > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes: artifact.len(),
            limit: limits.max_bytes,
        });
    }

    let view = OleanView::parse(artifact)?;
    require_pinned_header(artifact, None)?;
    view.shared_audit()?;
    let walk = view.walk(limits.graph)?;
    let module = view.module_data(limits.module)?;
    let constants = DeclDecoder::new(&view, limits.declarations).decode_module_constants()?;

    Ok(DecodedOlean {
        header: view.header.clone(),
        walk,
        module,
        constants,
        independent: checker_reading(&[artifact], limits, reading),
        companion_parts_loaded: false,
    })
}

/// The direct imports of one `.olean`, read from its exported part without
/// decoding its declarations: enough to compute an import closure before
/// deciding which artifacts to read in full.
pub fn olean_module_imports(
    artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<Vec<Name>, OleanDecodeError> {
    if artifact.len() > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes: artifact.len(),
            limit: limits.max_bytes,
        });
    }
    let view = OleanView::parse(artifact)?;
    require_pinned_header(artifact, None)?;
    let module = view.module_data(limits.module)?;
    Ok(module
        .imports
        .iter()
        .map(|import| import.module.clone())
        .collect())
}

/// Audit and decode one complete module-system `.olean` artifact chain.
///
/// The exported part supplies the import graph and public module metadata.
/// The private part supplies the authoritative constant array used by Lean's
/// `import all` path, including definition bodies and private equation-compiler
/// auxiliaries. The server and private regions are parsed in their original
/// compacted address spaces, given the shared runtime's full-surface audit in
/// that same address space (every object, reachable or not, with pointers
/// allowed to land in the earlier parts), walked through their
/// dependency-aware object graphs, and their declarations validated before
/// any result is returned. A server whose declaration arrays reuse the exact
/// exported-region objects reuses their successful decode under the same
/// declaration budget; other server arrays are decoded in full. This function
/// does not resolve imports or admit any declaration into an [`Engine`].
pub fn decode_olean_module_artifacts(
    artifact: &[u8],
    server_artifact: &[u8],
    private_artifact: &[u8],
    limits: OleanDecodeLimits,
) -> Result<DecodedOlean, OleanDecodeError> {
    decode_olean_module_artifacts_with(
        artifact,
        server_artifact,
        private_artifact,
        limits,
        CheckerReading::Read,
    )
}

fn decode_olean_module_artifacts_with(
    artifact: &[u8],
    server_artifact: &[u8],
    private_artifact: &[u8],
    limits: OleanDecodeLimits,
    reading: CheckerReading,
) -> Result<DecodedOlean, OleanDecodeError> {
    let bytes = artifact
        .len()
        .checked_add(server_artifact.len())
        .and_then(|total| total.checked_add(private_artifact.len()))
        .ok_or(OleanDecodeError::ArtifactTooLarge {
            bytes: usize::MAX,
            limit: limits.max_bytes,
        })?;
    if bytes > limits.max_bytes {
        return Err(OleanDecodeError::ArtifactTooLarge {
            bytes,
            limit: limits.max_bytes,
        });
    }

    let public_view = OleanView::parse(artifact)?;
    require_pinned_header(artifact, None)?;
    public_view.shared_audit()?;
    public_view.walk(limits.graph)?;
    let module = public_view.module_data(limits.module)?;
    if !module.is_module {
        return Err(OleanDecodeError::UnexpectedCompanionParts);
    }
    let exported_constants =
        DeclDecoder::new(&public_view, limits.declarations).decode_module_constants()?;

    let same_identity = |header: &OleanHeader| {
        header.version == public_view.header.version
            && header.flags == public_view.header.flags
            && header.lean_version == public_view.header.lean_version
            && header.githash == public_view.header.githash
    };

    let server_part = OleanCompanionPart::Server;
    let server_view =
        OleanView::parse_with_dependencies(server_artifact, &[artifact]).map_err(|error| {
            OleanDecodeError::CompanionRegion {
                part: server_part,
                error,
            }
        })?;
    require_pinned_header(server_artifact, Some(server_part))?;
    if !same_identity(&server_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: server_part });
    }
    server_view
        .shared_audit()
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
    server_view
        .walk(limits.graph)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
    server_view
        .module_data(limits.module)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?;
    // The pinned server part points its declaration arrays back into the
    // exported region. Reuse that completed decode only when both arrays name
    // the same immutable objects under an unambiguous dependency map. Equal
    // names, counts or stored addresses alone are not a reuse proof.
    if !server_view
        .reuses_module_constant_arrays(&public_view)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: server_part,
            error,
        })?
    {
        DeclDecoder::new(&server_view, limits.declarations)
            .decode_module_constants()
            .map_err(|error| OleanDecodeError::CompanionDeclaration {
                part: server_part,
                error,
            })?;
    }

    let private_part = OleanCompanionPart::Private;
    let private_view =
        OleanView::parse_with_dependencies(private_artifact, &[artifact, server_artifact])
            .map_err(|error| OleanDecodeError::CompanionRegion {
                part: private_part,
                error,
            })?;
    require_pinned_header(private_artifact, Some(private_part))?;
    if !same_identity(&private_view.header) {
        return Err(OleanDecodeError::CompanionHeaderMismatch { part: private_part });
    }
    private_view
        .shared_audit()
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: private_part,
            error,
        })?;
    let walk =
        private_view
            .walk(limits.graph)
            .map_err(|error| OleanDecodeError::CompanionRegion {
                part: private_part,
                error,
            })?;
    private_view
        .module_data(limits.module)
        .map_err(|error| OleanDecodeError::CompanionRegion {
            part: private_part,
            error,
        })?;
    let constants = DeclDecoder::new(&private_view, limits.declarations)
        .decode_module_constants()
        .map_err(|error| OleanDecodeError::CompanionDeclaration {
            part: private_part,
            error,
        })?;

    // Returning the private array INSTEAD of the exported one is sound only
    // because it is a superset. That is a property of the Reference's emitter,
    // not something the format enforces, and an unguarded assumption here would
    // silently hand the kernel fewer declarations than the module declares —
    // franken_lean-timy's failure mode reached by a different cause. The
    // exported array was decoded above to validate it and was previously
    // discarded; this makes that work load-bearing instead of adding a pass.
    verify_private_superset(&exported_constants, &constants).map_err(|error| {
        OleanDecodeError::CompanionDeclaration {
            part: private_part,
            error,
        }
    })?;

    Ok(DecodedOlean {
        header: public_view.header.clone(),
        walk,
        module,
        constants,
        independent: checker_reading(
            &[artifact, server_artifact, private_artifact],
            limits,
            reading,
        ),
        companion_parts_loaded: true,
    })
}

/// Independent ceilings for decoding and checking standalone `.olean` input.
///
/// `max_declarations` bounds the planning tables before they are allocated;
/// `max_dependency_presentations` bounds the iterative walk used to recover a
/// deterministic declaration order. The kernel and independent checker retain
/// their own, separate limits in [`EngineAdmissionLimits`].
#[derive(Debug, Clone, Copy)]
pub struct OleanCheckLimits {
    pub decode: OleanDecodeLimits,
    pub admission: EngineAdmissionLimits,
    pub max_modules: usize,
    pub max_total_bytes: usize,
    pub max_declarations: usize,
    pub max_dependency_presentations: usize,
}

impl OleanCheckLimits {
    /// Construct conservative product limits around explicit artifact and
    /// kernel-stack ceilings.
    pub fn new(max_bytes: usize, kernel: Budget) -> Self {
        Self {
            decode: OleanDecodeLimits::new(max_bytes),
            admission: EngineAdmissionLimits::new(kernel),
            max_modules: 100_000,
            max_total_bytes: max_bytes,
            max_declarations: 1_000_000,
            max_dependency_presentations: 100_000_000,
        }
    }
}

/// One declaration whose K1 verdict and independent-checker veto both
/// completed while checking an `.olean`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanCheckedDeclaration {
    pub name: Name,
    pub checker: CheckerAgreement,
}

/// Authoritative result of checking every decoded declaration in one
/// standalone `.olean`.
///
/// The returned engine is the only successor. Every error or non-answer
/// exposes no partially advanced snapshot, so checking is atomic from the
/// caller's point of view.
#[derive(Debug)]
pub struct CheckedOlean<E = Admitted> {
    pub engine: E,
    pub decoded: DecodedOlean,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub declarations: Vec<OleanCheckedDeclaration>,
}

impl<E> CheckedOlean<E> {
    /// The same result around another representation of its successor engine.
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> CheckedOlean<F> {
        CheckedOlean {
            engine: map(self.engine),
            decoded: self.decoded,
            base_logical_root: self.base_logical_root,
            result_logical_root: self.result_logical_root,
            declarations: self.declarations,
        }
    }
}

/// [`CheckedOlean`] before its logical roots are computed.
struct UnrootedOlean {
    engine: Admitted,
    decoded: DecodedOlean,
    declarations: Vec<OleanCheckedDeclaration>,
    /// Nothing was admitted: `engine` is the checking engine's clone, so the
    /// result root is the base root.
    unchanged: bool,
}

/// Borrowed bytes and their authoritative module name in a closed import set.
#[derive(Debug, Clone, Copy)]
pub struct OleanModuleInput<'a> {
    pub name: &'a Name,
    pub artifact: &'a [u8],
    pub server_artifact: Option<&'a [u8]>,
    pub private_artifact: Option<&'a [u8]>,
}

/// One checked module inside a closed `.olean` import set.
#[derive(Debug)]
pub struct CheckedOleanModule {
    pub name: Name,
    pub decoded: DecodedOlean,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub declarations: Vec<OleanCheckedDeclaration>,
}

/// Whether a module stopped because the host refused memory. An explicit
/// checking/decode allowance, a silent council and an unsupported construct do
/// not belong here: retrying those with the same budget cannot remove another
/// worker's memory pressure.
pub fn olean_host_memory_refusal(error: &OleanCheckError) -> bool {
    fn admission(error: &EngineAdmissionError) -> bool {
        match error {
            EngineAdmissionError::BatchDeclaration { error, .. } => admission(error),
            EngineAdmissionError::AllocationFailure { .. } => true,
            _ => false,
        }
    }
    match error {
        OleanCheckError::AllocationFailure { .. } | OleanCheckError::HostMemory { .. } => true,
        OleanCheckError::Admission(error) => admission(error),
        OleanCheckError::Decode(error) | OleanCheckError::ModuleDecode { error, .. } => {
            error.is_host_allocation_refusal()
        }
        _ => false,
    }
}

/// The frontier's verdict for a module whose check ended in an error.
///
/// FL-INV-07: a council whose objecting seats were all silent or ran out
/// ([`EngineAdmissionError::CouncilNoAnswer`]) and a planning budget that ran
/// out are non-answers, so the module is `Inconclusive`, never refused. Our own
/// accounting failing is an `InternalFault`. A kernel rejection, a council
/// disagreement and a malformed artifact stay `Failed`, and so, for now, does a
/// decode budget stop. A refused allocation is a non-answer too: it is not a
/// verdict about the module. It carries no declared allowance for a
/// [`ResourceUsage`](fln_core::outcome::ResourceUsage) to report, so, like a
/// silent council, it says what was unavailable (fln-frontier-oom-abort-w9dx).
pub fn frontier_error_verdict(error: OleanCheckError) -> OleanModuleVerdict {
    fn admission_leaf(error: &EngineAdmissionError) -> &EngineAdmissionError {
        match error {
            EngineAdmissionError::BatchDeclaration { error, .. } => admission_leaf(error),
            other => other,
        }
    }
    let fault = |detail: String| {
        OleanModuleVerdict::InternalFault(InternalFault::new("olean frontier", detail))
    };
    match &error {
        OleanCheckError::Admission(admission) => match admission_leaf(admission) {
            EngineAdmissionError::CouncilNoAnswer { summary } => OleanModuleVerdict::Inconclusive(
                Inconclusive::dependency_unavailable(format!("council had no answer: {summary}")),
            ),
            leaf @ EngineAdmissionError::AllocationFailure { .. } => {
                OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                    "host memory: {leaf}"
                )))
            }
            leaf @ (EngineAdmissionError::CheckerBridge { .. }
            | EngineAdmissionError::UnexpectedPublication { .. }) => fault(leaf.to_string()),
            _ => OleanModuleVerdict::Failed(error),
        },
        OleanCheckError::DependencyPresentationLimit { observed, limit }
        | OleanCheckError::DeclarationLimit { observed, limit } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::resource(
                fln_core::outcome::ResourceUsage {
                    reason: fln_core::diag::ResourceReason::StructuralBudget {
                        unit: fln_core::diag::StructuralUnit::ProducedNodes,
                    },
                    allowed: u64::try_from(*limit).unwrap_or(u64::MAX),
                    observed: u64::try_from(*observed).unwrap_or(u64::MAX),
                },
            ))
        }
        OleanCheckError::AllocationFailure { .. } | OleanCheckError::HostMemory { .. } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "host memory: {error}"
            )))
        }
        // A decode stop is a non-answer when the decoder ran out of an explicit
        // allowance or the host refused it memory (fln-s97y). Malformed input and
        // identity failures stay `Failed`.
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. }
            if decode.is_host_allocation_refusal() =>
        {
            OleanModuleVerdict::Inconclusive(Inconclusive::dependency_unavailable(format!(
                "host memory: {error}"
            )))
        }
        // A construct this implementation cannot judge yet is a non-answer about the
        // tool, never evidence against the module (FL-INV-07): a payload the decoder
        // does not interpret, or an envelope the checker facade cannot rebuild.
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. }
            if decode.unsupported_construct().is_some() =>
        {
            OleanModuleVerdict::Inconclusive(Inconclusive::unsupported(error.to_string()))
        }
        OleanCheckError::UnsupportedDeclaration { .. }
        | OleanCheckError::MutualEnvelopeUnsupported { .. }
        | OleanCheckError::InductiveEnvelopeUnsupported { .. }
        | OleanCheckError::QuotientEnvelopeUnsupported { .. } => {
            OleanModuleVerdict::Inconclusive(Inconclusive::unsupported(error.to_string()))
        }
        OleanCheckError::Decode(decode) | OleanCheckError::ModuleDecode { error: decode, .. } => {
            match decode.resource_usage() {
                Some(usage) => OleanModuleVerdict::Inconclusive(Inconclusive::resource(usage)),
                None => OleanModuleVerdict::Failed(error),
            }
        }
        OleanCheckError::InternalInvariant { .. } => fault(error.to_string()),
        _ => OleanModuleVerdict::Failed(error),
    }
}

/// The panic payload [`install_host_allocation_failure_hook`] raises when the
/// host refuses an allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HostAllocationFailure {
    /// The size of the refused request, in bytes.
    pub requested: usize,
}

/// Make a refused host allocation unwind instead of aborting the process
/// (fln-frontier-oom-abort-w9dx). Rust's default handler aborts every thread at
/// once, so one module's exhaustion used to end a whole frontier run and lose
/// every verdict in it. With this hook, the unwind reaches the frontier's
/// per-module guard, and that module's row is a typed non-answer while the run
/// continues. A binary calls this once, before any work. The process-wide hook
/// belongs to whoever owns the process, so the library never installs it.
pub fn install_host_allocation_failure_hook() {
    std::alloc::set_alloc_error_hook(host_allocation_failure);
}

fn host_allocation_failure(layout: std::alloc::Layout) {
    // The default handler's message; stderr is unbuffered, so this allocates
    // nothing.
    eprintln!("memory allocation of {} bytes failed", layout.size());
    std::panic::panic_any(HostAllocationFailure {
        requested: layout.size(),
    });
}

/// Run one module's check. An unwind out of it ends only that module, as its
/// row; it never ends the run. Without this, a panicking worker thread died
/// before reporting, and its scheduler waited for the module forever.
pub fn frontier_guarded(
    index: usize,
    retain: bool,
    started: std::time::Instant,
    check: impl FnOnce() -> FrontierDone,
) -> FrontierDone {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)).unwrap_or_else(|payload| {
        let error = frontier_unwound(payload);
        FrontierDone {
            index,
            host_memory_refusal: olean_host_memory_refusal(&error),
            verdict: frontier_error_verdict(error.clone()),
            accepted: None,
            engine: None,
            elapsed: started.elapsed(),
            retained: retain.then_some(FrontierRetained::Failed(error)),
        }
    })
}

/// What an unwind out of a module check means: the host refused an allocation,
/// or one of our invariants broke. A panic is never a verdict.
pub fn frontier_unwound(payload: Box<dyn std::any::Any + Send>) -> OleanCheckError {
    olean_unwound(payload, "a frontier module check panicked")
}

fn olean_unwound(payload: Box<dyn std::any::Any + Send>, detail: &'static str) -> OleanCheckError {
    match payload.downcast::<HostAllocationFailure>() {
        Ok(failure) => OleanCheckError::HostMemory {
            requested: failure.requested,
        },
        Err(_) => OleanCheckError::InternalInvariant { detail },
    }
}

/// One module's outcome in an [`Engine::check_olean_frontier`] run.
#[derive(Debug)]
pub enum OleanModuleVerdict {
    /// Every declaration was admitted by K1 and the independent checker.
    Accepted { declarations: usize },
    /// The module was refused: its artifact, its import set, or one of its
    /// declarations.
    Failed(OleanCheckError),
    /// No verdict was reached (FL-INV-07). Counted neither as accepted nor rejected.
    Inconclusive(Inconclusive),
    /// An invariant failure while checking the module.
    InternalFault(InternalFault),
    /// Not checked, because the named import has no accepted verdict. A module is
    /// never checked against an import that was not itself admitted.
    Blocked { by: Name },
}

/// One row of a frontier run. `elapsed` is operational wall time, never part of any
/// logical identity.
#[derive(Debug)]
pub struct OleanFrontierRow {
    pub name: Name,
    pub verdict: OleanModuleVerdict,
    /// Total time spent checking this module, including a refused first attempt.
    pub elapsed: std::time::Duration,
    /// A first attempt refused host memory while another module was in flight.
    /// When present, the final verdict above comes from one full retry with no
    /// other module check in flight, under the original limits. No more than one
    /// retry is made, and neither attempt is an additional module row.
    pub memory_retry: Option<OleanFrontierMemoryRetry>,
    /// An initial parallel decode refused host memory and was repeated once
    /// after every decoder worker exited. A successful decode is only input to
    /// the council: its result here does not imply this row was accepted.
    /// Decode times are separate from the checking time in `elapsed`.
    pub decode_memory_retry: Option<OleanDecodeMemoryRetry>,
}

/// The first attempt of a module checked again in isolation. Its final attempt
/// is the enclosing row's verdict and `elapsed - first_elapsed`.
#[derive(Debug)]
pub struct OleanFrontierMemoryRetry {
    pub first_refusal: Inconclusive,
    pub first_elapsed: std::time::Duration,
}

/// Both attempts of an initial decode retried without another decoder running.
/// The same bytes and limits are used again; successfully decoded sibling
/// artifacts remain available for import planning.
#[derive(Debug)]
pub struct OleanDecodeMemoryRetry {
    pub first_error: OleanCheckError,
    pub first_elapsed: std::time::Duration,
    pub retry_elapsed: std::time::Duration,
    /// `Ok(())` means the artifact decoded. Declarations still need the ordinary
    /// K1 and independent-checker judgments before they can be admitted.
    pub retry_result: Result<(), OleanCheckError>,
}

/// What a frontier observer is told: `Started` just before a module's
/// declarations go to the council, `Settled` the moment its row exists, and
/// `Decided` once its row and every earlier one exist. A module that is blocked,
/// or that failed to decode, settles and is decided without ever starting.
///
/// `Decided` arrives in frontier order, so that stream is the same at any thread
/// count. `Settled` arrives in completion order, which is not: it exists so a row
/// survives a crash that would have held it back behind a slower module still in
/// flight (bead fln-frontier-oom-abort-w9dx). Every module settles exactly once,
/// before it is decided, and both carry its frontier `position`.
#[derive(Debug, Clone, Copy)]
pub enum OleanFrontierEvent<'a> {
    Started {
        position: usize,
        total: usize,
        module: &'a Name,
    },
    /// A host-memory refusal is retried only after all other module checks have
    /// finished. This is attempt two, not another module or a settled verdict.
    Retrying {
        position: usize,
        total: usize,
        module: &'a Name,
        previous: &'a OleanFrontierMemoryRetry,
    },
    Settled {
        position: usize,
        total: usize,
        row: &'a OleanFrontierRow,
    },
    Decided {
        position: usize,
        total: usize,
        row: &'a OleanFrontierRow,
    },
}

/// Per-module result of checking a closed `.olean` set without stopping at the first
/// failure.
#[derive(Debug)]
pub struct OleanFrontier<E = Admitted> {
    /// One engine holding exactly the accepted modules, if one can exist. Two
    /// accepted modules that never import each other may declare different
    /// constants under one name: Lean permits it (each of two executables has its
    /// own `main`), and no single environment holds both. Then this is the
    /// `DuplicateDeclaration` that stops the merge, and every row still stands.
    pub engine: Result<E, OleanCheckError>,
    pub rows: Vec<OleanFrontierRow>,
}

impl<E> OleanFrontier<E> {
    /// The same frontier around another representation of its merged engine.
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> OleanFrontier<F> {
        OleanFrontier {
            engine: self.engine.map(map),
            rows: self.rows,
        }
    }
}

/// How a frontier run spreads its modules over threads. Logical checking uses
/// only each module's own closure. A concurrent host-memory refusal is retried
/// once in isolation; timings and attempt records can differ with this count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OleanFrontierJobs {
    /// Modules checked at once. One checks every module on the calling thread.
    pub threads: std::num::NonZeroUsize,
    /// Stack for each worker thread when `threads` is above one. The kernel budget
    /// in the run's limits must be calibrated for it, as for the calling thread.
    pub worker_stack_bytes: usize,
}

impl OleanFrontierJobs {
    /// One module at a time, on the calling thread.
    pub const SERIAL: OleanFrontierJobs = OleanFrontierJobs {
        threads: std::num::NonZeroUsize::MIN,
        worker_stack_bytes: 0,
    };
}

/// A module whose council check passed, as its importers need it.
pub struct FrontierAccepted {
    pub index: usize,
    pub position: usize,
    pub name: Name,
    /// Every constant the module added, with the digest its engine computed.
    pub admitted: Vec<EnvironmentEntry>,
}

/// The accepted import a module's closure engine starts from, and its closure.
#[derive(Clone)]
pub struct FrontierBase {
    engine: std::sync::Arc<Admitted>,
    pub closure: std::sync::Arc<BTreeSet<usize>>,
}

/// One module handed to the council, with the accepted modules of its closure.
pub struct FrontierJob {
    pub index: usize,
    pub position: usize,
    pub name: Name,
    pub artifact: DecodedOlean,
    pub base: Option<FrontierBase>,
    pub closure: Vec<std::sync::Arc<FrontierAccepted>>,
    /// Keep what [`Engine::check_olean_modules_scheduled`] reassembles the serial
    /// result from; the frontier itself keeps only verdicts.
    pub retain: bool,
}

/// Only the already accepted, shared imports survive a failed attempt. The
/// attempted module's decoded constants and checker state are dropped by the
/// worker; its unchanged input bytes are decoded again for the isolated retry.
#[derive(Clone)]
struct FrontierRetryImports {
    base: Option<FrontierBase>,
    closure: Vec<std::sync::Arc<FrontierAccepted>>,
}

struct FrontierWork {
    index: usize,
    position: usize,
    /// Absent only for a retry, whose original artifact was dropped.
    artifact: Option<DecodedOlean>,
    imports: FrontierRetryImports,
}

pub struct FrontierDone {
    pub index: usize,
    pub verdict: OleanModuleVerdict,
    /// Derived from the original typed error, before its public nonanswer is
    /// rendered. Never inferred by matching diagnostic text.
    pub host_memory_refusal: bool,
    pub accepted: Option<FrontierAccepted>,
    /// The engine after checking an accepted module: its closure's environment
    /// plus what it admitted. A scheduler keeps it only while a module not yet
    /// dispatched will start from it ([`FrontierEngines`]).
    pub engine: Option<Admitted>,
    pub elapsed: std::time::Duration,
    /// Present only for a [`FrontierJob::retain`] job that completed or failed.
    pub retained: Option<FrontierRetained>,
}

/// A retaining frontier job's own record: what the serial result is reassembled
/// from for a module whose check completed (its decoded artifact and checker
/// rows; for each decoded constant, the digest its own engine holds under that
/// name; each admitted constant's checker entry), or the exact error its check
/// returned, which the frontier's verdict reclassifies.
pub enum FrontierRetained {
    Checked {
        decoded: Box<DecodedOlean>,
        declarations: Vec<OleanCheckedDeclaration>,
        closure_digests: Vec<Option<fln_hash::domain::Digest>>,
        checker_entries: BTreeMap<Name, Result<CheckerConstantEntry, &'static str>>,
    },
    Failed(OleanCheckError),
}

/// The import a frontier module's closure engine starts from: the import with
/// the largest closure, the earlier on a tie. It depends only on the import
/// graph, so a scheduler can count each engine's future users before any check.
pub fn frontier_base_of(
    dependencies: &[BTreeSet<usize>],
    closures: &[std::sync::Arc<BTreeSet<usize>>],
    position: impl Fn(usize) -> usize,
    index: usize,
) -> Option<usize> {
    dependencies[index]
        .iter()
        .copied()
        .filter(|dependency| *dependency != index)
        .max_by(|left, right| {
            closures[*left]
                .len()
                .cmp(&closures[*right].len())
                .then(position(*right).cmp(&position(*left)))
        })
}

/// Each admitted constant's checker entry in `engine`'s retained projection,
/// which a scheduled module set reassembles its serial projection from. A
/// constant without one is recorded as the invariant the reassembly reports.
pub fn frontier_checker_entries(
    engine: &Admitted,
    admitted: &[EnvironmentEntry],
    limits: OleanCheckLimits,
) -> BTreeMap<Name, Result<CheckerConstantEntry, &'static str>> {
    admitted
        .iter()
        .map(|entry| {
            let name = entry.declaration().name().clone();
            let checker = engine
                .checker_environment
                .as_ref()
                .ok_or("a module that admitted constants retains no checker projection")
                .and_then(|projection| {
                    let wire = decode_checker_name(&name, limits.admission.checker.decode)
                        .map_err(|_| "an admitted constant has no checker name")?;
                    let declaration = projection
                        .find(&wire)
                        .ok_or("an admitted constant is missing from its checker projection")?;
                    Ok(CheckerConstantEntry::new(wire, declaration.clone()))
                });
            (name, checker)
        })
        .collect()
}

/// Accepted engines a frontier still needs. Each module's engine is kept only
/// while a module not yet dispatched (or decided without a check) will start
/// from it; every other module of a closure contributes only its admitted
/// entries. Without this, every accepted module's whole engine, with the
/// checker terms it decoded for itself, lived until the run ended.
pub struct FrontierEngines {
    base_of: Vec<Option<usize>>,
    users: Vec<usize>,
    pub engines: Vec<Option<std::sync::Arc<Admitted>>>,
}

impl FrontierEngines {
    pub fn new(base_of: Vec<Option<usize>>) -> Self {
        let mut users = vec![0_usize; base_of.len()];
        for base in base_of.iter().flatten() {
            users[*base] += 1;
        }
        let engines = (0..base_of.len()).map(|_| None).collect();
        Self {
            base_of,
            users,
            engines,
        }
    }

    /// Keep an accepted module's engine if some later module starts from it.
    pub fn keep(&mut self, index: usize, engine: Option<Admitted>) {
        if self.users[index] > 0 {
            self.engines[index] = engine.map(std::sync::Arc::new);
        }
    }

    /// `index` leaves the schedule: dispatched (`take` its base) or decided
    /// without a check. Its base loses a user and is dropped at the last one.
    pub fn release(
        &mut self,
        index: usize,
        closures: &[std::sync::Arc<BTreeSet<usize>>],
        take: bool,
    ) -> Result<Option<FrontierBase>, OleanCheckError> {
        let Some(base) = self.base_of[index] else {
            return Ok(None);
        };
        self.users[base] =
            self.users[base]
                .checked_sub(1)
                .ok_or(OleanCheckError::InternalInvariant {
                    detail: "a frontier base engine lost more users than it had",
                })?;
        let engine = if take {
            Some(
                self.engines[base]
                    .clone()
                    .ok_or(OleanCheckError::InternalInvariant {
                        detail: "a dispatched module's base engine was not kept",
                    })?,
            )
        } else {
            None
        };
        if self.users[base] == 0 {
            self.engines[base] = None;
        }
        Ok(engine.map(|engine| FrontierBase {
            engine,
            closure: std::sync::Arc::clone(&closures[base]),
        }))
    }
}

/// One module of a scheduled set whose check completed, with what the serial result
/// keeps of it.
pub struct ScheduledOleanModule {
    pub module: std::sync::Arc<FrontierAccepted>,
    pub decoded: DecodedOlean,
    pub declarations: Vec<OleanCheckedDeclaration>,
    /// For each of `decoded.constants`, the digest the module's own engine held
    /// under that name after its check.
    pub closure_digests: Vec<Option<fln_hash::domain::Digest>>,
    pub checker_entries: BTreeMap<Name, Result<CheckerConstantEntry, &'static str>>,
}

/// The rows the serial planner gives a module checked after `before`, the
/// environment of every module ahead of it in the serial order, built from the
/// agreements the module's own check against its closure issued. Names the serial
/// planner finds present carry the grounds it records for them; a repeat it would
/// recheck under a scratch name carries the agreement issued for this module's copy.
pub fn serial_olean_rows(
    before: &Environment,
    decoded: &DecodedOlean,
    own: Vec<OleanCheckedDeclaration>,
    limits: OleanCheckLimits,
) -> Result<Vec<OleanCheckedDeclaration>, OleanCheckError> {
    let plan = plan_olean_declarations(before, &decoded.constants, limits)?;
    let agreements: BTreeMap<Name, CheckerAgreement> =
        own.into_iter().map(|row| (row.name, row.checker)).collect();
    let agreement = |name: &Name| {
        agreements
            .get(name)
            .copied()
            .ok_or(OleanCheckError::InternalInvariant {
                detail: "a serial row has no agreement from its module's own check",
            })
    };
    let mut rows = Vec::new();
    rows.try_reserve_exact(decoded.constants.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean reassembled declaration records",
            requested: decoded.constants.len(),
        })?;
    for unit_index in &plan.order {
        let Some(unit) = plan.units.get(*unit_index) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "planned declaration unit is outside the unit table",
            });
        };
        for name in &unit.names {
            rows.push(OleanCheckedDeclaration {
                name: name.clone(),
                checker: agreement(name)?,
            });
        }
    }
    for (name, checker) in plan.already_present {
        rows.push(OleanCheckedDeclaration { name, checker });
    }
    for repeat in plan.subsumed {
        let name = repeat.name().clone();
        let checker = match repeat {
            ConstantInfo::Thm(_) => agreement(&name)?,
            ConstantInfo::Axiom(_) => CheckerAgreement {
                schema: "fln-checker/v1",
                ground: CheckerAdmissionGround::AxiomPreamble,
            },
            _ => {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "only theorems and axioms can subsume an admitted repeat",
                });
            }
        };
        rows.push(OleanCheckedDeclaration { name, checker });
    }
    if rows.len() != decoded.constants.len() {
        return Err(OleanCheckError::InternalInvariant {
            detail: "reassembled declaration count differs from the decoded declaration table",
        });
    }
    Ok(rows)
}

/// Add one admitted constant to an import closure under the serial planner's
/// rule for a repeated name: an identical copy is already there, a copy that
/// subsumes or is subsumed by the present one keeps the present one, and any
/// other pair cannot be imported together.
pub fn merge_frontier_entry(
    environment: Environment,
    entry: &EnvironmentEntry,
) -> Result<Environment, OleanCheckError> {
    let name = entry.declaration().name();
    let Some(present) = environment.entry(name) else {
        return environment.with_entry(entry.clone()).map_err(|_| {
            OleanCheckError::InternalInvariant {
                detail: "an absent frontier constant could not be added",
            }
        });
    };
    if present.digest() == entry.digest() {
        return Ok(environment);
    }
    let lookup = |name: &Name| environment.find(name);
    if olean_imports::subsumes_info(&lookup, present.declaration(), entry.declaration())
        || olean_imports::subsumes_info(&lookup, entry.declaration(), present.declaration())
    {
        return Ok(environment);
    }
    Err(OleanCheckError::DuplicateDeclaration { name: name.clone() })
}

/// Atomic result of checking a closed set of named `.olean` modules.
#[derive(Debug)]
pub struct CheckedOleanSet<E = Admitted> {
    pub engine: E,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub modules: Vec<CheckedOleanModule>,
}

impl<E> CheckedOleanSet<E> {
    /// The same result around another representation of its successor engine.
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> CheckedOleanSet<F> {
        CheckedOleanSet {
            engine: map(self.engine),
            base_logical_root: self.base_logical_root,
            result_logical_root: self.result_logical_root,
            modules: self.modules,
        }
    }
}

/// Typed non-success from the `.olean` declaration-checking doors.
///
/// This production slice handles closed import sets and reconstructs complete
/// non-safe mutual definition envelopes, the fixed quotient initializer, and
/// safe bounded nonrecursive `Type` inductive units as authority transitions. Other
/// inductive shapes remain explicit checker non-answers rather than silently
/// entering trusted context. Safe definitions, theorems, and opaques retain
/// their multi-name metadata and check individually inside the atomic artifact
/// batch when their actual dependency graph is acyclic. Environment extensions
/// are decoded and counted by [`DecodedOlean`] but are not interpreted by this
/// declaration-only operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanCheckError {
    Decode(OleanDecodeError),
    EmptyModuleSet,
    ModuleLimit {
        observed: usize,
        limit: usize,
    },
    TotalBytesLimit {
        observed: usize,
        limit: usize,
    },
    MissingCompanionParts {
        module: Option<Name>,
        missing_server: bool,
        missing_private: bool,
    },
    ImportsRequireResolver {
        imports: Vec<Name>,
    },
    DuplicateModule {
        module: Name,
    },
    ModuleDecode {
        module: Name,
        error: OleanDecodeError,
    },
    MissingModuleImports {
        module: Name,
        imports: Vec<Name>,
    },
    ModuleImportCycle {
        modules: Vec<Name>,
    },
    InternalInvariant {
        detail: &'static str,
    },
    DeclarationLimit {
        observed: usize,
        limit: usize,
    },
    DependencyPresentationLimit {
        observed: usize,
        limit: usize,
    },
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    /// The host refused an allocation, and its handler unwound instead of
    /// aborting ([`install_host_allocation_failure_hook`]). `requested` is in
    /// bytes, where [`OleanCheckError::AllocationFailure`] counts entries.
    HostMemory {
        requested: usize,
    },
    DuplicateDeclaration {
        name: Name,
    },
    /// Two modules of one closed set decode to declarations sharing a name
    /// where neither subsumes the other.
    ///
    /// Re-generated equation and congruence lemmas legitimately repeat a name
    /// across modules, so a name collision alone is not a fault, and neither
    /// is a repeat the Reference's import accepts (`subsumesInfo`). A
    /// collision neither side subsumes is: the set has no single coherent
    /// meaning for that name, and admitting it in dependency order would let
    /// whichever module sorted first silently win while the other was rejected
    /// as already-declared — a kernel-shaped complaint about what is really a
    /// property of the input set.
    ConflictingModuleDeclaration {
        name: Name,
        first_module: Name,
        second_module: Name,
    },
    UnsupportedDeclaration {
        name: Name,
        kind: &'static str,
    },
    MutualEnvelopeUnsupported {
        name: Name,
        members: Vec<Name>,
    },
    InductiveEnvelopeUnsupported {
        name: Name,
        members: Vec<Name>,
    },
    QuotientEnvelopeUnsupported {
        names: Vec<Name>,
    },
    MissingConstants {
        declaration: Name,
        names: Vec<Name>,
    },
    DependencyCycle {
        declarations: Vec<Name>,
    },
    /// The independent checker's own reading of the artifact differs from the
    /// primary decode for a declaration no council reviews: one already present,
    /// or an axiom repeat, each reported checked because the primary decode
    /// equals one already admitted (bead `franken_lean-z8j.1.14`). One of the two
    /// decoders is wrong, so the module is not checked; it is the same objection
    /// a council seat raises for a declaration it does review.
    IndependentReadingDiffers {
        name: Name,
        detail: String,
    },
    Admission(EngineAdmissionError),
}

impl fmt::Display for OleanCheckError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Decode(error) => error.fmt(formatter),
            Self::EmptyModuleSet => write!(formatter, ".olean module set must not be empty"),
            Self::ModuleLimit { observed, limit } => write!(
                formatter,
                ".olean set contains {observed} modules; planning limit is {limit}"
            ),
            Self::TotalBytesLimit { observed, limit } => write!(
                formatter,
                ".olean set contains {observed} bytes; aggregate limit is {limit}"
            ),
            Self::MissingCompanionParts {
                module,
                missing_server,
                missing_private,
            } => {
                let subject = module.as_ref().map_or_else(
                    || "module-system .olean artifact".to_owned(),
                    |name| format!("module `{}`", name.to_display_string()),
                );
                let missing = match (*missing_server, *missing_private) {
                    (true, true) => ".olean.server and .olean.private",
                    (true, false) => ".olean.server",
                    (false, true) => ".olean.private",
                    (false, false) => "no companion parts",
                };
                write!(formatter, "{subject} is missing {missing}")
            }
            Self::ImportsRequireResolver { imports } => write!(
                formatter,
                "standalone declaration checking cannot resolve imports: {}",
                display_names(imports)
            ),
            Self::DuplicateModule { module } => write!(
                formatter,
                ".olean set repeats module `{}`",
                module.to_display_string()
            ),
            Self::ModuleDecode { module, error } => write!(
                formatter,
                "module `{}` failed to decode: {error}",
                module.to_display_string()
            ),
            Self::MissingModuleImports { module, imports } => write!(
                formatter,
                "module `{}` imports modules absent from the closed set: {}",
                module.to_display_string(),
                display_names(imports)
            ),
            Self::ModuleImportCycle { modules } => write!(
                formatter,
                "module import graph contains a cycle: {}",
                display_names(modules)
            ),
            Self::InternalInvariant { detail } => {
                write!(
                    formatter,
                    "internal .olean checking invariant failed: {detail}"
                )
            }
            Self::DeclarationLimit { observed, limit } => write!(
                formatter,
                ".olean contains {observed} declarations; planning limit is {limit}"
            ),
            Self::DependencyPresentationLimit { observed, limit } => write!(
                formatter,
                ".olean dependency walk reached {observed} expression presentations; limit is {limit}"
            ),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::HostMemory { requested } => write!(
                formatter,
                "the host refused an allocation of {requested} bytes"
            ),
            Self::DuplicateDeclaration { name } => write!(
                formatter,
                ".olean repeats declaration `{}`",
                name.to_display_string()
            ),
            Self::ConflictingModuleDeclaration {
                name,
                first_module,
                second_module,
            } => write!(
                formatter,
                "modules `{}` and `{}` decode to different declarations both named `{}`",
                first_module.to_display_string(),
                second_module.to_display_string(),
                name.to_display_string()
            ),
            Self::UnsupportedDeclaration { name, kind } => write!(
                formatter,
                "cannot check {kind} `{}` through the independent-checker facade yet",
                name.to_display_string()
            ),
            Self::MutualEnvelopeUnsupported { name, members } => write!(
                formatter,
                "cannot reconstruct the mutual declaration envelope for `{}` with members {}",
                name.to_display_string(),
                display_names(members)
            ),
            Self::InductiveEnvelopeUnsupported { name, members } => write!(
                formatter,
                "cannot reconstruct the inductive declaration envelope for `{}` from {}",
                name.to_display_string(),
                display_names(members)
            ),
            Self::QuotientEnvelopeUnsupported { names } => write!(
                formatter,
                "cannot reconstruct the four-row quotient initialization envelope from {}",
                display_names(names)
            ),
            Self::MissingConstants { declaration, names } => write!(
                formatter,
                "declaration `{}` references constants absent from the base environment and artifact: {}",
                declaration.to_display_string(),
                display_names(names)
            ),
            Self::DependencyCycle { declarations } => write!(
                formatter,
                "cannot reconstruct declaration units for dependency cycle: {}",
                display_names(declarations)
            ),
            Self::IndependentReadingDiffers { name, detail } => write!(
                formatter,
                "the independent checker's reading of `{}` is not the primary decode's: {detail}",
                name.to_display_string()
            ),
            Self::Admission(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for OleanCheckError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Decode(error) => Some(error),
            Self::ModuleDecode { error, .. } => Some(error),
            Self::Admission(error) => Some(error),
            _ => None,
        }
    }
}

impl From<OleanDecodeError> for OleanCheckError {
    fn from(error: OleanDecodeError) -> Self {
        Self::Decode(error)
    }
}

pub fn display_names(names: &[Name]) -> String {
    names
        .iter()
        .map(Name::to_display_string)
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn checked_olean_declaration(info: &ConstantInfo) -> Result<Declaration, OleanCheckError> {
    let name = info.name().clone();
    match info {
        ConstantInfo::Axiom(value) => Ok(Declaration::Axiom(value.clone())),
        ConstantInfo::Defn(value) => Ok(Declaration::Defn(value.clone())),
        ConstantInfo::Thm(value) => Ok(Declaration::Thm(value.clone())),
        ConstantInfo::Opaque(value) => Ok(Declaration::Opaque(value.clone())),
        ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_)
        | ConstantInfo::Rec(_) => Err(OleanCheckError::UnsupportedDeclaration {
            name,
            kind: info.kind_name(),
        }),
    }
}

#[derive(Debug, Clone)]
pub struct OleanDeclarationUnit {
    pub constant_indices: Vec<usize>,
    pub names: Vec<Name>,
    pub declaration: Declaration,
}

#[derive(Debug)]
pub struct OleanDeclarationPlan {
    pub units: Vec<OleanDeclarationUnit>,
    pub order: Vec<usize>,
    pub already_present: Vec<(Name, CheckerAgreement)>,
    /// Non-identical repeats of an admitted name that the Reference's import
    /// accepts (`subsumesInfo`); their own bodies still need a check.
    pub subsumed: Vec<ConstantInfo>,
}

fn unsupported_mutual_envelope(value: &DefinitionVal) -> OleanCheckError {
    OleanCheckError::MutualEnvelopeUnsupported {
        name: value.base.name.clone(),
        members: value.all.clone(),
    }
}

fn unsupported_inductive_envelope(name: &Name, members: Vec<Name>) -> OleanCheckError {
    OleanCheckError::InductiveEnvelopeUnsupported {
        name: name.clone(),
        members,
    }
}

fn quotient_initialization_names() -> [Name; 4] {
    [
        Name::from_components(["Quot"]),
        Name::from_components(["Quot", "mk"]),
        Name::from_components(["Quot", "lift"]),
        Name::from_components(["Quot", "ind"]),
    ]
}

fn unsupported_quotient_envelope(constants: &[ConstantInfo]) -> OleanCheckError {
    OleanCheckError::QuotientEnvelopeUnsupported {
        names: constants
            .iter()
            .filter(|constant| matches!(constant, ConstantInfo::Quot(_)))
            .map(|constant| constant.name().clone())
            .collect(),
    }
}

fn build_olean_declaration_units(
    constants: &[ConstantInfo],
    owners: &BTreeMap<Name, usize>,
) -> Result<(Vec<OleanDeclarationUnit>, Vec<usize>), OleanCheckError> {
    let mut units = Vec::new();
    units
        .try_reserve_exact(constants.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean declaration units",
            requested: constants.len(),
        })?;
    let mut constant_units = vec![usize::MAX; constants.len()];

    for (index, info) in constants.iter().enumerate() {
        if constant_units[index] != usize::MAX {
            continue;
        }
        if let ConstantInfo::Induct(inductive) = info {
            if inductive.all.first() != Some(&inductive.base.name) {
                continue;
            }
            let mut member_indices = Vec::new();
            let mut members = Vec::new();
            let mut unique = BTreeSet::new();
            for type_name in &inductive.all {
                if !unique.insert(type_name.clone()) {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                }
                let Some(&type_index) = owners.get(type_name) else {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                };
                let Some(ConstantInfo::Induct(member)) = constants.get(type_index) else {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                };
                if member.all != inductive.all || constant_units[type_index] != usize::MAX {
                    return Err(unsupported_inductive_envelope(
                        &inductive.base.name,
                        inductive.all.clone(),
                    ));
                }
                member_indices.push(type_index);
                members.push(member.base.name.clone());
                for (ctor_index, ctor_name) in member.ctors.iter().enumerate() {
                    let Some(&constant_index) = owners.get(ctor_name) else {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    };
                    let Some(ConstantInfo::Ctor(constructor)) = constants.get(constant_index)
                    else {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    };
                    if constructor.induct != member.base.name
                        || usize::try_from(constructor.cidx).ok() != Some(ctor_index)
                        || constant_units[constant_index] != usize::MAX
                    {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    }
                    member_indices.push(constant_index);
                    members.push(constructor.base.name.clone());
                }
            }
            for (constant_index, candidate) in constants.iter().enumerate() {
                let ConstantInfo::Rec(recursor) = candidate else {
                    continue;
                };
                if recursor.all.first() == Some(&inductive.base.name) {
                    if constant_units[constant_index] != usize::MAX {
                        return Err(unsupported_inductive_envelope(
                            &inductive.base.name,
                            inductive.all.clone(),
                        ));
                    }
                    member_indices.push(constant_index);
                    members.push(recursor.base.name.clone());
                }
            }
            let mut types = Vec::new();
            let mut constructors = Vec::new();
            let mut recursors = Vec::new();
            for member_index in &member_indices {
                match &constants[*member_index] {
                    ConstantInfo::Induct(value) => types.push(value.clone()),
                    ConstantInfo::Ctor(value) => constructors.push(value.clone()),
                    ConstantInfo::Rec(value) => recursors.push(value.clone()),
                    _ => {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "inductive unit contains a non-inductive row",
                        });
                    }
                }
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: members,
                declaration: Declaration::Inductive(fln_kernel::InductiveBlock {
                    types,
                    ctors: constructors,
                    recursors,
                }),
            });
            continue;
        }
        if matches!(info, ConstantInfo::Ctor(_) | ConstantInfo::Rec(_)) {
            continue;
        }
        if matches!(info, ConstantInfo::Quot(_)) {
            let names = quotient_initialization_names();
            let mut member_indices = Vec::new();
            member_indices.try_reserve_exact(names.len()).map_err(|_| {
                OleanCheckError::AllocationFailure {
                    resource: ".olean quotient member indices",
                    requested: names.len(),
                }
            })?;
            let mut members = Vec::new();
            members.try_reserve_exact(names.len()).map_err(|_| {
                OleanCheckError::AllocationFailure {
                    resource: ".olean quotient declarations",
                    requested: names.len(),
                }
            })?;
            for name in &names {
                let Some(&member_index) = owners.get(name) else {
                    return Err(unsupported_quotient_envelope(constants));
                };
                if constant_units[member_index] != usize::MAX {
                    return Err(unsupported_quotient_envelope(constants));
                }
                let Some(ConstantInfo::Quot(member)) = constants.get(member_index) else {
                    return Err(unsupported_quotient_envelope(constants));
                };
                member_indices.push(member_index);
                members.push(member.clone());
            }
            if !names.contains(info.name()) {
                return Err(unsupported_quotient_envelope(constants));
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: names.to_vec(),
                declaration: Declaration::Quotient(members),
            });
            continue;
        }
        let ConstantInfo::Defn(definition) = info else {
            let declaration = checked_olean_declaration(info)?;
            let unit = units.len();
            constant_units[index] = unit;
            units.push(OleanDeclarationUnit {
                constant_indices: vec![index],
                names: vec![info.name().clone()],
                declaration,
            });
            continue;
        };
        // Lean adds every partial definition as a `mutualDefnDecl`, a singleton
        // included, and the pin's `add_definition` would refuse a partial one that
        // recurses (fln-tio5). So a partial definition is presented as the mutual
        // unit it was admitted as; a singleton unsafe one keeps `add_definition`'s
        // unsafe branch, which accepts the same recursion.
        let singleton_definition = definition.all.is_empty()
            || (definition.all.len() == 1 && definition.safety != DefinitionSafety::Partial);
        if singleton_definition || definition.safety == DefinitionSafety::Safe {
            let declaration = checked_olean_declaration(info)?;
            let unit = units.len();
            constant_units[index] = unit;
            units.push(OleanDeclarationUnit {
                constant_indices: vec![index],
                names: vec![info.name().clone()],
                declaration,
            });
            continue;
        }
        // Mathlib's `compile_inductive` (Mathlib/Util/CompileInductive.lean)
        // builds each compiled recursor as `{ rv with name, value, .. }`, so its
        // `all` is the recursor's inductive block (`[List]`), not the
        // definitions it was admitted with. The pin's `add_mutual` never reads
        // `all`. A definition whose `all` does not name it is grouped with every
        // non-safe definition of the same safety sharing that `all`: the one
        // `mutualDefnDecl` that built them.
        if !definition.all.contains(&definition.base.name) {
            let mut member_indices = Vec::new();
            let mut members = Vec::new();
            for (candidate_index, candidate) in constants.iter().enumerate() {
                let ConstantInfo::Defn(candidate) = candidate else {
                    continue;
                };
                if candidate.safety == definition.safety
                    && candidate.all == definition.all
                    && !candidate.all.contains(&candidate.base.name)
                    && constant_units[candidate_index] == usize::MAX
                {
                    member_indices.push(candidate_index);
                    members.push(candidate.clone());
                }
            }
            let unit = units.len();
            for member_index in &member_indices {
                constant_units[*member_index] = unit;
            }
            units.push(OleanDeclarationUnit {
                constant_indices: member_indices,
                names: members
                    .iter()
                    .map(|member| member.base.name.clone())
                    .collect(),
                declaration: Declaration::Mutual(members),
            });
            continue;
        }
        let mut member_indices = Vec::new();
        member_indices
            .try_reserve_exact(definition.all.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean mutual member indices",
                requested: definition.all.len(),
            })?;
        let mut members = Vec::new();
        members
            .try_reserve_exact(definition.all.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean mutual definitions",
                requested: definition.all.len(),
            })?;
        let mut unique = BTreeSet::new();
        for name in &definition.all {
            if !unique.insert(name.clone()) {
                return Err(unsupported_mutual_envelope(definition));
            }
            let Some(&member_index) = owners.get(name) else {
                return Err(unsupported_mutual_envelope(definition));
            };
            if constant_units[member_index] != usize::MAX {
                return Err(unsupported_mutual_envelope(definition));
            }
            let Some(ConstantInfo::Defn(member)) = constants.get(member_index) else {
                return Err(unsupported_mutual_envelope(definition));
            };
            if member.safety == DefinitionSafety::Safe || member.all != definition.all {
                return Err(unsupported_mutual_envelope(definition));
            }
            member_indices.push(member_index);
            members.push(member.clone());
        }
        if !unique.contains(&definition.base.name) {
            return Err(unsupported_mutual_envelope(definition));
        }

        let unit = units.len();
        for member_index in &member_indices {
            constant_units[*member_index] = unit;
        }
        units.push(OleanDeclarationUnit {
            constant_indices: member_indices,
            names: definition.all.clone(),
            declaration: Declaration::Mutual(members),
        });
    }

    if let Some((index, _)) = constant_units
        .iter()
        .enumerate()
        .find(|(_, unit)| **unit == usize::MAX)
    {
        let name = constants[index].name();
        let members = match &constants[index] {
            ConstantInfo::Induct(value) => value.all.clone(),
            ConstantInfo::Ctor(value) => vec![value.induct.clone(), value.base.name.clone()],
            ConstantInfo::Rec(value) => value.all.clone(),
            _ => Vec::new(),
        };
        return Err(unsupported_inductive_envelope(name, members));
    }
    Ok((units, constant_units))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantReferenceCollectionError {
    PresentationLimit { observed: usize, limit: usize },
    AllocationFailure { requested: usize },
}

/// Collect the constants `expression` names. A decoded term is a DAG whose
/// subterms are shared, so each distinct node is presented once: walked as a
/// tree, `blastDivSubtractShift_decl_eq` alone presents 69,111,656 nodes over
/// 1,719 distinct ones (bead fln-32rr).
pub fn collect_constant_references(
    expression: &Expr,
    names: &mut BTreeSet<Name>,
    presentations: &mut usize,
    limit: usize,
) -> Result<(), ConstantReferenceCollectionError> {
    use fln_core::expr::ExprNode;

    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| ConstantReferenceCollectionError::AllocationFailure { requested: 1 })?;
    pending.push(expression);
    let mut seen = std::collections::HashSet::<*const ExprNode>::new();
    while let Some(expression) = pending.pop() {
        seen.try_reserve(1)
            .map_err(|_| ConstantReferenceCollectionError::AllocationFailure {
                requested: seen.len().saturating_add(1),
            })?;
        if !seen.insert(std::ptr::from_ref(expression.node())) {
            continue;
        }
        *presentations = presentations.saturating_add(1);
        if *presentations > limit {
            return Err(ConstantReferenceCollectionError::PresentationLimit {
                observed: *presentations,
                limit,
            });
        }
        match expression.node() {
            ExprNode::Const { name, .. } => {
                names.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                pending.try_reserve(2).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(2),
                    }
                })?;
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.try_reserve(2).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(2),
                    }
                })?;
                pending.push(body);
                pending.push(binder_type);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.try_reserve(3).map_err(|_| {
                    ConstantReferenceCollectionError::AllocationFailure {
                        requested: pending.len().saturating_add(3),
                    }
                })?;
                pending.push(body);
                pending.push(value);
                pending.push(type_);
            }
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                names.insert(struct_name.clone());
                pending.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    Ok(())
}

fn collect_olean_dependencies(
    expression: &Expr,
    names: &mut BTreeSet<Name>,
    presentations: &mut usize,
    limit: usize,
) -> Result<(), OleanCheckError> {
    collect_constant_references(expression, names, presentations, limit).map_err(
        |error| match error {
            ConstantReferenceCollectionError::PresentationLimit { observed, limit } => {
                OleanCheckError::DependencyPresentationLimit { observed, limit }
            }
            ConstantReferenceCollectionError::AllocationFailure { requested } => {
                OleanCheckError::AllocationFailure {
                    resource: ".olean dependency worklist",
                    requested,
                }
            }
        },
    )
}

fn olean_dependencies(
    info: &ConstantInfo,
    presentations: &mut usize,
    limit: usize,
) -> Result<BTreeSet<Name>, OleanCheckError> {
    let mut names = BTreeSet::new();
    collect_olean_dependencies(&info.constant_val().type_, &mut names, presentations, limit)?;
    match info {
        ConstantInfo::Defn(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Thm(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Opaque(value) => {
            collect_olean_dependencies(&value.value, &mut names, presentations, limit)?
        }
        ConstantInfo::Axiom(_)
        | ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_)
        | ConstantInfo::Rec(_) => {}
    }
    Ok(names)
}

/// Whole-set bounds for a closed `.olean` module set: non-empty, within the module and
/// byte limits, and no module named twice. Returns each module's input index by name.
fn olean_module_owners(
    modules: &[OleanModuleInput<'_>],
    limits: OleanCheckLimits,
) -> Result<BTreeMap<Name, usize>, OleanCheckError> {
    if modules.is_empty() {
        return Err(OleanCheckError::EmptyModuleSet);
    }
    if modules.len() > limits.max_modules {
        return Err(OleanCheckError::ModuleLimit {
            observed: modules.len(),
            limit: limits.max_modules,
        });
    }
    let mut total_bytes = 0_usize;
    let mut owners = BTreeMap::new();
    for (index, module) in modules.iter().enumerate() {
        for artifact in [
            Some(module.artifact),
            module.server_artifact,
            module.private_artifact,
        ]
        .into_iter()
        .flatten()
        {
            total_bytes = total_bytes.checked_add(artifact.len()).ok_or(
                OleanCheckError::TotalBytesLimit {
                    observed: usize::MAX,
                    limit: limits.max_total_bytes,
                },
            )?;
        }
        if total_bytes > limits.max_total_bytes {
            return Err(OleanCheckError::TotalBytesLimit {
                observed: total_bytes,
                limit: limits.max_total_bytes,
            });
        }
        if owners.insert(module.name.clone(), index).is_some() {
            return Err(OleanCheckError::DuplicateModule {
                module: module.name.clone(),
            });
        }
    }
    Ok(owners)
}

/// Decode one module of a closed set, requiring the server and private parts exactly
/// when the artifact is a module-system `.olean`.
pub fn decode_olean_module_input(
    module: &OleanModuleInput<'_>,
    limits: OleanCheckLimits,
) -> Result<DecodedOlean, OleanCheckError> {
    decode_olean_module_input_with(module, limits, CheckerReading::Read)
}

pub struct OleanModuleDecode {
    pub result: Result<DecodedOlean, OleanCheckError>,
    pub memory_retry: Option<OleanDecodeMemoryRetry>,
}

struct TimedOleanDecode {
    result: Result<DecodedOlean, OleanCheckError>,
    elapsed: std::time::Duration,
}

fn guarded_olean_decode(
    decode: impl FnOnce() -> Result<DecodedOlean, OleanCheckError>,
) -> TimedOleanDecode {
    let started = std::time::Instant::now();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(decode))
        .unwrap_or_else(|payload| Err(olean_unwound(payload, "an .olean module decode panicked")));
    TimedOleanDecode {
        result,
        elapsed: started.elapsed(),
    }
}

/// Decode every module of a set, initially `jobs.threads` at once, each result
/// at its module's input index. The first host-memory refusal closes parallel
/// dispatch. After those workers exit, retry each memory-refused decode that
/// overlapped another once, then decode any unstarted modules one at a time.
///
/// This ends the parallel workers and releases transient decoding state.
/// Successful sibling artifacts remain, so it does not promise the memory
/// footprint of a fresh serial run. Explicit budgets and artifact errors are
/// never retried. The outer `Err` denotes orchestration failure; module errors
/// stay at their input index.
fn decode_olean_module_inputs(
    modules: &[OleanModuleInput<'_>],
    limits: OleanCheckLimits,
    reading: CheckerReading,
    jobs: OleanFrontierJobs,
) -> Result<Vec<OleanModuleDecode>, OleanCheckError> {
    decode_olean_module_inputs_using(modules.len(), jobs, &|index| {
        decode_olean_module_input_with(&modules[index], limits, reading)
    })
}

/// Keep fault injection at the decoder boundary, so tests exercise the same
/// dispatch, unwinding, retry and collection paths as real artifact reads.
pub fn decode_olean_module_inputs_using(
    count: usize,
    jobs: OleanFrontierJobs,
    decode: &(dyn Fn(usize) -> Result<DecodedOlean, OleanCheckError> + Sync),
) -> Result<Vec<OleanModuleDecode>, OleanCheckError> {
    let allocation = |_| OleanCheckError::AllocationFailure {
        resource: ".olean decoder work records",
        requested: count,
    };
    let mut results = Vec::new();
    results.try_reserve_exact(count).map_err(allocation)?;
    let threads = jobs.threads.get().min(count);
    if threads <= 1 {
        for index in 0..count {
            results.push(OleanModuleDecode {
                result: guarded_olean_decode(|| decode(index)).result,
                memory_retry: None,
            });
        }
        return Ok(results);
    }
    /// The decoder is iterative; this only has to hold its ordinary frames.
    const MIN_DECODE_STACK_BYTES: usize = 8 << 20;
    let stack_bytes = jobs.worker_stack_bytes.max(MIN_DECODE_STACK_BYTES);
    struct Dispatch {
        next: usize,
        running: Vec<usize>,
        overlapped: Vec<bool>,
        completed: Vec<Option<TimedOleanDecode>>,
        memory_refused: bool,
    }
    let mut running = Vec::new();
    running.try_reserve_exact(threads).map_err(allocation)?;
    let mut overlapped = Vec::new();
    overlapped.try_reserve_exact(count).map_err(allocation)?;
    overlapped.resize(count, false);
    let mut completed = Vec::new();
    completed.try_reserve_exact(count).map_err(allocation)?;
    completed.resize_with(count, || None);
    let dispatch = std::sync::Mutex::new(Dispatch {
        next: 0,
        running,
        overlapped,
        completed,
        memory_refused: false,
    });
    let lock_failure = |_| OleanCheckError::InternalInvariant {
        detail: "the .olean decode dispatcher was poisoned",
    };
    std::thread::scope(|scope| -> Result<(), OleanCheckError> {
        let mut workers = Vec::new();
        workers.try_reserve_exact(threads).map_err(allocation)?;
        for worker in 0..threads {
            let dispatch = &dispatch;
            workers.push(
                std::thread::Builder::new()
                    .name(format!("fln-olean-decode-{worker}"))
                    .stack_size(stack_bytes)
                    .spawn_scoped(scope, move || -> Result<(), OleanCheckError> {
                        loop {
                            let index = {
                                let mut state = dispatch.lock().map_err(lock_failure)?;
                                if state.memory_refused || state.next == count {
                                    return Ok(());
                                }
                                let index = state.next;
                                state.next += 1;
                                if !state.running.is_empty() {
                                    state.overlapped[index] = true;
                                    // The earlier worker overlaps too, even if it
                                    // was alone when it first claimed its module.
                                    for at in 0..state.running.len() {
                                        let other = state.running[at];
                                        state.overlapped[other] = true;
                                    }
                                }
                                state.running.push(index);
                                index
                            };
                            let attempt = guarded_olean_decode(|| decode(index));
                            let mut state = dispatch.lock().map_err(lock_failure)?;
                            if attempt
                                .result
                                .as_ref()
                                .is_err_and(olean_host_memory_refusal)
                            {
                                // Claim and stop share this lock: no fresh job can
                                // slip into the parallel pool after this refusal.
                                state.memory_refused = true;
                            }
                            let at = state
                                .running
                                .iter()
                                .position(|active| *active == index)
                                .ok_or(OleanCheckError::InternalInvariant {
                                    detail: "a finished .olean decode was not running",
                                })?;
                            state.running.swap_remove(at);
                            state.completed[index] = Some(attempt);
                        }
                    })
                    .map_err(|_| OleanCheckError::InternalInvariant {
                        detail: "could not start an .olean decode worker thread",
                    })?,
            );
        }
        for worker in workers {
            worker.join().map_err(|payload| {
                olean_unwound(payload, "an .olean decode dispatcher worker panicked")
            })??;
        }
        Ok(())
    })?;
    let mut state = dispatch
        .into_inner()
        .map_err(|_| OleanCheckError::InternalInvariant {
            detail: "the .olean decode dispatcher was poisoned",
        })?;
    let needs_isolation = state.next < count
        || state.completed.iter().enumerate().any(|(index, attempt)| {
            state.overlapped[index]
                && attempt.as_ref().is_some_and(|attempt| {
                    attempt
                        .result
                        .as_ref()
                        .is_err_and(olean_host_memory_refusal)
                })
        });
    let finish = move || -> Result<Vec<OleanModuleDecode>, OleanCheckError> {
        for index in 0..count {
            let first = match state.completed[index].take() {
                Some(first) => first,
                None if index >= state.next => guarded_olean_decode(|| decode(index)),
                None => {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "an .olean decode worker left a claimed module undecoded",
                    });
                }
            };
            let (result, memory_retry) = match first.result {
                Err(error) if state.overlapped[index] && olean_host_memory_refusal(&error) => {
                    let retry = guarded_olean_decode(|| decode(index));
                    let memory_retry = OleanDecodeMemoryRetry {
                        first_error: error,
                        first_elapsed: first.elapsed,
                        retry_elapsed: retry.elapsed,
                        retry_result: retry.result.as_ref().map(|_| ()).map_err(Clone::clone),
                    };
                    (retry.result, Some(memory_retry))
                }
                result => (result, None),
            };
            results.push(OleanModuleDecode {
                result,
                memory_retry,
            });
        }
        Ok(results)
    };
    if !needs_isolation {
        return finish();
    }
    // The whole first pool has joined. Retrying on one new worker preserves the
    // original decoder stack allowance; the host may cache exited thread stacks.
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("fln-olean-decode-isolated".to_owned())
            .stack_size(stack_bytes)
            .spawn_scoped(scope, finish)
            .map_err(|_| OleanCheckError::InternalInvariant {
                detail: "could not start an isolated .olean decode worker thread",
            })?
            .join()
            .map_err(|payload| {
                olean_unwound(payload, "an isolated .olean decode worker panicked")
            })?
    })
}

pub fn decode_olean_module_input_with(
    module: &OleanModuleInput<'_>,
    limits: OleanCheckLimits,
    reading: CheckerReading,
) -> Result<DecodedOlean, OleanCheckError> {
    match (module.server_artifact, module.private_artifact) {
        (Some(server), Some(private)) => decode_olean_module_artifacts_with(
            module.artifact,
            server,
            private,
            limits.decode,
            reading,
        ),
        (server, private) => {
            let decoded = decode_olean_artifact_with(module.artifact, limits.decode, reading);
            match decoded {
                Ok(decoded) if decoded.module.is_module => {
                    return Err(OleanCheckError::MissingCompanionParts {
                        module: Some(module.name.clone()),
                        missing_server: server.is_none(),
                        missing_private: private.is_none(),
                    });
                }
                Ok(_) if server.is_some() || private.is_some() => {
                    return Err(OleanCheckError::Decode(
                        OleanDecodeError::UnexpectedCompanionParts,
                    ));
                }
                other => other,
            }
        }
    }
    .map_err(|error| OleanCheckError::ModuleDecode {
        module: module.name.clone(),
        error,
    })
}

pub fn plan_olean_declarations(
    base: &Environment,
    constants: &[ConstantInfo],
    limits: OleanCheckLimits,
) -> Result<OleanDeclarationPlan, OleanCheckError> {
    if constants.len() > limits.max_declarations {
        return Err(OleanCheckError::DeclarationLimit {
            observed: constants.len(),
            limit: limits.max_declarations,
        });
    }

    let mut seen_names = BTreeSet::new();
    let mut owners = BTreeMap::new();
    let mut already_present = Vec::new();
    let mut subsumed = Vec::new();
    let mut new_constants = Vec::new();

    for info in constants {
        if !seen_names.insert(info.name().clone()) {
            return Err(OleanCheckError::DuplicateDeclaration {
                name: info.name().clone(),
            });
        }

        if let Some(existing) = base.find(info.name()) {
            if *existing != *info {
                let lookup = |name: &Name| base.find(name);
                if olean_imports::subsumes_info(&lookup, existing, info)
                    || olean_imports::subsumes_info(&lookup, info, existing)
                {
                    subsumed.push(info.clone());
                    continue;
                }
                return Err(OleanCheckError::DuplicateDeclaration {
                    name: info.name().clone(),
                });
            }
            let ground = match info {
                ConstantInfo::Thm(_) | ConstantInfo::Defn(_) | ConstantInfo::Opaque(_) => {
                    CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
                }
                ConstantInfo::Axiom(_) => CheckerAdmissionGround::AxiomPreamble,
                ConstantInfo::Quot(_) => CheckerAdmissionGround::QuotientPrimitiveChecked,
                ConstantInfo::Induct(_) | ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {
                    CheckerAdmissionGround::InductiveNonrecursiveChecked
                }
            };
            already_present.push((
                info.name().clone(),
                CheckerAgreement {
                    schema: "fln-checker/v1",
                    ground,
                },
            ));
            continue;
        }

        owners.insert(info.name().clone(), new_constants.len());
        new_constants.push(info.clone());
    }

    let (units, constant_units) = build_olean_declaration_units(&new_constants, &owners)?;

    let mut remaining = vec![0_usize; units.len()];
    let mut dependents = vec![Vec::new(); units.len()];
    let mut presentations = 0_usize;
    for (unit_index, unit) in units.iter().enumerate() {
        let mut missing = BTreeSet::new();
        let mut dependencies = BTreeSet::new();
        for constant_index in &unit.constant_indices {
            let Some(info) = new_constants.get(*constant_index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "authority unit names a declaration outside the decoded table",
                });
            };
            for dependency in olean_dependencies(
                info,
                &mut presentations,
                limits.max_dependency_presentations,
            )? {
                match owners.get(&dependency).copied() {
                    Some(owner) => {
                        let Some(&dependency_unit) = constant_units.get(owner) else {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "declaration owner has no authority unit",
                            });
                        };
                        if dependency_unit != unit_index {
                            dependencies.insert(dependency_unit);
                        }
                    }
                    None if base.find(&dependency).is_some() => {}
                    None => {
                        missing.insert(dependency);
                    }
                }
            }
        }
        if !missing.is_empty() {
            return Err(OleanCheckError::MissingConstants {
                declaration: unit.names[0].clone(),
                names: missing.into_iter().collect(),
            });
        }
        remaining[unit_index] = dependencies.len();
        for dependency in dependencies {
            dependents[dependency].push(unit_index);
        }
    }

    let mut ready: BTreeSet<(Name, usize)> = units
        .iter()
        .enumerate()
        .filter(|(index, _)| remaining[*index] == 0)
        .map(|(index, unit)| {
            let key = unit
                .names
                .iter()
                .min()
                .cloned()
                .unwrap_or_else(Name::anonymous);
            (key, index)
        })
        .collect();
    let mut order = Vec::new();
    order
        .try_reserve_exact(units.len())
        .map_err(|_| OleanCheckError::AllocationFailure {
            resource: ".olean declaration order",
            requested: units.len(),
        })?;
    while let Some((_, index)) = ready.pop_first() {
        order.push(index);
        let Some(next) = dependents.get(index) else {
            return Err(OleanCheckError::InternalInvariant {
                detail: "declaration owner is outside the dependent table",
            });
        };
        for dependent in next {
            let Some(count) = remaining.get_mut(*dependent) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "dependent declaration is outside the remaining table",
                });
            };
            *count = count
                .checked_sub(1)
                .ok_or(OleanCheckError::InternalInvariant {
                    detail: "declaration dependency count underflowed",
                })?;
            if *count == 0 {
                let Some(unit) = units.get(*dependent) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "ready dependent is outside the constant table",
                    });
                };
                let key = unit
                    .names
                    .iter()
                    .min()
                    .cloned()
                    .unwrap_or_else(Name::anonymous);
                ready.insert((key, *dependent));
            }
        }
    }
    if order.len() != units.len() {
        let declarations = units
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] != 0)
            .flat_map(|(_, unit)| unit.names.iter().cloned())
            .collect();
        return Err(OleanCheckError::DependencyCycle { declarations });
    }
    Ok(OleanDeclarationPlan {
        units,
        order,
        already_present,
        subsumed,
    })
}

impl Admitted {
    /// Decode and atomically check every declaration in one standalone
    /// pinned-format `.olean`.
    ///
    /// The declaration array is not trusted to be dependency-ordered. This
    /// method reconstructs validated non-safe mutual definition units, derives
    /// a stable Kahn order from exact inter-unit constant references, then sends
    /// every unit through the same K1-plus-independent-checker council as
    /// [`Self::admit_declaration`]. Acyclic safe definitions, theorems, and
    /// opaques preserve multi-name metadata while remaining individual units.
    /// The artifact must be import-free:
    /// resolving module names to exact predecessor environments belongs to the
    /// module loader, and treating unresolved imports as axioms would violate
    /// the Oracle-Only and single-authority laws.
    ///
    /// A completed result means all decoded declarations were checked and the
    /// returned engine contains all of them. It does not mean environment
    /// extension payloads were interpreted or that K2/receipt/release gates
    /// were satisfied. Module-system artifacts are refused here because this
    /// convenience door has no companion-part arguments; use
    /// [`Self::check_olean_artifact_parts`] for those.
    pub fn check_olean_artifact(
        &self,
        artifact: &[u8],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        self.check_olean_artifact_parts(artifact, None, None, options, limits)
    }

    /// Decode and atomically check one standalone or complete module-system
    /// pinned-format `.olean` artifact.
    ///
    /// Module-system inputs must provide both companion parts. Refusing an
    /// incomplete chain is load-bearing: checking only the exported part would
    /// turn stripped definitions into axioms and omit private auxiliaries.
    pub fn check_olean_artifact_parts(
        &self,
        artifact: &[u8],
        server_artifact: Option<&[u8]>,
        private_artifact: Option<&[u8]>,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let decoded = match (server_artifact, private_artifact) {
            (Some(server), Some(private)) => {
                decode_olean_module_artifacts(artifact, server, private, limits.decode)?
            }
            (server, private) => {
                let decoded = decode_olean_artifact(artifact, limits.decode)?;
                if decoded.module.is_module {
                    return Err(OleanCheckError::MissingCompanionParts {
                        module: None,
                        missing_server: server.is_none(),
                        missing_private: private.is_none(),
                    });
                }
                if server.is_some() || private.is_some() {
                    return Err(OleanCheckError::Decode(
                        OleanDecodeError::UnexpectedCompanionParts,
                    ));
                }
                decoded
            }
        };
        if !decoded.module.imports.is_empty() {
            return Err(OleanCheckError::ImportsRequireResolver {
                imports: decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            });
        }
        self.check_decoded_olean(decoded, options, limits)
    }

    /// Decode and atomically check a closed set of named `.olean` modules.
    ///
    /// Every direct import must name another input row. Modules are checked in
    /// a deterministic import-topological order; declarations within each
    /// module are independently dependency-sorted. Nothing from a missing
    /// import is synthesized, and no prefix engine is returned on a later
    /// failure or non-answer.
    pub fn check_olean_modules(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        self.check_olean_modules_with_cancel(modules, options, limits, None)
    }

    /// The serial council retains completed modules only in local successors.
    /// Cancellation at a module boundary or before the final return discards
    /// those successors; the caller receives no partially admitted import set.
    fn check_olean_modules_with_cancel(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "olean-modules/before-decode",
            )));
        }
        let ordered = self.decode_olean_module_set(
            modules,
            limits,
            CheckerReading::Read,
            OleanFrontierJobs::SERIAL,
        )?;
        let bound_base = (self.environment == Environment::new()
            || self
                .imported_environment
                .as_ref()
                .is_some_and(|snapshot| snapshot == &self.environment))
            && modules
                .iter()
                .all(|module| !self.imported_modules.contains(module.name));
        let base_logical_root = self.logical_root(options);
        let mut engine = self.clone();
        let mut checked_modules = Vec::new();
        checked_modules
            .try_reserve_exact(ordered.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean checked module records",
                requested: ordered.len(),
            })?;
        for (name, artifact) in ordered {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                    "olean-modules/before-module",
                )));
            }
            let checked = match engine.check_decoded_olean(artifact, options, limits)? {
                Outcome::Complete(checked) => checked,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
            engine = checked.engine;
            checked_modules.push(CheckedOleanModule {
                name,
                decoded: checked.decoded,
                base_logical_root: checked.base_logical_root,
                result_logical_root: checked.result_logical_root,
                declarations: checked.declarations,
            });
        }
        let mut imported = (*engine.imported_modules).clone();
        imported.extend(checked_modules.iter().map(|module| module.name.clone()));
        engine.imported_modules = std::sync::Arc::new(imported);
        let mut dependencies = (*self.imported_module_dependencies).clone();
        for module in &checked_modules {
            dependencies.insert(
                module.name.clone(),
                module
                    .decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            );
        }
        engine.imported_module_dependencies = std::sync::Arc::new(dependencies);
        engine.imported_environment = bound_base.then(|| engine.environment.clone());
        let result_logical_root = engine.logical_root(options);
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "olean-modules/before-publication",
            )));
        }
        Ok(Outcome::Complete(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root,
            modules: checked_modules,
        }))
    }

    /// Check a closed set of named `.olean` modules module by module, reporting a
    /// verdict for every one instead of stopping at the first failure.
    ///
    /// Modules are visited in the same deterministic import-topological order as
    /// [`Engine::check_olean_modules`]. A module whose artifact does not decode, whose
    /// imports are not all in the set, or which sits on an import cycle is `Failed`;
    /// a module any of whose imports lacks an accepted verdict is `Blocked` and is
    /// never checked. Only whole-set problems (an empty set, the module or byte limit,
    /// a module named twice) are returned as an error.
    pub fn check_olean_frontier(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<OleanFrontier, OleanCheckError> {
        self.check_olean_frontier_observed(modules, options, limits, &mut |_| {})
    }

    /// [`Engine::check_olean_frontier`], reporting each [`OleanFrontierEvent`] as it
    /// happens, so a long lane always names the module in flight and a run stopped
    /// part-way still leaves the rows it had decided. The observer sees the rows in
    /// the order of the returned frontier and cannot change them.
    pub fn check_olean_frontier_observed(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
    ) -> Result<OleanFrontier, OleanCheckError> {
        self.check_olean_frontier_scheduled(
            modules,
            options,
            limits,
            OleanFrontierJobs::SERIAL,
            on_event,
        )
    }

    /// [`Engine::check_olean_frontier_observed`] over `jobs.threads` modules at once.
    ///
    /// Each module is checked against the environment of exactly its own import
    /// closure: this engine's environment plus what every module of the closure
    /// admitted, merged in frontier order under the rule the serial planner applies
    /// to a repeated name. An identical copy is one constant; a copy that subsumes
    /// or is subsumed by the first keeps the first; any other pair is a
    /// `DuplicateDeclaration` for the importing module. The logical context does
    /// not depend on another module's completion order.
    /// A module refused host memory while other checks were in flight is retried
    /// once after those workers finish, under the same limits. Only that retry's
    /// verdict is settled; both attempts remain in its row. The retry does not
    /// raise budgets or assume any declaration. Other resource stops are final.
    /// The initial decode pass follows the same once-only retry rule, stops
    /// parallel dispatch at the first host-memory refusal and completes unstarted
    /// decodes serially. Its attempts are recorded separately from the council's.
    /// Retained artifacts and unrelated host memory remain; this is not a claim
    /// of resource-independent verdicts.
    /// `Decided` events arrive in row order; `Started` and `Retrying` events arrive
    /// as modules are dispatched, which above one thread is not row order.
    pub fn check_olean_frontier_scheduled(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
    ) -> Result<OleanFrontier, OleanCheckError> {
        self.check_olean_frontier_using(
            modules,
            limits,
            jobs,
            on_event,
            &|job| self.frontier_check_module(job, options, limits),
            &|index| decode_olean_module_input_with(&modules[index], limits, CheckerReading::Read),
        )
    }

    /// The scheduler's decoding and checking operations are private so fault
    /// tests can refuse a real job at its worker boundary without installing a
    /// global allocator or changing any successful declaration-admission path.
    pub fn check_olean_frontier_using(
        &self,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        on_event: &mut dyn FnMut(OleanFrontierEvent<'_>),
        check: &(dyn Fn(FrontierJob) -> FrontierDone + Sync),
        decode: &(dyn Fn(usize) -> Result<DecodedOlean, OleanCheckError> + Sync),
    ) -> Result<OleanFrontier, OleanCheckError> {
        let owners = olean_module_owners(modules, limits)?;
        let mut decode_memory_retries = Vec::new();
        decode_memory_retries
            .try_reserve_exact(modules.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean decode retry records",
                requested: modules.len(),
            })?;
        let mut decoded: Vec<Option<Result<DecodedOlean, OleanCheckError>>> =
            decode_olean_module_inputs_using(modules.len(), jobs, decode)?
                .into_iter()
                .map(|entry| {
                    decode_memory_retries.push(entry.memory_retry);
                    Some(entry.result)
                })
                .collect();

        let mut dependencies: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); modules.len()];
        for (index, entry) in decoded.iter_mut().enumerate() {
            let Some(Ok(artifact)) = entry.as_ref() else {
                continue;
            };
            let mut missing = BTreeSet::new();
            for import in &artifact.module.imports {
                match owners.get(&import.module).copied() {
                    Some(owner) if owner != index => {
                        dependencies[index].insert(owner);
                    }
                    Some(_) => {
                        dependencies[index].insert(index);
                    }
                    None => {
                        missing.insert(import.module.clone());
                    }
                }
            }
            if !missing.is_empty() {
                dependencies[index].clear();
                *entry = Some(Err(OleanCheckError::MissingModuleImports {
                    module: modules[index].name.clone(),
                    imports: missing.into_iter().collect(),
                }));
            }
        }

        let mut remaining: Vec<usize> = dependencies.iter().map(BTreeSet::len).collect();
        let mut dependents = vec![Vec::new(); modules.len()];
        for (index, deps) in dependencies.iter().enumerate() {
            for dependency in deps {
                dependents[*dependency].push(index);
            }
        }
        let mut ready: BTreeSet<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] == 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        let mut order = Vec::with_capacity(modules.len());
        while let Some(name) = ready.pop_first() {
            let index = owners[&name];
            order.push(index);
            for dependent in &dependents[index] {
                remaining[*dependent] -= 1;
                if remaining[*dependent] == 0 {
                    ready.insert(modules[*dependent].name.clone());
                }
            }
        }
        let cycle: Vec<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] != 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        for (index, left) in remaining.iter().enumerate() {
            if *left != 0 {
                decoded[index] = Some(Err(OleanCheckError::ModuleImportCycle {
                    modules: cycle.clone(),
                }));
                order.push(index);
            }
        }

        let count = modules.len();
        let mut position = vec![0_usize; count];
        for (at, index) in order.iter().enumerate() {
            position[*index] = at;
        }
        // Each module's transitive import closure, itself included. Frontier order
        // is topological, so every import's closure exists before its importer's.
        let mut closures: Vec<std::sync::Arc<BTreeSet<usize>>> =
            vec![std::sync::Arc::default(); count];
        for index in &order {
            let mut closure = BTreeSet::new();
            for dependency in &dependencies[*index] {
                if dependency != index {
                    closure.extend(closures[*dependency].iter().copied());
                }
            }
            closure.insert(*index);
            closures[*index] = std::sync::Arc::new(closure);
        }

        // A row waits here from its decision until every earlier row has left.
        let mut pending_rows: Vec<Option<OleanFrontierRow>> = (0..count).map(|_| None).collect();
        let mut decided = vec![false; count];
        let mut accepted: Vec<Option<std::sync::Arc<FrontierAccepted>>> = vec![None; count];
        let mut engines = FrontierEngines::new(
            (0..count)
                .map(|index| frontier_base_of(&dependencies, &closures, |i| position[i], index))
                .collect(),
        );
        let mut rows = Vec::with_capacity(count);
        let threads = jobs.threads.get();

        let run = |work: FrontierWork| {
            let FrontierWork {
                index,
                position,
                artifact,
                imports,
            } = work;
            let started = std::time::Instant::now();
            frontier_guarded(index, false, started, || {
                let artifact = match artifact {
                    Some(artifact) => Ok(artifact),
                    None => decode_olean_module_input_with(
                        &modules[index],
                        limits,
                        CheckerReading::Read,
                    ),
                };
                match artifact {
                    Ok(artifact) => {
                        let mut done = check(FrontierJob {
                            index,
                            position,
                            name: modules[index].name.clone(),
                            artifact,
                            base: imports.base,
                            closure: imports.closure,
                            retain: false,
                        });
                        done.elapsed = started.elapsed();
                        done
                    }
                    Err(error) => FrontierDone {
                        index,
                        host_memory_refusal: olean_host_memory_refusal(&error),
                        verdict: frontier_error_verdict(error),
                        accepted: None,
                        engine: None,
                        elapsed: started.elapsed(),
                        retained: None,
                    },
                }
            })
        };
        std::thread::scope(|scope| -> Result<(), OleanCheckError> {
            let (job_sender, job_receiver) = std::sync::mpsc::channel::<FrontierWork>();
            let (done_sender, done_receiver) = std::sync::mpsc::channel::<FrontierDone>();
            let job_receiver = std::sync::Arc::new(std::sync::Mutex::new(job_receiver));
            if threads > 1 {
                for worker in 0..threads {
                    let job_receiver = std::sync::Arc::clone(&job_receiver);
                    let done_sender = done_sender.clone();
                    let run = &run;
                    std::thread::Builder::new()
                        .name(format!("fln-frontier-{worker}"))
                        .stack_size(jobs.worker_stack_bytes)
                        .spawn_scoped(scope, move || {
                            loop {
                                let next = match job_receiver.lock() {
                                    Ok(receiver) => receiver.recv(),
                                    Err(_) => return,
                                };
                                let Ok(job) = next else { return };
                                if done_sender.send(run(job)).is_err() {
                                    return;
                                }
                            }
                        })
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "could not start a frontier worker thread",
                        })?;
                }
            }
            drop(done_sender);

            let mut running = vec![false; count];
            let mut in_flight = 0_usize;
            let mut overlapped = vec![false; count];
            let mut retry_imports: Vec<Option<FrontierRetryImports>> = vec![None; count];
            let mut memory_retries: Vec<Option<OleanFrontierMemoryRetry>> =
                (0..count).map(|_| None).collect();
            let mut retry_pending = BTreeSet::new();
            let mut isolated_running = None;
            // A council result's row, reported the moment it exists.
            let settle =
                |index: usize,
                 pending_rows: &[Option<OleanFrontierRow>],
                 on_event: &mut dyn FnMut(OleanFrontierEvent<'_>)| {
                    if let Some(row) = &pending_rows[index] {
                        on_event(OleanFrontierEvent::Settled {
                            position: position[index] + 1,
                            total: count,
                            row,
                        });
                    }
                };
            let record =
                |done: FrontierDone,
                 running: &mut Vec<bool>,
                 decided: &mut Vec<bool>,
                 accepted: &mut Vec<Option<std::sync::Arc<FrontierAccepted>>>,
                 engines: &mut FrontierEngines,
                 pending_rows: &mut Vec<Option<OleanFrontierRow>>,
                 memory_retry: Option<OleanFrontierMemoryRetry>,
                 decode_memory_retry: Option<OleanDecodeMemoryRetry>| {
                    running[done.index] = false;
                    decided[done.index] = true;
                    accepted[done.index] = done.accepted.map(std::sync::Arc::new);
                    engines.keep(done.index, done.engine);
                    pending_rows[done.index] = Some(OleanFrontierRow {
                        name: modules[done.index].name.clone(),
                        verdict: done.verdict,
                        elapsed: done.elapsed.saturating_add(
                            memory_retry
                                .as_ref()
                                .map_or(std::time::Duration::ZERO, |retry| retry.first_elapsed),
                        ),
                        memory_retry,
                        decode_memory_retry,
                    });
                };
            loop {
                // Decide every module that needs no council, and collect the ready.
                let mut ready = Vec::new();
                for index in &order {
                    let index = *index;
                    if decided[index]
                        || running[index]
                        || retry_pending.contains(&(position[index], index))
                    {
                        continue;
                    }
                    let verdict = match &decoded[index] {
                        Some(Ok(_)) => {
                            if !dependencies[index]
                                .iter()
                                .all(|dependency| decided[*dependency])
                            {
                                continue;
                            }
                            match dependencies[index]
                                .iter()
                                .find(|dependency| accepted[**dependency].is_none())
                            {
                                Some(blocker) => OleanModuleVerdict::Blocked {
                                    by: modules[*blocker].name.clone(),
                                },
                                None => {
                                    ready.push(index);
                                    continue;
                                }
                            }
                        }
                        Some(Err(_)) => match decoded[index].take() {
                            Some(Err(error)) => frontier_error_verdict(error),
                            _ => continue,
                        },
                        None => frontier_error_verdict(OleanCheckError::InternalInvariant {
                            detail: "frontier module was visited twice",
                        }),
                    };
                    // A blocked module's decoded bodies are no longer needed.
                    // Release them before any isolated retry has to allocate.
                    decoded[index] = None;
                    decided[index] = true;
                    engines.release(index, &closures, false)?;
                    let row = pending_rows[index].insert(OleanFrontierRow {
                        name: modules[index].name.clone(),
                        verdict,
                        elapsed: std::time::Duration::ZERO,
                        memory_retry: None,
                        decode_memory_retry: decode_memory_retries[index].take(),
                    });
                    on_event(OleanFrontierEvent::Settled {
                        position: position[index] + 1,
                        total: count,
                        row,
                    });
                }

                // Rows leave in frontier order, as soon as every earlier row exists.
                while let Some(row) = order
                    .get(rows.len())
                    .and_then(|index| pending_rows[*index].take())
                {
                    on_event(OleanFrontierEvent::Decided {
                        position: rows.len() + 1,
                        total: count,
                        row: &row,
                    });
                    rows.push(row);
                }
                if rows.len() == count {
                    break;
                }

                let mut dispatched = 0_usize;
                if isolated_running.is_none()
                    && in_flight == 0
                    && let Some((_, index)) = retry_pending.pop_first()
                {
                    let imports =
                        retry_imports[index]
                            .take()
                            .ok_or(OleanCheckError::InternalInvariant {
                                detail: "an isolated retry lost its accepted import closure",
                            })?;
                    let previous = memory_retries[index].as_ref().ok_or(
                        OleanCheckError::InternalInvariant {
                            detail: "an isolated retry has no first memory refusal",
                        },
                    )?;
                    on_event(OleanFrontierEvent::Retrying {
                        position: position[index] + 1,
                        total: count,
                        module: modules[index].name,
                        previous,
                    });
                    running[index] = true;
                    isolated_running = Some(index);
                    in_flight = 1;
                    job_sender
                        .send(FrontierWork {
                            index,
                            position: position[index],
                            artifact: None,
                            imports,
                        })
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "every frontier worker thread has stopped",
                        })?;
                }
                // A queued refusal drains the current workers before retrying.
                // Once that retry starts, no new job may overlap it, including
                // when it was the last entry in the pending retry queue.
                for index in ready
                    .into_iter()
                    .filter(|_| retry_pending.is_empty() && isolated_running.is_none())
                {
                    if in_flight >= threads {
                        break;
                    }
                    let Some(Ok(artifact)) = decoded[index].take() else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "a ready frontier module has no decoded artifact",
                        });
                    };
                    let base = engines.release(index, &closures, true)?;
                    let mut closure: Vec<_> = closures[index]
                        .iter()
                        .filter(|member| **member != index)
                        .filter_map(|member| accepted[*member].clone())
                        .collect();
                    closure.sort_by_key(|module| module.position);
                    on_event(OleanFrontierEvent::Started {
                        position: position[index] + 1,
                        total: count,
                        module: modules[index].name,
                    });
                    if in_flight > 0 {
                        overlapped[index] = true;
                        for (other, active) in running.iter().enumerate() {
                            if *active {
                                overlapped[other] = true;
                            }
                        }
                    }
                    running[index] = true;
                    in_flight += 1;
                    dispatched += 1;
                    let job = FrontierJob {
                        index,
                        position: position[index],
                        name: modules[index].name.clone(),
                        artifact,
                        base,
                        closure,
                        retain: false,
                    };
                    if threads == 1 {
                        // Serial: finish this module before deciding anything else,
                        // so the events keep the one-at-a-time order.
                        let done = check(job);
                        in_flight -= 1;
                        let index = done.index;
                        record(
                            done,
                            &mut running,
                            &mut decided,
                            &mut accepted,
                            &mut engines,
                            &mut pending_rows,
                            None,
                            decode_memory_retries[index].take(),
                        );
                        settle(index, &pending_rows, on_event);
                        break;
                    }
                    retry_imports[index] = Some(FrontierRetryImports {
                        base: job.base.clone(),
                        closure: job.closure.clone(),
                    });
                    if job_sender
                        .send(FrontierWork {
                            index,
                            position: position[index],
                            artifact: Some(job.artifact),
                            imports: FrontierRetryImports {
                                base: job.base,
                                closure: job.closure,
                            },
                        })
                        .is_err()
                    {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "every frontier worker thread has stopped",
                        });
                    }
                }
                if threads == 1 {
                    if dispatched == 0 {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "the frontier stalled with modules undecided",
                        });
                    }
                    continue;
                }
                if in_flight == 0 {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "the frontier stalled with modules undecided",
                    });
                }
                let done =
                    done_receiver
                        .recv()
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "every frontier worker thread has stopped",
                        })?;
                in_flight -= 1;
                let index = done.index;
                if done.host_memory_refusal && overlapped[index] && memory_retries[index].is_none()
                {
                    let OleanModuleVerdict::Inconclusive(first_refusal) = done.verdict else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "a host-memory refusal was not a typed nonanswer",
                        });
                    };
                    running[index] = false;
                    memory_retries[index] = Some(OleanFrontierMemoryRetry {
                        first_refusal,
                        first_elapsed: done.elapsed,
                    });
                    retry_pending.insert((position[index], index));
                    continue;
                }
                if isolated_running == Some(index) {
                    isolated_running = None;
                }
                // Drop completed jobs' extra closure references before a queued
                // retry is dispatched. Only imports the run still needs remain.
                retry_imports[index] = None;
                record(
                    done,
                    &mut running,
                    &mut decided,
                    &mut accepted,
                    &mut engines,
                    &mut pending_rows,
                    memory_retries[index].take(),
                    decode_memory_retries[index].take(),
                );
                settle(index, &pending_rows, on_event);
            }
            drop(job_sender);
            Ok(())
        })?;

        // A merge conflict between modules that never meet is not an error of the
        // run: every row above is already decided (fln-elp6's stdlib run lost its
        // whole --json to two executables' `main`).
        let engine = self
            .frontier_union_engine(order.iter().filter_map(|index| accepted[*index].as_deref()));
        Ok(OleanFrontier { engine, rows })
    }

    /// One engine holding exactly these accepted modules, merged in this order by
    /// the same rule as every closure, or the duplicate that rules it out.
    pub fn frontier_union_engine<'a>(
        &self,
        accepted: impl IntoIterator<Item = &'a FrontierAccepted>,
    ) -> Result<Admitted, OleanCheckError> {
        let mut engine = self.clone();
        let mut environment = self.environment.clone();
        let mut imported = (*self.imported_modules).clone();
        for module in accepted {
            for entry in &module.admitted {
                environment = merge_frontier_entry(environment, entry)?;
            }
            imported.insert(module.name.clone());
        }
        engine.environment = environment;
        engine.checker_environment = None;
        engine.imported_modules = std::sync::Arc::new(imported);
        Ok(engine)
    }

    /// [`Engine::check_olean_modules`] over `jobs.threads` modules at once, returning
    /// what the serial door returns.
    ///
    /// The set is decoded, refused and ordered by the serial door's own planner, so
    /// every whole-set refusal is the serial one. Each module then goes through the
    /// frontier's per-module council ([`Engine::check_olean_frontier_scheduled`])
    /// against exactly its own import closure, and the serial result is reassembled
    /// in the serial order: one environment merged from what each module admitted,
    /// each module's two logical roots over that cumulative environment, its checker
    /// rows, and the retained checker projection of every admitted declaration. A
    /// module that repeats a name which an earlier module outside its closure
    /// declared is re-planned against the cumulative environment, so its rows split
    /// as the serial planner splits them.
    ///
    /// The serial door stops at the first module of that order whose check does not
    /// complete, and so does this one: it returns that module's error, non-answer or
    /// fault. Once a module has stopped no later module is dispatched; earlier ones
    /// still finish, since one of them may be the first to stop.
    ///
    /// One thread, or a base engine whose environment is not empty, takes the serial
    /// door itself: over a nonempty base the serial projection also holds the base
    /// constants each review covered, which the per-module projections do not
    /// reproduce. `cancellation` is sampled at module boundaries; a running
    /// council is not interrupted. The serial fallback also samples before
    /// decoding and before publishing the completed set, returning no partial
    /// successor on cancellation. Parallel work whose answer is already fixed
    /// retains its existing completed-answer precedence.
    pub fn check_olean_modules_scheduled(
        &self,
        modules: &[OleanModuleInput<'_>],
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<CheckedOleanSet>, OleanCheckError> {
        if jobs.threads.get() == 1 || !self.environment.is_empty() {
            return self.check_olean_modules_with_cancel(modules, options, limits, cancellation);
        }
        let ordered = self.decode_olean_module_set(modules, limits, CheckerReading::Read, jobs)?;
        let bound_base = (self.environment == Environment::new()
            || self
                .imported_environment
                .as_ref()
                .is_some_and(|snapshot| snapshot == &self.environment))
            && modules
                .iter()
                .all(|module| !self.imported_modules.contains(module.name));
        let names: Vec<Name> = ordered.iter().map(|(name, _)| name.clone()).collect();
        let scheduled =
            match self.schedule_olean_module_set(ordered, options, limits, jobs, cancellation)? {
                Outcome::Complete(scheduled) => scheduled,
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            };
        self.reassemble_olean_module_set(names, scheduled, bound_base, options, limits)
            .map(Outcome::Complete)
    }

    /// Check a decoded set, in the serial door's order, over `jobs.threads` workers,
    /// each module against its own import closure, keeping what the serial result
    /// is reassembled from. The answer is the serial one: the first module of the
    /// order whose check did not complete decides it.
    fn schedule_olean_module_set(
        &self,
        ordered: Vec<(Name, DecodedOlean)>,
        options: &KVMap,
        limits: OleanCheckLimits,
        jobs: OleanFrontierJobs,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Result<Outcome<Vec<ScheduledOleanModule>>, OleanCheckError> {
        let count = ordered.len();
        let positions: BTreeMap<Name, usize> = ordered
            .iter()
            .enumerate()
            .map(|(position, (name, _))| (name.clone(), position))
            .collect();
        let mut names = Vec::with_capacity(count);
        let mut artifacts = Vec::with_capacity(count);
        let mut dependencies: Vec<BTreeSet<usize>> = Vec::with_capacity(count);
        // Each module's transitive import closure, itself included.
        let mut closures: Vec<std::sync::Arc<BTreeSet<usize>>> = Vec::with_capacity(count);
        for (position, (name, artifact)) in ordered.into_iter().enumerate() {
            let mut imports = BTreeSet::new();
            let mut closure = BTreeSet::new();
            for import in &artifact.module.imports {
                let Some(&dependency) = positions
                    .get(&import.module)
                    .filter(|dependency| **dependency < position)
                else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "a serially ordered module imports a module that is not before it",
                    });
                };
                imports.insert(dependency);
                closure.extend(closures[dependency].iter().copied());
            }
            closure.insert(position);
            names.push(name);
            artifacts.push(Some(artifact));
            dependencies.push(imports);
            closures.push(std::sync::Arc::new(closure));
        }

        let threads = jobs.threads.get();
        let mut accepted: Vec<Option<std::sync::Arc<FrontierAccepted>>> = vec![None; count];
        let mut engines = FrontierEngines::new(
            (0..count)
                .map(|index| frontier_base_of(&dependencies, &closures, |i| i, index))
                .collect(),
        );
        let mut retained: Vec<Option<FrontierRetained>> = (0..count).map(|_| None).collect();
        let mut decided = vec![false; count];
        let mut running = vec![false; count];
        // The first position whose check did not complete, and how it ended.
        let mut stop_at = count;
        let mut stopped: Option<(OleanModuleVerdict, Option<FrontierRetained>)> = None;
        let mut cancelled = false;
        let base = self;
        let check = |job: FrontierJob| base.frontier_check_module(job, options, limits);
        std::thread::scope(|scope| -> Result<(), OleanCheckError> {
            let (job_sender, job_receiver) = std::sync::mpsc::channel::<FrontierJob>();
            let (done_sender, done_receiver) = std::sync::mpsc::channel::<FrontierDone>();
            let job_receiver = std::sync::Arc::new(std::sync::Mutex::new(job_receiver));
            for worker in 0..threads {
                let job_receiver = std::sync::Arc::clone(&job_receiver);
                let done_sender = done_sender.clone();
                let check = &check;
                std::thread::Builder::new()
                    .name(format!("fln-olean-set-{worker}"))
                    .stack_size(jobs.worker_stack_bytes)
                    .spawn_scoped(scope, move || {
                        loop {
                            let next = match job_receiver.lock() {
                                Ok(receiver) => receiver.recv(),
                                Err(_) => return,
                            };
                            let Ok(job) = next else { return };
                            if done_sender.send(check(job)).is_err() {
                                return;
                            }
                        }
                    })
                    .map_err(|_| OleanCheckError::InternalInvariant {
                        detail: "could not start a module-set worker thread",
                    })?;
            }
            drop(done_sender);

            let mut in_flight = 0_usize;
            loop {
                cancelled = cancelled || cancellation.is_some_and(CancellationProbe::is_cancelled);
                // Dispatch in serial order, never past the first stopped module: a
                // module is ready once every import it names has been accepted.
                if !cancelled {
                    for index in 0..stop_at {
                        if in_flight >= threads {
                            break;
                        }
                        if decided[index]
                            || running[index]
                            || !dependencies[index]
                                .iter()
                                .all(|dependency| accepted[*dependency].is_some())
                        {
                            continue;
                        }
                        let Some(artifact) = artifacts[index].take() else {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "a ready module-set member has no decoded artifact",
                            });
                        };
                        let base = engines.release(index, &closures, true)?;
                        let mut closure: Vec<_> = closures[index]
                            .iter()
                            .filter(|member| **member != index)
                            .filter_map(|member| accepted[*member].clone())
                            .collect();
                        closure.sort_by_key(|module| module.position);
                        running[index] = true;
                        in_flight += 1;
                        let job = FrontierJob {
                            index,
                            position: index,
                            name: names[index].clone(),
                            artifact,
                            base,
                            closure,
                            retain: true,
                        };
                        if job_sender.send(job).is_err() {
                            return Err(OleanCheckError::InternalInvariant {
                                detail: "every module-set worker thread has stopped",
                            });
                        }
                    }
                }
                if in_flight == 0 {
                    if cancelled || decided[..stop_at].iter().all(|done| *done) {
                        break;
                    }
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "the module-set schedule stalled with modules undecided",
                    });
                }
                let done =
                    done_receiver
                        .recv()
                        .map_err(|_| OleanCheckError::InternalInvariant {
                            detail: "every module-set worker thread has stopped",
                        })?;
                in_flight -= 1;
                let FrontierDone {
                    index,
                    verdict,
                    accepted: module,
                    engine,
                    retained: kept,
                    ..
                } = done;
                running[index] = false;
                decided[index] = true;
                match (module, kept) {
                    (Some(module), Some(checked @ FrontierRetained::Checked { .. })) => {
                        accepted[index] = Some(std::sync::Arc::new(module));
                        engines.keep(index, engine);
                        retained[index] = Some(checked);
                    }
                    (Some(_), _) => {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "an accepted module-set member kept no checked record",
                        });
                    }
                    (None, kept) => {
                        if index < stop_at {
                            stop_at = index;
                            stopped = Some((verdict, kept));
                        }
                    }
                }
            }
            drop(job_sender);
            Ok(())
        })?;

        if !decided[..stop_at].iter().all(|done| *done) {
            // Cancelled before the answer was fixed.
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "olean-modules/scheduled",
            )));
        }
        if let Some((verdict, kept)) = stopped {
            return match (kept, verdict) {
                (Some(FrontierRetained::Failed(error)), _) => Err(error),
                (_, OleanModuleVerdict::Inconclusive(reason)) => Ok(Outcome::Inconclusive(reason)),
                (_, OleanModuleVerdict::InternalFault(fault)) => Ok(Outcome::InternalFault(fault)),
                _ => Err(OleanCheckError::InternalInvariant {
                    detail: "a stopped module-set member kept neither its error nor its non-answer",
                }),
            };
        }
        let mut scheduled = Vec::with_capacity(count);
        for (module, kept) in accepted.into_iter().zip(retained) {
            let (
                Some(module),
                Some(FrontierRetained::Checked {
                    decoded,
                    declarations,
                    closure_digests,
                    checker_entries,
                }),
            ) = (module, kept)
            else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "a decided module-set member lost its checked record",
                });
            };
            scheduled.push(ScheduledOleanModule {
                module,
                decoded: *decoded,
                declarations,
                closure_digests,
                checker_entries,
            });
        }
        Ok(Outcome::Complete(scheduled))
    }

    /// The serial door's [`CheckedOleanSet`] from modules each checked against its
    /// own closure, visited in the serial order. The environment, roots, rows and
    /// retained checker projection are those of admitting the modules one after
    /// another into this (empty) engine.
    pub fn reassemble_olean_module_set(
        &self,
        names: Vec<Name>,
        scheduled: Vec<ScheduledOleanModule>,
        bound_base: bool,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<CheckedOleanSet, OleanCheckError> {
        let invariant = |detail| OleanCheckError::InternalInvariant { detail };
        let base_logical_root = self.logical_root(options);
        let mut environment = self.environment.clone();
        let mut root = base_logical_root;
        let mut admitted_any = false;
        let mut candidates = Vec::new();
        let mut checked_modules = Vec::new();
        checked_modules
            .try_reserve_exact(scheduled.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean checked module records",
                requested: scheduled.len(),
            })?;
        for (name, scheduled) in names.into_iter().zip(scheduled) {
            let ScheduledOleanModule {
                module,
                decoded,
                declarations,
                closure_digests,
                checker_entries,
            } = scheduled;
            if closure_digests.len() != decoded.constants.len() {
                return Err(invariant(
                    "a module's closure digests do not cover its constants",
                ));
            }
            let module_base_root = root;
            // A constant the serial environment already holds, while this module's
            // closure did not (or held another copy), is planned differently there.
            let own: BTreeSet<&Name> = module
                .admitted
                .iter()
                .map(|entry| entry.declaration().name())
                .collect();
            let repeats = decoded
                .constants
                .iter()
                .zip(&closure_digests)
                .any(|(info, copy)| {
                    environment.entry(info.name()).is_some_and(|present| {
                        own.contains(info.name())
                            || copy.is_none_or(|copy| copy != present.digest())
                    })
                });
            let declarations = if repeats {
                serial_olean_rows(&environment, &decoded, declarations, limits)?
            } else {
                declarations
            };
            let mut added = Vec::new();
            for entry in &module.admitted {
                let name = entry.declaration().name();
                if environment.contains(name) {
                    environment = merge_frontier_entry(environment, entry)?;
                } else {
                    environment = environment
                        .with_entry(entry.clone())
                        .map_err(|_| invariant("an absent admitted constant could not be added"))?;
                    added.push(name.clone());
                }
            }
            if !added.is_empty() {
                admitted_any = true;
                root = environment.logical_root(options);
                for name in added {
                    match checker_entries.get(&name) {
                        Some(Ok(entry)) => candidates.push(entry.clone()),
                        Some(Err(detail)) => return Err(invariant(detail)),
                        None => {
                            return Err(invariant(
                                "an admitted constant is missing from its checker projection",
                            ));
                        }
                    }
                }
            }
            checked_modules.push(CheckedOleanModule {
                name,
                decoded,
                base_logical_root: module_base_root,
                result_logical_root: root,
                declarations,
            });
        }

        // Serially, every admission extends the retained projection with its own
        // candidate; over an empty base nothing else is ever covered.
        let checker_environment = if admitted_any {
            let mut projection = self.checker_environment.clone().unwrap_or_default();
            for entry in candidates {
                projection = match projection.extend(entry, limits.admission.checker.environment) {
                    CheckerEnvironmentOutcome::Complete { environment, .. } => environment,
                    _ => {
                        return Err(invariant(
                            "the admitted checker entries could not be reassembled",
                        ));
                    }
                };
            }
            Some(projection)
        } else {
            self.checker_environment.clone()
        };
        let mut imported = (*self.imported_modules).clone();
        imported.extend(checked_modules.iter().map(|module| module.name.clone()));
        let mut dependencies = (*self.imported_module_dependencies).clone();
        for module in &checked_modules {
            dependencies.insert(
                module.name.clone(),
                module
                    .decoded
                    .module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
            );
        }
        let imported_environment = bound_base.then(|| environment.clone());
        let engine = Admitted {
            environment,
            checker_environment,
            imported_modules: std::sync::Arc::new(imported),
            imported_environment,
            imported_module_dependencies: std::sync::Arc::new(dependencies),
            executable_opaques: std::sync::Arc::clone(&self.executable_opaques),
            runtime_initializers: std::sync::Arc::clone(&self.runtime_initializers),
            options: if admitted_any {
                options.clone()
            } else {
                self.options.clone()
            },
        };
        Ok(CheckedOleanSet {
            engine,
            base_logical_root,
            result_logical_root: root,
            modules: checked_modules,
        })
    }

    /// Check one frontier module against its import closure's environment.
    pub fn frontier_check_module(
        &self,
        job: FrontierJob,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> FrontierDone {
        let started = std::time::Instant::now();
        let (index, retain) = (job.index, job.retain);
        frontier_guarded(index, retain, started, || {
            self.frontier_check_module_unguarded(job, options, limits, started)
        })
    }

    fn frontier_check_module_unguarded(
        &self,
        job: FrontierJob,
        options: &KVMap,
        limits: OleanCheckLimits,
        started: std::time::Instant,
    ) -> FrontierDone {
        let index = job.index;
        let retain = job.retain;
        let finish = |verdict: OleanModuleVerdict,
                      accepted: Option<(FrontierAccepted, Admitted)>,
                      retained: Option<FrontierRetained>| {
            let (accepted, engine) = accepted.unzip();
            FrontierDone {
                index,
                verdict,
                host_memory_refusal: false,
                accepted,
                engine,
                elapsed: started.elapsed(),
                retained,
            }
        };
        let failed = |error: OleanCheckError| {
            let host_memory_refusal = olean_host_memory_refusal(&error);
            let retained = retain.then(|| FrontierRetained::Failed(error.clone()));
            let mut done = finish(frontier_error_verdict(error), None, retained);
            done.host_memory_refusal = host_memory_refusal;
            done
        };
        let engine = match self.frontier_closure_engine(&job) {
            Ok(engine) => engine,
            Err(error) => return failed(error),
        };
        let start = engine.environment.clone();
        match engine.check_decoded_olean_unrooted(job.artifact, options, limits) {
            Ok(Outcome::Complete(checked)) => {
                let declarations = checked.declarations.len();
                let admitted: Vec<EnvironmentEntry> = checked
                    .decoded
                    .constants
                    .iter()
                    .filter(|info| !start.contains(info.name()))
                    .filter_map(|info| checked.engine.environment.entry(info.name()))
                    .collect();
                let mut engine = checked.engine;
                let mut imported = (*engine.imported_modules).clone();
                imported.insert(job.name.clone());
                engine.imported_modules = std::sync::Arc::new(imported);
                let retained = retain.then(|| FrontierRetained::Checked {
                    closure_digests: checked
                        .decoded
                        .constants
                        .iter()
                        .map(|info| engine.environment.entry(info.name()).map(|e| e.digest()))
                        .collect(),
                    checker_entries: frontier_checker_entries(&engine, &admitted, limits),
                    decoded: Box::new(checked.decoded),
                    declarations: checked.declarations,
                });
                finish(
                    OleanModuleVerdict::Accepted { declarations },
                    Some((
                        FrontierAccepted {
                            index,
                            position: job.position,
                            name: job.name,
                            admitted,
                        },
                        engine,
                    )),
                    retained,
                )
            }
            Ok(Outcome::Inconclusive(reason)) => {
                finish(OleanModuleVerdict::Inconclusive(reason), None, None)
            }
            Ok(Outcome::InternalFault(fault)) => {
                finish(OleanModuleVerdict::InternalFault(fault), None, None)
            }
            Err(error) => failed(error),
        }
    }

    /// The engine a frontier module is checked with: its import with the largest
    /// closure (the earlier on a tie), plus what the rest of its closure admitted.
    pub fn frontier_closure_engine(&self, job: &FrontierJob) -> Result<Admitted, OleanCheckError> {
        let Some(base) = &job.base else {
            return Ok(self.clone());
        };
        let mut engine = (*base.engine).clone();
        let mut environment = engine.environment.clone();
        let mut imported = (*engine.imported_modules).clone();
        for module in &job.closure {
            if base.closure.contains(&module.index) {
                continue;
            }
            for entry in &module.admitted {
                environment = merge_frontier_entry(environment, entry)?;
            }
            imported.insert(module.name.clone());
        }
        engine.environment = environment;
        engine.imported_modules = std::sync::Arc::new(imported);
        Ok(engine)
    }

    /// Decode a closed set of named `.olean` modules and return them in the
    /// deterministic import-topological order both import trust levels use.
    ///
    /// Every direct import must name another input row, and a name declared by
    /// several modules must be a repeat the Reference's import accepts
    /// (`subsumesInfo`); nothing is admitted here.
    pub fn decode_olean_module_set(
        &self,
        modules: &[OleanModuleInput<'_>],
        limits: OleanCheckLimits,
        reading: CheckerReading,
        jobs: OleanFrontierJobs,
    ) -> Result<Vec<(Name, DecodedOlean)>, OleanCheckError> {
        let owners = olean_module_owners(modules, limits)?;

        let mut decoded = Vec::new();
        decoded.try_reserve_exact(modules.len()).map_err(|_| {
            OleanCheckError::AllocationFailure {
                resource: ".olean decoded module set",
                requested: modules.len(),
            }
        })?;
        for (module, artifact) in modules
            .iter()
            .zip(decode_olean_module_inputs(modules, limits, reading, jobs)?)
        {
            decoded.push(Some((module.name.clone(), artifact.result?)));
        }

        // The per-module companion guard (see `decode_olean_module_artifacts`)
        // proves no single module loses a declaration its exported part
        // declared. It says nothing about the SET: two modules can decode to
        // declarations sharing a name, and at corpus scale they do. Across the
        // 2,431 pinned modules that carry a complete chain, 215,111 per-module
        // constants collapse to 214,919 distinct names — 128 names are declared
        // by more than one module, all re-generated `eq_N` and `congr_simp`
        // lemmas.
        //
        // A repeat is therefore NOT a fault by itself, and refusing one would
        // reject the real corpus. Nor does a repeat need to be byte-identical:
        // the Reference's import accepts one copy that subsumes the other
        // (`subsumesInfo`: the same name, level parameters, and a statement
        // equal up to binder names and binder info, with the kind rules in
        // `olean_imports`), and the pinned `Init` closure carries 16 such pairs:
        // identical statements, different proof terms, so the per-module plan
        // rechecks each repeat's own proof. A repeat that
        // neither side subsumes is a fault: the set has no single meaning for
        // that name, and admission in dependency order would let whichever
        // module sorted first silently win while the loser surfaced as an
        // already-declared rejection from the kernel — attributing to the
        // kernel what is a property of the input. This names both modules
        // instead, at decode time.
        let mut declared: BTreeMap<&Name, (&Name, &ConstantInfo)> = BTreeMap::new();
        for entry in &decoded {
            let Some((module_name, artifact)) = entry.as_ref() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "decoded module disappeared before the set-wide declaration scan",
                });
            };
            for info in &artifact.constants {
                match declared.get(info.name()) {
                    Some(&(owner, previous)) if previous != info => {
                        let lookup = |name: &Name| {
                            declared
                                .get(name)
                                .map(|entry| entry.1)
                                .or_else(|| self.environment.find(name))
                        };
                        if !olean_imports::subsumes_info(&lookup, previous, info)
                            && !olean_imports::subsumes_info(&lookup, info, previous)
                        {
                            return Err(OleanCheckError::ConflictingModuleDeclaration {
                                name: info.name().clone(),
                                first_module: owner.clone(),
                                second_module: module_name.clone(),
                            });
                        }
                    }
                    // An identical or subsuming repeat is coherent. Keep the
                    // first owner so a later conflict is reported against it;
                    // the per-module plan rechecks a subsuming copy's body.
                    Some(_) => {}
                    None => {
                        declared.insert(info.name(), (module_name, info));
                    }
                }
            }
        }

        let mut remaining = vec![0_usize; modules.len()];
        let mut dependents = vec![Vec::new(); modules.len()];
        for (index, module) in decoded.iter().enumerate() {
            let Some((_, artifact)) = module.as_ref() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "decoded module disappeared before planning",
                });
            };
            let mut missing = BTreeSet::new();
            let mut dependencies = BTreeSet::new();
            for import in &artifact.module.imports {
                match owners.get(&import.module).copied() {
                    Some(owner) if owner != index => {
                        dependencies.insert(owner);
                    }
                    Some(_) => {
                        dependencies.insert(index);
                    }
                    None => {
                        missing.insert(import.module.clone());
                    }
                }
            }
            if !missing.is_empty() {
                let Some(input) = modules.get(index) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "decoded module has no corresponding input",
                    });
                };
                return Err(OleanCheckError::MissingModuleImports {
                    module: input.name.clone(),
                    imports: missing.into_iter().collect(),
                });
            }
            remaining[index] = dependencies.len();
            for dependency in dependencies {
                dependents[dependency].push(index);
            }
        }

        let mut ready: BTreeSet<Name> = modules
            .iter()
            .enumerate()
            .filter(|(index, _)| remaining[*index] == 0)
            .map(|(_, module)| module.name.clone())
            .collect();
        let mut order = Vec::new();
        order
            .try_reserve_exact(modules.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean module order",
                requested: modules.len(),
            })?;
        while let Some(name) = ready.pop_first() {
            let Some(&index) = owners.get(&name) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "ready module has no owner",
                });
            };
            order.push(index);
            let Some(next) = dependents.get(index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "module owner is outside the dependent table",
                });
            };
            for dependent in next {
                let Some(count) = remaining.get_mut(*dependent) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "dependent module is outside the remaining table",
                    });
                };
                *count = count
                    .checked_sub(1)
                    .ok_or(OleanCheckError::InternalInvariant {
                        detail: "module dependency count underflowed",
                    })?;
                if *count == 0 {
                    let Some(module) = modules.get(*dependent) else {
                        return Err(OleanCheckError::InternalInvariant {
                            detail: "ready dependent is outside the module table",
                        });
                    };
                    ready.insert(module.name.clone());
                }
            }
        }
        if order.len() != modules.len() {
            return Err(OleanCheckError::ModuleImportCycle {
                modules: modules
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| remaining[*index] != 0)
                    .map(|(_, module)| module.name.clone())
                    .collect(),
            });
        }

        let mut ordered = Vec::new();
        ordered
            .try_reserve_exact(order.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean ordered module set",
                requested: order.len(),
            })?;
        for index in order {
            let Some(slot) = decoded.get_mut(index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module is outside the decoded table",
                });
            };
            let Some(module) = slot.take() else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "topological module was consumed more than once",
                });
            };
            ordered.push(module);
        }
        Ok(ordered)
    }

    pub fn check_decoded_olean(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<CheckedOlean>, OleanCheckError> {
        let checked = match self.check_decoded_olean_unrooted(decoded, options, limits)? {
            Outcome::Complete(checked) => checked,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let base_logical_root = self.logical_root(options);
        let result_logical_root = if checked.unchanged {
            base_logical_root
        } else {
            checked.engine.logical_root(options)
        };
        Ok(Outcome::Complete(CheckedOlean {
            engine: checked.engine,
            decoded: checked.decoded,
            base_logical_root,
            result_logical_root,
            declarations: checked.declarations,
        }))
    }

    /// [`Engine::check_decoded_olean`] without the two whole-environment logical
    /// roots, for the frontier, whose rows carry neither. Each root encodes and
    /// hashes every constant of the environment, which on a Mathlib-sized closure
    /// is a large share of a small module's check.
    fn check_decoded_olean_unrooted(
        &self,
        decoded: DecodedOlean,
        options: &KVMap,
        limits: OleanCheckLimits,
    ) -> Result<Outcome<UnrootedOlean>, OleanCheckError> {
        let plan = plan_olean_declarations(&self.environment, &decoded.constants, limits)?;
        // The checker seat judges each declaration against its own reading of the
        // artifact (bead `franken_lean-z8j.1.14`); without one it has no
        // independent answer about any of them.
        let readings = match ArtifactReadings::new(&decoded.independent) {
            Ok(readings) => readings,
            Err(error) => return error.into_nonanswer(),
        };
        // A constant already present is reported checked because the primary
        // decode equals one admitted earlier, and no council reviews it.
        if !plan.already_present.is_empty() {
            let by_name: BTreeMap<&Name, &ConstantInfo> = decoded
                .constants
                .iter()
                .map(|info| (info.name(), info))
                .collect();
            for (name, _) in &plan.already_present {
                let Some(info) = by_name.get(name) else {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "an already-present declaration is not in the decoded table",
                    });
                };
                if let Some(objection) = readings.objection(info, limits.admission.checker.decode) {
                    return unreviewed_reading_refusal(name, objection);
                }
            }
        }
        let reading = ReadingCheck::Artifact(&readings);
        if plan.order.is_empty() {
            let mut checked: Vec<OleanCheckedDeclaration> = plan
                .already_present
                .into_iter()
                .map(|(name, checker)| OleanCheckedDeclaration { name, checker })
                .collect();
            match self.recheck_subsumed_repeats(
                plan.subsumed,
                options,
                limits.admission,
                reading,
            )? {
                Outcome::Complete(rechecked) => checked.extend(rechecked),
                Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
            }
            return Ok(Outcome::Complete(UnrootedOlean {
                engine: self.clone(),
                decoded,
                declarations: checked,
                unchanged: true,
            }));
        }

        let mut declarations = Vec::new();
        declarations
            .try_reserve_exact(plan.order.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean declaration batch",
                requested: plan.order.len(),
            })?;
        for index in &plan.order {
            let Some(unit) = plan.units.get(*index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "planned declaration unit is outside the unit table",
                });
            };
            declarations.push(unit.declaration.clone());
        }
        let (engine, checkers) = match self
            .admit_declarations_unrooted(&declarations, options, limits.admission, reading)
            .map_err(OleanCheckError::Admission)?
        {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        if checkers.len() != plan.order.len() {
            return Err(OleanCheckError::InternalInvariant {
                detail: "admission result count differs from the authority-unit plan",
            });
        }
        let mut checked = Vec::new();
        checked
            .try_reserve_exact(decoded.constants.len())
            .map_err(|_| OleanCheckError::AllocationFailure {
                resource: ".olean completed declaration records",
                requested: decoded.constants.len(),
            })?;
        for (unit_index, checker) in plan.order.iter().zip(&checkers) {
            let Some(unit) = plan.units.get(*unit_index) else {
                return Err(OleanCheckError::InternalInvariant {
                    detail: "completed declaration unit is outside the unit table",
                });
            };
            for name in &unit.names {
                checked.push(OleanCheckedDeclaration {
                    name: name.clone(),
                    checker: *checker,
                });
            }
        }
        for (name, checker) in plan.already_present {
            checked.push(OleanCheckedDeclaration { name, checker });
        }
        match engine.recheck_subsumed_repeats(plan.subsumed, options, limits.admission, reading)? {
            Outcome::Complete(rechecked) => checked.extend(rechecked),
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
        if checked.len() != decoded.constants.len() {
            return Err(OleanCheckError::InternalInvariant {
                detail: "checked declaration count differs from the decoded declaration table",
            });
        }
        Ok(Outcome::Complete(UnrootedOlean {
            engine,
            decoded,
            declarations: checked,
            unchanged: false,
        }))
    }

    /// Check the body of each repeat the Reference's import accepts over an
    /// already admitted copy (`subsumesInfo`), so that "checked" stays literal.
    ///
    /// A theorem is admitted under a fresh scratch name against this engine and
    /// the successor is discarded: the published environment keeps the first
    /// copy. An axiom repeat has no body, and its statement is equal up to
    /// binder names and binder info to one already checked.
    ///
    /// Each repeat is compared with the checker's own reading as the artifact
    /// states it, before any renaming: a theorem's council then carries that
    /// comparison, and an axiom repeat, which no council reviews, is refused on a
    /// difference here.
    pub fn recheck_subsumed_repeats(
        &self,
        repeats: Vec<ConstantInfo>,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<Vec<OleanCheckedDeclaration>>, OleanCheckError> {
        let mut checked = Vec::new();
        for repeat in repeats {
            let name = repeat.name().clone();
            let objection = match reading {
                ReadingCheck::Artifact(readings) => {
                    readings.objection(&repeat, limits.checker.decode)
                }
                ReadingCheck::Unread | ReadingCheck::Settled(_) => None,
            };
            let checker = match repeat {
                ConstantInfo::Thm(mut theorem) => {
                    let mut scratch = Name::str(name.clone(), "_fln_subsumed_repeat");
                    let mut suffix = 0_u64;
                    while self.environment.contains(&scratch) {
                        suffix += 1;
                        scratch =
                            Name::num(Name::str(name.clone(), "_fln_subsumed_repeat"), suffix);
                    }
                    theorem.base.name = scratch.clone();
                    for member in &mut theorem.all {
                        if *member == name {
                            *member = scratch.clone();
                        }
                    }
                    let reading = match reading {
                        ReadingCheck::Artifact(_) => ReadingCheck::Settled(objection.as_ref()),
                        other => other,
                    };
                    match self
                        .admit_declaration_unrooted(
                            Declaration::Thm(theorem),
                            options,
                            limits,
                            reading,
                        )
                        .map_err(OleanCheckError::Admission)?
                    {
                        Outcome::Complete(admission) => admission.checker,
                        Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
                        Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
                    }
                }
                ConstantInfo::Axiom(_) => {
                    if let Some(objection) = objection {
                        return unreviewed_reading_refusal(&name, objection);
                    }
                    CheckerAgreement {
                        schema: "fln-checker/v1",
                        ground: CheckerAdmissionGround::AxiomPreamble,
                    }
                }
                _ => {
                    return Err(OleanCheckError::InternalInvariant {
                        detail: "only theorems and axioms can subsume an admitted repeat",
                    });
                }
            };
            checked.push(OleanCheckedDeclaration { name, checker });
        }
        Ok(Outcome::Complete(checked))
    }

    /// Admit and publish one declaration without compiling or executing it.
    ///
    /// This is the environment-building counterpart to
    /// [`Self::execute_definition`]. It currently accepts the declaration kinds
    /// on which both K1 and the independent checker can issue a completed
    /// verdict: axioms, definitions, theorems, opaques, non-safe mutual
    /// definition blocks, the fixed quotient initialization unit, and safe,
    /// nonrecursive, non-nested, parameter-free `Type` inductives with bounded
    /// constructor fields. Other inductive families remain checker
    /// non-answers until an independent complete-unit ground exists for them.
    ///
    /// Success returns a new immutable engine snapshot. A rejection,
    /// independent-checker non-answer, duplicate, resource stop, or internal
    /// fault exposes no successor and leaves `self` unchanged.
    pub fn admit_declaration(
        &self,
        declaration: Declaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
    ) -> Result<Outcome<DeclarationAdmission>, EngineAdmissionError> {
        let mut admitted = match self.admit_declaration_unrooted(
            declaration,
            options,
            limits,
            ReadingCheck::Unread,
        )? {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        // No artifact metadata exists for a handed declaration, so its value is
        // what the pin's compiler runs (`toDecl`, `value? (allowOpaque := true)`).
        if let Declaration::Opaque(value) = &admitted.declaration {
            let mut names = (*self.executable_opaques).clone();
            names.insert(value.base.name.clone());
            admitted.engine.executable_opaques = std::sync::Arc::new(names);
        }
        // `self` is immutable, so its root is the same before or after the council.
        let base_logical_root = self.logical_root(options);
        let result_logical_root = admitted.engine.environment.logical_root(options);
        Ok(Outcome::Complete(DeclarationAdmission {
            engine: admitted.engine,
            declaration: admitted.declaration,
            base_logical_root,
            result_logical_root,
            checker: admitted.checker,
        }))
    }

    /// [`Self::admit_declaration`] without the two logical roots. Each root is a
    /// pass over the whole environment (every constant's name encoded and sorted),
    /// about 0.8 s at Mathlib's 133K constants; the `.olean` check admits a module
    /// one declaration at a time and reads neither, so it pays for them nowhere.
    ///
    /// `reading` is what the checker seat compares the declaration against: an
    /// `.olean` declaration must be the one the checker itself read from the
    /// artifact (bead `franken_lean-z8j.1.14`).
    pub fn admit_declaration_unrooted(
        &self,
        declaration: Declaration,
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<UnrootedAdmission>, EngineAdmissionError> {
        if !matches!(
            declaration,
            Declaration::Axiom(_)
                | Declaration::Defn(_)
                | Declaration::Thm(_)
                | Declaration::Opaque(_)
                | Declaration::Mutual(_)
                | Declaration::Inductive(_)
                | Declaration::Quotient(_)
        ) {
            return Err(EngineAdmissionError::UnsupportedDeclaration {
                kind: declaration_kind(&declaration),
            });
        }

        let checker_review = review_with_independent_checker(
            &self.environment,
            self.checker_environment.as_ref(),
            &declaration,
            limits.checker,
            reading,
        );
        let admitted = match admit(&self.environment, declaration.clone(), limits.kernel) {
            Outcome::Complete(admitted) => admitted,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        let checked = match convene(&checker_review.council, admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, message, .. } => {
                return Err(EngineAdmissionError::KernelRejected { class, message });
            }
            // A halt with no disagreement is a non-answer about the declaration
            // (FL-INV-07); only a disagreement is evidence against it.
            CouncilOutcome::Halted(halt) if halt.is_purely_resource() => {
                return Err(EngineAdmissionError::CouncilNoAnswer {
                    summary: halt.summary(),
                });
            }
            CouncilOutcome::Halted(halt) => {
                return Err(EngineAdmissionError::CouncilHalted {
                    summary: halt.summary(),
                });
            }
        };
        let checker =
            checker_review
                .agreement
                .ok_or_else(|| EngineAdmissionError::CheckerBridge {
                    detail: "the checker council agreed without an admission record".to_owned(),
                })?;
        let checker_environment = checker_review.successor_environment.ok_or_else(|| {
            EngineAdmissionError::CheckerBridge {
                detail: "the checker council agreed without a retained successor environment"
                    .to_owned(),
            }
        })?;
        let expects_block = matches!(
            declaration,
            Declaration::Mutual(_) | Declaration::Inductive(_) | Declaration::Quotient(_)
        );
        let environment = match checked.publish(limits.declaration, limits.collisions, None) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                publication,
            ))) => {
                if expects_block {
                    return Err(EngineAdmissionError::UnexpectedPublication {
                        detail: "a block declaration published as one constant",
                    });
                }
                publication.environment
            }
            Outcome::Complete(Published::Committed(DeclarationCommitted::DuplicateName {
                name,
            }))
            | Outcome::Complete(Published::DuplicateName { name }) => {
                return Err(EngineAdmissionError::DuplicateName { name });
            }
            Outcome::Complete(Published::BlockCommitted(publication)) => {
                if !expects_block {
                    return Err(EngineAdmissionError::UnexpectedPublication {
                        detail: "a non-block declaration published as a block",
                    });
                }
                publication.environment
            }
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };

        Ok(Outcome::Complete(UnrootedAdmission {
            engine: Admitted {
                environment,
                checker_environment: Some(checker_environment),
                imported_modules: std::sync::Arc::clone(&self.imported_modules),
                imported_environment: self.imported_environment.clone(),
                imported_module_dependencies: std::sync::Arc::clone(
                    &self.imported_module_dependencies,
                ),
                executable_opaques: std::sync::Arc::clone(&self.executable_opaques),
                runtime_initializers: std::sync::Arc::clone(&self.runtime_initializers),
                options: options.clone(),
            },
            declaration,
            checker,
        }))
    }

    /// The `.olean` check's batch: [`Self::admit_declarations`] without the root
    /// transitions it records for continuity checks, which the check never reads.
    /// A Mathlib module of a few hundred declarations spent most of its council
    /// time recomputing them, two whole-environment passes per declaration.
    pub fn admit_declarations_unrooted(
        &self,
        declarations: &[Declaration],
        options: &KVMap,
        limits: EngineAdmissionLimits,
        reading: ReadingCheck<'_>,
    ) -> Result<Outcome<(Admitted, Vec<CheckerAgreement>)>, EngineAdmissionError> {
        if declarations.is_empty() {
            return Err(EngineAdmissionError::EmptyBatch);
        }
        let mut checkers = Vec::new();
        checkers
            .try_reserve_exact(declarations.len())
            .map_err(|_| EngineAdmissionError::AllocationFailure {
                resource: "declaration batch results",
                requested: declarations.len(),
            })?;
        let mut engine = self.clone();
        for (index, declaration) in declarations.iter().cloned().enumerate() {
            let admitted =
                match engine.admit_declaration_unrooted(declaration, options, limits, reading) {
                    Ok(Outcome::Complete(admitted)) => admitted,
                    Ok(Outcome::Inconclusive(reason)) => return Ok(Outcome::Inconclusive(reason)),
                    Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
                    Err(error) => {
                        return Err(EngineAdmissionError::BatchDeclaration {
                            index,
                            error: Box::new(error),
                        });
                    }
                };
            engine = admitted.engine;
            checkers.push(admitted.checker);
        }
        Ok(Outcome::Complete((engine, checkers)))
    }
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom(_) => "axiom",
        Declaration::Defn(_) => "definition",
        Declaration::Thm(_) => "theorem",
        Declaration::Opaque(_) => "opaque",
        Declaration::Mutual(_) => "mutual block",
        Declaration::Inductive(_) => "inductive block",
        Declaration::Quotient(_) => "quotient initialization",
    }
}

#[derive(Debug)]
struct CheckerReview {
    council: Council,
    agreement: Option<CheckerAgreement>,
    successor_environment: Option<CheckerConstantEnvironment>,
}

impl CheckerReview {
    fn from_seat(
        verdict: SeatVerdict,
        agreement: Option<CheckerAgreement>,
        successor_environment: Option<CheckerConstantEnvironment>,
    ) -> Self {
        Self {
            council: Council::of(vec![Seat::new(
                "fln-checker",
                SeatOrigin::IndependentImplementation,
                SeatBounds::not_established(
                    "fln-checker uses an independent structural budget taxonomy",
                ),
                verdict,
            )]),
            agreement,
            successor_environment,
        }
    }

    fn no_answer(reason: String) -> Self {
        Self::from_seat(SeatVerdict::NoAnswer { reason }, None, None)
    }
}

pub fn decode_checker_name(
    name: &Name,
    budget: CheckerDecodeBudget,
) -> Result<CheckerName, String> {
    match checker_decode_name(&name.to_canonical_bytes(), budget) {
        CheckerDecodeOutcome::Complete(Ok(name)) => Ok(name),
        CheckerDecodeOutcome::Complete(Err(malformed)) => {
            Err(format!("canonical name decode failed: {malformed:?}"))
        }
        CheckerDecodeOutcome::Inconclusive(stop) => {
            Err(format!("canonical name decode did not finish: {stop:?}"))
        }
    }
}

/// Write `expression` in the checker's sharing-preserving transport
/// ([`fln_checker::wire::SCHEMA_EXPR_DAG`]): one record per distinct node
/// allocation, children before parents, so a term shared in memory crosses as
/// its DAG rather than its tree. `None` once the encoding would pass `limit`
/// bytes, without ever holding more than that.
fn encode_checker_expr_dag(expression: &Expr, limit: usize) -> Option<Vec<u8>> {
    use fln_checker::wire as tag;
    use fln_core::expr::ExprNode;

    fn children(node: &ExprNode) -> [Option<&Expr>; 3] {
        match node {
            ExprNode::App { f, a } => [Some(f), Some(a), None],
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => [Some(binder_type), Some(body), None],
            ExprNode::LetE {
                type_, value, body, ..
            } => [Some(type_), Some(value), Some(body)],
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => [Some(expr), None, None],
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => [None, None, None],
        }
    }
    // A node's identity is the address of its shared allocation, stable while
    // `expression` is borrowed; structurally equal but separately allocated
    // nodes stay separate records, which costs bytes and never meaning.
    let identity = |term: &Expr| std::ptr::from_ref(term.node()).addr();

    let mut index: std::collections::HashMap<usize, u32> = std::collections::HashMap::new();
    let mut order: Vec<&Expr> = Vec::new();
    let mut pending: Vec<(&Expr, bool)> = vec![(expression, false)];
    while let Some((term, children_done)) = pending.pop() {
        let id = identity(term);
        if index.contains_key(&id) {
            continue;
        }
        if children_done {
            index.insert(id, u32::try_from(order.len()).ok()?);
            order.push(term);
            continue;
        }
        pending.push((term, true));
        for child in children(term.node()).into_iter().rev().flatten() {
            if !index.contains_key(&identity(child)) {
                pending.push((child, false));
            }
        }
    }

    let reference = |term: &Expr| index[&identity(term)];
    let mut w = CanonWriter::with_limit(limit);
    w.schema(tag::SCHEMA_EXPR_DAG);
    w.u64(order.len() as u64);
    for term in order {
        if w.overflowed() {
            return None;
        }
        match term.node() {
            ExprNode::BVar { idx } => {
                w.u8(tag::EXPR_BVAR);
                w.u32(*idx);
            }
            ExprNode::FVar { id } => {
                w.u8(tag::EXPR_FVAR);
                id.0.write_body(&mut w);
            }
            ExprNode::MVar { id } => {
                w.u8(tag::EXPR_MVAR);
                id.0.write_body(&mut w);
            }
            ExprNode::Sort { level } => {
                w.u8(tag::EXPR_SORT);
                level.write_body(&mut w);
            }
            ExprNode::Const { name, levels } => {
                w.u8(tag::EXPR_CONST);
                name.write_body(&mut w);
                w.u64(levels.len() as u64);
                for level in levels {
                    level.write_body(&mut w);
                }
            }
            ExprNode::App { f, a } => {
                w.u8(tag::EXPR_APP);
                w.u32(reference(f));
                w.u32(reference(a));
            }
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            }
            | ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                w.u8(if matches!(term.node(), ExprNode::Lam { .. }) {
                    tag::EXPR_LAM
                } else {
                    tag::EXPR_FORALL
                });
                binder_name.write_body(&mut w);
                w.u32(reference(binder_type));
                w.u32(reference(body));
                // The upstream `BinderInfo.toUInt64` numbering, as in `SCHEMA_EXPR`.
                w.u8(binder_info.to_u64() as u8);
            }
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => {
                w.u8(tag::EXPR_LET);
                decl_name.write_body(&mut w);
                w.u32(reference(type_));
                w.u32(reference(value));
                w.u32(reference(body));
                w.bool(*non_dep);
            }
            ExprNode::Lit { literal } => match literal {
                Literal::Nat(n) => {
                    w.u8(tag::EXPR_LIT_NAT);
                    w.u64(n.limbs_le().len() as u64);
                    for limb in n.limbs_le() {
                        w.u64(*limb);
                    }
                }
                Literal::Str(s) => {
                    w.u8(tag::EXPR_LIT_STR);
                    w.str(s);
                }
            },
            ExprNode::MData { data, expr } => {
                w.u8(tag::EXPR_MDATA);
                data.write_body(&mut w);
                w.u32(reference(expr));
            }
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => {
                w.u8(tag::EXPR_PROJ);
                struct_name.write_body(&mut w);
                w.u64(*idx);
                w.u32(reference(expr));
            }
        }
    }
    (!w.overflowed()).then(|| w.into_bytes())
}

fn decode_checker_expr(
    expression: &Expr,
    budget: CheckerDecodeBudget,
) -> Result<CheckerExpr, String> {
    // Terms cross as their DAG: canonical tree bytes do not preserve sharing,
    // and one Init theorem's tree encoding is 727 MB over 7,419 distinct nodes.
    // The checker would refuse anything past its input budget, so never build
    // more encoding than it can read.
    let limit = usize::try_from(budget.max_input_bytes).unwrap_or(usize::MAX);
    let Some(bytes) = encode_checker_expr_dag(expression, limit) else {
        return Err(format!(
            "shared expression encoding exceeds the checker's {limit}-byte decode budget"
        ));
    };
    match checker_decode_expr_dag(&bytes, budget) {
        CheckerDecodeOutcome::Complete(Ok(expression)) => Ok(expression),
        CheckerDecodeOutcome::Complete(Err(malformed)) => {
            Err(format!("shared expression decode failed: {malformed:?}"))
        }
        CheckerDecodeOutcome::Inconclusive(stop) => {
            Err(format!("shared expression decode did not finish: {stop:?}"))
        }
    }
}

fn decode_checker_names(
    names: &[Name],
    budget: CheckerDecodeBudget,
) -> Result<Vec<CheckerName>, String> {
    let mut decoded = Vec::new();
    decoded
        .try_reserve_exact(names.len())
        .map_err(|_| format!("could not reserve {} checker names", names.len()))?;
    for name in names {
        decoded.push(decode_checker_name(name, budget)?);
    }
    Ok(decoded)
}

fn checker_constant_safety(is_unsafe: bool) -> CheckerConstantSafety {
    if is_unsafe {
        CheckerConstantSafety::Unsafe
    } else {
        CheckerConstantSafety::Safe
    }
}

fn checker_entry(
    info: &ConstantInfo,
    budget: CheckerDecodeBudget,
) -> Result<CheckerConstantEntry, String> {
    let base = info.constant_val();
    let name = decode_checker_name(&base.name, budget)?;
    let level_parameters = decode_checker_names(&base.level_params, budget)?;
    let type_ = decode_checker_expr(&base.type_, budget)?;
    let declaration = match info {
        ConstantInfo::Axiom(value) => CheckerConstantDeclaration::header(
            level_parameters,
            type_,
            CheckerConstantKind::Axiom,
            checker_constant_safety(value.is_unsafe),
        ),
        ConstantInfo::Defn(value) => {
            let hint = match value.hints {
                ReducibilityHints::Opaque => CheckerReducibilityHint::Opaque,
                ReducibilityHints::Abbrev => CheckerReducibilityHint::Abbrev,
                ReducibilityHints::Regular(height) => CheckerReducibilityHint::Regular(height),
            };
            let safety = match value.safety {
                DefinitionSafety::Unsafe => CheckerDefinitionSafety::Unsafe,
                DefinitionSafety::Safe => CheckerDefinitionSafety::Safe,
                DefinitionSafety::Partial => CheckerDefinitionSafety::Partial,
            };
            let body = CheckerDefinitionBody::new(
                decode_checker_expr(&value.value, budget)?,
                hint,
                safety,
                decode_checker_names(&value.all, budget)?,
            );
            CheckerConstantDeclaration::definition(
                level_parameters,
                type_,
                checker_constant_safety(matches!(value.safety, DefinitionSafety::Unsafe)),
                body,
            )
        }
        ConstantInfo::Thm(value) => CheckerConstantDeclaration::theorem(
            level_parameters,
            type_,
            decode_checker_expr(&value.value, budget)?,
            decode_checker_names(&value.all, budget)?,
        ),
        ConstantInfo::Opaque(value) => CheckerConstantDeclaration::opaque(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            decode_checker_expr(&value.value, budget)?,
            decode_checker_names(&value.all, budget)?,
        ),
        ConstantInfo::Quot(value) => {
            let kind = match value.kind {
                QuotKind::Type => CheckerQuotientKind::Type,
                QuotKind::Ctor => CheckerQuotientKind::Constructor,
                QuotKind::Lift => CheckerQuotientKind::Lift,
                QuotKind::Ind => CheckerQuotientKind::Induction,
            };
            CheckerConstantDeclaration::quotient(level_parameters, type_, kind)
        }
        ConstantInfo::Induct(value) => CheckerConstantDeclaration::inductive(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            CheckerInductiveDeclaration::new(
                value.num_params,
                value.num_indices,
                decode_checker_names(&value.all, budget)?,
                decode_checker_names(&value.ctors, budget)?,
                value.num_nested,
                value.is_rec,
                value.is_reflexive,
            ),
        ),
        ConstantInfo::Ctor(value) => CheckerConstantDeclaration::constructor(
            level_parameters,
            type_,
            checker_constant_safety(value.is_unsafe),
            CheckerConstructorDeclaration::new(
                decode_checker_name(&value.induct, budget)?,
                value.cidx,
                value.num_params,
                value.num_fields,
            ),
        ),
        ConstantInfo::Rec(value) => {
            let mut rules = Vec::new();
            rules.try_reserve_exact(value.rules.len()).map_err(|_| {
                format!(
                    "could not reserve {} checker recursor rules",
                    value.rules.len()
                )
            })?;
            for rule in &value.rules {
                rules.push(CheckerRecursorRule::new(
                    decode_checker_name(&rule.ctor, budget)?,
                    rule.nfields,
                    decode_checker_expr(&rule.rhs, budget)?,
                ));
            }
            CheckerConstantDeclaration::recursor(
                level_parameters,
                type_,
                checker_constant_safety(value.is_unsafe),
                CheckerRecursorDeclaration::new(
                    decode_checker_names(&value.all, budget)?,
                    value.num_params,
                    value.num_indices,
                    value.num_motives,
                    value.num_minors,
                    rules,
                    value.k,
                ),
            )
        }
    };
    Ok(CheckerConstantEntry::new(name, declaration))
}

/// Constants the independent checker resolves by spelling (literal typing and
/// the Nat, String and Bool reducers) rather than by a reference in the term,
/// so a projection covering a candidate carries them whenever they exist.
const CHECKER_BUILTIN_NAMES: &[&[&str]] = &[
    &["Nat"],
    &["Nat", "zero"],
    &["Nat", "succ"],
    &["Nat", "rec"],
    &["Bool"],
    &["Bool", "true"],
    &["Bool", "false"],
    &["Eq"],
    &["Eq", "refl"],
    &["String"],
    &["String", "ofList"],
    &["Char"],
    &["Char", "ofNat"],
    &["List"],
    &["List", "nil"],
    &["List", "cons"],
];

const QUOTIENT_FAMILY: &[&[&str]] = &[
    &["Quot"],
    &["Quot", "mk"],
    &["Quot", "lift"],
    &["Quot", "ind"],
];

fn collect_constant_names(
    root: &Expr,
    seen: &mut std::collections::HashSet<*const ExprNode>,
    out: &mut Vec<Name>,
) {
    let mut stack = vec![root];
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(expr.node())) {
            continue;
        }
        match expr.node() {
            ExprNode::Const { name, .. } => out.push(name.clone()),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                out.push(struct_name.clone());
                stack.push(expr);
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } => stack.push(expr),
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
}

/// Queue what the checker can reach through one projected base constant.
/// Theorem and opaque bodies are never unfolded by the checker, so they are
/// not followed (and [`checker_base_entry`] does not project them).
fn queue_base_dependencies(
    info: &ConstantInfo,
    seen: &mut std::collections::HashSet<*const ExprNode>,
    pending: &mut Vec<Name>,
) {
    collect_constant_names(&info.constant_val().type_, seen, pending);
    match info {
        ConstantInfo::Defn(value) => collect_constant_names(&value.value, seen, pending),
        ConstantInfo::Induct(value) => {
            pending.extend(value.all.iter().cloned());
            pending.extend(value.ctors.iter().cloned());
        }
        ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
        ConstantInfo::Rec(value) => {
            pending.extend(value.all.iter().cloned());
            for rule in &value.rules {
                pending.push(rule.ctor.clone());
                collect_constant_names(&rule.rhs, seen, pending);
            }
        }
        ConstantInfo::Quot(_) => pending.extend(
            QUOTIENT_FAMILY
                .iter()
                .map(|parts| Name::from_components(parts.iter().copied())),
        ),
        ConstantInfo::Axiom(_) | ConstantInfo::Thm(_) | ConstantInfo::Opaque(_) => {}
    }
}

/// A base constant as the checker sees it: theorem and opaque bodies are
/// dropped because the checker only delta-unfolds safe definitions, which keeps
/// proof terms whose tree encoding runs to hundreds of megabytes out of every
/// check that merely cites them.
fn checker_base_entry(
    info: &ConstantInfo,
    budget: CheckerDecodeBudget,
) -> Result<CheckerConstantEntry, String> {
    let (kind, safety) = match info {
        ConstantInfo::Thm(_) => (CheckerConstantKind::Theorem, CheckerConstantSafety::Safe),
        ConstantInfo::Opaque(value) => (
            CheckerConstantKind::Opaque,
            checker_constant_safety(value.is_unsafe),
        ),
        _ => return checker_entry(info, budget),
    };
    let base = info.constant_val();
    Ok(CheckerConstantEntry::new(
        decode_checker_name(&base.name, budget)?,
        CheckerConstantDeclaration::header(
            decode_checker_names(&base.level_params, budget)?,
            decode_checker_expr(&base.type_, budget)?,
            kind,
            safety,
        ),
    ))
}

/// The checker environment a candidate is reviewed against: `retained` (or an
/// empty projection) extended with every base constant the candidate's terms
/// can reach and that is not projected yet.
///
/// A constant this walk misses can only make the checker report an unknown
/// constant, which is a non-answer and never an admission. With no retained
/// projection the aggregate environment budget bounds the whole closure; with
/// one, the constants added here are counted against `max_constants` because
/// each `extend` bounds only its own entry.
fn checker_environment_covering(
    environment: &Environment,
    retained: Option<&CheckerConstantEnvironment>,
    roots: &[&Expr],
    limits: CheckerExecutionLimits,
) -> Result<CheckerConstantEnvironment, String> {
    let mut seen = std::collections::HashSet::new();
    let mut pending = Vec::new();
    for root in roots {
        collect_constant_names(root, &mut seen, &mut pending);
    }
    pending.extend(
        CHECKER_BUILTIN_NAMES
            .iter()
            .map(|parts| Name::from_components(parts.iter().copied())),
    );
    let mut visited = BTreeSet::new();
    let mut entries = Vec::new();
    while let Some(name) = pending.pop() {
        if !visited.insert(name.clone()) {
            continue;
        }
        let Some(info) = environment.find(&name) else {
            continue;
        };
        if let Some(retained) = retained
            && retained
                .find(&decode_checker_name(&name, limits.decode)?)
                .is_some()
        {
            continue;
        }
        entries.push(checker_base_entry(info, limits.decode)?);
        queue_base_dependencies(info, &mut seen, &mut pending);
    }
    let outcome = match retained {
        None => CheckerConstantEnvironment::build(entries, limits.environment),
        Some(retained) => {
            let added = u64::try_from(entries.len()).unwrap_or(u64::MAX);
            if added > limits.environment.max_constants {
                return Err(format!(
                    "covering {added} base constants exceeds the checker constant budget {}",
                    limits.environment.max_constants
                ));
            }
            let mut projected = retained.clone();
            for entry in entries {
                match projected.extend(entry, limits.environment) {
                    CheckerEnvironmentOutcome::Complete { environment, .. } => {
                        projected = environment;
                    }
                    other => return checker_projection_failure(other),
                }
            }
            return Ok(projected);
        }
    };
    match outcome {
        CheckerEnvironmentOutcome::Complete { environment, .. } => Ok(environment),
        other => checker_projection_failure(other),
    }
}

fn checker_projection_failure(
    outcome: CheckerEnvironmentOutcome,
) -> Result<CheckerConstantEnvironment, String> {
    Err(match outcome {
        CheckerEnvironmentOutcome::Complete { .. } => {
            "checker environment projection completed where a failure was reported".to_owned()
        }
        CheckerEnvironmentOutcome::Refused { refusal, .. } => {
            format!("checker environment refused its projection: {refusal:?}")
        }
        CheckerEnvironmentOutcome::Inconclusive(stop) => {
            format!("checker environment projection did not finish: {stop:?}")
        }
        CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
            format!("checker environment projection hit an internal fault: {fault:?}")
        }
    })
}

fn review_mutual_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    definitions: &[DefinitionVal],
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(definitions.len()).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {} checker mutual-block members",
            definitions.len()
        ));
    }
    for (index, definition) in definitions.iter().enumerate() {
        match checker_entry(&ConstantInfo::Defn(definition.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "mutual-block member {index} projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let roots: Vec<&Expr> = definitions
        .iter()
        .flat_map(|definition| [&definition.base.type_, &definition.value])
        .collect();
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit_block(&environment, &candidates, limits.admission) {
        CheckerBlockVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            let mut successor = environment;
            for candidate in candidates {
                let member = candidate.name().clone();
                match successor.extend(candidate, limits.environment) {
                    CheckerEnvironmentOutcome::Complete {
                        environment: extended,
                        ..
                    } => successor = extended,
                    CheckerEnvironmentOutcome::Refused { refusal, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker refused mutual member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain mutual member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker hit an internal fault while retaining mutual member \
                             {member:?}: {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerBlockVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the mutual block: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerBlockVerdict::MemberRejected { member, rejection } => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected mutual member {member:?}: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerBlockVerdict::MemberDeferred { member, deferred } => CheckerReview::no_answer(
            format!("fln-checker deferred mutual member {member:?}: {deferred:?}"),
        ),
        CheckerBlockVerdict::MemberInconclusive { member, stop } => CheckerReview::no_answer(
            format!("fln-checker exhausted or was cancelled on mutual member {member:?}: {stop:?}"),
        ),
        CheckerBlockVerdict::MemberFault { member, fault } => CheckerReview::no_answer(format!(
            "fln-checker hit an internal fault on mutual member {member:?}: {fault:?}"
        )),
    }
}

fn review_quotient_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    declarations: &[QuotVal],
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(declarations.len()).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {} checker quotient members",
            declarations.len()
        ));
    }
    for (index, declaration) in declarations.iter().enumerate() {
        match checker_entry(&ConstantInfo::Quot(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "quotient member {index} projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let roots: Vec<&Expr> = declarations
        .iter()
        .map(|declaration| &declaration.base.type_)
        .collect();
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit_quotient(&environment, &candidates, limits.admission) {
        CheckerQuotientVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            let mut successor = environment;
            for candidate in candidates {
                let member = candidate.name().clone();
                match successor.extend(candidate, limits.environment) {
                    CheckerEnvironmentOutcome::Complete {
                        environment: extended,
                        ..
                    } => successor = extended,
                    CheckerEnvironmentOutcome::Refused { refusal, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker refused quotient member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain quotient member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker faulted while retaining quotient member {member:?}: \
                             {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerQuotientVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected quotient initialization: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerQuotientVerdict::Inconclusive(stop) => CheckerReview::no_answer(format!(
            "fln-checker exhausted or was cancelled during quotient initialization: {stop:?}"
        )),
        CheckerQuotientVerdict::InternalFault(fault) => CheckerReview::no_answer(format!(
            "fln-checker faulted during quotient initialization: {fault:?}"
        )),
    }
}

fn review_inductive_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    block: &fln_kernel::InductiveBlock,
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    let member_count = block
        .types
        .len()
        .saturating_add(block.ctors.len())
        .saturating_add(block.recursors.len());
    let mut candidates = Vec::new();
    if candidates.try_reserve_exact(member_count).is_err() {
        return CheckerReview::no_answer(format!(
            "could not reserve {member_count} checker inductive-block members"
        ));
    }
    for declaration in &block.types {
        match checker_entry(&ConstantInfo::Induct(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "inductive type projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    for declaration in &block.ctors {
        match checker_entry(&ConstantInfo::Ctor(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "constructor projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    for declaration in &block.recursors {
        match checker_entry(&ConstantInfo::Rec(declaration.clone()), limits.decode) {
            Ok(candidate) => candidates.push(candidate),
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "recursor projection into fln-checker failed: {detail}"
                ));
            }
        }
    }
    if let Some(review) = reading_review(&candidates, reading) {
        return review;
    }

    let mut roots: Vec<&Expr> = block
        .types
        .iter()
        .map(|declaration| &declaration.base.type_)
        .chain(
            block
                .ctors
                .iter()
                .map(|declaration| &declaration.base.type_),
        )
        .collect();
    for recursor in &block.recursors {
        roots.push(&recursor.base.type_);
        roots.extend(recursor.rules.iter().map(|rule| &rule.rhs));
    }
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit_inductive(
        &environment,
        &candidates,
        limits.admission,
        limits.environment,
    ) {
        CheckerInductiveVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            let mut successor = environment;
            for candidate in candidates {
                let member = candidate.name().clone();
                match successor.extend(candidate, limits.environment) {
                    CheckerEnvironmentOutcome::Complete {
                        environment: extended,
                        ..
                    } => successor = extended,
                    CheckerEnvironmentOutcome::Refused { refusal, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker refused inductive member {member:?} retention: {refusal:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::Inconclusive(stop) => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker could not retain inductive member {member:?}: {stop:?}"
                        ));
                    }
                    CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                        return CheckerReview::no_answer(format!(
                            "fln-checker faulted while retaining inductive member {member:?}: \
                             {fault:?}"
                        ));
                    }
                }
            }
            CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
        }
        CheckerInductiveVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the inductive block: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerInductiveVerdict::Deferred(limit) => {
            let names = block
                .types
                .iter()
                .map(|inductive| inductive.base.name.to_display_string())
                .collect::<Vec<_>>()
                .join(", ");
            CheckerReview::no_answer(format!(
                "fln-checker does not yet decide this inductive shape of [{names}]: {limit:?}"
            ))
        }
        CheckerInductiveVerdict::Inconclusive(stop) => CheckerReview::no_answer(format!(
            "fln-checker exhausted or was cancelled during inductive admission: {stop:?}"
        )),
        CheckerInductiveVerdict::InternalFault(fault) => CheckerReview::no_answer(format!(
            "fln-checker faulted during inductive admission: {fault:?}"
        )),
    }
}

fn review_with_independent_checker(
    environment: &Environment,
    retained_environment: Option<&CheckerConstantEnvironment>,
    declaration: &Declaration,
    limits: CheckerExecutionLimits,
    reading: ReadingCheck<'_>,
) -> CheckerReview {
    if let Declaration::Mutual(definitions) = declaration {
        return review_mutual_with_independent_checker(
            environment,
            retained_environment,
            definitions,
            limits,
            reading,
        );
    }
    if let Declaration::Quotient(declarations) = declaration {
        return review_quotient_with_independent_checker(
            environment,
            retained_environment,
            declarations,
            limits,
            reading,
        );
    }
    if let Declaration::Inductive(block) = declaration {
        return review_inductive_with_independent_checker(
            environment,
            retained_environment,
            block,
            limits,
            reading,
        );
    }

    let candidate = match declaration {
        Declaration::Axiom(axiom) => {
            checker_entry(&ConstantInfo::Axiom(axiom.clone()), limits.decode)
        }
        Declaration::Defn(definition) => {
            checker_entry(&ConstantInfo::Defn(definition.clone()), limits.decode)
        }
        Declaration::Thm(theorem) => {
            checker_entry(&ConstantInfo::Thm(theorem.clone()), limits.decode)
        }
        Declaration::Opaque(opaque) => {
            checker_entry(&ConstantInfo::Opaque(opaque.clone()), limits.decode)
        }
        _ => {
            return CheckerReview::no_answer(
                "the facade asked the independent checker to review an unsupported declaration"
                    .to_owned(),
            );
        }
    };
    let candidate = match candidate {
        Ok(candidate) => candidate,
        Err(detail) => {
            return CheckerReview::no_answer(format!(
                "candidate projection into fln-checker failed: {detail}"
            ));
        }
    };
    if let Some(review) = reading_review(std::slice::from_ref(&candidate), reading) {
        return review;
    }
    let roots: Vec<&Expr> = match declaration {
        Declaration::Axiom(axiom) => vec![&axiom.base.type_],
        Declaration::Defn(definition) => vec![&definition.base.type_, &definition.value],
        Declaration::Thm(theorem) => vec![&theorem.base.type_, &theorem.value],
        Declaration::Opaque(opaque) => vec![&opaque.base.type_, &opaque.value],
        _ => Vec::new(),
    };
    let environment =
        match checker_environment_covering(environment, retained_environment, &roots, limits) {
            Ok(environment) => environment,
            Err(detail) => {
                return CheckerReview::no_answer(format!(
                    "base projection into fln-checker failed: {detail}"
                ));
            }
        };

    match fln_checker::admit::admit(&environment, &candidate, limits.admission) {
        CheckerVerdict::Admitted(admission) => {
            let agreement = CheckerAgreement {
                schema: admission.schema(),
                ground: admission.ground(),
            };
            match environment.extend(candidate, limits.environment) {
                CheckerEnvironmentOutcome::Complete {
                    environment: successor,
                    ..
                } => {
                    CheckerReview::from_seat(SeatVerdict::Agrees, Some(agreement), Some(successor))
                }
                CheckerEnvironmentOutcome::Refused { refusal, .. } => CheckerReview::no_answer(
                    format!("fln-checker refused candidate retention: {refusal:?}"),
                ),
                CheckerEnvironmentOutcome::Inconclusive(stop) => CheckerReview::no_answer(format!(
                    "fln-checker could not retain the candidate: {stop:?}"
                )),
                CheckerEnvironmentOutcome::InternalFault { fault, .. } => {
                    CheckerReview::no_answer(format!(
                        "fln-checker hit an internal fault while retaining the candidate: {fault:?}"
                    ))
                }
            }
        }
        CheckerVerdict::Rejected(rejection) => CheckerReview::from_seat(
            SeatVerdict::Disagrees {
                detail: format!("fln-checker rejected the declaration: {rejection:?}"),
            },
            None,
            None,
        ),
        CheckerVerdict::Deferred(requirement) => CheckerReview::no_answer(format!(
            "fln-checker deferred the declaration: {requirement:?}"
        )),
        CheckerVerdict::Inconclusive(stop) => {
            CheckerReview::no_answer(format!("fln-checker exhausted or was cancelled: {stop:?}"))
        }
        CheckerVerdict::InternalFault(fault) => {
            CheckerReview::no_answer(format!("fln-checker hit an internal fault: {fault:?}"))
        }
    }
}

/// Independent checker bounds for one facade execution.
///
/// These defaults are finite and deliberately separate from K1's calibrated
/// stack budget. Callers may tighten or expand them explicitly without making a
/// checker non-answer count as agreement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerExecutionLimits {
    pub decode: CheckerDecodeBudget,
    pub environment: CheckerEnvironmentBudget,
    pub admission: CheckerAdmissionBudget,
}

impl Default for CheckerExecutionLimits {
    fn default() -> Self {
        let term = fln_checker::term::TermBudget::new(100_000_000, 200_000_000)
            .with_max_arena_nodes(100_000_000);
        let whnf = fln_checker::whnf::WhnfBudget::new(100_000_000, 100_000_000, term);
        let inference =
            fln_checker::infer::InferenceBudget::new(100_000_000, 100_000_000, term, term)
                .with_whnf(whnf);
        // Every unit the decoder produces reads at least one input byte right
        // after it is charged, so the byte bound already bounds the units. A
        // unit bound below it would refuse inputs the byte bound admits: at
        // 1_000_000 it stopped five whole-Init frontier modules on proofs well
        // under 16 MiB.
        let decode_bytes = 16 * 1024 * 1024;
        Self {
            decode: CheckerDecodeBudget::new(decode_bytes, decode_bytes),
            environment: CheckerEnvironmentBudget::new(
                20_000_000,
                100_000,
                100_000,
                100_000,
                20_000_000,
                200_000_000,
            ),
            admission: CheckerAdmissionBudget::new(inference, whnf, inference.defeq),
        }
    }
}

/// Caller-supplied bounds for admission and immutable environment publication.
///
/// There is deliberately no `Default`: as with [`EngineExecutionLimits`], the
/// kernel budget must be calibrated to the native stack on which it runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EngineAdmissionLimits {
    pub kernel: Budget,
    pub checker: CheckerExecutionLimits,
    pub declaration: DeclarationBudget,
    pub collisions: CollisionBudget,
}

impl EngineAdmissionLimits {
    /// Use subsystem defaults around an explicitly calibrated kernel budget.
    pub fn new(kernel: Budget) -> Self {
        Self {
            kernel,
            checker: CheckerExecutionLimits::default(),
            declaration: DeclarationBudget::default(),
            collisions: CollisionBudget::default(),
        }
    }

    /// Calibrate admission limits to the specified thread stack size in bytes.
    pub fn for_stack_bytes(bytes: usize) -> Self {
        Self::new(Budget::for_stack_bytes(bytes))
    }
}

/// The independent checker's exact completed admission observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckerAgreement {
    pub schema: &'static str,
    pub ground: CheckerAdmissionGround,
}

/// The authoritative outputs of one completed admission-only transition.
#[derive(Debug)]
pub struct DeclarationAdmission<E = Admitted> {
    /// The immutable snapshot containing the newly published declaration.
    pub engine: E,
    /// The exact declaration admitted by K1 and independently reviewed.
    pub declaration: Declaration,
    /// The exact base-environment identity under the caller's options.
    pub base_logical_root: LogicalRoot,
    /// The exact successor-environment identity under the same options.
    pub result_logical_root: LogicalRoot,
    /// The independent checker observation that allowed the council to agree.
    pub checker: CheckerAgreement,
}

impl<E> DeclarationAdmission<E> {
    /// The same admission around another representation of its successor engine.
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> DeclarationAdmission<F> {
        DeclarationAdmission {
            engine: map(self.engine),
            declaration: self.declaration,
            base_logical_root: self.base_logical_root,
            result_logical_root: self.result_logical_root,
            checker: self.checker,
        }
    }
}

/// One admission without its root transition: what
/// `Engine::admit_declaration_unrooted` returns, and all the `.olean` check reads.
pub struct UnrootedAdmission<E = Admitted> {
    pub engine: E,
    pub declaration: Declaration,
    pub checker: CheckerAgreement,
}

impl<E> UnrootedAdmission<E> {
    /// The same admission around another representation of its successor engine.
    pub fn map_engine<F>(self, map: impl FnOnce(E) -> F) -> UnrootedAdmission<F> {
        UnrootedAdmission {
            engine: map(self.engine),
            declaration: self.declaration,
            checker: self.checker,
        }
    }
}

/// A completed refusal before an admission-only successor is exposed.
/// Non-answers live in [`Outcome`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EngineAdmissionError {
    EmptyBatch,
    AllocationFailure {
        resource: &'static str,
        requested: usize,
    },
    BatchDeclaration {
        index: usize,
        error: Box<EngineAdmissionError>,
    },
    UnsupportedDeclaration {
        kind: &'static str,
    },
    KernelRejected {
        class: RejectClass,
        message: String,
    },
    /// A council seat disagreed with the kernel's acceptance.
    CouncilHalted {
        summary: String,
    },
    /// Every objecting seat was silent or ran out: nothing was learned about the
    /// declaration (FL-INV-07), and it was not published.
    CouncilNoAnswer {
        summary: String,
    },
    CheckerBridge {
        detail: String,
    },
    DuplicateName {
        name: Name,
    },
    UnexpectedPublication {
        detail: &'static str,
    },
}

impl fmt::Display for EngineAdmissionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyBatch => write!(formatter, "declaration batch must not be empty"),
            Self::AllocationFailure {
                resource,
                requested,
            } => write!(
                formatter,
                "could not reserve {requested} entries for {resource}"
            ),
            Self::BatchDeclaration { index, error } => {
                write!(formatter, "declaration batch item {index} failed: {error}")
            }
            Self::UnsupportedDeclaration { kind } => write!(
                formatter,
                "cannot admit {kind}: the independent checker has no completed representation"
            ),
            Self::KernelRejected { class, message } => {
                write!(
                    formatter,
                    "kernel rejected declaration ({class:?}): {message}"
                )
            }
            Self::CouncilHalted { summary } => write!(formatter, "council halted: {summary}"),
            Self::CouncilNoAnswer { summary } => {
                write!(formatter, "council had no answer: {summary}")
            }
            Self::CheckerBridge { detail } => {
                write!(formatter, "independent checker bridge failed: {detail}")
            }
            Self::DuplicateName { name } => write!(
                formatter,
                "environment already contains {}",
                name.to_display_string()
            ),
            Self::UnexpectedPublication { detail } => {
                write!(formatter, "unexpected publication result: {detail}")
            }
        }
    }
}

impl std::error::Error for EngineAdmissionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::BatchDeclaration { error, .. } => Some(error.as_ref()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Expr, Name, OleanCheckError, OleanDeclarationError, OleanDecodeError};
    use fln_core::level::Level;

    #[test]
    fn the_default_checker_decode_budget_binds_on_bytes_not_units() {
        let default = super::CheckerExecutionLimits::default().decode;
        assert!(
            default.max_produced_units >= default.max_input_bytes,
            "each produced unit reads at least one byte, so a unit bound below \
             the byte bound refuses inputs the byte bound admits"
        );
        // A left-nested application spine with a fresh leaf per argument: every
        // node is its own allocation, so the shared transport carries all
        // 1,200,001 of them as records (an application is 9 bytes, a bound
        // variable 5), past the old 1_000_000-unit bound and under the byte
        // bound.
        let mut spine = Expr::bvar(0).expect("small index");
        for index in 0..600_000u32 {
            spine = Expr::app(spine, Expr::bvar(index % 1000).expect("small index"));
        }
        let bytes = super::encode_checker_expr_dag(&spine, usize::MAX)
            .expect("unbounded")
            .len() as u64;
        assert!(
            bytes > 1_200_001 && bytes < default.max_input_bytes,
            "{bytes}"
        );
        super::decode_checker_expr(&spine, default)
            .expect("an expression within the byte bound decodes under the default budget");
        // The control: the old unit bound refuses this same input on units.
        let refusal = super::decode_checker_expr(
            &spine,
            super::CheckerDecodeBudget::new(default.max_input_bytes, 1_000_000),
        )
        .expect_err("the old unit bound stops before the spine is decoded");
        assert!(refusal.contains("ProducedUnits"), "{refusal}");
    }

    #[test]
    fn terms_cross_to_the_checker_as_their_dag() {
        use fln_hash::canon::Canonical;
        // A balanced application tree of depth 40 over `Sort 0`, shared in
        // memory: 2^41 - 1 tree nodes over 41 distinct ones. Its tree encoding
        // could never be built; its shared encoding is 41 records.
        let mut tree = Expr::sort(Level::zero());
        for _ in 0..40 {
            tree = Expr::app(tree.clone(), tree);
        }
        assert!(tree.to_canonical_bytes_within(1 << 20).is_none());
        let decoded =
            super::decode_checker_expr(&tree, super::CheckerExecutionLimits::default().decode)
                .expect("the shared encoding fits");
        assert_eq!(decoded.nodes().len(), 41);
    }

    /// A construct this implementation cannot judge yet is a typed `Unsupported`
    /// non-answer naming the construct, never `failed` (FL-INV-07): the decoder's
    /// `Name.num` that needs an `mpz`, and the planner's four `*Unsupported` refusals.
    /// None occurs in the stdlib receipt or S20's 5,712 rows, so each is planted. A
    /// genuinely malformed declaration payload stays `failed`.
    #[test]
    fn frontier_rows_type_unsupported_constructs_as_inconclusive_naming_them() {
        use fln_core::outcome::{Inconclusive, InconclusiveCause};

        let module = Name::from_components(["Planted"]);
        let name = |text: &str| Name::from_components(text.split('.'));
        let mpz = || OleanDeclarationError::Unsupported {
            offset: 4096,
            what: "Name.num mpz",
        };
        let cases = [
            (
                OleanCheckError::Decode(OleanDecodeError::Declaration(mpz())),
                "Name.num mpz",
            ),
            (
                OleanCheckError::ModuleDecode {
                    module: module.clone(),
                    error: OleanDecodeError::CompanionDeclaration {
                        part: super::OleanCompanionPart::Private,
                        error: mpz(),
                    },
                },
                "Name.num mpz",
            ),
            (
                OleanCheckError::UnsupportedDeclaration {
                    name: name("Planted.Quot"),
                    kind: "quotient",
                },
                "Planted.Quot",
            ),
            (
                OleanCheckError::MutualEnvelopeUnsupported {
                    name: name("Planted.left"),
                    members: vec![name("Planted.left"), name("Planted.right")],
                },
                "mutual declaration envelope for `Planted.left`",
            ),
            (
                OleanCheckError::InductiveEnvelopeUnsupported {
                    name: name("Planted.T"),
                    members: vec![name("Planted.T.mk")],
                },
                "inductive declaration envelope for `Planted.T`",
            ),
            (
                OleanCheckError::QuotientEnvelopeUnsupported {
                    names: vec![name("Quot"), name("Quot.mk")],
                },
                "quotient initialization envelope",
            ),
        ];
        for (error, construct) in cases {
            let verdict = super::frontier_error_verdict(error);
            match &verdict {
                super::OleanModuleVerdict::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::Unsupported { construct: named },
                    ..
                }) => assert!(
                    named.text().contains(construct),
                    "the row names the construct `{construct}`: {named:?}"
                ),
                other => panic!("an unsupported construct is a typed non-answer, got {other:?}"),
            }
        }
        let malformed = super::frontier_error_verdict(OleanCheckError::Decode(
            OleanDecodeError::Declaration(OleanDeclarationError::Shape {
                offset: 64,
                what: "planted shape",
            }),
        ));
        assert!(
            matches!(malformed, super::OleanModuleVerdict::Failed(_)),
            "malformed input stays failed, got {malformed:?}"
        );
    }
}
