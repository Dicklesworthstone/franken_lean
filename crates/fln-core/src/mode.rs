//! The product-mode and reproducibility contract (plan §4.2, D17, D18).
//!
//! This module owns values and pure admission rules only. It deliberately has no
//! filesystem reader, byte codec, evidence-ledger reader, or structural source
//! scanner: `fln-core` is the dependency root, while canonical encoding belongs in
//! `fln-hash` and release-wide leak scanning belongs in `fln-conformance` and
//! `tools/structure-guard`.
//!
//! Four axes remain distinct:
//!
//! * [`Mode`] is semantic input: faithful, sound, or frontier.
//! * [`DeterminismClass`] says how an operation becomes repeatable.
//! * [`ReproducibilityProfile`] requests standard or independently certified output.
//! * [`EvidenceLevel`] and [`ReleaseLevel`] describe evidence and never self-certify.
//!
//! Missing or unknown provenance has no default. [`Mode::DEFAULT`] names the explicit
//! CLI default, but `Mode` intentionally does not implement `Default`, and
//! [`Mode::from_tag`] refuses `None`.
//!
//! ```compile_fail
//! use fln_core::mode::Mode;
//! let silently_defaulted: Mode = Default::default();
//! ```
//!
//! ## D18 is also a compiler boundary
//!
//! Frontier-only APIs take a [`FrontierCapability`]. That capability is issued only
//! by [`ModeToken<FrontierMode>`], and mode-bound artifacts carry a sealed marker.
//! A runtime scanner remains valuable defense in depth, but ordinary Rust code cannot
//! pass a frontier artifact to a sound-only consumer:
//!
//! ```compile_fail
//! use fln_core::mode::{
//!     ArtifactCoordinates, ContentRoot, CgsePolicyId, DeterminismClass, EpochId,
//!     FrontierFeature, FrontierMode, ModeArtifact, ModeToken, ReproducibilityProfile,
//!     SoundMode, TargetId, BuildProfileId,
//! };
//!
//! fn coordinates() -> ArtifactCoordinates {
//!     ArtifactCoordinates {
//!         epoch: EpochId::new(1),
//!         cgse_policy: CgsePolicyId::new(1),
//!         determinism: DeterminismClass::D1Canonicalized,
//!         reproducibility: ReproducibilityProfile::Standard,
//!         target: TargetId::new(1),
//!         build_profile: BuildProfileId::new(1),
//!         closure_root: ContentRoot::new([1; 32]),
//!         product_root: ContentRoot::new([2; 32]),
//!         claim_row: None,
//!     }
//! }
//!
//! let frontier = ModeToken::<FrontierMode>::frontier();
//! let artifact = frontier.frontier_artifact(
//!     FrontierFeature::OleanNext,
//!     coordinates(),
//!     (),
//! );
//! fn admit_sound(_: ModeArtifact<SoundMode, ()>) {}
//! admit_sound(artifact.into_mode_artifact());
//! ```

use std::marker::PhantomData;

pub const MODE_SCHEMA: &str = "fln.mode/1";
pub const MODE_SCHEMA_VERSION: u16 = 1;

/// Which closed axis a failed boundary tag belonged to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Axis {
    Mode,
    Determinism,
    Reproducibility,
    Evidence,
    Release,
}

/// Typed refusal for an absent or unknown closed-axis tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AxisDecodeError {
    Missing { axis: Axis },
    Unknown { axis: Axis, tag: u8 },
}

/// The three semantic modes. One theory and one kernel exist in every variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Mode {
    Faithful = 1,
    Sound = 2,
    Frontier = 3,
}

impl Mode {
    /// Explicit product default. This is not a deserialization fallback.
    pub const DEFAULT: Mode = Mode::Sound;

    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn from_tag(tag: Option<u8>) -> Result<Mode, AxisDecodeError> {
        match tag {
            Some(1) => Ok(Mode::Faithful),
            Some(2) => Ok(Mode::Sound),
            Some(3) => Ok(Mode::Frontier),
            Some(tag) => Err(AxisDecodeError::Unknown {
                axis: Axis::Mode,
                tag,
            }),
            None => Err(AxisDecodeError::Missing { axis: Axis::Mode }),
        }
    }

    pub const fn permits_frontier(self) -> bool {
        matches!(self, Mode::Frontier)
    }
}

/// D0-D4 from doctrine D7. Ordering is from strongest control to weakest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum DeterminismClass {
    D0Mathematical = 0,
    D1Canonicalized = 1,
    D2Replayable = 2,
    D3Advisory = 3,
    D4External = 4,
}

impl DeterminismClass {
    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn from_tag(tag: Option<u8>) -> Result<DeterminismClass, AxisDecodeError> {
        match tag {
            Some(0) => Ok(DeterminismClass::D0Mathematical),
            Some(1) => Ok(DeterminismClass::D1Canonicalized),
            Some(2) => Ok(DeterminismClass::D2Replayable),
            Some(3) => Ok(DeterminismClass::D3Advisory),
            Some(4) => Ok(DeterminismClass::D4External),
            Some(tag) => Err(AxisDecodeError::Unknown {
                axis: Axis::Determinism,
                tag,
            }),
            None => Err(AxisDecodeError::Missing {
                axis: Axis::Determinism,
            }),
        }
    }
}

/// Orthogonal standard/certified axis. `Certified` corresponds to
/// `--reproducible`; it is eligibility proven by [`recompute_certified_eligibility`],
/// not a trusted bit in an artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ReproducibilityProfile {
    Standard = 1,
    Certified = 2,
}

impl ReproducibilityProfile {
    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn from_tag(tag: Option<u8>) -> Result<ReproducibilityProfile, AxisDecodeError> {
        match tag {
            Some(1) => Ok(ReproducibilityProfile::Standard),
            Some(2) => Ok(ReproducibilityProfile::Certified),
            Some(tag) => Err(AxisDecodeError::Unknown {
                axis: Axis::Reproducibility,
                tag,
            }),
            None => Err(AxisDecodeError::Missing {
                axis: Axis::Reproducibility,
            }),
        }
    }
}

/// Per-surface compatibility evidence. This never changes semantic identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum EvidenceLevel {
    L0Recognized = 0,
    L1ShapeCompatible = 1,
    L2Behavioral = 2,
    L3DifferentiallyClosed = 3,
    L4DropInAttested = 4,
}

impl EvidenceLevel {
    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn from_tag(tag: Option<u8>) -> Result<EvidenceLevel, AxisDecodeError> {
        match tag {
            Some(0) => Ok(EvidenceLevel::L0Recognized),
            Some(1) => Ok(EvidenceLevel::L1ShapeCompatible),
            Some(2) => Ok(EvidenceLevel::L2Behavioral),
            Some(3) => Ok(EvidenceLevel::L3DifferentiallyClosed),
            Some(4) => Ok(EvidenceLevel::L4DropInAttested),
            Some(tag) => Err(AxisDecodeError::Unknown {
                axis: Axis::Evidence,
                tag,
            }),
            None => Err(AxisDecodeError::Missing {
                axis: Axis::Evidence,
            }),
        }
    }
}

/// Per-release evidence level. Also descriptive, never semantic authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ReleaseLevel {
    R0Research = 0,
    R1CheckerPreview = 1,
    R2ProjectLocalToolchain = 2,
    R3EcosystemCandidate = 3,
    R4DropInEpochReplacement = 4,
    R5HardenedReplacement = 5,
}

impl ReleaseLevel {
    pub const fn tag(self) -> u8 {
        self as u8
    }

    pub const fn from_tag(tag: Option<u8>) -> Result<ReleaseLevel, AxisDecodeError> {
        match tag {
            Some(0) => Ok(ReleaseLevel::R0Research),
            Some(1) => Ok(ReleaseLevel::R1CheckerPreview),
            Some(2) => Ok(ReleaseLevel::R2ProjectLocalToolchain),
            Some(3) => Ok(ReleaseLevel::R3EcosystemCandidate),
            Some(4) => Ok(ReleaseLevel::R4DropInEpochReplacement),
            Some(5) => Ok(ReleaseLevel::R5HardenedReplacement),
            Some(tag) => Err(AxisDecodeError::Unknown {
                axis: Axis::Release,
                tag,
            }),
            None => Err(AxisDecodeError::Missing {
                axis: Axis::Release,
            }),
        }
    }
}

macro_rules! registry_id {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(u128);

        impl $name {
            pub const fn new(value: u128) -> Self {
                Self(value)
            }

            pub const fn get(self) -> u128 {
                self.0
            }
        }
    };
}

registry_id! {
    /// Registry identity of the pinned Reference epoch.
    EpochId
}
registry_id! {
    /// Registry identity of the CGSE policy set used by a producer.
    CgsePolicyId
}
registry_id! {
    /// Registry identity of the certified target contract.
    TargetId
}
registry_id! {
    /// Registry identity of the compiler/build profile and feature contract.
    BuildProfileId
}
registry_id! {
    /// Stable identity of an optional claim-matrix row.
    ClaimRowId
}
registry_id! {
    /// Stable identity of a Behavior Note.
    BehaviorNoteId
}
registry_id! {
    /// Registry identity of a mode-neutral schema.
    NeutralSchemaId
}

/// Content identity produced by `fln-hash`. Core carries it without choosing or
/// implementing a hash algorithm.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ContentRoot([u8; 32]);

impl ContentRoot {
    pub const fn new(bytes: [u8; 32]) -> ContentRoot {
        ContentRoot(bytes)
    }

    pub const fn bytes(self) -> [u8; 32] {
        self.0
    }
}

/// Semantic coordinates every artifact/cache key carries. Evidence is deliberately
/// absent; a stronger ledger row must not change the artifact being discussed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArtifactCoordinates {
    pub epoch: EpochId,
    pub cgse_policy: CgsePolicyId,
    pub determinism: DeterminismClass,
    pub reproducibility: ReproducibilityProfile,
    pub target: TargetId,
    pub build_profile: BuildProfileId,
    pub closure_root: ContentRoot,
    pub product_root: ContentRoot,
    pub claim_row: Option<ClaimRowId>,
}

/// Scope bound into artifact identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ArtifactScope {
    ModeBound(Mode),
    RegisteredNeutral(NeutralSchemaId),
}

/// Complete semantic identity used by artifacts, receipts, and cache keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArtifactIdentity {
    scope: ArtifactScope,
    coordinates: ArtifactCoordinates,
}

impl ArtifactIdentity {
    pub const fn scope(self) -> ArtifactScope {
        self.scope
    }

    pub const fn coordinates(self) -> ArtifactCoordinates {
        self.coordinates
    }
}

mod sealed {
    pub trait Sealed {}
}

/// Sealed marker implemented only by the three mode types in this module.
pub trait ModeMarker: sealed::Sealed + Copy + std::fmt::Debug + Eq + 'static {
    const MODE: Mode;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaithfulMode {}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SoundMode {}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrontierMode {}

impl sealed::Sealed for FaithfulMode {}
impl sealed::Sealed for SoundMode {}
impl sealed::Sealed for FrontierMode {}

impl ModeMarker for FaithfulMode {
    const MODE: Mode = Mode::Faithful;
}

impl ModeMarker for SoundMode {
    const MODE: Mode = Mode::Sound;
}

impl ModeMarker for FrontierMode {
    const MODE: Mode = Mode::Frontier;
}

/// Zero-sized authority for one statically known mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModeToken<M: ModeMarker> {
    marker: PhantomData<M>,
}

impl ModeToken<FaithfulMode> {
    pub const fn faithful() -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

impl ModeToken<SoundMode> {
    pub const fn sound() -> Self {
        Self {
            marker: PhantomData,
        }
    }
}

impl ModeToken<FrontierMode> {
    pub const fn frontier() -> Self {
        Self {
            marker: PhantomData,
        }
    }

    pub const fn frontier_capability(&self) -> FrontierCapability<'_> {
        FrontierCapability { token: self }
    }

    pub fn frontier_artifact<T>(
        &self,
        feature: FrontierFeature,
        coordinates: ArtifactCoordinates,
        payload: T,
    ) -> FrontierArtifact<T> {
        FrontierArtifact {
            feature,
            artifact: ModeArtifact::new(self, coordinates, payload),
        }
    }
}

impl<M: ModeMarker> ModeToken<M> {
    pub const fn mode(&self) -> Mode {
        M::MODE
    }
}

/// Capability required by frontier-only APIs. Its field is private and its lifetime
/// ties it to a genuine frontier token.
#[derive(Debug, Clone, Copy)]
pub struct FrontierCapability<'a> {
    token: &'a ModeToken<FrontierMode>,
}

impl FrontierCapability<'_> {
    pub const fn mode(self) -> Mode {
        self.token.mode()
    }
}

/// A mode-bound artifact. The marker is invariant at the type boundary; there is no
/// cross-mode `From` implementation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModeArtifact<M: ModeMarker, T> {
    identity: ArtifactIdentity,
    payload: T,
    marker: PhantomData<M>,
}

impl<M: ModeMarker, T> ModeArtifact<M, T> {
    pub fn new(
        _token: &ModeToken<M>,
        coordinates: ArtifactCoordinates,
        payload: T,
    ) -> ModeArtifact<M, T> {
        ModeArtifact {
            identity: ArtifactIdentity {
                scope: ArtifactScope::ModeBound(M::MODE),
                coordinates,
            },
            payload,
            marker: PhantomData,
        }
    }

    pub const fn identity(&self) -> ArtifactIdentity {
        self.identity
    }

    pub const fn payload(&self) -> &T {
        &self.payload
    }

    pub fn into_payload(self) -> T {
        self.payload
    }
}

/// Frontier products named by D18.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FrontierFeature {
    OleanNext,
    EGraphPortfolio,
    IronJit,
    McpWriteTools,
    EpochBridge,
}

/// Artifact whose construction requires the statically frontier token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrontierArtifact<T> {
    feature: FrontierFeature,
    artifact: ModeArtifact<FrontierMode, T>,
}

impl<T> FrontierArtifact<T> {
    pub const fn feature(&self) -> FrontierFeature {
        self.feature
    }

    pub const fn artifact(&self) -> &ModeArtifact<FrontierMode, T> {
        &self.artifact
    }

    pub fn into_mode_artifact(self) -> ModeArtifact<FrontierMode, T> {
        self.artifact
    }
}

/// Untrusted product classification at a mode boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductObservation {
    ReferenceParity,
    SoundDivergence {
        behavior_note: Option<BehaviorNoteId>,
    },
    FrontierFeature(FrontierFeature),
}

/// Product class after the pure mode rule validates it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValidatedProductClass {
    ReferenceParity,
    SoundDivergence { behavior_note: BehaviorNoteId },
    FrontierFeature(FrontierFeature),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProductRefusal {
    MissingBehaviorNote,
    SoundDivergenceInFaithful,
    FrontierLeak { consumer: Mode },
}

/// Validate a producer's product class against its declared mode.
pub const fn validate_mode_product(
    mode: Mode,
    observation: ProductObservation,
) -> Result<ValidatedProductClass, ProductRefusal> {
    match observation {
        ProductObservation::ReferenceParity => Ok(ValidatedProductClass::ReferenceParity),
        ProductObservation::SoundDivergence { behavior_note } => {
            let Some(behavior_note) = behavior_note else {
                return Err(ProductRefusal::MissingBehaviorNote);
            };
            if matches!(mode, Mode::Faithful) {
                Err(ProductRefusal::SoundDivergenceInFaithful)
            } else {
                Ok(ValidatedProductClass::SoundDivergence { behavior_note })
            }
        }
        ProductObservation::FrontierFeature(feature) => {
            if mode.permits_frontier() {
                Ok(ValidatedProductClass::FrontierFeature(feature))
            } else {
                Err(ProductRefusal::FrontierLeak { consumer: mode })
            }
        }
    }
}

/// Authoritative registry row for a schema whose semantics are mode-neutral.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NeutralSchemaRegistration {
    pub schema: NeutralSchemaId,
    pub semantic_root: ContentRoot,
}

/// A mode-neutral artifact still needs a registered schema and exact semantic root
/// before any mode may share it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NeutralArtifact<T> {
    identity: ArtifactIdentity,
    payload: T,
}

impl<T> NeutralArtifact<T> {
    pub fn new(
        schema: NeutralSchemaId,
        semantic_root: ContentRoot,
        mut coordinates: ArtifactCoordinates,
        payload: T,
    ) -> NeutralArtifact<T> {
        coordinates.product_root = semantic_root;
        NeutralArtifact {
            identity: ArtifactIdentity {
                scope: ArtifactScope::RegisteredNeutral(schema),
                coordinates,
            },
            payload,
        }
    }

    pub const fn identity(&self) -> ArtifactIdentity {
        self.identity
    }

    pub fn share_with<'a, M: ModeMarker>(
        &'a self,
        _consumer: &ModeToken<M>,
        expected_semantic_root: ContentRoot,
        registry: &[NeutralSchemaRegistration],
    ) -> Result<&'a T, CompatibilityRefusal> {
        let ArtifactScope::RegisteredNeutral(schema) = self.identity.scope else {
            return Err(CompatibilityRefusal::MissingProducerMode);
        };
        validate_neutral(
            schema,
            self.identity.coordinates.product_root,
            expected_semantic_root,
            registry,
        )?;
        Ok(&self.payload)
    }
}

/// Scope read from untrusted artifact provenance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObservedArtifactScope {
    Missing,
    ModeBound {
        tag: u8,
        semantic_root: ContentRoot,
    },
    Neutral {
        schema: NeutralSchemaId,
        semantic_root: ContentRoot,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompatibilityDecision {
    ExactMode,
    RegisteredNeutral,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompatibilityRefusal {
    MissingProducerMode,
    UnknownProducerMode { tag: u8 },
    MixedMode { producer: Mode, consumer: Mode },
    FrontierLeak { consumer: Mode },
    UnregisteredNeutralSchema { schema: NeutralSchemaId },
    DuplicateNeutralRegistration { schema: NeutralSchemaId },
    NeutralRegistryRootMismatch { schema: NeutralSchemaId },
    NeutralSemanticRootMismatch { schema: NeutralSchemaId },
    ModeSemanticRootMismatch { mode: Mode },
}

/// Pure cache/artifact compatibility rule. Mixed-mode reuse is rejected; the sole
/// exception is an explicitly registered neutral schema with identical roots.
pub fn artifact_compatibility(
    consumer: Mode,
    producer: ObservedArtifactScope,
    expected_semantic_root: ContentRoot,
    neutral_registry: &[NeutralSchemaRegistration],
) -> Result<CompatibilityDecision, CompatibilityRefusal> {
    match producer {
        ObservedArtifactScope::Missing => Err(CompatibilityRefusal::MissingProducerMode),
        ObservedArtifactScope::ModeBound { tag, semantic_root } => {
            let producer = Mode::from_tag(Some(tag)).map_err(|error| match error {
                AxisDecodeError::Unknown { tag, .. } => {
                    CompatibilityRefusal::UnknownProducerMode { tag }
                }
                AxisDecodeError::Missing { .. } => CompatibilityRefusal::MissingProducerMode,
            })?;
            if producer == Mode::Frontier && consumer != Mode::Frontier {
                return Err(CompatibilityRefusal::FrontierLeak { consumer });
            }
            if producer != consumer {
                return Err(CompatibilityRefusal::MixedMode { producer, consumer });
            }
            if semantic_root != expected_semantic_root {
                return Err(CompatibilityRefusal::ModeSemanticRootMismatch { mode: producer });
            }
            Ok(CompatibilityDecision::ExactMode)
        }
        ObservedArtifactScope::Neutral {
            schema,
            semantic_root,
        } => {
            validate_neutral(
                schema,
                semantic_root,
                expected_semantic_root,
                neutral_registry,
            )?;
            Ok(CompatibilityDecision::RegisteredNeutral)
        }
    }
}

fn validate_neutral(
    schema: NeutralSchemaId,
    artifact_root: ContentRoot,
    expected_root: ContentRoot,
    registry: &[NeutralSchemaRegistration],
) -> Result<(), CompatibilityRefusal> {
    let mut matching = registry.iter().filter(|row| row.schema == schema);
    let Some(row) = matching.next() else {
        return Err(CompatibilityRefusal::UnregisteredNeutralSchema { schema });
    };
    if matching.next().is_some() {
        return Err(CompatibilityRefusal::DuplicateNeutralRegistration { schema });
    }
    if row.semantic_root != artifact_root {
        return Err(CompatibilityRefusal::NeutralRegistryRootMismatch { schema });
    }
    if artifact_root != expected_root {
        return Err(CompatibilityRefusal::NeutralSemanticRootMismatch { schema });
    }
    Ok(())
}

/// Evidence attached to a receipt. It is deliberately outside [`ArtifactIdentity`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EvidenceBinding {
    pub surface: EvidenceLevel,
    pub release: ReleaseLevel,
    pub ledger_snapshot: ContentRoot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactReceipt {
    pub artifact: ArtifactIdentity,
    pub evidence: EvidenceBinding,
}

/// Every semantic root required by the certified closure contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum ClosureComponent {
    Sources = 0,
    Toolchain = 1,
    SuiteLock = 2,
    Options = 3,
    Plugins = 4,
    Mode = 5,
    Epoch = 6,
    Target = 7,
    BuildProfile = 8,
    Features = 9,
    PolicyEpochs = 10,
    SemanticInputs = 11,
    ReplayInputs = 12,
}

impl ClosureComponent {
    pub const ALL: [ClosureComponent; 13] = [
        ClosureComponent::Sources,
        ClosureComponent::Toolchain,
        ClosureComponent::SuiteLock,
        ClosureComponent::Options,
        ClosureComponent::Plugins,
        ClosureComponent::Mode,
        ClosureComponent::Epoch,
        ClosureComponent::Target,
        ClosureComponent::BuildProfile,
        ClosureComponent::Features,
        ClosureComponent::PolicyEpochs,
        ClosureComponent::SemanticInputs,
        ClosureComponent::ReplayInputs,
    ];

    const fn index(self) -> usize {
        self as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClosureEntry {
    pub component: ClosureComponent,
    pub root: ContentRoot,
}

/// Products of doctrine D2's two optional external tools. Either is structurally
/// excluded from certified output.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalToolProduct {
    SystemCCompiler,
    SystemGit,
}

/// Whether an operation completed far enough for atomic publication.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionState {
    Complete,
    Cancelled,
    ResourceExhausted,
    InternalFault,
}

/// One operation that may influence the artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OperationFact {
    pub class: DeterminismClass,
    pub affects_semantics: bool,
    /// D2 semantic operations must bind the exact aggregate replay-input root.
    pub replay_binding: Option<ContentRoot>,
}

/// Untrusted request to claim certified eligibility. `recomputed_root` must come from
/// the authoritative closure walker, independently of `claimed_root`.
#[derive(Debug, Clone, Copy)]
pub struct CertificationRequest<'a> {
    pub requested_profile: ReproducibilityProfile,
    pub completion: CompletionState,
    pub entries: &'a [ClosureEntry],
    pub claimed_root: ContentRoot,
    pub recomputed_root: ContentRoot,
    pub external_products: &'a [ExternalToolProduct],
    pub operations: &'a [OperationFact],
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CertificationRefusal {
    CertifiedProfileNotRequested,
    IncompletePublication { state: CompletionState },
    ExternalToolProduct { tool: ExternalToolProduct },
    MissingClosureComponent { component: ClosureComponent },
    DuplicateClosureComponent { component: ClosureComponent },
    ClosureRootMismatch,
    MissingReplayBinding,
    ReplayBindingMismatch,
    UnadmittedSemanticOperation { class: DeterminismClass },
    ArtifactProfileMismatch,
    ArtifactClosureMismatch,
    ArtifactDeterminismMismatch,
}

/// Complete roots after structural validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClosureRoots {
    roots: [ContentRoot; 13],
}

impl ClosureRoots {
    pub const fn root(self, component: ClosureComponent) -> ContentRoot {
        self.roots[component.index()]
    }
}

/// Non-forgeable-in-safe-API eligibility: fields are private and the only constructor
/// is [`recompute_certified_eligibility`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CertifiedEligibility {
    closure: ClosureRoots,
    aggregate_root: ContentRoot,
    determinism: DeterminismClass,
}

impl CertifiedEligibility {
    pub const fn closure(self) -> ClosureRoots {
        self.closure
    }

    pub const fn aggregate_root(self) -> ContentRoot {
        self.aggregate_root
    }

    pub const fn determinism(self) -> DeterminismClass {
        self.determinism
    }
}

/// Independently recompute whether a candidate is eligible for certified output.
/// A marker in the candidate is never authority.
pub fn recompute_certified_eligibility(
    request: CertificationRequest<'_>,
) -> Result<CertifiedEligibility, CertificationRefusal> {
    if request.requested_profile != ReproducibilityProfile::Certified {
        return Err(CertificationRefusal::CertifiedProfileNotRequested);
    }
    if request.completion != CompletionState::Complete {
        return Err(CertificationRefusal::IncompletePublication {
            state: request.completion,
        });
    }
    if let Some(tool) = request.external_products.first() {
        return Err(CertificationRefusal::ExternalToolProduct { tool: *tool });
    }

    let mut observed = [None; 13];
    for entry in request.entries {
        let slot = &mut observed[entry.component.index()];
        if slot.replace(entry.root).is_some() {
            return Err(CertificationRefusal::DuplicateClosureComponent {
                component: entry.component,
            });
        }
    }
    for component in ClosureComponent::ALL {
        if observed[component.index()].is_none() {
            return Err(CertificationRefusal::MissingClosureComponent { component });
        }
    }

    let roots = ClosureRoots {
        roots: [
            required_root(&observed, ClosureComponent::Sources)?,
            required_root(&observed, ClosureComponent::Toolchain)?,
            required_root(&observed, ClosureComponent::SuiteLock)?,
            required_root(&observed, ClosureComponent::Options)?,
            required_root(&observed, ClosureComponent::Plugins)?,
            required_root(&observed, ClosureComponent::Mode)?,
            required_root(&observed, ClosureComponent::Epoch)?,
            required_root(&observed, ClosureComponent::Target)?,
            required_root(&observed, ClosureComponent::BuildProfile)?,
            required_root(&observed, ClosureComponent::Features)?,
            required_root(&observed, ClosureComponent::PolicyEpochs)?,
            required_root(&observed, ClosureComponent::SemanticInputs)?,
            required_root(&observed, ClosureComponent::ReplayInputs)?,
        ],
    };

    if request.claimed_root != request.recomputed_root {
        return Err(CertificationRefusal::ClosureRootMismatch);
    }

    let replay_root = roots.root(ClosureComponent::ReplayInputs);
    let mut determinism = DeterminismClass::D0Mathematical;
    for operation in request.operations {
        if !operation.affects_semantics {
            continue;
        }
        determinism = determinism.max(operation.class);
        match operation.class {
            DeterminismClass::D0Mathematical | DeterminismClass::D1Canonicalized => {}
            DeterminismClass::D2Replayable => match operation.replay_binding {
                None => return Err(CertificationRefusal::MissingReplayBinding),
                Some(binding) if binding != replay_root => {
                    return Err(CertificationRefusal::ReplayBindingMismatch);
                }
                Some(_) => {}
            },
            DeterminismClass::D3Advisory | DeterminismClass::D4External => {
                return Err(CertificationRefusal::UnadmittedSemanticOperation {
                    class: operation.class,
                });
            }
        }
    }

    Ok(CertifiedEligibility {
        closure: roots,
        aggregate_root: request.recomputed_root,
        determinism,
    })
}

fn required_root(
    observed: &[Option<ContentRoot>; 13],
    component: ClosureComponent,
) -> Result<ContentRoot, CertificationRefusal> {
    observed[component.index()].ok_or(CertificationRefusal::MissingClosureComponent { component })
}

/// Artifact whose certified claim has been independently admitted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertifiedArtifact<M: ModeMarker, T> {
    artifact: ModeArtifact<M, T>,
    eligibility: CertifiedEligibility,
}

impl<M: ModeMarker, T> CertifiedArtifact<M, T> {
    pub fn publish(
        artifact: ModeArtifact<M, T>,
        eligibility: CertifiedEligibility,
    ) -> Result<CertifiedArtifact<M, T>, CertificationRefusal> {
        let coordinates = artifact.identity.coordinates;
        if coordinates.reproducibility != ReproducibilityProfile::Certified {
            return Err(CertificationRefusal::ArtifactProfileMismatch);
        }
        if coordinates.closure_root != eligibility.aggregate_root {
            return Err(CertificationRefusal::ArtifactClosureMismatch);
        }
        if coordinates.determinism != eligibility.determinism {
            return Err(CertificationRefusal::ArtifactDeterminismMismatch);
        }
        Ok(CertifiedArtifact {
            artifact,
            eligibility,
        })
    }

    pub const fn artifact(&self) -> &ModeArtifact<M, T> {
        &self.artifact
    }

    pub const fn eligibility(&self) -> CertifiedEligibility {
        self.eligibility
    }

    pub fn into_artifact(self) -> ModeArtifact<M, T> {
        self.artifact
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    fn root(byte: u8) -> ContentRoot {
        ContentRoot::new([byte; 32])
    }

    fn coordinates(
        reproducibility: ReproducibilityProfile,
        closure_root: ContentRoot,
        determinism: DeterminismClass,
    ) -> ArtifactCoordinates {
        ArtifactCoordinates {
            epoch: EpochId::new(4_032_000),
            cgse_policy: CgsePolicyId::new(7),
            determinism,
            reproducibility,
            target: TargetId::new(11),
            build_profile: BuildProfileId::new(13),
            closure_root,
            product_root: root(99),
            claim_row: Some(ClaimRowId::new(17)),
        }
    }

    fn complete_entries() -> Vec<ClosureEntry> {
        ClosureComponent::ALL
            .into_iter()
            .enumerate()
            .map(|(index, component)| ClosureEntry {
                component,
                root: root(index as u8 + 1),
            })
            .collect()
    }

    #[test]
    fn mode_product_lattice_model() {
        let note = BehaviorNoteId::new(1);
        for mode in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
            assert_eq!(
                validate_mode_product(mode, ProductObservation::ReferenceParity),
                Ok(ValidatedProductClass::ReferenceParity)
            );

            let sound = validate_mode_product(
                mode,
                ProductObservation::SoundDivergence {
                    behavior_note: Some(note),
                },
            );
            if mode == Mode::Faithful {
                assert_eq!(sound, Err(ProductRefusal::SoundDivergenceInFaithful));
            } else {
                assert_eq!(
                    sound,
                    Ok(ValidatedProductClass::SoundDivergence {
                        behavior_note: note
                    })
                );
            }

            assert_eq!(
                validate_mode_product(
                    mode,
                    ProductObservation::SoundDivergence {
                        behavior_note: None
                    }
                ),
                Err(ProductRefusal::MissingBehaviorNote)
            );

            for feature in [
                FrontierFeature::OleanNext,
                FrontierFeature::EGraphPortfolio,
                FrontierFeature::IronJit,
                FrontierFeature::McpWriteTools,
                FrontierFeature::EpochBridge,
            ] {
                let observed =
                    validate_mode_product(mode, ProductObservation::FrontierFeature(feature));
                if mode == Mode::Frontier {
                    assert_eq!(
                        observed,
                        Ok(ValidatedProductClass::FrontierFeature(feature))
                    );
                } else {
                    assert_eq!(
                        observed,
                        Err(ProductRefusal::FrontierLeak { consumer: mode })
                    );
                }
            }
        }

        assert_eq!(Mode::DEFAULT, Mode::Sound);
        assert_eq!(
            Mode::from_tag(None),
            Err(AxisDecodeError::Missing { axis: Axis::Mode })
        );
        assert_eq!(
            Mode::from_tag(Some(0xff)),
            Err(AxisDecodeError::Unknown {
                axis: Axis::Mode,
                tag: 0xff
            })
        );
    }

    #[test]
    fn artifact_compatibility_matrix() {
        let schema = NeutralSchemaId::new(1);
        let semantic_root = root(31);
        let registry = [NeutralSchemaRegistration {
            schema,
            semantic_root,
        }];

        for consumer in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
            assert_eq!(
                artifact_compatibility(
                    consumer,
                    ObservedArtifactScope::ModeBound {
                        tag: consumer.tag(),
                        semantic_root,
                    },
                    semantic_root,
                    &registry
                ),
                Ok(CompatibilityDecision::ExactMode)
            );
            assert_eq!(
                artifact_compatibility(
                    consumer,
                    ObservedArtifactScope::Neutral {
                        schema,
                        semantic_root
                    },
                    semantic_root,
                    &registry
                ),
                Ok(CompatibilityDecision::RegisteredNeutral)
            );
        }

        for producer in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
            for consumer in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
                if producer == consumer {
                    continue;
                }
                let observed = artifact_compatibility(
                    consumer,
                    ObservedArtifactScope::ModeBound {
                        tag: producer.tag(),
                        semantic_root,
                    },
                    semantic_root,
                    &registry,
                );
                if producer == Mode::Frontier {
                    assert_eq!(
                        observed,
                        Err(CompatibilityRefusal::FrontierLeak { consumer })
                    );
                } else {
                    assert_eq!(
                        observed,
                        Err(CompatibilityRefusal::MixedMode { producer, consumer })
                    );
                }
            }
        }

        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::Missing,
                semantic_root,
                &registry
            ),
            Err(CompatibilityRefusal::MissingProducerMode)
        );
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::ModeBound {
                    tag: 99,
                    semantic_root,
                },
                semantic_root,
                &registry
            ),
            Err(CompatibilityRefusal::UnknownProducerMode { tag: 99 })
        );
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::ModeBound {
                    tag: Mode::Sound.tag(),
                    semantic_root
                },
                root(32),
                &registry
            ),
            Err(CompatibilityRefusal::ModeSemanticRootMismatch { mode: Mode::Sound })
        );
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::Neutral {
                    schema,
                    semantic_root
                },
                root(32),
                &registry
            ),
            Err(CompatibilityRefusal::NeutralSemanticRootMismatch { schema })
        );
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::Neutral {
                    schema: NeutralSchemaId::new(2),
                    semantic_root
                },
                semantic_root,
                &registry
            ),
            Err(CompatibilityRefusal::UnregisteredNeutralSchema {
                schema: NeutralSchemaId::new(2)
            })
        );

        let duplicate_registry = [
            NeutralSchemaRegistration {
                schema,
                semantic_root,
            },
            NeutralSchemaRegistration {
                schema,
                semantic_root,
            },
        ];
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::Neutral {
                    schema,
                    semantic_root
                },
                semantic_root,
                &duplicate_registry
            ),
            Err(CompatibilityRefusal::DuplicateNeutralRegistration { schema })
        );
        let wrong_registry = [NeutralSchemaRegistration {
            schema,
            semantic_root: root(33),
        }];
        assert_eq!(
            artifact_compatibility(
                Mode::Sound,
                ObservedArtifactScope::Neutral {
                    schema,
                    semantic_root
                },
                semantic_root,
                &wrong_registry
            ),
            Err(CompatibilityRefusal::NeutralRegistryRootMismatch { schema })
        );
    }

    #[test]
    fn certified_closure_model() -> Result<(), CertificationRefusal> {
        let entries = complete_entries();
        let replay_root = entries[ClosureComponent::ReplayInputs.index()].root;
        let operations = [
            OperationFact {
                class: DeterminismClass::D0Mathematical,
                affects_semantics: true,
                replay_binding: None,
            },
            OperationFact {
                class: DeterminismClass::D1Canonicalized,
                affects_semantics: true,
                replay_binding: None,
            },
            OperationFact {
                class: DeterminismClass::D2Replayable,
                affects_semantics: true,
                replay_binding: Some(replay_root),
            },
            OperationFact {
                class: DeterminismClass::D4External,
                affects_semantics: false,
                replay_binding: None,
            },
        ];
        let aggregate = root(200);
        let eligible = recompute_certified_eligibility(CertificationRequest {
            requested_profile: ReproducibilityProfile::Certified,
            completion: CompletionState::Complete,
            entries: &entries,
            claimed_root: aggregate,
            recomputed_root: aggregate,
            external_products: &[],
            operations: &operations,
        })?;
        assert_eq!(eligible.determinism(), DeterminismClass::D2Replayable);
        assert_eq!(
            eligible.closure().root(ClosureComponent::SuiteLock),
            entries[ClosureComponent::SuiteLock.index()].root
        );

        let sound = ModeToken::<SoundMode>::sound();
        let artifact = ModeArtifact::new(
            &sound,
            coordinates(
                ReproducibilityProfile::Certified,
                aggregate,
                DeterminismClass::D2Replayable,
            ),
            "payload",
        );
        assert!(CertifiedArtifact::publish(artifact, eligible).is_ok());

        for omitted in ClosureComponent::ALL {
            let missing: Vec<_> = entries
                .iter()
                .copied()
                .filter(|entry| entry.component != omitted)
                .collect();
            assert_eq!(
                recompute_certified_eligibility(CertificationRequest {
                    requested_profile: ReproducibilityProfile::Certified,
                    completion: CompletionState::Complete,
                    entries: &missing,
                    claimed_root: aggregate,
                    recomputed_root: aggregate,
                    external_products: &[],
                    operations: &operations,
                }),
                Err(CertificationRefusal::MissingClosureComponent { component: omitted })
            );
        }

        for tool in [
            ExternalToolProduct::SystemCCompiler,
            ExternalToolProduct::SystemGit,
        ] {
            assert_eq!(
                recompute_certified_eligibility(CertificationRequest {
                    requested_profile: ReproducibilityProfile::Certified,
                    completion: CompletionState::Complete,
                    entries: &entries,
                    claimed_root: aggregate,
                    recomputed_root: aggregate,
                    external_products: &[tool],
                    operations: &operations,
                }),
                Err(CertificationRefusal::ExternalToolProduct { tool })
            );
        }

        for state in [
            CompletionState::Cancelled,
            CompletionState::ResourceExhausted,
            CompletionState::InternalFault,
        ] {
            assert_eq!(
                recompute_certified_eligibility(CertificationRequest {
                    requested_profile: ReproducibilityProfile::Certified,
                    completion: state,
                    entries: &entries,
                    claimed_root: aggregate,
                    recomputed_root: aggregate,
                    external_products: &[],
                    operations: &operations,
                }),
                Err(CertificationRefusal::IncompletePublication { state })
            );
        }

        assert_eq!(
            recompute_certified_eligibility(CertificationRequest {
                requested_profile: ReproducibilityProfile::Certified,
                completion: CompletionState::Complete,
                entries: &entries,
                claimed_root: root(201),
                recomputed_root: aggregate,
                external_products: &[],
                operations: &operations,
            }),
            Err(CertificationRefusal::ClosureRootMismatch)
        );

        assert_eq!(
            recompute_certified_eligibility(CertificationRequest {
                requested_profile: ReproducibilityProfile::Standard,
                completion: CompletionState::Complete,
                entries: &entries,
                claimed_root: aggregate,
                recomputed_root: aggregate,
                external_products: &[],
                operations: &operations,
            }),
            Err(CertificationRefusal::CertifiedProfileNotRequested)
        );

        let mut duplicate = entries.clone();
        duplicate.push(entries[ClosureComponent::Sources.index()]);
        assert_eq!(
            recompute_certified_eligibility(CertificationRequest {
                requested_profile: ReproducibilityProfile::Certified,
                completion: CompletionState::Complete,
                entries: &duplicate,
                claimed_root: aggregate,
                recomputed_root: aggregate,
                external_products: &[],
                operations: &operations,
            }),
            Err(CertificationRefusal::DuplicateClosureComponent {
                component: ClosureComponent::Sources
            })
        );

        let replay_missing = [OperationFact {
            class: DeterminismClass::D2Replayable,
            affects_semantics: true,
            replay_binding: None,
        }];
        assert_eq!(
            recompute_certified_eligibility(CertificationRequest {
                requested_profile: ReproducibilityProfile::Certified,
                completion: CompletionState::Complete,
                entries: &entries,
                claimed_root: aggregate,
                recomputed_root: aggregate,
                external_products: &[],
                operations: &replay_missing,
            }),
            Err(CertificationRefusal::MissingReplayBinding)
        );

        let replay_mismatch = [OperationFact {
            class: DeterminismClass::D2Replayable,
            affects_semantics: true,
            replay_binding: Some(root(255)),
        }];
        assert_eq!(
            recompute_certified_eligibility(CertificationRequest {
                requested_profile: ReproducibilityProfile::Certified,
                completion: CompletionState::Complete,
                entries: &entries,
                claimed_root: aggregate,
                recomputed_root: aggregate,
                external_products: &[],
                operations: &replay_mismatch,
            }),
            Err(CertificationRefusal::ReplayBindingMismatch)
        );

        for class in [DeterminismClass::D3Advisory, DeterminismClass::D4External] {
            let unadmitted = [OperationFact {
                class,
                affects_semantics: true,
                replay_binding: None,
            }];
            assert_eq!(
                recompute_certified_eligibility(CertificationRequest {
                    requested_profile: ReproducibilityProfile::Certified,
                    completion: CompletionState::Complete,
                    entries: &entries,
                    claimed_root: aggregate,
                    recomputed_root: aggregate,
                    external_products: &[],
                    operations: &unadmitted,
                }),
                Err(CertificationRefusal::UnadmittedSemanticOperation { class })
            );
        }

        let standard_artifact = ModeArtifact::new(
            &sound,
            coordinates(
                ReproducibilityProfile::Standard,
                aggregate,
                DeterminismClass::D2Replayable,
            ),
            (),
        );
        assert_eq!(
            CertifiedArtifact::publish(standard_artifact, eligible),
            Err(CertificationRefusal::ArtifactProfileMismatch)
        );
        let wrong_closure = ModeArtifact::new(
            &sound,
            coordinates(
                ReproducibilityProfile::Certified,
                root(202),
                DeterminismClass::D2Replayable,
            ),
            (),
        );
        assert_eq!(
            CertifiedArtifact::publish(wrong_closure, eligible),
            Err(CertificationRefusal::ArtifactClosureMismatch)
        );
        let wrong_class = ModeArtifact::new(
            &sound,
            coordinates(
                ReproducibilityProfile::Certified,
                aggregate,
                DeterminismClass::D1Canonicalized,
            ),
            (),
        );
        assert_eq!(
            CertifiedArtifact::publish(wrong_class, eligible),
            Err(CertificationRefusal::ArtifactDeterminismMismatch)
        );
        Ok(())
    }

    #[test]
    fn closed_axes_refuse_missing_unknown_and_cross_axis_defaults() {
        assert_eq!(
            DeterminismClass::from_tag(None),
            Err(AxisDecodeError::Missing {
                axis: Axis::Determinism
            })
        );
        assert_eq!(
            ReproducibilityProfile::from_tag(Some(9)),
            Err(AxisDecodeError::Unknown {
                axis: Axis::Reproducibility,
                tag: 9
            })
        );
        assert_eq!(
            EvidenceLevel::from_tag(None),
            Err(AxisDecodeError::Missing {
                axis: Axis::Evidence
            })
        );
        assert_eq!(
            ReleaseLevel::from_tag(Some(9)),
            Err(AxisDecodeError::Unknown {
                axis: Axis::Release,
                tag: 9
            })
        );

        for class in [
            DeterminismClass::D0Mathematical,
            DeterminismClass::D1Canonicalized,
            DeterminismClass::D2Replayable,
            DeterminismClass::D3Advisory,
            DeterminismClass::D4External,
        ] {
            assert_eq!(DeterminismClass::from_tag(Some(class.tag())), Ok(class));
        }
        for level in [
            EvidenceLevel::L0Recognized,
            EvidenceLevel::L1ShapeCompatible,
            EvidenceLevel::L2Behavioral,
            EvidenceLevel::L3DifferentiallyClosed,
            EvidenceLevel::L4DropInAttested,
        ] {
            assert_eq!(EvidenceLevel::from_tag(Some(level.tag())), Ok(level));
        }
    }

    #[test]
    fn mode_propagation_property() {
        let closure = root(41);
        let faithful = ModeArtifact::new(
            &ModeToken::<FaithfulMode>::faithful(),
            coordinates(
                ReproducibilityProfile::Standard,
                closure,
                DeterminismClass::D1Canonicalized,
            ),
            1_u8,
        );
        let sound = ModeArtifact::new(
            &ModeToken::<SoundMode>::sound(),
            coordinates(
                ReproducibilityProfile::Standard,
                closure,
                DeterminismClass::D1Canonicalized,
            ),
            2_u8,
        );
        let frontier = ModeToken::<FrontierMode>::frontier().frontier_artifact(
            FrontierFeature::IronJit,
            coordinates(
                ReproducibilityProfile::Standard,
                closure,
                DeterminismClass::D1Canonicalized,
            ),
            3_u8,
        );
        assert_eq!(
            faithful.identity().scope(),
            ArtifactScope::ModeBound(Mode::Faithful)
        );
        assert_eq!(
            sound.identity().scope(),
            ArtifactScope::ModeBound(Mode::Sound)
        );
        assert_eq!(
            frontier.artifact().identity().scope(),
            ArtifactScope::ModeBound(Mode::Frontier)
        );

        let first = ArtifactReceipt {
            artifact: sound.identity(),
            evidence: EvidenceBinding {
                surface: EvidenceLevel::L1ShapeCompatible,
                release: ReleaseLevel::R1CheckerPreview,
                ledger_snapshot: root(50),
            },
        };
        let second = ArtifactReceipt {
            artifact: sound.identity(),
            evidence: EvidenceBinding {
                surface: EvidenceLevel::L4DropInAttested,
                release: ReleaseLevel::R5HardenedReplacement,
                ledger_snapshot: root(51),
            },
        };
        assert_eq!(first.artifact, second.artifact);
        assert_ne!(first.evidence, second.evidence);
    }

    #[test]
    fn mode_isolation_e2e() {
        let sound = ModeToken::<SoundMode>::sound();
        let coordinates = coordinates(
            ReproducibilityProfile::Standard,
            root(61),
            DeterminismClass::D1Canonicalized,
        );
        let ordinary = ModeArtifact::new(&sound, coordinates, b"sound product".to_vec());
        assert_eq!(
            ordinary.identity().scope(),
            ArtifactScope::ModeBound(Mode::Sound)
        );

        let planted = validate_mode_product(
            Mode::Sound,
            ProductObservation::FrontierFeature(FrontierFeature::OleanNext),
        );
        assert_eq!(
            planted,
            Err(ProductRefusal::FrontierLeak {
                consumer: Mode::Sound
            })
        );
        let repaired = validate_mode_product(Mode::Sound, ProductObservation::ReferenceParity);
        assert_eq!(repaired, Ok(ValidatedProductClass::ReferenceParity));
    }

    #[test]
    fn mode_rules_are_schedule_independent_at_one_eight_and_thirty_two() {
        fn matrix() -> Vec<Result<CompatibilityDecision, CompatibilityRefusal>> {
            let semantic_root = root(71);
            let registry = [NeutralSchemaRegistration {
                schema: NeutralSchemaId::new(7),
                semantic_root,
            }];
            let mut decisions = Vec::new();
            for consumer in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
                for producer in [Mode::Faithful, Mode::Sound, Mode::Frontier] {
                    decisions.push(artifact_compatibility(
                        consumer,
                        ObservedArtifactScope::ModeBound {
                            tag: producer.tag(),
                            semantic_root,
                        },
                        semantic_root,
                        &registry,
                    ));
                }
            }
            decisions
        }

        let expected = matrix();
        for workers in [1_usize, 8, 32] {
            let handles: Vec<_> = (0..workers).map(|_| thread::spawn(matrix)).collect();
            for handle in handles {
                match handle.join() {
                    Ok(actual) => assert_eq!(actual, expected),
                    Err(payload) => std::panic::resume_unwind(payload),
                }
            }
        }
    }
}
