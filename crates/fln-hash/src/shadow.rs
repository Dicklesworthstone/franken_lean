//! Generic shadow-run promotion authority (plan §§12.6, 18.9, 20.4; bead
//! `fln-52mc`).
//!
//! A successful candidate execution is data, never authority. Authority appears only
//! after [`prepare_promotion`] joins the complete fixture population, exact
//! mode/profile/epoch roots, engine and policy versions, claim and evidence classes,
//! independent validation, mutation status, limitations, and continued-sampling
//! obligation. The returned [`PreparedPromotionV1`] has no public constructor and is
//! revalidated against the immutable cell immediately before publication.
//!
//! Publication has three deliberately separate identities:
//!
//! * the canonical [`ShadowCellV1`] and semantic NDJSON are hashed under
//!   [`Domain::ShadowSemantic`];
//! * operational telemetry is hashed under [`Domain::ShadowTelemetry`] and cannot
//!   enter the cell;
//! * [`Domain::ShadowPublication`] joins those two roots into an outer receipt.
//!
//! [`ShadowAuthorityV1`] holds the write lock while it validates a consumer guard and
//! runs the consumer closure. If a stale root, incompatible version, disagreement, or
//! incident is observed, it constructs and independently validates the quarantined
//! publication before replacing the live cell; the candidate closure is never called.
//! Non-authoritative [`Outcome`] arms are returned unchanged and leave the cell
//! byte-for-byte intact (FL-INV-07).

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::RwLock;

use fln_core::mode::{
    BuildProfileId, CgsePolicyId, ContentRoot, EpochId, Mode, ReproducibilityProfile, TargetId,
};
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};

use crate::canon::{
    CanonError, CanonReader, CanonWriter, Canonical, SCHEMA_SHADOW_CELL,
    SCHEMA_SHADOW_SEMANTIC_NDJSON, SCHEMA_SHADOW_TELEMETRY_NDJSON, SchemaId,
};
use crate::domain::{Domain, hash};

/// Protocol version carried independently of the canonical schema header. This lets a
/// future reader distinguish a changed state-machine law from a changed byte envelope.
pub const SHADOW_PROTOCOL_VERSION: u16 = 1;

const SHADOW_PROTOCOL_TAG: &str = "fln.shadow.protocol/1";
const SHADOW_SCOPE_TAG: &str = "fln.shadow.scope/1";
const SHADOW_EVIDENCE_TAG: &str = "fln.shadow.promotion-evidence/1";
const SHADOW_INCIDENT_TAG: &str = "fln.shadow.incident/1";
const SHADOW_BUNDLE_TAG: &str = "fln.shadow.publication-bundle/1";
const SHADOW_FIXTURE_TAG: &str = "fln.shadow.fixture-manifest/1";
const SHADOW_SAMPLE_TAG: &str = "fln.shadow.sample/1";
const JOURNAL_MAGIC: &[u8; 12] = b"FLNSHADOWV1\n";
const MAX_LIMITATIONS: usize = 256;
const MAX_SAMPLE_RECEIPTS: usize = 65_536;
const MAX_FRAME_BYTES: usize = 64 * 1024 * 1024;

fn content_root(domain: Domain, bytes: &[u8]) -> ContentRoot {
    ContentRoot::new(hash(domain, bytes).0)
}

fn write_u128(writer: &mut CanonWriter, value: u128) {
    writer.bytes(&value.to_le_bytes());
}

fn read_u128(reader: &mut CanonReader<'_>) -> Result<u128, CanonError> {
    let bytes: [u8; 16] = reader.bytes()?.try_into().map_err(|_| CanonError {
        at: 0,
        what: "registry identity is not 16 bytes",
    })?;
    Ok(u128::from_le_bytes(bytes))
}

fn write_root(writer: &mut CanonWriter, root: ContentRoot) {
    writer.bytes(&root.bytes());
}

fn read_root(reader: &mut CanonReader<'_>) -> Result<ContentRoot, CanonError> {
    let bytes = reader.bytes()?;
    let bytes: [u8; 32] = bytes.try_into().map_err(|_| CanonError {
        at: 0,
        what: "content root is not 32 bytes",
    })?;
    Ok(ContentRoot::new(bytes))
}

fn write_engine(writer: &mut CanonWriter, engine: EngineVersionV1) {
    write_u128(writer, engine.engine_id);
    writer.u64(engine.version);
    write_root(writer, engine.binary_root);
}

fn read_engine(reader: &mut CanonReader<'_>) -> Result<EngineVersionV1, CanonError> {
    Ok(EngineVersionV1 {
        engine_id: read_u128(reader)?,
        version: reader.u64()?,
        binary_root: read_root(reader)?,
    })
}

fn write_policy(writer: &mut CanonWriter, policy: PolicyVersionV1) {
    write_u128(writer, policy.policy_id.get());
    writer.u64(policy.version);
    write_root(writer, policy.policy_root);
}

fn read_policy(reader: &mut CanonReader<'_>) -> Result<PolicyVersionV1, CanonError> {
    Ok(PolicyVersionV1 {
        policy_id: CgsePolicyId::new(read_u128(reader)?),
        version: reader.u64()?,
        policy_root: read_root(reader)?,
    })
}

/// Versioned identity of one implementation that can produce a semantic result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EngineVersionV1 {
    pub engine_id: u128,
    pub version: u64,
    pub binary_root: ContentRoot,
}

impl EngineVersionV1 {
    fn is_valid(self) -> bool {
        self.engine_id != 0 && self.version != 0
    }
}

/// Versioned CGSE/promotion policy identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PolicyVersionV1 {
    pub policy_id: CgsePolicyId,
    pub version: u64,
    pub policy_root: ContentRoot,
}

impl PolicyVersionV1 {
    fn is_valid(self) -> bool {
        self.policy_id.get() != 0 && self.version != 0
    }
}

/// Every semantic coordinate whose drift invalidates promotion evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ShadowScopeV1 {
    pub workload_id: u128,
    pub workload_root: ContentRoot,
    pub epoch: EpochId,
    pub epoch_root: ContentRoot,
    pub mode: Mode,
    pub reproducibility: ReproducibilityProfile,
    pub build_profile: BuildProfileId,
    pub profile_root: ContentRoot,
    pub target: TargetId,
    pub target_root: ContentRoot,
}

impl ShadowScopeV1 {
    pub fn semantic_root(self) -> ContentRoot {
        let mut writer = CanonWriter::new();
        writer.str(SHADOW_SCOPE_TAG);
        write_u128(&mut writer, self.workload_id);
        write_root(&mut writer, self.workload_root);
        write_u128(&mut writer, self.epoch.get());
        write_root(&mut writer, self.epoch_root);
        writer.u8(self.mode.tag());
        writer.u8(self.reproducibility.tag());
        write_u128(&mut writer, self.build_profile.get());
        write_root(&mut writer, self.profile_root);
        write_u128(&mut writer, self.target.get());
        write_root(&mut writer, self.target_root);
        content_root(Domain::ShadowSemantic, &writer.into_bytes())
    }

    fn is_valid(self) -> bool {
        self.workload_id != 0
            && self.epoch.get() != 0
            && self.build_profile.get() != 0
            && self.target.get() != 0
    }
}

fn write_scope(writer: &mut CanonWriter, scope: ShadowScopeV1) {
    write_u128(writer, scope.workload_id);
    write_root(writer, scope.workload_root);
    write_u128(writer, scope.epoch.get());
    write_root(writer, scope.epoch_root);
    writer.u8(scope.mode.tag());
    writer.u8(scope.reproducibility.tag());
    write_u128(writer, scope.build_profile.get());
    write_root(writer, scope.profile_root);
    write_u128(writer, scope.target.get());
    write_root(writer, scope.target_root);
}

fn read_scope(reader: &mut CanonReader<'_>) -> Result<ShadowScopeV1, CanonError> {
    let workload_id = read_u128(reader)?;
    let workload_root = read_root(reader)?;
    let epoch = EpochId::new(read_u128(reader)?);
    let epoch_root = read_root(reader)?;
    let mode = Mode::from_tag(Some(reader.u8()?)).map_err(|_| CanonError {
        at: 0,
        what: "unknown mode tag in shadow scope",
    })?;
    let reproducibility =
        ReproducibilityProfile::from_tag(Some(reader.u8()?)).map_err(|_| CanonError {
            at: 0,
            what: "unknown reproducibility tag in shadow scope",
        })?;
    let build_profile = BuildProfileId::new(read_u128(reader)?);
    let profile_root = read_root(reader)?;
    let target = TargetId::new(read_u128(reader)?);
    let target_root = read_root(reader)?;
    Ok(ShadowScopeV1 {
        workload_id,
        workload_root,
        epoch,
        epoch_root,
        mode,
        reproducibility,
        build_profile,
        profile_root,
        target,
        target_root,
    })
}

/// Completed semantic result. A rejection is a completed domain answer, not an
/// inconclusive operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticResultV1 {
    Accepted { result_root: ContentRoot },
    Rejected { result_root: ContentRoot },
}

impl SemanticResultV1 {
    pub const fn root(self) -> ContentRoot {
        match self {
            SemanticResultV1::Accepted { result_root }
            | SemanticResultV1::Rejected { result_root } => result_root,
        }
    }

    const fn tag(self) -> u8 {
        match self {
            SemanticResultV1::Accepted { .. } => 1,
            SemanticResultV1::Rejected { .. } => 2,
        }
    }
}

fn write_semantic_result(writer: &mut CanonWriter, result: SemanticResultV1) {
    writer.u8(result.tag());
    write_root(writer, result.root());
}

fn read_semantic_result(reader: &mut CanonReader<'_>) -> Result<SemanticResultV1, CanonError> {
    let tag = reader.u8()?;
    let result_root = read_root(reader)?;
    match tag {
        1 => Ok(SemanticResultV1::Accepted { result_root }),
        2 => Ok(SemanticResultV1::Rejected { result_root }),
        _ => Err(CanonError {
            at: 0,
            what: "unknown semantic-result tag",
        }),
    }
}

/// One versioned engine product and its completed semantic result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProductV1 {
    pub engine: EngineVersionV1,
    pub product_root: ContentRoot,
    pub semantic_result: SemanticResultV1,
}

fn write_product(writer: &mut CanonWriter, product: ProductV1) {
    write_engine(writer, product.engine);
    write_root(writer, product.product_root);
    write_semantic_result(writer, product.semantic_result);
}

fn read_product(reader: &mut CanonReader<'_>) -> Result<ProductV1, CanonError> {
    Ok(ProductV1 {
        engine: read_engine(reader)?,
        product_root: read_root(reader)?,
        semantic_result: read_semantic_result(reader)?,
    })
}

/// Candidate execution state. Non-authoritative operation outcomes are deliberately
/// absent: observing one leaves the previous cell unchanged.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CandidateResultV1 {
    NotObserved,
    Complete(ProductV1),
}

/// What sort of semantic comparison this cell permits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ComparisonClassV1 {
    ExactParity = 1,
    SoundnessPreserving = 2,
    FrontierExperiment = 3,
}

impl ComparisonClassV1 {
    fn from_tag(tag: u8) -> Result<Self, CanonError> {
        match tag {
            1 => Ok(Self::ExactParity),
            2 => Ok(Self::SoundnessPreserving),
            3 => Ok(Self::FrontierExperiment),
            _ => Err(CanonError {
                at: 0,
                what: "unknown comparison-class tag",
            }),
        }
    }
}

/// D7 claim class. This axis is intentionally independent from [`EvidenceStateV1`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ClaimTypeV1 {
    Invariant = 1,
    Proof = 2,
    BoundedModel = 3,
    Statistical = 4,
    Slo = 5,
    Benchmark = 6,
}

impl ClaimTypeV1 {
    fn from_tag(tag: u8) -> Result<Self, CanonError> {
        match tag {
            1 => Ok(Self::Invariant),
            2 => Ok(Self::Proof),
            3 => Ok(Self::BoundedModel),
            4 => Ok(Self::Statistical),
            5 => Ok(Self::Slo),
            6 => Ok(Self::Benchmark),
            _ => Err(CanonError {
                at: 0,
                what: "unknown claim-type tag",
            }),
        }
    }
}

/// State of evidence, not the kind of claim it may support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum EvidenceStateV1 {
    CandidateOnly = 1,
    Compared = 2,
    IndependentlyValidated = 3,
    Proven = 4,
}

impl EvidenceStateV1 {
    fn from_tag(tag: u8) -> Result<Self, CanonError> {
        match tag {
            1 => Ok(Self::CandidateOnly),
            2 => Ok(Self::Compared),
            3 => Ok(Self::IndependentlyValidated),
            4 => Ok(Self::Proven),
            _ => Err(CanonError {
                at: 0,
                what: "unknown evidence-state tag",
            }),
        }
    }
}

/// Exact Parity Ledger row bound into the promotion cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParityRowV1 {
    pub row_id: u128,
    pub row_root: ContentRoot,
}

/// Complete fixture manifest identity. Construction derives the root from the exact,
/// sorted population so an aggregate "pass" cannot stand in for per-fixture evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FixtureManifestV1 {
    pub manifest_root: ContentRoot,
    pub fixture_count: u32,
}

impl FixtureManifestV1 {
    pub fn from_fixture_ids(mut fixture_ids: Vec<u128>) -> Result<Self, CellRefusalV1> {
        fixture_ids.sort_unstable();
        fixture_ids.dedup();
        if fixture_ids.is_empty() || fixture_ids.len() > u32::MAX as usize {
            return Err(CellRefusalV1::InvalidFixtureManifest);
        }
        let mut writer = CanonWriter::new();
        writer.str(SHADOW_FIXTURE_TAG);
        let fixture_count = fixture_ids.len();
        writer.u64(fixture_count as u64);
        for fixture_id in &fixture_ids {
            if *fixture_id == 0 {
                return Err(CellRefusalV1::InvalidFixtureManifest);
            }
            write_u128(&mut writer, *fixture_id);
        }
        Ok(FixtureManifestV1 {
            manifest_root: content_root(Domain::Fixture, &writer.into_bytes()),
            fixture_count: u32::try_from(fixture_count)
                .map_err(|_| CellRefusalV1::InvalidFixtureManifest)?,
        })
    }
}

/// Deterministic, mandatory continued-sampling policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SamplingObligationV1 {
    pub policy: PolicyVersionV1,
    pub seed_root: ContentRoot,
    pub divisor: u32,
    pub required_initial_passes: u32,
}

impl SamplingObligationV1 {
    pub fn requires_sample(self, request_root: ContentRoot) -> bool {
        let mut writer = CanonWriter::new();
        writer.str(SHADOW_SAMPLE_TAG);
        write_policy(&mut writer, self.policy);
        write_root(&mut writer, self.seed_root);
        write_root(&mut writer, request_root);
        let digest = hash(Domain::ShadowSampling, &writer.into_bytes()).0;
        let [first, second, third, fourth, ..] = digest;
        let bucket = u32::from_le_bytes([first, second, third, fourth]);
        bucket % self.divisor == 0
    }

    fn is_valid(self) -> bool {
        self.policy.is_valid() && self.divisor != 0 && self.required_initial_passes != 0
    }
}

/// Current authority state. There is no automatic edge from `Quarantined` or
/// `Revalidating` to `Promoted`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ShadowStateV1 {
    Shadowing,
    Promoted {
        promotion_evidence_root: ContentRoot,
        revalidated_incident: Option<ContentRoot>,
    },
    Quarantined {
        incident_root: ContentRoot,
        reason: IncidentReasonV1,
    },
    Revalidating {
        incident_root: ContentRoot,
    },
}

/// Why candidate authority was revoked before another consumer could receive it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum IncidentReasonV1 {
    Regression = 1,
    CandidateDisagreement = 2,
    StaleEvidence = 3,
    RootMismatch = 4,
    IncompatibleVersion = 5,
    EvidenceIncomplete = 6,
    SamplingBreach = 7,
    PublicationFault = 8,
}

impl IncidentReasonV1 {
    fn from_tag(tag: u8) -> Result<Self, CanonError> {
        match tag {
            1 => Ok(Self::Regression),
            2 => Ok(Self::CandidateDisagreement),
            3 => Ok(Self::StaleEvidence),
            4 => Ok(Self::RootMismatch),
            5 => Ok(Self::IncompatibleVersion),
            6 => Ok(Self::EvidenceIncomplete),
            7 => Ok(Self::SamplingBreach),
            8 => Ok(Self::PublicationFault),
            _ => Err(CanonError {
                at: 0,
                what: "unknown incident-reason tag",
            }),
        }
    }
}

/// Inputs for a new shadow cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowCellSpecV1 {
    pub scope: ShadowScopeV1,
    pub baseline: ProductV1,
    pub candidate: CandidateResultV1,
    pub comparison_class: ComparisonClassV1,
    pub fixture_manifest: FixtureManifestV1,
    pub policy: PolicyVersionV1,
    pub claim_type: ClaimTypeV1,
    pub parity_row: ParityRowV1,
    pub sampling: SamplingObligationV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellRefusalV1 {
    InvalidScope,
    InvalidEngineVersion,
    InvalidPolicyVersion,
    InvalidFixtureManifest,
    InvalidParityRow,
    InvalidSamplingObligation,
    CandidateEqualsBaselineEngine,
    TooManySampleReceipts,
}

/// Versioned durable state of one workload/epoch/profile/platform cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowCellV1 {
    protocol_version: u16,
    generation: u64,
    scope: ShadowScopeV1,
    baseline: ProductV1,
    candidate: CandidateResultV1,
    comparison_class: ComparisonClassV1,
    fixture_manifest: FixtureManifestV1,
    policy: PolicyVersionV1,
    evidence_state: EvidenceStateV1,
    claim_type: ClaimTypeV1,
    parity_row: ParityRowV1,
    sampling: SamplingObligationV1,
    state: ShadowStateV1,
    sample_receipts: BTreeMap<ContentRoot, ContentRoot>,
}

impl ShadowCellV1 {
    pub fn new(spec: ShadowCellSpecV1) -> Result<Self, CellRefusalV1> {
        let cell = ShadowCellV1 {
            protocol_version: SHADOW_PROTOCOL_VERSION,
            generation: 0,
            scope: spec.scope,
            baseline: spec.baseline,
            candidate: spec.candidate,
            comparison_class: spec.comparison_class,
            fixture_manifest: spec.fixture_manifest,
            policy: spec.policy,
            evidence_state: EvidenceStateV1::CandidateOnly,
            claim_type: spec.claim_type,
            parity_row: spec.parity_row,
            sampling: spec.sampling,
            state: ShadowStateV1::Shadowing,
            sample_receipts: BTreeMap::new(),
        };
        cell.validate_static()?;
        Ok(cell)
    }

    fn validate_static(&self) -> Result<(), CellRefusalV1> {
        if self.protocol_version != SHADOW_PROTOCOL_VERSION || !self.scope.is_valid() {
            return Err(CellRefusalV1::InvalidScope);
        }
        if !self.baseline.engine.is_valid()
            || matches!(
                self.candidate,
                CandidateResultV1::Complete(product) if !product.engine.is_valid()
            )
        {
            return Err(CellRefusalV1::InvalidEngineVersion);
        }
        if !self.policy.is_valid() {
            return Err(CellRefusalV1::InvalidPolicyVersion);
        }
        if self.fixture_manifest.fixture_count == 0 {
            return Err(CellRefusalV1::InvalidFixtureManifest);
        }
        if self.parity_row.row_id == 0 {
            return Err(CellRefusalV1::InvalidParityRow);
        }
        if !self.sampling.is_valid() {
            return Err(CellRefusalV1::InvalidSamplingObligation);
        }
        if matches!(
            self.candidate,
            CandidateResultV1::Complete(product)
                if product.engine.engine_id == self.baseline.engine.engine_id
        ) {
            return Err(CellRefusalV1::CandidateEqualsBaselineEngine);
        }
        if self.sample_receipts.len() > MAX_SAMPLE_RECEIPTS {
            return Err(CellRefusalV1::TooManySampleReceipts);
        }
        Ok(())
    }

    pub const fn protocol_version(&self) -> u16 {
        self.protocol_version
    }

    pub const fn generation(&self) -> u64 {
        self.generation
    }

    pub const fn scope(&self) -> ShadowScopeV1 {
        self.scope
    }

    pub const fn baseline(&self) -> ProductV1 {
        self.baseline
    }

    pub const fn candidate(&self) -> CandidateResultV1 {
        self.candidate
    }

    pub const fn comparison_class(&self) -> ComparisonClassV1 {
        self.comparison_class
    }

    pub const fn fixture_manifest(&self) -> FixtureManifestV1 {
        self.fixture_manifest
    }

    pub const fn policy(&self) -> PolicyVersionV1 {
        self.policy
    }

    pub const fn evidence_state(&self) -> EvidenceStateV1 {
        self.evidence_state
    }

    pub const fn claim_type(&self) -> ClaimTypeV1 {
        self.claim_type
    }

    pub const fn parity_row(&self) -> ParityRowV1 {
        self.parity_row
    }

    pub const fn sampling(&self) -> SamplingObligationV1 {
        self.sampling
    }

    pub const fn state(&self) -> ShadowStateV1 {
        self.state
    }

    pub fn sample_receipts(&self) -> &BTreeMap<ContentRoot, ContentRoot> {
        &self.sample_receipts
    }

    pub fn semantic_root(&self) -> ContentRoot {
        content_root(Domain::ShadowSemantic, &self.to_canonical_bytes())
    }

    pub fn serving_product(&self) -> ServingProductV1 {
        match self.state {
            ShadowStateV1::Promoted { .. } => match self.candidate {
                CandidateResultV1::Complete(product) => ServingProductV1 {
                    source: ServingSourceV1::Candidate,
                    product,
                },
                CandidateResultV1::NotObserved => ServingProductV1 {
                    source: ServingSourceV1::Baseline,
                    product: self.baseline,
                },
            },
            ShadowStateV1::Shadowing
            | ShadowStateV1::Quarantined { .. }
            | ShadowStateV1::Revalidating { .. } => ServingProductV1 {
                source: ServingSourceV1::Baseline,
                product: self.baseline,
            },
        }
    }

    pub fn consumer_guard(&self) -> ConsumerGuardV1 {
        let serving = self.serving_product();
        ConsumerGuardV1 {
            cell_root: self.semantic_root(),
            scope_root: self.scope.semantic_root(),
            policy: self.policy,
            source: serving.source,
            engine: serving.product.engine,
            product_root: serving.product.product_root,
        }
    }
}

/// Which product the authority currently permits a consumer to execute.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ServingSourceV1 {
    Baseline,
    Candidate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ServingProductV1 {
    pub source: ServingSourceV1,
    pub product: ProductV1,
}

/// Exact dependency set a consumer observed before requesting a serving grant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConsumerGuardV1 {
    pub cell_root: ContentRoot,
    pub scope_root: ContentRoot,
    pub policy: PolicyVersionV1,
    pub source: ServingSourceV1,
    pub engine: EngineVersionV1,
    pub product_root: ContentRoot,
}

/// Per-fixture semantic judgment. `Disagreement` can never enter a prepared promotion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum FixtureVerdictV1 {
    Match = 1,
    ApprovedDivergence = 2,
    Disagreement = 3,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FixtureComparisonV1 {
    pub fixture_id: u128,
    pub reference_result_root: ContentRoot,
    pub candidate_result_root: ContentRoot,
    pub verdict: FixtureVerdictV1,
}

/// Whether a validation lane applied and, when it did, the exact receipt it produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValidationStatusV1 {
    NotApplicable,
    Passed { receipt_root: ContentRoot },
}

/// Mutation evidence is explicit; `Complete` means every enumerated plant was killed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MutationStatusV1 {
    NotRequired {
        ruling_root: ContentRoot,
    },
    Complete {
        campaign_root: ContentRoot,
        killed: u32,
        total: u32,
    },
}

/// Untrusted promotion evidence. Every field is joined; no field grants authority by
/// merely being present.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PromotionEvidenceV1 {
    pub protocol_version: u16,
    pub observed_generation: u64,
    pub observed_cell_root: ContentRoot,
    pub scope_root: ContentRoot,
    pub candidate_engine: EngineVersionV1,
    pub policy: PolicyVersionV1,
    pub fixture_manifest: FixtureManifestV1,
    pub comparisons: Vec<FixtureComparisonV1>,
    pub claim_type: ClaimTypeV1,
    pub evidence_state: EvidenceStateV1,
    pub parity_row: ParityRowV1,
    pub kernel_validation: ValidationStatusV1,
    pub independent_validation: ValidationStatusV1,
    pub mutation_status: MutationStatusV1,
    pub limitation_roots: Vec<ContentRoot>,
    pub continued_sampling: SamplingObligationV1,
    pub revalidation_incident: Option<ContentRoot>,
    pub publication_generation: u64,
}

impl PromotionEvidenceV1 {
    pub fn semantic_root(&self) -> ContentRoot {
        let mut writer = CanonWriter::new();
        writer.str(SHADOW_EVIDENCE_TAG);
        writer.u16(self.protocol_version);
        writer.u64(self.observed_generation);
        write_root(&mut writer, self.observed_cell_root);
        write_root(&mut writer, self.scope_root);
        write_engine(&mut writer, self.candidate_engine);
        write_policy(&mut writer, self.policy);
        write_root(&mut writer, self.fixture_manifest.manifest_root);
        writer.u32(self.fixture_manifest.fixture_count);
        writer.u64(self.comparisons.len() as u64);
        for comparison in &self.comparisons {
            write_u128(&mut writer, comparison.fixture_id);
            write_root(&mut writer, comparison.reference_result_root);
            write_root(&mut writer, comparison.candidate_result_root);
            writer.u8(comparison.verdict as u8);
        }
        writer.u8(self.claim_type as u8);
        writer.u8(self.evidence_state as u8);
        write_u128(&mut writer, self.parity_row.row_id);
        write_root(&mut writer, self.parity_row.row_root);
        write_validation_status(&mut writer, self.kernel_validation);
        write_validation_status(&mut writer, self.independent_validation);
        write_mutation_status(&mut writer, self.mutation_status);
        writer.u64(self.limitation_roots.len() as u64);
        for root in &self.limitation_roots {
            write_root(&mut writer, *root);
        }
        write_sampling(&mut writer, self.continued_sampling);
        write_optional_root(&mut writer, self.revalidation_incident);
        writer.u64(self.publication_generation);
        content_root(Domain::ShadowSemantic, &writer.into_bytes())
    }
}

fn write_validation_status(writer: &mut CanonWriter, status: ValidationStatusV1) {
    match status {
        ValidationStatusV1::NotApplicable => writer.u8(0),
        ValidationStatusV1::Passed { receipt_root } => {
            writer.u8(1);
            write_root(writer, receipt_root);
        }
    }
}

fn write_mutation_status(writer: &mut CanonWriter, status: MutationStatusV1) {
    match status {
        MutationStatusV1::NotRequired { ruling_root } => {
            writer.u8(0);
            write_root(writer, ruling_root);
        }
        MutationStatusV1::Complete {
            campaign_root,
            killed,
            total,
        } => {
            writer.u8(1);
            write_root(writer, campaign_root);
            writer.u32(killed);
            writer.u32(total);
        }
    }
}

fn write_optional_root(writer: &mut CanonWriter, root: Option<ContentRoot>) {
    writer.bool(root.is_some());
    if let Some(root) = root {
        write_root(writer, root);
    }
}

fn read_optional_root(reader: &mut CanonReader<'_>) -> Result<Option<ContentRoot>, CanonError> {
    if reader.bool()? {
        Ok(Some(read_root(reader)?))
    } else {
        Ok(None)
    }
}

fn write_sampling(writer: &mut CanonWriter, sampling: SamplingObligationV1) {
    write_policy(writer, sampling.policy);
    write_root(writer, sampling.seed_root);
    writer.u32(sampling.divisor);
    writer.u32(sampling.required_initial_passes);
}

fn read_sampling(reader: &mut CanonReader<'_>) -> Result<SamplingObligationV1, CanonError> {
    Ok(SamplingObligationV1 {
        policy: read_policy(reader)?,
        seed_root: read_root(reader)?,
        divisor: reader.u32()?,
        required_initial_passes: reader.u32()?,
    })
}

/// Reviewed promotion policy. Claim type and evidence state are separate exact joins,
/// so neither can be silently used as the other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PromotionPolicyV1 {
    pub candidate_engine: EngineVersionV1,
    pub policy: PolicyVersionV1,
    pub required_claim_type: ClaimTypeV1,
    pub required_evidence_state: EvidenceStateV1,
    pub require_kernel_validation: bool,
    pub require_independent_validation: bool,
    pub require_mutation_completion: bool,
    pub minimum_fixture_count: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromotionRefusalV1 {
    UnsupportedProtocolVersion,
    WrongState,
    CandidateNotComplete,
    CandidateEngineMismatch,
    PolicyVersionMismatch,
    StaleGeneration,
    StaleCellRoot,
    ScopeRootMismatch,
    FixtureManifestMismatch,
    FixturePopulationIncomplete,
    FixturePopulationNotCanonical,
    CandidateDisagreement,
    ComparisonClassMismatch,
    ClaimTypeMismatch,
    EvidenceStateMismatch,
    ParityRowMismatch,
    KernelValidationMissing,
    IndependentValidationMissing,
    MutationEvidenceMissing,
    MutationSurvivors,
    LimitationsNotCanonical,
    TooManyLimitations,
    SamplingObligationMismatch,
    RevalidationProofMissing,
    UnexpectedRevalidationProof,
    PublicationGenerationMismatch,
}

impl PromotionRefusalV1 {
    pub const fn incident_reason(self) -> IncidentReasonV1 {
        match self {
            PromotionRefusalV1::CandidateDisagreement
            | PromotionRefusalV1::ComparisonClassMismatch => {
                IncidentReasonV1::CandidateDisagreement
            }
            PromotionRefusalV1::StaleGeneration
            | PromotionRefusalV1::StaleCellRoot
            | PromotionRefusalV1::ParityRowMismatch => IncidentReasonV1::StaleEvidence,
            PromotionRefusalV1::ScopeRootMismatch
            | PromotionRefusalV1::FixtureManifestMismatch
            | PromotionRefusalV1::SamplingObligationMismatch => IncidentReasonV1::RootMismatch,
            PromotionRefusalV1::UnsupportedProtocolVersion
            | PromotionRefusalV1::CandidateEngineMismatch
            | PromotionRefusalV1::PolicyVersionMismatch
            | PromotionRefusalV1::PublicationGenerationMismatch => {
                IncidentReasonV1::IncompatibleVersion
            }
            PromotionRefusalV1::WrongState
            | PromotionRefusalV1::CandidateNotComplete
            | PromotionRefusalV1::FixturePopulationIncomplete
            | PromotionRefusalV1::FixturePopulationNotCanonical
            | PromotionRefusalV1::ClaimTypeMismatch
            | PromotionRefusalV1::EvidenceStateMismatch
            | PromotionRefusalV1::KernelValidationMissing
            | PromotionRefusalV1::IndependentValidationMissing
            | PromotionRefusalV1::MutationEvidenceMissing
            | PromotionRefusalV1::MutationSurvivors
            | PromotionRefusalV1::LimitationsNotCanonical
            | PromotionRefusalV1::TooManyLimitations
            | PromotionRefusalV1::RevalidationProofMissing
            | PromotionRefusalV1::UnexpectedRevalidationProof => {
                IncidentReasonV1::EvidenceIncomplete
            }
        }
    }
}

/// Opaque, joined promotion authority. It can be committed only against the exact
/// generation and semantic root it observed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedPromotionV1 {
    observed_generation: u64,
    observed_cell_root: ContentRoot,
    promotion_evidence_root: ContentRoot,
    evidence_state: EvidenceStateV1,
    claim_type: ClaimTypeV1,
    revalidation_incident: Option<ContentRoot>,
    publication_generation: u64,
}

impl PreparedPromotionV1 {
    pub const fn evidence_root(&self) -> ContentRoot {
        self.promotion_evidence_root
    }
}

/// Join untrusted evidence without mutating the cell.
pub fn prepare_promotion(
    cell: &ShadowCellV1,
    evidence: Outcome<PromotionEvidenceV1>,
    policy: PromotionPolicyV1,
) -> Outcome<Result<PreparedPromotionV1, PromotionRefusalV1>> {
    let evidence = match evidence {
        Outcome::Complete(evidence) => evidence,
        Outcome::Inconclusive(inconclusive) => return Outcome::Inconclusive(inconclusive),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    };
    Outcome::Complete(
        validate_promotion(cell, &evidence, policy).map(|()| PreparedPromotionV1 {
            observed_generation: evidence.observed_generation,
            observed_cell_root: evidence.observed_cell_root,
            promotion_evidence_root: evidence.semantic_root(),
            evidence_state: evidence.evidence_state,
            claim_type: evidence.claim_type,
            revalidation_incident: evidence.revalidation_incident,
            publication_generation: evidence.publication_generation,
        }),
    )
}

fn validate_promotion(
    cell: &ShadowCellV1,
    evidence: &PromotionEvidenceV1,
    policy: PromotionPolicyV1,
) -> Result<(), PromotionRefusalV1> {
    // ubs:ignore — public protocol version, not authentication material.
    if evidence.protocol_version != SHADOW_PROTOCOL_VERSION {
        return Err(PromotionRefusalV1::UnsupportedProtocolVersion);
    }
    match cell.state {
        ShadowStateV1::Shadowing if evidence.revalidation_incident.is_none() => {}
        ShadowStateV1::Shadowing => {
            return Err(PromotionRefusalV1::UnexpectedRevalidationProof);
        }
        ShadowStateV1::Revalidating { incident_root }
            // ubs:ignore — public incident identity, not authentication material.
            if evidence.revalidation_incident == Some(incident_root) => {}
        ShadowStateV1::Revalidating { .. } => {
            return Err(PromotionRefusalV1::RevalidationProofMissing);
        }
        ShadowStateV1::Promoted { .. } | ShadowStateV1::Quarantined { .. } => {
            return Err(PromotionRefusalV1::WrongState);
        }
    }
    let CandidateResultV1::Complete(candidate) = cell.candidate else {
        return Err(PromotionRefusalV1::CandidateNotComplete);
    };
    // ubs:ignore — public engine version identity, not authentication material.
    if candidate.engine != policy.candidate_engine
        // ubs:ignore — public engine version identity, not authentication material.
        || evidence.candidate_engine != policy.candidate_engine
    {
        return Err(PromotionRefusalV1::CandidateEngineMismatch);
    }
    // ubs:ignore — public policy version identity, not authentication material.
    if cell.policy != policy.policy || evidence.policy != policy.policy {
        return Err(PromotionRefusalV1::PolicyVersionMismatch);
    }
    // ubs:ignore — public journal generation, not authentication material.
    if evidence.observed_generation != cell.generation {
        return Err(PromotionRefusalV1::StaleGeneration);
    }
    // ubs:ignore — public content-integrity root, not authentication material.
    if evidence.observed_cell_root != cell.semantic_root() {
        return Err(PromotionRefusalV1::StaleCellRoot);
    }
    // ubs:ignore — public content-integrity root, not authentication material.
    if evidence.scope_root != cell.scope.semantic_root() {
        return Err(PromotionRefusalV1::ScopeRootMismatch);
    }
    // ubs:ignore — public fixture inventory identity, not authentication material.
    if evidence.fixture_manifest != cell.fixture_manifest {
        return Err(PromotionRefusalV1::FixtureManifestMismatch);
    }
    // ubs:ignore — public fixture population count, not authentication material.
    if evidence.fixture_manifest.fixture_count < policy.minimum_fixture_count
        // ubs:ignore — public fixture population count, not authentication material.
        || evidence.comparisons.len() != evidence.fixture_manifest.fixture_count as usize
        || evidence.comparisons.len() < cell.sampling.required_initial_passes as usize
    {
        return Err(PromotionRefusalV1::FixturePopulationIncomplete);
    }
    let fixture_ids: Vec<u128> = evidence
        .comparisons
        .iter()
        .map(|comparison| comparison.fixture_id)
        .collect();
    if fixture_ids.windows(2).any(|pair| pair[0] >= pair[1])
        || FixtureManifestV1::from_fixture_ids(fixture_ids)
            // ubs:ignore — public fixture inventory identity, not authentication material.
            .map(|manifest| manifest != evidence.fixture_manifest)
            .unwrap_or(true)
    {
        return Err(PromotionRefusalV1::FixturePopulationNotCanonical);
    }
    for comparison in &evidence.comparisons {
        match comparison.verdict {
            FixtureVerdictV1::Disagreement => {
                return Err(PromotionRefusalV1::CandidateDisagreement);
            }
            FixtureVerdictV1::Match
                // ubs:ignore — public result roots, not authentication material.
                if comparison.reference_result_root != comparison.candidate_result_root =>
            {
                return Err(PromotionRefusalV1::ComparisonClassMismatch);
            }
            FixtureVerdictV1::ApprovedDivergence
                if matches!(cell.comparison_class, ComparisonClassV1::ExactParity) =>
            {
                return Err(PromotionRefusalV1::ComparisonClassMismatch);
            }
            FixtureVerdictV1::ApprovedDivergence
                // ubs:ignore — public result roots, not authentication material.
                if comparison.reference_result_root == comparison.candidate_result_root =>
            {
                return Err(PromotionRefusalV1::ComparisonClassMismatch);
            }
            FixtureVerdictV1::Match | FixtureVerdictV1::ApprovedDivergence => {}
        }
    }
    // ubs:ignore — public claim classification, not authentication material.
    if evidence.claim_type != cell.claim_type || evidence.claim_type != policy.required_claim_type {
        return Err(PromotionRefusalV1::ClaimTypeMismatch);
    }
    // ubs:ignore — public evidence classification, not authentication material.
    if evidence.evidence_state != policy.required_evidence_state
        || matches!(
            evidence.evidence_state,
            EvidenceStateV1::CandidateOnly | EvidenceStateV1::Compared
        )
    {
        return Err(PromotionRefusalV1::EvidenceStateMismatch);
    }
    // ubs:ignore — public parity-ledger row, not authentication material.
    if evidence.parity_row != cell.parity_row {
        return Err(PromotionRefusalV1::ParityRowMismatch);
    }
    if policy.require_kernel_validation
        && !matches!(
            evidence.kernel_validation,
            ValidationStatusV1::Passed { .. }
        )
    {
        return Err(PromotionRefusalV1::KernelValidationMissing);
    }
    if policy.require_independent_validation
        && !matches!(
            evidence.independent_validation,
            ValidationStatusV1::Passed { .. }
        )
    {
        return Err(PromotionRefusalV1::IndependentValidationMissing);
    }
    match evidence.mutation_status {
        // ubs:ignore — public mutation-campaign counts, not authentication material.
        MutationStatusV1::Complete { killed, total, .. } if total > 0 && killed == total => {}
        MutationStatusV1::Complete { .. } => {
            return Err(PromotionRefusalV1::MutationSurvivors);
        }
        MutationStatusV1::NotRequired { .. } if !policy.require_mutation_completion => {}
        MutationStatusV1::NotRequired { .. } => {
            return Err(PromotionRefusalV1::MutationEvidenceMissing);
        }
    }
    if evidence.limitation_roots.len() > MAX_LIMITATIONS {
        return Err(PromotionRefusalV1::TooManyLimitations);
    }
    if evidence
        .limitation_roots
        .windows(2)
        .any(|pair| pair[0] >= pair[1])
    {
        return Err(PromotionRefusalV1::LimitationsNotCanonical);
    }
    // ubs:ignore — public sampling policy, not authentication material.
    if evidence.continued_sampling != cell.sampling {
        return Err(PromotionRefusalV1::SamplingObligationMismatch);
    }
    let Some(expected_publication_generation) = cell.generation.checked_add(1) else {
        return Err(PromotionRefusalV1::PublicationGenerationMismatch);
    };
    // ubs:ignore — public journal generation, not authentication material.
    if evidence.publication_generation != expected_publication_generation {
        return Err(PromotionRefusalV1::PublicationGenerationMismatch);
    }
    Ok(())
}

impl Canonical for ShadowCellV1 {
    const SCHEMA: SchemaId = SCHEMA_SHADOW_CELL;

    fn write_body(&self, writer: &mut CanonWriter) {
        writer.u16(self.protocol_version);
        writer.u64(self.generation);
        write_scope(writer, self.scope);
        write_product(writer, self.baseline);
        match self.candidate {
            CandidateResultV1::NotObserved => writer.u8(0),
            CandidateResultV1::Complete(product) => {
                writer.u8(1);
                write_product(writer, product);
            }
        }
        writer.u8(self.comparison_class as u8);
        write_root(writer, self.fixture_manifest.manifest_root);
        writer.u32(self.fixture_manifest.fixture_count);
        write_policy(writer, self.policy);
        writer.u8(self.evidence_state as u8);
        writer.u8(self.claim_type as u8);
        write_u128(writer, self.parity_row.row_id);
        write_root(writer, self.parity_row.row_root);
        write_sampling(writer, self.sampling);
        match self.state {
            ShadowStateV1::Shadowing => writer.u8(0),
            ShadowStateV1::Promoted {
                promotion_evidence_root,
                revalidated_incident,
            } => {
                writer.u8(1);
                write_root(writer, promotion_evidence_root);
                write_optional_root(writer, revalidated_incident);
            }
            ShadowStateV1::Quarantined {
                incident_root,
                reason,
            } => {
                writer.u8(2);
                write_root(writer, incident_root);
                writer.u8(reason as u8);
            }
            ShadowStateV1::Revalidating { incident_root } => {
                writer.u8(3);
                write_root(writer, incident_root);
            }
        }
        writer.u64(self.sample_receipts.len() as u64);
        for (request_root, receipt_root) in &self.sample_receipts {
            write_root(writer, *request_root);
            write_root(writer, *receipt_root);
        }
    }

    fn read_body(reader: &mut CanonReader<'_>) -> Result<Self, CanonError> {
        let protocol_version = reader.u16()?;
        let generation = reader.u64()?;
        let scope = read_scope(reader)?;
        let baseline = read_product(reader)?;
        let candidate = match reader.u8()? {
            0 => CandidateResultV1::NotObserved,
            1 => CandidateResultV1::Complete(read_product(reader)?),
            _ => {
                return Err(CanonError {
                    at: 0,
                    what: "unknown candidate-result tag",
                });
            }
        };
        let comparison_class = ComparisonClassV1::from_tag(reader.u8()?)?;
        let fixture_manifest = FixtureManifestV1 {
            manifest_root: read_root(reader)?,
            fixture_count: reader.u32()?,
        };
        let policy = read_policy(reader)?;
        let evidence_state = EvidenceStateV1::from_tag(reader.u8()?)?;
        let claim_type = ClaimTypeV1::from_tag(reader.u8()?)?;
        let parity_row = ParityRowV1 {
            row_id: read_u128(reader)?,
            row_root: read_root(reader)?,
        };
        let sampling = read_sampling(reader)?;
        let state = match reader.u8()? {
            0 => ShadowStateV1::Shadowing,
            1 => ShadowStateV1::Promoted {
                promotion_evidence_root: read_root(reader)?,
                revalidated_incident: read_optional_root(reader)?,
            },
            2 => ShadowStateV1::Quarantined {
                incident_root: read_root(reader)?,
                reason: IncidentReasonV1::from_tag(reader.u8()?)?,
            },
            3 => ShadowStateV1::Revalidating {
                incident_root: read_root(reader)?,
            },
            _ => {
                return Err(CanonError {
                    at: 0,
                    what: "unknown shadow-state tag",
                });
            }
        };
        let sample_count = usize::try_from(reader.u64()?).map_err(|_| CanonError {
            at: 0,
            what: "sample count exceeds address space",
        })?;
        if sample_count > MAX_SAMPLE_RECEIPTS {
            return Err(CanonError {
                at: 0,
                what: "sample count exceeds protocol ceiling",
            });
        }
        let mut sample_receipts = BTreeMap::new();
        let mut previous = None;
        for _ in 0..sample_count {
            let request_root = read_root(reader)?;
            let receipt_root = read_root(reader)?;
            if previous.is_some_and(|prior| prior >= request_root) {
                return Err(CanonError {
                    at: 0,
                    what: "sample receipts are not in canonical key order",
                });
            }
            previous = Some(request_root);
            sample_receipts.insert(request_root, receipt_root);
        }
        let cell = ShadowCellV1 {
            protocol_version,
            generation,
            scope,
            baseline,
            candidate,
            comparison_class,
            fixture_manifest,
            policy,
            evidence_state,
            claim_type,
            parity_row,
            sampling,
            state,
            sample_receipts,
        };
        cell.validate_static().map_err(|_| CanonError {
            at: 0,
            what: "shadow cell violates a structural invariant",
        })?;
        if matches!(
            cell.state,
            ShadowStateV1::Promoted { .. } | ShadowStateV1::Revalidating { .. }
        ) && matches!(cell.candidate, CandidateResultV1::NotObserved)
        {
            return Err(CanonError {
                at: 0,
                what: "authoritative state has no completed candidate",
            });
        }
        Ok(cell)
    }
}

/// Operational observations carried beside a transition. No field is reachable from
/// [`ShadowCellV1::semantic_root`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ShadowTelemetryV1 {
    pub attempts: u64,
    pub latency_micros: u64,
    pub worker_count: u16,
    pub dropped_events: u64,
}

/// Canonical publication carrying immutable semantic and operational planes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShadowPublicationV1 {
    cell: ShadowCellV1,
    semantic_ndjson: String,
    telemetry_ndjson: String,
    semantic_root: ContentRoot,
    telemetry_root: ContentRoot,
    publication_root: ContentRoot,
}

impl ShadowPublicationV1 {
    pub fn build(
        cell: ShadowCellV1,
        telemetry: ShadowTelemetryV1,
    ) -> Result<Self, PublicationErrorV1> {
        let cell_root = cell.semantic_root();
        let snapshot = hex_encode(&cell.to_canonical_bytes());
        let semantic_ndjson = format!(
            "{{\"schema\":\"{}/{}\",\"generation\":{},\"cell_root\":\"{}\",\
             \"snapshot\":\"{}\"}}\n",
            SCHEMA_SHADOW_SEMANTIC_NDJSON.name,
            SCHEMA_SHADOW_SEMANTIC_NDJSON.version,
            cell.generation,
            hex_encode(&cell_root.bytes()),
            snapshot
        );
        let telemetry_ndjson = format!(
            "{{\"schema\":\"{}/{}\",\"generation\":{},\"cell_root\":\"{}\",\
             \"attempts\":{},\"latency_micros\":{},\"worker_count\":{},\
             \"dropped_events\":{}}}\n",
            SCHEMA_SHADOW_TELEMETRY_NDJSON.name,
            SCHEMA_SHADOW_TELEMETRY_NDJSON.version,
            cell.generation,
            hex_encode(&cell_root.bytes()),
            telemetry.attempts,
            telemetry.latency_micros,
            telemetry.worker_count,
            telemetry.dropped_events
        );
        let semantic_root = content_root(Domain::ShadowSemantic, semantic_ndjson.as_bytes());
        let telemetry_root = content_root(Domain::ShadowTelemetry, telemetry_ndjson.as_bytes());
        let publication_root = publication_root(cell.generation, semantic_root, telemetry_root);
        let publication = ShadowPublicationV1 {
            cell,
            semantic_ndjson,
            telemetry_ndjson,
            semantic_root,
            telemetry_root,
            publication_root,
        };
        let validated = validate_publication(
            publication.semantic_ndjson.as_bytes(),
            publication.telemetry_ndjson.as_bytes(),
            publication.publication_root,
        )?;
        // ubs:ignore — public canonical cell identity, not authentication material.
        if validated != publication.cell {
            return Err(PublicationErrorV1::CellMismatch);
        }
        Ok(publication)
    }

    pub const fn cell(&self) -> &ShadowCellV1 {
        &self.cell
    }

    pub fn semantic_ndjson(&self) -> &str {
        &self.semantic_ndjson
    }

    pub fn telemetry_ndjson(&self) -> &str {
        &self.telemetry_ndjson
    }

    pub const fn semantic_root(&self) -> ContentRoot {
        self.semantic_root
    }

    pub const fn telemetry_root(&self) -> ContentRoot {
        self.telemetry_root
    }

    pub const fn publication_root(&self) -> ContentRoot {
        self.publication_root
    }

    /// One immutable append-only journal frame. Recovery publishes a frame only after
    /// the whole body and both independent projections validate.
    pub fn journal_frame(&self) -> Vec<u8> {
        let mut body = Vec::new();
        body.extend_from_slice(&self.publication_root.bytes());
        body.extend_from_slice(&(self.semantic_ndjson.len() as u64).to_le_bytes());
        body.extend_from_slice(self.semantic_ndjson.as_bytes());
        body.extend_from_slice(&(self.telemetry_ndjson.len() as u64).to_le_bytes());
        body.extend_from_slice(self.telemetry_ndjson.as_bytes());

        let mut frame = Vec::with_capacity(JOURNAL_MAGIC.len() + 8 + body.len());
        frame.extend_from_slice(JOURNAL_MAGIC);
        frame.extend_from_slice(&(body.len() as u64).to_le_bytes());
        frame.extend_from_slice(&body);
        frame
    }
}

fn publication_root(
    generation: u64,
    semantic_root: ContentRoot,
    telemetry_root: ContentRoot,
) -> ContentRoot {
    let mut writer = CanonWriter::new();
    writer.str(SHADOW_BUNDLE_TAG);
    writer.u64(generation);
    write_root(&mut writer, semantic_root);
    write_root(&mut writer, telemetry_root);
    content_root(Domain::ShadowPublication, &writer.into_bytes())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublicationErrorV1 {
    SemanticShape,
    TelemetryShape,
    InvalidNumber,
    InvalidHex,
    OversizedSnapshot,
    CellDecode,
    CellReencodeMismatch,
    CellRootMismatch,
    GenerationMismatch,
    PlaneLinkMismatch,
    PublicationRootMismatch,
    CellMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedSemanticV1 {
    generation: u64,
    cell_root: ContentRoot,
    snapshot: Vec<u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ParsedTelemetryV1 {
    generation: u64,
    cell_root: ContentRoot,
    telemetry: ShadowTelemetryV1,
}

fn validate_publication(
    semantic_ndjson: &[u8],
    telemetry_ndjson: &[u8],
    expected_publication_root: ContentRoot,
) -> Result<ShadowCellV1, PublicationErrorV1> {
    let semantic = parse_semantic_ndjson(semantic_ndjson)?;
    let telemetry = parse_telemetry_ndjson(telemetry_ndjson)?;
    // ubs:ignore — public generation and content roots, not authentication material.
    if semantic.generation != telemetry.generation || semantic.cell_root != telemetry.cell_root {
        return Err(PublicationErrorV1::PlaneLinkMismatch);
    }
    let cell = ShadowCellV1::from_canonical_bytes(&semantic.snapshot)
        .map_err(|_| PublicationErrorV1::CellDecode)?;
    // ubs:ignore — public canonical bytes, not authentication material.
    if cell.to_canonical_bytes() != semantic.snapshot {
        return Err(PublicationErrorV1::CellReencodeMismatch);
    }
    // ubs:ignore — public journal generation, not authentication material.
    if cell.generation != semantic.generation {
        return Err(PublicationErrorV1::GenerationMismatch);
    }
    // ubs:ignore — public content-integrity root, not authentication material.
    if cell.semantic_root() != semantic.cell_root {
        return Err(PublicationErrorV1::CellRootMismatch);
    }
    let semantic_root = content_root(Domain::ShadowSemantic, semantic_ndjson);
    let telemetry_root = content_root(Domain::ShadowTelemetry, telemetry_ndjson);
    // ubs:ignore — public publication root, not authentication material.
    if publication_root(cell.generation, semantic_root, telemetry_root) != expected_publication_root
    {
        return Err(PublicationErrorV1::PublicationRootMismatch);
    }
    // Reconstruct both lines from parsed values. This is a separate parser and a
    // separate canonicality check: reordered keys or alternate number spellings do
    // not become a second valid NDJSON encoding.
    let reconstructed_semantic = format!(
        "{{\"schema\":\"{}/{}\",\"generation\":{},\"cell_root\":\"{}\",\
         \"snapshot\":\"{}\"}}\n",
        SCHEMA_SHADOW_SEMANTIC_NDJSON.name,
        SCHEMA_SHADOW_SEMANTIC_NDJSON.version,
        semantic.generation,
        hex_encode(&semantic.cell_root.bytes()),
        hex_encode(&semantic.snapshot)
    );
    // ubs:ignore — public canonical NDJSON bytes, not authentication material.
    if reconstructed_semantic.as_bytes() != semantic_ndjson {
        return Err(PublicationErrorV1::SemanticShape);
    }
    let reconstructed_telemetry = format!(
        "{{\"schema\":\"{}/{}\",\"generation\":{},\"cell_root\":\"{}\",\
         \"attempts\":{},\"latency_micros\":{},\"worker_count\":{},\
         \"dropped_events\":{}}}\n",
        SCHEMA_SHADOW_TELEMETRY_NDJSON.name,
        SCHEMA_SHADOW_TELEMETRY_NDJSON.version,
        telemetry.generation,
        hex_encode(&telemetry.cell_root.bytes()),
        telemetry.telemetry.attempts,
        telemetry.telemetry.latency_micros,
        telemetry.telemetry.worker_count,
        telemetry.telemetry.dropped_events
    );
    // ubs:ignore — public canonical NDJSON bytes, not authentication material.
    if reconstructed_telemetry.as_bytes() != telemetry_ndjson {
        return Err(PublicationErrorV1::TelemetryShape);
    }
    Ok(cell)
}

fn parse_semantic_ndjson(bytes: &[u8]) -> Result<ParsedSemanticV1, PublicationErrorV1> {
    let text = std::str::from_utf8(bytes).map_err(|_| PublicationErrorV1::SemanticShape)?;
    let prefix = format!(
        "{{\"schema\":\"{}/{}\",\"generation\":",
        SCHEMA_SHADOW_SEMANTIC_NDJSON.name, SCHEMA_SHADOW_SEMANTIC_NDJSON.version
    );
    let rest = text
        .strip_prefix(&prefix)
        .ok_or(PublicationErrorV1::SemanticShape)?;
    let (generation, rest) = split_number(rest, ",\"cell_root\":\"")?;
    let (cell_root, rest) = split_hex_root(rest, "\",\"snapshot\":\"")?;
    let snapshot_hex = rest
        .strip_suffix("\"}\n")
        .ok_or(PublicationErrorV1::SemanticShape)?;
    if snapshot_hex.len() > MAX_FRAME_BYTES.saturating_mul(2) {
        return Err(PublicationErrorV1::OversizedSnapshot);
    }
    let snapshot = parse_hex(snapshot_hex)?;
    Ok(ParsedSemanticV1 {
        generation,
        cell_root,
        snapshot,
    })
}

fn parse_telemetry_ndjson(bytes: &[u8]) -> Result<ParsedTelemetryV1, PublicationErrorV1> {
    let text = std::str::from_utf8(bytes).map_err(|_| PublicationErrorV1::TelemetryShape)?;
    let prefix = format!(
        "{{\"schema\":\"{}/{}\",\"generation\":",
        SCHEMA_SHADOW_TELEMETRY_NDJSON.name, SCHEMA_SHADOW_TELEMETRY_NDJSON.version
    );
    let rest = text
        .strip_prefix(&prefix)
        .ok_or(PublicationErrorV1::TelemetryShape)?;
    let (generation, rest) = split_number(rest, ",\"cell_root\":\"")?;
    let (cell_root, rest) = split_hex_root(rest, "\",\"attempts\":")?;
    let (attempts, rest) = split_number(rest, ",\"latency_micros\":")?;
    let (latency_micros, rest) = split_number(rest, ",\"worker_count\":")?;
    let (worker_count, rest) = split_number(rest, ",\"dropped_events\":")?;
    let dropped_events = rest
        .strip_suffix("}\n")
        .ok_or(PublicationErrorV1::TelemetryShape)?
        .parse::<u64>()
        .map_err(|_| PublicationErrorV1::InvalidNumber)?;
    let worker_count =
        u16::try_from(worker_count).map_err(|_| PublicationErrorV1::InvalidNumber)?;
    Ok(ParsedTelemetryV1 {
        generation,
        cell_root,
        telemetry: ShadowTelemetryV1 {
            attempts,
            latency_micros,
            worker_count,
            dropped_events,
        },
    })
}

fn split_number<'a>(text: &'a str, delimiter: &str) -> Result<(u64, &'a str), PublicationErrorV1> {
    let (number, rest) = text
        .split_once(delimiter)
        .ok_or(PublicationErrorV1::InvalidNumber)?;
    if number.is_empty() || (number.len() > 1 && number.starts_with('0')) {
        return Err(PublicationErrorV1::InvalidNumber);
    }
    let value = number
        .parse::<u64>()
        .map_err(|_| PublicationErrorV1::InvalidNumber)?;
    Ok((value, rest))
}

fn split_hex_root<'a>(
    text: &'a str,
    delimiter: &str,
) -> Result<(ContentRoot, &'a str), PublicationErrorV1> {
    let (root, rest) = text
        .split_once(delimiter)
        .ok_or(PublicationErrorV1::InvalidHex)?;
    let bytes = parse_hex(root)?;
    let bytes: [u8; 32] = bytes
        .try_into()
        .map_err(|_| PublicationErrorV1::InvalidHex)?;
    Ok((ContentRoot::new(bytes), rest))
}

fn hex_encode(bytes: &[u8]) -> String {
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from_digit(u32::from(byte >> 4), 16).expect("nibble"));
        encoded.push(char::from_digit(u32::from(byte & 0x0f), 16).expect("nibble"));
    }
    encoded
}

fn parse_hex(text: &str) -> Result<Vec<u8>, PublicationErrorV1> {
    if !text.len().is_multiple_of(2) || !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(PublicationErrorV1::InvalidHex);
    }
    if text.bytes().any(|byte| byte.is_ascii_uppercase()) {
        return Err(PublicationErrorV1::InvalidHex);
    }
    let mut bytes = Vec::with_capacity(text.len() / 2);
    for pair in text.as_bytes().as_chunks::<2>().0 {
        let high = hex_nibble(pair[0]).ok_or(PublicationErrorV1::InvalidHex)?;
        let low = hex_nibble(pair[1]).ok_or(PublicationErrorV1::InvalidHex)?;
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

/// One independently validated journal publication recovered from a complete frame.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveredPublicationV1 {
    pub publication: ShadowPublicationV1,
    pub frame_end: usize,
}

/// Exact append-only recovery result. An incomplete final frame never replaces
/// `latest`; its byte count remains diagnostic evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryReportV1 {
    pub latest: Option<RecoveredPublicationV1>,
    pub complete_frames: usize,
    pub incomplete_tail_bytes: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryErrorV1 {
    InvalidMagic {
        at: usize,
    },
    FrameTooLarge {
        at: usize,
        declared: u64,
    },
    FrameShape {
        at: usize,
    },
    Publication {
        at: usize,
        cause: PublicationErrorV1,
    },
    FirstGenerationNotZero {
        seen: u64,
    },
    NonMonotonicGeneration {
        previous: u64,
        seen: u64,
    },
}

/// Recover the newest complete publication from an append-only byte journal.
///
/// A partial tail after a valid frame is ignored and reported. A partial first frame
/// is non-authoritative because there is no prior safe state to recover.
pub fn recover_journal(bytes: &[u8]) -> Outcome<Result<RecoveryReportV1, RecoveryErrorV1>> {
    let mut at = 0usize;
    let mut latest: Option<RecoveredPublicationV1> = None;
    let mut complete_frames = 0usize;
    let mut previous_generation: Option<u64> = None;

    while at < bytes.len() {
        let frame_start = at;
        let header_len = JOURNAL_MAGIC.len() + 8;
        if bytes.len() - at < header_len {
            return incomplete_recovery(bytes, frame_start, latest, complete_frames);
        }
        // ubs:ignore — public wire-format magic, not authentication material.
        if &bytes[at..at + JOURNAL_MAGIC.len()] != JOURNAL_MAGIC {
            return Outcome::Complete(Err(RecoveryErrorV1::InvalidMagic { at }));
        }
        at += JOURNAL_MAGIC.len();
        let Some(length_bytes) = bytes.get(at..at + 8) else {
            return Outcome::InternalFault(
                InternalFault::new(
                    "FL-INV-07",
                    "journal header length check disagreed with its fixed-width read",
                )
                .with_evidence(SHADOW_PROTOCOL_TAG),
            );
        };
        let &[a, b, c, d, e, f, g, h] = length_bytes else {
            return Outcome::InternalFault(
                InternalFault::new(
                    "FL-INV-07",
                    "journal length field was not eight bytes after its bounds check",
                )
                .with_evidence(SHADOW_PROTOCOL_TAG),
            );
        };
        let declared = u64::from_le_bytes([a, b, c, d, e, f, g, h]);
        at += 8;
        let body_len = match usize::try_from(declared) {
            Ok(body_len) if body_len <= MAX_FRAME_BYTES => body_len,
            _ => {
                return Outcome::Complete(Err(RecoveryErrorV1::FrameTooLarge {
                    at: frame_start,
                    declared,
                }));
            }
        };
        if bytes.len() - at < body_len {
            return incomplete_recovery(bytes, frame_start, latest, complete_frames);
        }
        let body = &bytes[at..at + body_len];
        let publication = match publication_from_frame_body(body) {
            Ok(publication) => publication,
            Err(error) => {
                return Outcome::Complete(Err(match error {
                    FrameBodyErrorV1::Shape => RecoveryErrorV1::FrameShape { at: frame_start },
                    FrameBodyErrorV1::Publication(cause) => RecoveryErrorV1::Publication {
                        at: frame_start,
                        cause,
                    },
                }));
            }
        };
        let generation = publication.cell.generation;
        match previous_generation {
            // ubs:ignore — public journal generation, not authentication material.
            None if generation != 0 => {
                return Outcome::Complete(Err(RecoveryErrorV1::FirstGenerationNotZero {
                    seen: generation,
                }));
            }
            // ubs:ignore — public journal generation, not authentication material.
            Some(previous) if generation != previous.saturating_add(1) => {
                return Outcome::Complete(Err(RecoveryErrorV1::NonMonotonicGeneration {
                    previous,
                    seen: generation,
                }));
            }
            None | Some(_) => {}
        }
        previous_generation = Some(generation);
        at += body_len;
        complete_frames += 1;
        latest = Some(RecoveredPublicationV1 {
            publication,
            frame_end: at,
        });
    }

    Outcome::Complete(Ok(RecoveryReportV1 {
        latest,
        complete_frames,
        incomplete_tail_bytes: 0,
    }))
}

fn incomplete_recovery(
    bytes: &[u8],
    frame_start: usize,
    latest: Option<RecoveredPublicationV1>,
    complete_frames: usize,
) -> Outcome<Result<RecoveryReportV1, RecoveryErrorV1>> {
    let incomplete_tail_bytes = bytes.len().saturating_sub(frame_start);
    if latest.is_none() {
        return Outcome::Inconclusive(
            Inconclusive::authority_incomplete(
                "shadow journal contains no complete publication frame",
            )
            .with_progress(format!(
                "incomplete first frame begins at byte {frame_start}; \
                 {incomplete_tail_bytes} byte(s) observed"
            )),
        );
    }
    Outcome::Complete(Ok(RecoveryReportV1 {
        latest,
        complete_frames,
        incomplete_tail_bytes,
    }))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FrameBodyErrorV1 {
    Shape,
    Publication(PublicationErrorV1),
}

fn publication_from_frame_body(body: &[u8]) -> Result<ShadowPublicationV1, FrameBodyErrorV1> {
    if body.len() < 32 + 8 + 8 {
        return Err(FrameBodyErrorV1::Shape);
    }
    let publication_root =
        ContentRoot::new(body[..32].try_into().map_err(|_| FrameBodyErrorV1::Shape)?);
    let mut at = 32usize;
    let semantic_len = read_frame_len(body, &mut at)?;
    let semantic_end = at
        .checked_add(semantic_len)
        .filter(|end| *end <= body.len())
        .ok_or(FrameBodyErrorV1::Shape)?;
    let semantic = &body[at..semantic_end];
    at = semantic_end;
    let telemetry_len = read_frame_len(body, &mut at)?;
    let telemetry_end = at
        .checked_add(telemetry_len)
        // ubs:ignore — public frame length, not authentication material.
        .filter(|end| *end == body.len())
        .ok_or(FrameBodyErrorV1::Shape)?;
    let telemetry = &body[at..telemetry_end];
    let cell = validate_publication(semantic, telemetry, publication_root)
        .map_err(FrameBodyErrorV1::Publication)?;
    let semantic_ndjson = std::str::from_utf8(semantic)
        .map_err(|_| FrameBodyErrorV1::Shape)?
        .to_string();
    let telemetry_ndjson = std::str::from_utf8(telemetry)
        .map_err(|_| FrameBodyErrorV1::Shape)?
        .to_string();
    Ok(ShadowPublicationV1 {
        semantic_root: content_root(Domain::ShadowSemantic, semantic),
        telemetry_root: content_root(Domain::ShadowTelemetry, telemetry),
        publication_root,
        cell,
        semantic_ndjson,
        telemetry_ndjson,
    })
}

fn read_frame_len(body: &[u8], at: &mut usize) -> Result<usize, FrameBodyErrorV1> {
    let end = at.checked_add(8).ok_or(FrameBodyErrorV1::Shape)?;
    let raw = body.get(*at..end).ok_or(FrameBodyErrorV1::Shape)?;
    let len = u64::from_le_bytes(raw.try_into().map_err(|_| FrameBodyErrorV1::Shape)?);
    let len = usize::try_from(len).map_err(|_| FrameBodyErrorV1::Shape)?;
    if len > MAX_FRAME_BYTES {
        return Err(FrameBodyErrorV1::Shape);
    }
    *at = end;
    Ok(len)
}

/// Fully built transition. The live cell is replaced only after this value exists and
/// its publication has passed the independent validator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TransitionReceiptV1 {
    pub previous_root: ContentRoot,
    pub current_root: ContentRoot,
    pub publication: ShadowPublicationV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransitionRefusalV1 {
    StalePreparedGeneration,
    StalePreparedRoot,
    WrongState,
    GenerationOverflow,
    Publication(PublicationErrorV1),
}

impl PreparedPromotionV1 {
    pub fn commit(
        self,
        cell: &ShadowCellV1,
        telemetry: ShadowTelemetryV1,
    ) -> Result<TransitionReceiptV1, TransitionRefusalV1> {
        // ubs:ignore — public journal generation, not authentication material.
        if cell.generation != self.observed_generation {
            return Err(TransitionRefusalV1::StalePreparedGeneration);
        }
        // ubs:ignore — public content-integrity root, not authentication material.
        if cell.semantic_root() != self.observed_cell_root {
            return Err(TransitionRefusalV1::StalePreparedRoot);
        }
        match cell.state {
            ShadowStateV1::Shadowing if self.revalidation_incident.is_none() => {}
            ShadowStateV1::Revalidating { incident_root }
                // ubs:ignore — public incident identity, not authentication material.
                if self.revalidation_incident == Some(incident_root) => {}
            ShadowStateV1::Shadowing
            | ShadowStateV1::Promoted { .. }
            | ShadowStateV1::Quarantined { .. }
            | ShadowStateV1::Revalidating { .. } => {
                return Err(TransitionRefusalV1::WrongState);
            }
        }
        let expected_generation = cell
            .generation
            .checked_add(1)
            .ok_or(TransitionRefusalV1::GenerationOverflow)?;
        // ubs:ignore — public journal generation, not authentication material.
        if self.publication_generation != expected_generation {
            return Err(TransitionRefusalV1::StalePreparedGeneration);
        }
        let previous_root = cell.semantic_root();
        let mut next = cell.clone();
        next.generation = expected_generation;
        next.evidence_state = self.evidence_state;
        next.claim_type = self.claim_type;
        next.state = ShadowStateV1::Promoted {
            promotion_evidence_root: self.promotion_evidence_root,
            revalidated_incident: self.revalidation_incident,
        };
        next.sample_receipts.clear();
        let publication = ShadowPublicationV1::build(next, telemetry)
            .map_err(TransitionRefusalV1::Publication)?;
        let current_root = publication.cell.semantic_root();
        Ok(TransitionReceiptV1 {
            previous_root,
            current_root,
            publication,
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PromotionDecisionV1 {
    Promoted(TransitionReceiptV1),
    Quarantined {
        refusal: PromotionRefusalV1,
        transition: TransitionReceiptV1,
    },
}

/// Authoritative incident observation. An operation-level non-answer never reaches
/// this value and therefore cannot demote or promote anything.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IncidentObservationV1 {
    pub observed_generation: u64,
    pub observed_cell_root: ContentRoot,
    pub scope_root: ContentRoot,
    pub candidate_engine: EngineVersionV1,
    pub policy: PolicyVersionV1,
    pub reason: IncidentReasonV1,
    pub evidence_root: ContentRoot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncidentDecisionV1 {
    pub effective_reason: IncidentReasonV1,
    pub transition: TransitionReceiptV1,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RevalidationRefusalV1 {
    NotQuarantined,
    IncidentMismatch,
    GenerationOverflow,
}

/// One deterministic continued-sampling observation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SampleObservationV1 {
    promotion_evidence_root: ContentRoot,
    scope_root: ContentRoot,
    candidate_engine: EngineVersionV1,
    policy: PolicyVersionV1,
    request_root: ContentRoot,
    baseline_result_root: ContentRoot,
    candidate_result_root: ContentRoot,
    verdict: FixtureVerdictV1,
    receipt_root: ContentRoot,
}

impl SampleObservationV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        promotion_evidence_root: ContentRoot,
        scope_root: ContentRoot,
        candidate_engine: EngineVersionV1,
        policy: PolicyVersionV1,
        request_root: ContentRoot,
        baseline_result_root: ContentRoot,
        candidate_result_root: ContentRoot,
        verdict: FixtureVerdictV1,
    ) -> Self {
        let mut writer = CanonWriter::new();
        writer.str(SHADOW_SAMPLE_TAG);
        write_root(&mut writer, promotion_evidence_root);
        write_root(&mut writer, scope_root);
        write_engine(&mut writer, candidate_engine);
        write_policy(&mut writer, policy);
        write_root(&mut writer, request_root);
        write_root(&mut writer, baseline_result_root);
        write_root(&mut writer, candidate_result_root);
        writer.u8(verdict as u8);
        let receipt_root = content_root(Domain::ShadowSampling, &writer.into_bytes());
        SampleObservationV1 {
            promotion_evidence_root,
            scope_root,
            candidate_engine,
            policy,
            request_root,
            baseline_result_root,
            candidate_result_root,
            verdict,
            receipt_root,
        }
    }

    pub const fn request_root(self) -> ContentRoot {
        self.request_root
    }

    pub const fn receipt_root(self) -> ContentRoot {
        self.receipt_root
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SampleRefusalV1 {
    NotPromoted,
    NotScheduled,
    StalePromotion,
    ScopeMismatch,
    CandidateEngineMismatch,
    PolicyMismatch,
    NonCanonicalVerdict,
    GenerationOverflow,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SampleDecisionV1 {
    Recorded(TransitionReceiptV1),
    AlreadyRecorded,
    Quarantined {
        reason: IncidentReasonV1,
        transition: TransitionReceiptV1,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseRefusalV1 {
    StaleGuard,
    Quarantined(Box<TransitionReceiptV1>),
}

/// Live authority with atomic publication and quarantine transitions.
#[derive(Debug)]
pub struct ShadowAuthorityV1 {
    inner: RwLock<ShadowCellV1>,
}

impl ShadowAuthorityV1 {
    pub fn new(cell: ShadowCellV1) -> ShadowAuthorityV1 {
        ShadowAuthorityV1 {
            inner: RwLock::new(cell),
        }
    }

    pub fn snapshot(&self) -> Outcome<ShadowCellV1> {
        match self.inner.read() {
            Ok(cell) => Outcome::Complete(cell.clone()),
            Err(_) => Outcome::InternalFault(lock_fault("snapshot")),
        }
    }

    pub fn attempt_promotion(
        &self,
        evidence: Outcome<PromotionEvidenceV1>,
        policy: PromotionPolicyV1,
        telemetry: ShadowTelemetryV1,
    ) -> Outcome<PromotionDecisionV1> {
        let mut live = match self.inner.write() {
            Ok(live) => live,
            Err(_) => return Outcome::InternalFault(lock_fault("attempt_promotion")),
        };
        let prepared = match prepare_promotion(&live, evidence, policy) {
            Outcome::Complete(prepared) => prepared,
            Outcome::Inconclusive(inconclusive) => {
                return Outcome::Inconclusive(inconclusive);
            }
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        match prepared {
            Ok(prepared) => match prepared.commit(&live, telemetry) {
                Ok(transition) => {
                    *live = transition.publication.cell.clone();
                    Outcome::Complete(PromotionDecisionV1::Promoted(transition))
                }
                Err(error) => {
                    Outcome::InternalFault(transition_fault("commit prepared promotion", error))
                }
            },
            Err(refusal) => {
                let incident_root = promotion_refusal_root(&live, refusal);
                match build_quarantine_transition(
                    &live,
                    refusal.incident_reason(),
                    incident_root,
                    telemetry,
                ) {
                    Ok(transition) => {
                        *live = transition.publication.cell.clone();
                        Outcome::Complete(PromotionDecisionV1::Quarantined {
                            refusal,
                            transition,
                        })
                    }
                    Err(error) => Outcome::InternalFault(transition_fault(
                        "quarantine refused promotion",
                        error,
                    )),
                }
            }
        }
    }

    pub fn report_incident(
        &self,
        observation: Outcome<IncidentObservationV1>,
        telemetry: ShadowTelemetryV1,
    ) -> Outcome<IncidentDecisionV1> {
        let observation = match observation {
            Outcome::Complete(observation) => observation,
            Outcome::Inconclusive(inconclusive) => {
                return Outcome::Inconclusive(inconclusive);
            }
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        let mut live = match self.inner.write() {
            Ok(live) => live,
            Err(_) => return Outcome::InternalFault(lock_fault("report_incident")),
        };
        // ubs:ignore — public journal generation, not authentication material.
        let effective_reason = if observation.observed_generation != live.generation {
            IncidentReasonV1::StaleEvidence
        // ubs:ignore — public content-integrity root, not authentication material.
        } else if observation.observed_cell_root != live.semantic_root()
            // ubs:ignore — public content-integrity root, not authentication material.
            || observation.scope_root != live.scope.semantic_root()
        {
            IncidentReasonV1::RootMismatch
        } else if observation.candidate_engine
            // ubs:ignore — public engine version identity, not authentication material.
            != match live.candidate {
                CandidateResultV1::Complete(product) => product.engine,
                CandidateResultV1::NotObserved => observation.candidate_engine,
            }
            // ubs:ignore — public policy version identity, not authentication material.
            || observation.policy != live.policy
        {
            IncidentReasonV1::IncompatibleVersion
        } else {
            observation.reason
        };
        let incident_root = incident_root(&live, effective_reason, observation.evidence_root);
        match build_quarantine_transition(&live, effective_reason, incident_root, telemetry) {
            Ok(transition) => {
                *live = transition.publication.cell.clone();
                Outcome::Complete(IncidentDecisionV1 {
                    effective_reason,
                    transition,
                })
            }
            Err(error) => Outcome::InternalFault(transition_fault("report incident", error)),
        }
    }

    pub fn begin_revalidation(
        &self,
        incident_root: ContentRoot,
        telemetry: ShadowTelemetryV1,
    ) -> Outcome<Result<TransitionReceiptV1, RevalidationRefusalV1>> {
        let mut live = match self.inner.write() {
            Ok(live) => live,
            Err(_) => return Outcome::InternalFault(lock_fault("begin_revalidation")),
        };
        let ShadowStateV1::Quarantined {
            incident_root: current,
            ..
        } = live.state
        else {
            return Outcome::Complete(Err(RevalidationRefusalV1::NotQuarantined));
        };
        // ubs:ignore — public incident identity, not authentication material.
        if current != incident_root {
            return Outcome::Complete(Err(RevalidationRefusalV1::IncidentMismatch));
        }
        let generation = match live.generation.checked_add(1) {
            Some(generation) => generation,
            None => {
                return Outcome::Complete(Err(RevalidationRefusalV1::GenerationOverflow));
            }
        };
        let previous_root = live.semantic_root();
        let mut next = live.clone();
        next.generation = generation;
        next.state = ShadowStateV1::Revalidating { incident_root };
        let publication = match ShadowPublicationV1::build(next, telemetry) {
            Ok(publication) => publication,
            Err(error) => {
                return Outcome::InternalFault(
                    InternalFault::new(
                        "FL-INV-01",
                        format!("revalidation publication failed: {error:?}"),
                    )
                    .with_evidence(SHADOW_PROTOCOL_TAG),
                );
            }
        };
        let transition = TransitionReceiptV1 {
            previous_root,
            current_root: publication.cell.semantic_root(),
            publication,
        };
        *live = transition.publication.cell.clone();
        Outcome::Complete(Ok(transition))
    }

    pub fn record_sample(
        &self,
        observation: Outcome<SampleObservationV1>,
        telemetry: ShadowTelemetryV1,
    ) -> Outcome<Result<SampleDecisionV1, SampleRefusalV1>> {
        let observation = match observation {
            Outcome::Complete(observation) => observation,
            Outcome::Inconclusive(inconclusive) => {
                return Outcome::Inconclusive(inconclusive);
            }
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        let mut live = match self.inner.write() {
            Ok(live) => live,
            Err(_) => return Outcome::InternalFault(lock_fault("record_sample")),
        };
        let ShadowStateV1::Promoted {
            promotion_evidence_root,
            ..
        } = live.state
        else {
            return Outcome::Complete(Err(SampleRefusalV1::NotPromoted));
        };
        if !live.sampling.requires_sample(observation.request_root) {
            return Outcome::Complete(Err(SampleRefusalV1::NotScheduled));
        }
        // ubs:ignore — public promotion evidence root, not authentication material.
        let refusal = if observation.promotion_evidence_root != promotion_evidence_root {
            Some((
                SampleRefusalV1::StalePromotion,
                IncidentReasonV1::StaleEvidence,
            ))
        // ubs:ignore — public content-integrity root, not authentication material.
        } else if observation.scope_root != live.scope.semantic_root() {
            Some((
                SampleRefusalV1::ScopeMismatch,
                IncidentReasonV1::RootMismatch,
            ))
        } else if observation.candidate_engine
            // ubs:ignore — public engine version identity, not authentication material.
            != match live.candidate {
                CandidateResultV1::Complete(product) => product.engine,
                CandidateResultV1::NotObserved => observation.candidate_engine,
            }
        {
            Some((
                SampleRefusalV1::CandidateEngineMismatch,
                IncidentReasonV1::IncompatibleVersion,
            ))
        // ubs:ignore — public policy version identity, not authentication material.
        } else if observation.policy != live.policy {
            Some((
                SampleRefusalV1::PolicyMismatch,
                IncidentReasonV1::IncompatibleVersion,
            ))
        } else if !sample_verdict_is_valid(live.comparison_class, observation) {
            Some((
                SampleRefusalV1::NonCanonicalVerdict,
                IncidentReasonV1::CandidateDisagreement,
            ))
        } else {
            None
        };
        if let Some((_refusal, reason)) = refusal {
            let root = incident_root(&live, reason, observation.receipt_root);
            return match build_quarantine_transition(&live, reason, root, telemetry) {
                Ok(transition) => {
                    *live = transition.publication.cell.clone();
                    Outcome::Complete(Ok(SampleDecisionV1::Quarantined { reason, transition }))
                }
                Err(error) => Outcome::InternalFault(transition_fault("quarantine sample", error)),
            };
        }
        if let Some(existing) = live.sample_receipts.get(&observation.request_root) {
            // ubs:ignore — public sample receipt root, not authentication material.
            if *existing == observation.receipt_root {
                return Outcome::Complete(Ok(SampleDecisionV1::AlreadyRecorded));
            }
            let reason = IncidentReasonV1::SamplingBreach;
            let root = incident_root(&live, reason, observation.receipt_root);
            return match build_quarantine_transition(&live, reason, root, telemetry) {
                Ok(transition) => {
                    *live = transition.publication.cell.clone();
                    Outcome::Complete(Ok(SampleDecisionV1::Quarantined { reason, transition }))
                }
                Err(error) => {
                    Outcome::InternalFault(transition_fault("quarantine duplicate sample", error))
                }
            };
        }
        let generation = match live.generation.checked_add(1) {
            Some(generation) => generation,
            None => return Outcome::Complete(Err(SampleRefusalV1::GenerationOverflow)),
        };
        let previous_root = live.semantic_root();
        let mut next = live.clone();
        next.generation = generation;
        next.sample_receipts
            .insert(observation.request_root, observation.receipt_root);
        let publication = match ShadowPublicationV1::build(next, telemetry) {
            Ok(publication) => publication,
            Err(error) => {
                return Outcome::InternalFault(
                    InternalFault::new(
                        "FL-INV-01",
                        format!("sampling publication failed: {error:?}"),
                    )
                    .with_evidence(SHADOW_PROTOCOL_TAG),
                );
            }
        };
        let transition = TransitionReceiptV1 {
            previous_root,
            current_root: publication.cell.semantic_root(),
            publication,
        };
        *live = transition.publication.cell.clone();
        Outcome::Complete(Ok(SampleDecisionV1::Recorded(transition)))
    }

    /// Run a consumer only while the exact serving grant remains locked.
    ///
    /// On a promoted candidate, any mismatch constructs and publishes quarantine
    /// first; `consume` is not called. On a baseline state the candidate is already
    /// unavailable, so a stale guard is simply refused.
    pub fn with_authoritative_product<R>(
        &self,
        guard: ConsumerGuardV1,
        telemetry: ShadowTelemetryV1,
        consume: impl FnOnce(ServingProductV1) -> R,
    ) -> Outcome<Result<R, UseRefusalV1>> {
        let mut live = match self.inner.write() {
            Ok(live) => live,
            Err(_) => {
                return Outcome::InternalFault(lock_fault("with_authoritative_product"));
            }
        };
        let current_guard = live.consumer_guard();
        // ubs:ignore — public serving grant identity, not authentication material.
        if current_guard != guard {
            if matches!(live.state, ShadowStateV1::Promoted { .. }) {
                let reason = guard_mismatch_reason(current_guard, guard);
                let root = incident_root(&live, reason, guard.cell_root);
                return match build_quarantine_transition(&live, reason, root, telemetry) {
                    Ok(transition) => {
                        *live = transition.publication.cell.clone();
                        Outcome::Complete(Err(UseRefusalV1::Quarantined(Box::new(transition))))
                    }
                    Err(error) => Outcome::InternalFault(transition_fault(
                        "quarantine before consumer use",
                        error,
                    )),
                };
            }
            return Outcome::Complete(Err(UseRefusalV1::StaleGuard));
        }
        let serving = live.serving_product();
        match catch_unwind(AssertUnwindSafe(|| consume(serving))) {
            Ok(result) => Outcome::Complete(Ok(result)),
            Err(_) => Outcome::InternalFault(
                InternalFault::new(
                    "FL-INV-07",
                    "shadow consumer panicked while the serving grant was held",
                )
                .with_evidence(SHADOW_PROTOCOL_TAG),
            ),
        }
    }
}

fn sample_verdict_is_valid(
    comparison_class: ComparisonClassV1,
    observation: SampleObservationV1,
) -> bool {
    match observation.verdict {
        FixtureVerdictV1::Disagreement => false,
        FixtureVerdictV1::Match => {
            // ubs:ignore — public result roots, not authentication material.
            observation.baseline_result_root == observation.candidate_result_root
        }
        FixtureVerdictV1::ApprovedDivergence => {
            !matches!(comparison_class, ComparisonClassV1::ExactParity)
                // ubs:ignore — public result roots, not authentication material.
                && observation.baseline_result_root != observation.candidate_result_root
        }
    }
}

fn build_quarantine_transition(
    cell: &ShadowCellV1,
    reason: IncidentReasonV1,
    incident_root: ContentRoot,
    telemetry: ShadowTelemetryV1,
) -> Result<TransitionReceiptV1, TransitionRefusalV1> {
    let generation = cell
        .generation
        .checked_add(1)
        .ok_or(TransitionRefusalV1::GenerationOverflow)?;
    let previous_root = cell.semantic_root();
    let mut next = cell.clone();
    next.generation = generation;
    next.state = ShadowStateV1::Quarantined {
        incident_root,
        reason,
    };
    let publication =
        ShadowPublicationV1::build(next, telemetry).map_err(TransitionRefusalV1::Publication)?;
    Ok(TransitionReceiptV1 {
        previous_root,
        current_root: publication.cell.semantic_root(),
        publication,
    })
}

fn promotion_refusal_root(cell: &ShadowCellV1, refusal: PromotionRefusalV1) -> ContentRoot {
    let mut writer = CanonWriter::new();
    writer.str(SHADOW_INCIDENT_TAG);
    write_root(&mut writer, cell.semantic_root());
    writer.u8(promotion_refusal_tag(refusal));
    content_root(Domain::ShadowSemantic, &writer.into_bytes())
}

fn promotion_refusal_tag(refusal: PromotionRefusalV1) -> u8 {
    match refusal {
        PromotionRefusalV1::UnsupportedProtocolVersion => 1,
        PromotionRefusalV1::WrongState => 2,
        PromotionRefusalV1::CandidateNotComplete => 3,
        PromotionRefusalV1::CandidateEngineMismatch => 4,
        PromotionRefusalV1::PolicyVersionMismatch => 5,
        PromotionRefusalV1::StaleGeneration => 6,
        PromotionRefusalV1::StaleCellRoot => 7,
        PromotionRefusalV1::ScopeRootMismatch => 8,
        PromotionRefusalV1::FixtureManifestMismatch => 9,
        PromotionRefusalV1::FixturePopulationIncomplete => 10,
        PromotionRefusalV1::FixturePopulationNotCanonical => 11,
        PromotionRefusalV1::CandidateDisagreement => 12,
        PromotionRefusalV1::ComparisonClassMismatch => 13,
        PromotionRefusalV1::ClaimTypeMismatch => 14,
        PromotionRefusalV1::EvidenceStateMismatch => 15,
        PromotionRefusalV1::ParityRowMismatch => 16,
        PromotionRefusalV1::KernelValidationMissing => 17,
        PromotionRefusalV1::IndependentValidationMissing => 18,
        PromotionRefusalV1::MutationEvidenceMissing => 19,
        PromotionRefusalV1::MutationSurvivors => 20,
        PromotionRefusalV1::LimitationsNotCanonical => 21,
        PromotionRefusalV1::TooManyLimitations => 22,
        PromotionRefusalV1::SamplingObligationMismatch => 23,
        PromotionRefusalV1::RevalidationProofMissing => 24,
        PromotionRefusalV1::UnexpectedRevalidationProof => 25,
        PromotionRefusalV1::PublicationGenerationMismatch => 26,
    }
}

fn incident_root(
    cell: &ShadowCellV1,
    reason: IncidentReasonV1,
    evidence_root: ContentRoot,
) -> ContentRoot {
    let mut writer = CanonWriter::new();
    writer.str(SHADOW_INCIDENT_TAG);
    writer.u64(cell.generation);
    write_root(&mut writer, cell.semantic_root());
    writer.u8(reason as u8);
    write_root(&mut writer, evidence_root);
    content_root(Domain::ShadowSemantic, &writer.into_bytes())
}

fn guard_mismatch_reason(current: ConsumerGuardV1, observed: ConsumerGuardV1) -> IncidentReasonV1 {
    // ubs:ignore — public engine and policy identities, not authentication material.
    if current.engine != observed.engine || current.policy != observed.policy {
        IncidentReasonV1::IncompatibleVersion
    // ubs:ignore — public content-integrity root, not authentication material.
    } else if current.scope_root != observed.scope_root
        // ubs:ignore — public content-integrity root, not authentication material.
        || current.product_root != observed.product_root
    {
        IncidentReasonV1::RootMismatch
    } else {
        IncidentReasonV1::StaleEvidence
    }
}

fn lock_fault(operation: &'static str) -> InternalFault {
    InternalFault::new(
        "FL-INV-07",
        format!("shadow authority lock was poisoned during {operation}"),
    )
    .with_evidence(SHADOW_PROTOCOL_TAG)
}

fn transition_fault(operation: &'static str, error: TransitionRefusalV1) -> InternalFault {
    InternalFault::new(
        "FL-INV-01",
        format!("{operation} failed after its evidence join: {error:?}"),
    )
    .with_evidence(SHADOW_PROTOCOL_TAG)
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use fln_core::diag::{ResourceReason, StructuralUnit};
    use fln_core::outcome::ResourceUsage;

    use super::*;

    macro_rules! fixture_panic {
        ($($arg:tt)*) => {
            panic!(/* ubs:ignore — test-only diagnostic. */ $($arg)*)
        };
    }

    fn root(seed: u8) -> ContentRoot {
        ContentRoot::new([seed; 32])
    }

    fn baseline_engine() -> EngineVersionV1 {
        EngineVersionV1 {
            engine_id: 10,
            version: 7,
            binary_root: root(10),
        }
    }

    fn candidate_engine() -> EngineVersionV1 {
        EngineVersionV1 {
            engine_id: 20,
            version: 9,
            binary_root: root(20),
        }
    }

    fn policy_version() -> PolicyVersionV1 {
        PolicyVersionV1 {
            policy_id: CgsePolicyId::new(31),
            version: 4,
            policy_root: root(31),
        }
    }

    fn scope() -> ShadowScopeV1 {
        ShadowScopeV1 {
            workload_id: 41,
            workload_root: root(41),
            epoch: EpochId::new(42),
            epoch_root: root(42),
            mode: Mode::Sound,
            reproducibility: ReproducibilityProfile::Certified,
            build_profile: BuildProfileId::new(43),
            profile_root: root(43),
            target: TargetId::new(44),
            target_root: root(44),
        }
    }

    fn sampling() -> SamplingObligationV1 {
        SamplingObligationV1 {
            policy: policy_version(),
            seed_root: root(45),
            divisor: 1,
            required_initial_passes: 2,
        }
    }

    fn fixture_manifest() -> FixtureManifestV1 {
        FixtureManifestV1::from_fixture_ids(vec![101, 102]).expect("fixture manifest")
    }

    fn cell() -> ShadowCellV1 {
        ShadowCellV1::new(ShadowCellSpecV1 {
            scope: scope(),
            baseline: ProductV1 {
                engine: baseline_engine(),
                product_root: root(50),
                semantic_result: SemanticResultV1::Accepted {
                    result_root: root(51),
                },
            },
            candidate: CandidateResultV1::Complete(ProductV1 {
                engine: candidate_engine(),
                product_root: root(52),
                semantic_result: SemanticResultV1::Accepted {
                    result_root: root(51),
                },
            }),
            comparison_class: ComparisonClassV1::ExactParity,
            fixture_manifest: fixture_manifest(),
            policy: policy_version(),
            claim_type: ClaimTypeV1::BoundedModel,
            parity_row: ParityRowV1 {
                row_id: 61,
                row_root: root(61),
            },
            sampling: sampling(),
        })
        .expect("valid shadow cell")
    }

    fn promotion_policy() -> PromotionPolicyV1 {
        PromotionPolicyV1 {
            candidate_engine: candidate_engine(),
            policy: policy_version(),
            required_claim_type: ClaimTypeV1::BoundedModel,
            required_evidence_state: EvidenceStateV1::IndependentlyValidated,
            require_kernel_validation: true,
            require_independent_validation: true,
            require_mutation_completion: true,
            minimum_fixture_count: 2,
        }
    }

    fn evidence(cell: &ShadowCellV1) -> PromotionEvidenceV1 {
        let revalidation_incident = match cell.state {
            ShadowStateV1::Revalidating { incident_root } => Some(incident_root),
            ShadowStateV1::Shadowing
            | ShadowStateV1::Promoted { .. }
            | ShadowStateV1::Quarantined { .. } => None,
        };
        PromotionEvidenceV1 {
            protocol_version: SHADOW_PROTOCOL_VERSION,
            observed_generation: cell.generation,
            observed_cell_root: cell.semantic_root(),
            scope_root: cell.scope.semantic_root(),
            candidate_engine: candidate_engine(),
            policy: policy_version(),
            fixture_manifest: fixture_manifest(),
            comparisons: vec![
                FixtureComparisonV1 {
                    fixture_id: 101,
                    reference_result_root: root(71),
                    candidate_result_root: root(71),
                    verdict: FixtureVerdictV1::Match,
                },
                FixtureComparisonV1 {
                    fixture_id: 102,
                    reference_result_root: root(72),
                    candidate_result_root: root(72),
                    verdict: FixtureVerdictV1::Match,
                },
            ],
            claim_type: ClaimTypeV1::BoundedModel,
            evidence_state: EvidenceStateV1::IndependentlyValidated,
            parity_row: cell.parity_row,
            kernel_validation: ValidationStatusV1::Passed {
                receipt_root: root(73),
            },
            independent_validation: ValidationStatusV1::Passed {
                receipt_root: root(74),
            },
            mutation_status: MutationStatusV1::Complete {
                campaign_root: root(75),
                killed: 7,
                total: 7,
            },
            limitation_roots: vec![root(76), root(77)],
            continued_sampling: cell.sampling,
            revalidation_incident,
            publication_generation: cell.generation + 1,
        }
    }

    fn telemetry(worker_count: u16) -> ShadowTelemetryV1 {
        ShadowTelemetryV1 {
            attempts: 2,
            latency_micros: 500,
            worker_count,
            dropped_events: 0,
        }
    }

    fn complete<T: std::fmt::Debug>(outcome: Outcome<T>) -> T {
        outcome.into_complete().unwrap_or_else(|non_authoritative| {
            fixture_panic!("non-authoritative: {non_authoritative:?}")
        })
    }

    fn promoted_authority() -> (Arc<ShadowAuthorityV1>, ContentRoot) {
        let authority = Arc::new(ShadowAuthorityV1::new(cell()));
        let snapshot = complete(authority.snapshot());
        let decision = complete(authority.attempt_promotion(
            Outcome::Complete(evidence(&snapshot)),
            promotion_policy(),
            telemetry(1),
        ));
        let PromotionDecisionV1::Promoted(transition) = decision else {
            fixture_panic!("valid evidence must promote");
        };
        let ShadowStateV1::Promoted {
            promotion_evidence_root,
            ..
        } = transition.publication.cell.state
        else {
            fixture_panic!("transition must publish promoted state");
        };
        (authority, promotion_evidence_root)
    }

    /// Suite: shadow_cell_state_model.
    #[test]
    fn shadow_cell_state_model() {
        let initial = cell();
        assert_eq!(initial.state(), ShadowStateV1::Shadowing);
        assert_eq!(initial.serving_product().source, ServingSourceV1::Baseline);
        let bytes = initial.to_canonical_bytes();
        assert_eq!(
            ShadowCellV1::from_canonical_bytes(&bytes).expect("round trip"),
            initial
        );

        // A completed candidate alone is explicitly still shadow-only.
        assert!(matches!(
            initial.candidate(),
            CandidateResultV1::Complete(_)
        ));
        assert_eq!(initial.evidence_state(), EvidenceStateV1::CandidateOnly);

        let authority = ShadowAuthorityV1::new(initial.clone());
        let promoted = complete(authority.attempt_promotion(
            Outcome::Complete(evidence(&initial)),
            promotion_policy(),
            telemetry(1),
        ));
        let PromotionDecisionV1::Promoted(promoted) = promoted else {
            fixture_panic!("promotion");
        };
        assert!(matches!(
            promoted.publication.cell.state(),
            ShadowStateV1::Promoted { .. }
        ));
        assert_eq!(
            promoted.publication.cell.serving_product().source,
            ServingSourceV1::Candidate
        );

        let promoted_cell = complete(authority.snapshot());
        let incident_evidence = root(80);
        let incident = IncidentObservationV1 {
            observed_generation: promoted_cell.generation(),
            observed_cell_root: promoted_cell.semantic_root(),
            scope_root: promoted_cell.scope().semantic_root(),
            candidate_engine: candidate_engine(),
            policy: policy_version(),
            reason: IncidentReasonV1::Regression,
            evidence_root: incident_evidence,
        };
        let quarantined =
            complete(authority.report_incident(Outcome::Complete(incident), telemetry(1)));
        let ShadowStateV1::Quarantined { incident_root, .. } =
            quarantined.transition.publication.cell.state()
        else {
            fixture_panic!("incident must quarantine");
        };
        assert_eq!(
            quarantined
                .transition
                .publication
                .cell
                .serving_product()
                .source,
            ServingSourceV1::Baseline
        );

        let revalidating = complete(authority.begin_revalidation(incident_root, telemetry(1)))
            .expect("explicit revalidation");
        assert!(matches!(
            revalidating.publication.cell.state(),
            ShadowStateV1::Revalidating { .. }
        ));
        assert_eq!(
            revalidating.publication.cell.serving_product().source,
            ServingSourceV1::Baseline,
            "beginning revalidation is not automatic re-promotion"
        );

        let revalidating_cell = complete(authority.snapshot());
        let re_promoted = complete(authority.attempt_promotion(
            Outcome::Complete(evidence(&revalidating_cell)),
            promotion_policy(),
            telemetry(1),
        ));
        let PromotionDecisionV1::Promoted(re_promoted) = re_promoted else {
            fixture_panic!("independently revalidated evidence promotes explicitly");
        };
        assert!(matches!(
            re_promoted.publication.cell.state(),
            ShadowStateV1::Promoted {
                revalidated_incident: Some(_),
                ..
            }
        ));

        // Cancellation carries no transition payload and leaves the byte identity exact.
        let before = complete(authority.snapshot());
        let stopped = authority.attempt_promotion(
            Outcome::Inconclusive(Inconclusive::cancelled("promotion join")),
            promotion_policy(),
            telemetry(1),
        );
        assert!(matches!(stopped, Outcome::Inconclusive(_)));
        assert_eq!(complete(authority.snapshot()), before);

        let unavailable = authority.attempt_promotion(
            Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                "comparison oracle unavailable",
            )),
            promotion_policy(),
            telemetry(1),
        );
        assert!(matches!(unavailable, Outcome::Inconclusive(_)));
        assert_eq!(complete(authority.snapshot()), before);

        let exhausted = authority.attempt_promotion(
            Outcome::Inconclusive(Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::StructuralBudget {
                    unit: StructuralUnit::ProducedNodes,
                },
                allowed: 10,
                observed: 11,
            })),
            promotion_policy(),
            telemetry(1),
        );
        assert!(matches!(exhausted, Outcome::Inconclusive(_)));
        assert_eq!(complete(authority.snapshot()), before);

        let faulted = authority.attempt_promotion(
            Outcome::InternalFault(InternalFault::new(
                "FL-INV-01",
                "comparison producer contradicted its root",
            )),
            promotion_policy(),
            telemetry(1),
        );
        assert!(matches!(faulted, Outcome::InternalFault(_)));
        assert_eq!(complete(authority.snapshot()), before);
    }

    /// Suite: promotion_evidence_join.
    #[test]
    fn promotion_evidence_join() {
        let cell = cell();
        let policy = promotion_policy();
        assert!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(evidence(&cell)),
                policy
            ))
            .is_ok()
        );

        let mut stale = evidence(&cell);
        stale.observed_generation += 1;
        assert_eq!(
            complete(prepare_promotion(&cell, Outcome::Complete(stale), policy)),
            Err(PromotionRefusalV1::StaleGeneration)
        );

        let mut wrong_root = evidence(&cell);
        wrong_root.scope_root = root(90);
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(wrong_root),
                policy
            )),
            Err(PromotionRefusalV1::ScopeRootMismatch)
        );

        let mut wrong_engine = evidence(&cell);
        wrong_engine.candidate_engine.version += 1;
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(wrong_engine),
                policy
            )),
            Err(PromotionRefusalV1::CandidateEngineMismatch)
        );

        let mut conflated = evidence(&cell);
        conflated.evidence_state = EvidenceStateV1::Compared;
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(conflated),
                policy
            )),
            Err(PromotionRefusalV1::EvidenceStateMismatch)
        );

        let mut stale_row = evidence(&cell);
        stale_row.parity_row.row_root = root(91);
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(stale_row),
                policy
            )),
            Err(PromotionRefusalV1::ParityRowMismatch)
        );

        let mut aggregate_only = evidence(&cell);
        aggregate_only.comparisons.pop();
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(aggregate_only),
                policy
            )),
            Err(PromotionRefusalV1::FixturePopulationIncomplete)
        );

        let mut disagreement = evidence(&cell);
        disagreement.comparisons[0].verdict = FixtureVerdictV1::Disagreement;
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(disagreement.clone()),
                policy
            )),
            Err(PromotionRefusalV1::CandidateDisagreement)
        );

        let mut survived = evidence(&cell);
        survived.mutation_status = MutationStatusV1::Complete {
            campaign_root: root(75),
            killed: 6,
            total: 7,
        };
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(survived),
                policy
            )),
            Err(PromotionRefusalV1::MutationSurvivors)
        );

        let mut no_sampling = evidence(&cell);
        no_sampling.continued_sampling.divisor = 2;
        assert_eq!(
            complete(prepare_promotion(
                &cell,
                Outcome::Complete(no_sampling),
                policy
            )),
            Err(PromotionRefusalV1::SamplingObligationMismatch)
        );

        let authority = ShadowAuthorityV1::new(cell.clone());
        let decision = complete(authority.attempt_promotion(
            Outcome::Complete(disagreement),
            policy,
            telemetry(1),
        ));
        assert!(matches!(
            decision,
            PromotionDecisionV1::Quarantined {
                refusal: PromotionRefusalV1::CandidateDisagreement,
                ..
            }
        ));
        assert!(matches!(
            complete(authority.snapshot()).state(),
            ShadowStateV1::Quarantined { .. }
        ));

        // Telemetry changes its own and the outer root, never semantic authority.
        let a = ShadowPublicationV1::build(cell.clone(), telemetry(1)).expect("publication");
        let b = ShadowPublicationV1::build(
            cell,
            ShadowTelemetryV1 {
                latency_micros: 999_999,
                ..telemetry(32)
            },
        )
        .expect("publication");
        assert_eq!(a.semantic_root(), b.semantic_root());
        assert_ne!(a.telemetry_root(), b.telemetry_root());
        assert_ne!(a.publication_root(), b.publication_root());
    }

    /// Suite: atomic_demotion_recovery.
    #[test]
    fn atomic_demotion_recovery() {
        let initial = cell();
        let initial_publication =
            ShadowPublicationV1::build(initial.clone(), telemetry(1)).expect("initial");
        let stale_guard = initial.consumer_guard();
        let authority = ShadowAuthorityV1::new(initial.clone());
        let promoted = complete(authority.attempt_promotion(
            Outcome::Complete(evidence(&initial)),
            promotion_policy(),
            telemetry(1),
        ));
        let PromotionDecisionV1::Promoted(promoted) = promoted else {
            fixture_panic!("promoted");
        };

        let mut consumer_ran = false;
        let use_result =
            complete(
                authority.with_authoritative_product(stale_guard, telemetry(1), |_| {
                    consumer_ran = true;
                }),
            );
        assert!(!consumer_ran, "quarantine must precede candidate execution");
        let Err(UseRefusalV1::Quarantined(quarantined)) = use_result else {
            fixture_panic!("stale promoted guard must quarantine");
        };
        assert_eq!(
            quarantined.publication.cell.serving_product().source,
            ServingSourceV1::Baseline
        );

        let mut journal = initial_publication.journal_frame();
        journal.extend_from_slice(&promoted.publication.journal_frame());
        let quarantine_frame = quarantined.publication.journal_frame();
        let (quarantine_prefix, _) = quarantine_frame.split_at(quarantine_frame.len() / 2);
        journal.extend_from_slice(quarantine_prefix);
        let recovered = complete(recover_journal(&journal)).expect("recover prior safe frame");
        assert_eq!(recovered.complete_frames, 2);
        assert!(recovered.incomplete_tail_bytes > 0);
        assert_eq!(
            recovered.latest.expect("latest").publication.cell.state(),
            promoted.publication.cell.state()
        );

        // Once the frame is complete, recovery advances exactly to quarantine.
        let mut complete_journal = initial_publication.journal_frame();
        complete_journal.extend_from_slice(&promoted.publication.journal_frame());
        complete_journal.extend_from_slice(&quarantine_frame);
        let recovered = complete(recover_journal(&complete_journal)).expect("recover quarantine");
        assert_eq!(recovered.complete_frames, 3);
        assert!(matches!(
            recovered.latest.expect("latest").publication.cell.state(),
            ShadowStateV1::Quarantined { .. }
        ));

        // Internal faults and unavailable observations cannot change the prior safe cell.
        let before = complete(authority.snapshot());
        let stopped = authority.report_incident(
            Outcome::InternalFault(InternalFault::new(
                "FL-INV-07",
                "incident producer unavailable",
            )),
            telemetry(1),
        );
        assert!(matches!(stopped, Outcome::InternalFault(_)));
        assert_eq!(complete(authority.snapshot()), before);
    }

    fn sampling_root(worker_count: usize) -> ContentRoot {
        let (authority, promotion_evidence_root) = promoted_authority();
        let initial = complete(authority.snapshot());
        let candidate = match initial.candidate() {
            CandidateResultV1::Complete(product) => product,
            CandidateResultV1::NotObserved => fixture_panic!("candidate"),
        };
        let scope_root = initial.scope().semantic_root();
        let policy = initial.policy();
        let requests: Vec<ContentRoot> = (0u8..64).map(root).collect();
        let next = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        std::thread::scope(|scope_threads| {
            for _ in 0..worker_count {
                let authority = Arc::clone(&authority);
                let next = Arc::clone(&next);
                let requests = &requests;
                scope_threads.spawn(move || {
                    loop {
                        let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(request_root) = requests.get(index).copied() else {
                            break;
                        };
                        let observation = SampleObservationV1::new(
                            promotion_evidence_root,
                            scope_root,
                            candidate.engine,
                            policy,
                            request_root,
                            root(index as u8),
                            root(index as u8),
                            FixtureVerdictV1::Match,
                        );
                        let decision = complete(authority.record_sample(
                            Outcome::Complete(observation),
                            telemetry(worker_count as u16),
                        ))
                        .expect("scheduled sample");
                        assert!(matches!(
                            decision,
                            SampleDecisionV1::Recorded(_) | SampleDecisionV1::AlreadyRecorded
                        ));
                    }
                });
            }
        });
        let final_cell = complete(authority.snapshot());
        assert_eq!(final_cell.sample_receipts().len(), requests.len());
        final_cell.semantic_root()
    }

    /// Suite: continued_sampling_dpor.
    #[test]
    fn continued_sampling_dpor() {
        let one = sampling_root(1);
        let eight = sampling_root(8);
        let thirty_two = sampling_root(32);
        assert_eq!(one, eight);
        assert_eq!(one, thirty_two);

        let (authority, promotion_evidence_root) = promoted_authority();
        let promoted = complete(authority.snapshot());
        let candidate = match promoted.candidate() {
            CandidateResultV1::Complete(product) => product,
            CandidateResultV1::NotObserved => fixture_panic!("candidate"),
        };
        let disagreement = SampleObservationV1::new(
            promotion_evidence_root,
            promoted.scope().semantic_root(),
            candidate.engine,
            promoted.policy(),
            root(200),
            root(201),
            root(202),
            FixtureVerdictV1::Disagreement,
        );
        let decision =
            complete(authority.record_sample(Outcome::Complete(disagreement), telemetry(32)))
                .expect("authoritative disagreement");
        assert!(matches!(
            decision,
            SampleDecisionV1::Quarantined {
                reason: IncidentReasonV1::CandidateDisagreement,
                ..
            }
        ));
        assert_eq!(
            complete(authority.snapshot()).serving_product().source,
            ServingSourceV1::Baseline
        );
    }
}
