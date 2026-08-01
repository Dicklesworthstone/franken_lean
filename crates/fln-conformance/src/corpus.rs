//! The conformance corpus's durable-format descriptors, as a **projection** of
//! [`fln_hash::canon::SCHEMA_REGISTRY`] (bead `franken_lean-dgxa`; plan Appendix B:
//! every durable format specified once, generated into both the codecs *and* the
//! conformance corpus).
//!
//! ## Derived, not restated
//!
//! A [`CorpusDescriptor`] **borrows** its [`SchemaRow`]. The format's name, version,
//! owner and `covers` line exist in exactly one place — the registry — and this crate
//! reads them there. Nothing here retypes them, so there is no second copy to drift.
//!
//! What the corpus does add is the half the registry cannot know: what the Tribunal
//! actually *does* with each format. That is a [`CorpusCoverage`], and it is joined
//! against the registry in both directions by [`project`]:
//!
//! * a registry row no coverage claim names is [`ProjectionFault::Uncovered`] — a
//!   durable format the corpus is silently blind to, which is the exact failure the
//!   requirement exists to stop: a partial projection reads as a full one;
//! * a coverage claim no registry row names is [`ProjectionFault::Unregistered`] —
//!   coverage of a format with no published identity, or of one that has been renamed
//!   out from under it;
//! * a claim written against a version the registry has since moved is
//!   [`ProjectionFault::VersionDrift`], reported *as drift* rather than as the
//!   `Uncovered` + `Unregistered` pair a name-only join would produce, because the two
//!   situations call for opposite repairs.
//!
//! ## A coverage claim carries the code that proves it
//!
//! [`CorpusCoverage::run`] is a function pointer, not prose. To say the corpus covers a
//! format you must supply the exercise that demonstrates it, and every exercise is run
//! by the suite. This is deliberate: a coverage table whose rows are sentences is a
//! table that can claim anything, and the registry join would still pass.
//!
//! Each exercise is handed the registry row it is registered against and **binds itself
//! to that row's identity first** — against `<T as Canonical>::SCHEMA` for the term
//! plane, against the owning crate's declared constant for the others. Without that
//! step a copy-pasted exercise could sit under the wrong row and cover a format twice
//! while another goes untested, which the name join alone cannot see.
//!
//! ## Total, with no escape hatch
//!
//! Every registered format has a runnable exercise. There is no "declared exclusion"
//! variant, because the crate map (§21) puts fln-conformance last: it may depend on any
//! crate that owns a durable format, so an uncoverable row would be a layering claim
//! that is not true. A format added without an exercise fails the join with
//! instructions rather than quietly shrinking the corpus.

use fln_core::diag::{Diagnostic, ErrorValue, ResourceReason, Severity, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::mode::{
    BuildProfileId, CgsePolicyId, ContentRoot, EpochId, Mode, ReproducibilityProfile, TargetId,
};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap};
use fln_core::pos::Position;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_env::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, DirectImport, ModuleEpoch, ModuleId,
    ModuleRecord,
};
use fln_env::provenance::{
    CaptureStatus, EXTENSION_ENTRY_ID_SCHEMA, ExtensionContribution, ExtensionEntryId,
    MODULE_PROVENANCE_SCHEMA, ModuleContributionRecord, ModuleProvenanceLimits,
    ModuleProvenanceManifest, PayloadTransparency, ProvenanceCompleteness,
};
use fln_hash::canon::{
    CanonWriter, Canonical, SCHEMA_DECLARATION_CERTIFICATE, SCHEMA_KVMAP_SET, SCHEMA_REGISTRY,
    SCHEMA_SHADOW_CELL, SCHEMA_SHADOW_SEMANTIC_NDJSON, SCHEMA_SHADOW_TELEMETRY_NDJSON, SchemaId,
    SchemaRow, kvmap_canonical_set_bytes,
};
use fln_hash::certificate::{
    CertificateBindingV1, CertificateExtensionV1, CertificateJudgmentV1, ClaimedResultV1,
    ConsensusPolicyV1, DeclarationCertificateV1, DeclarationKindV1, FuelProfileV1, NatHintResultV1,
    NatOperationV1, ReductionHintV1, TermDagV1, TermNodeId, TermNodeV1,
};
use fln_hash::domain::{Digest, Domain, DomainHasher};
use fln_hash::shadow::{
    CandidateResultV1, ClaimTypeV1, ComparisonClassV1, EngineVersionV1, FixtureManifestV1,
    ParityRowV1, PolicyVersionV1, ProductV1, SamplingObligationV1, SemanticResultV1,
    ShadowCellSpecV1, ShadowCellV1, ShadowPublicationV1, ShadowScopeV1, ShadowTelemetryV1,
    recover_journal,
};
use fln_verdict::{
    Assignment, CNF_SCHEMA, Clause, ClauseId, Cnf, InputClause, Literal as SatLiteral, ProofRule,
    ProofStep, SAT_MODEL_SCHEMA, SatModel, SchemaLimits, UNSAT_PROOF_SCHEMA, UnsatProof,
    VariableId,
};

/// Domain-separation tag for the projection root.
///
/// [`Domain::CanonicalSchema`] is documented as the domain of "a canonical-serialization
/// schema descriptor (self-describing corpora)". This is that corpus.
const PROJECTION_TAG: &[u8] = b"fln.conformance.corpus-schema-projection/1";

/// What the conformance corpus does with one durable format.
///
/// `schema` and `version` are the identity this claim was **written against**; they are
/// join keys, never a second source of truth. The row they resolve to is what a
/// descriptor carries.
#[derive(Clone, Copy)]
pub struct CorpusCoverage {
    /// The registry name this claim is written against.
    pub schema: &'static str,
    /// The registry version this claim is written against. Drift is a fault, not a
    /// silent re-point.
    pub version: u16,
    /// Exactly what the exercise does — the reviewable half, and deliberately narrow.
    /// "Round-trips four shapes" is a claim someone can check; "covered" is not.
    pub exercise: &'static str,
    /// The runnable demonstration, handed the row it is registered against.
    pub run: fn(&SchemaRow) -> Result<(), String>,
}

impl std::fmt::Debug for CorpusCoverage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // The function pointer's address is deliberately omitted: it is not stable
        // across builds and would make failure output non-reproducible.
        f.debug_struct("CorpusCoverage")
            .field("schema", &self.schema)
            .field("version", &self.version)
            .field("exercise", &self.exercise)
            .finish_non_exhaustive()
    }
}

/// One durable format as the corpus sees it: the registry's row, plus the corpus's
/// coverage of it. The row is borrowed — never copied, never retyped.
#[derive(Debug, Clone, Copy)]
pub struct CorpusDescriptor<'a> {
    pub row: &'a SchemaRow,
    pub coverage: &'a CorpusCoverage,
}

/// A way the corpus and the registry can disagree.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProjectionFault {
    /// A registered format the corpus does not cover.
    Uncovered { schema: String, version: u16 },
    /// A coverage claim naming no registered format.
    Unregistered { schema: String, version: u16 },
    /// Same name, different version. Reported apart from the pair above because the
    /// repair is different: re-verify the exercise against the new encoding, rather
    /// than add or delete a row.
    VersionDrift {
        schema: String,
        registry: u16,
        corpus: u16,
    },
    /// Two coverage claims for one name. One would shadow the other, so the corpus
    /// would report coverage it does not run.
    DuplicateCoverage { schema: String },
    /// Two registry rows for one name. fln-hash's own suite forbids this; the
    /// projection refuses rather than silently binding to whichever came first.
    DuplicateRegistryRow { schema: String },
}

impl std::fmt::Display for ProjectionFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProjectionFault::Uncovered { schema, version } => write!(
                f,
                "SCHEMA_REGISTRY carries {schema}/{version} and the conformance corpus \
                 does not cover it.\n\
                 Add a CorpusCoverage row to CORPUS_COVERAGE in \
                 crates/fln-conformance/src/corpus.rs naming the schema, the version, \
                 what the exercise does, and the exercise itself. A durable format the \
                 corpus cannot see is a format whose encoding can change with nothing \
                 in the Tribunal disagreeing."
            ),
            ProjectionFault::Unregistered { schema, version } => write!(
                f,
                "the conformance corpus claims coverage of {schema}/{version}, which \
                 SCHEMA_REGISTRY does not carry.\n\
                 Either the format was renamed or removed and this row is stale, or it \
                 was never registered — in which case register it in \
                 crates/fln-hash/src/canon.rs first. Coverage of an unpublished \
                 identity certifies nothing."
            ),
            ProjectionFault::VersionDrift {
                schema,
                registry,
                corpus,
            } => write!(
                f,
                "{schema} is at version {registry} in SCHEMA_REGISTRY and the \
                 conformance corpus covers version {corpus}.\n\
                 A version bump is a new encoding. Re-verify the exercise against it \
                 and then move the version in CORPUS_COVERAGE — do not move the number \
                 alone, which would leave the corpus asserting a round trip it has not \
                 re-run."
            ),
            ProjectionFault::DuplicateCoverage { schema } => write!(
                f,
                "CORPUS_COVERAGE has more than one row for {schema}; one would shadow \
                 the other and its exercise would never run."
            ),
            ProjectionFault::DuplicateRegistryRow { schema } => write!(
                f,
                "SCHEMA_REGISTRY has more than one row for {schema}; the projection \
                 refuses rather than binding to whichever comes first."
            ),
        }
    }
}

/// Join a registry against a coverage table, in both directions.
///
/// Takes slices rather than reading the constants directly so the planted-mismatch
/// cases drive **this** function — a mutation harness that exercises a weaker
/// re-implementation of the join can report a false green.
///
/// Descriptors come back in registry order, and faults sorted, so both are
/// schedule-independent (FL-INV-01).
pub fn project<'a>(
    registry: &'a [SchemaRow],
    coverage: &'a [CorpusCoverage],
) -> Result<Vec<CorpusDescriptor<'a>>, Vec<ProjectionFault>> {
    let mut faults: Vec<ProjectionFault> = Vec::new();

    for (index, row) in registry.iter().enumerate() {
        if registry[..index]
            .iter()
            .any(|prior| prior.id.name == row.id.name)
        {
            faults.push(ProjectionFault::DuplicateRegistryRow {
                schema: row.id.name.to_string(),
            });
        }
    }
    for (index, claim) in coverage.iter().enumerate() {
        if coverage[..index]
            .iter()
            .any(|prior| prior.schema == claim.schema)
        {
            faults.push(ProjectionFault::DuplicateCoverage {
                schema: claim.schema.to_string(),
            });
        }
    }

    let mut descriptors: Vec<CorpusDescriptor<'a>> = Vec::with_capacity(registry.len());
    for row in registry {
        match coverage.iter().find(|claim| claim.schema == row.id.name) {
            None => faults.push(ProjectionFault::Uncovered {
                schema: row.id.name.to_string(),
                version: row.id.version,
            }),
            Some(claim) if claim.version != row.id.version => {
                faults.push(ProjectionFault::VersionDrift {
                    schema: row.id.name.to_string(),
                    registry: row.id.version,
                    corpus: claim.version,
                });
            }
            Some(claim) => descriptors.push(CorpusDescriptor {
                row,
                coverage: claim,
            }),
        }
    }

    for claim in coverage {
        // A name the registry does have is already accounted for above, as a match or
        // as drift; only a name it does not have at all is unregistered.
        if !registry.iter().any(|row| row.id.name == claim.schema) {
            faults.push(ProjectionFault::Unregistered {
                schema: claim.schema.to_string(),
                version: claim.version,
            });
        }
    }

    if faults.is_empty() {
        Ok(descriptors)
    } else {
        faults.sort();
        faults.dedup();
        Err(faults)
    }
}

/// The live projection: the real registry joined against the real corpus.
pub fn descriptors() -> Result<Vec<CorpusDescriptor<'static>>, Vec<ProjectionFault>> {
    project(&SCHEMA_REGISTRY, &CORPUS_COVERAGE)
}

/// One digest over the whole projection.
///
/// Every field that a reader would rely on is bound and length-prefixed, so no two
/// distinct projections share a root by field-boundary ambiguity. A format added,
/// removed, renamed, version-bumped, re-owned, re-described, or given a different
/// exercise moves this value.
pub fn projection_root(descriptors: &[CorpusDescriptor<'_>]) -> Digest {
    let mut hasher = DomainHasher::new(Domain::CanonicalSchema);
    hasher.update(PROJECTION_TAG);
    hasher.update(&[0]);
    hasher.update(&(descriptors.len() as u64).to_le_bytes());
    for descriptor in descriptors {
        for field in [
            descriptor.row.id.name,
            descriptor.row.owner.crate_name(),
            descriptor.row.covers,
            descriptor.coverage.exercise,
        ] {
            hasher.update(&(field.len() as u64).to_le_bytes());
            hasher.update(field.as_bytes());
        }
        hasher.update(&descriptor.row.id.version.to_le_bytes());
    }
    hasher.finalize()
}

/// **The corpus's coverage of every durable format in the program.**
///
/// One row per `SCHEMA_REGISTRY` row, joined in both directions by [`project`]. The
/// order matches the registry's for readability only — the join does not depend on it.
pub const CORPUS_COVERAGE: [CorpusCoverage; 15] = [
    CorpusCoverage {
        schema: "fln.canon.name",
        version: 1,
        exercise: "round trip and re-encode byte identity over four shapes: anonymous, \
                   a two-component string name, a numeric component, and the \
                   overflowing numeric component",
        run: exercise_name,
    },
    CorpusCoverage {
        schema: "fln.canon.level",
        version: 1,
        exercise: "round trip and re-encode byte identity over zero, a parameter, a \
                   successor, max, imax and a level metavariable",
        run: exercise_level,
    },
    CorpusCoverage {
        schema: "fln.canon.expr",
        version: 1,
        exercise: "round trip and re-encode byte identity over one value of each of the \
                   twelve ExprNode variants",
        run: exercise_expr,
    },
    CorpusCoverage {
        schema: "fln.canon.kvmap",
        version: 1,
        exercise: "round trip and re-encode byte identity over all six DataValue \
                   constructors, plus a proof that insertion order is significant: two \
                   maps with the same pairs in different order encode differently",
        run: exercise_kvmap,
    },
    CorpusCoverage {
        schema: "fln.canon.kvmap-set",
        version: 1,
        exercise: "permutation invariance of the set projection, its distinctness from \
                   the ordered encoding, and its refusal (None) on a duplicate-keyed \
                   map; a hashing projection with no decoder, so no round trip",
        run: exercise_kvmap_set,
    },
    CorpusCoverage {
        schema: "fln.canon.diag",
        version: 3,
        exercise: "round trip and re-encode byte identity over a kernel rejection \
                   carrying a position, an end position, an error name and a caption, \
                   and over a kernel-inconclusive carrying the structural-budget \
                   resource reason whose tag forced the v1 -> v2 bump plus the \
                   execution-step reason whose tag forced the v2 -> v3 bump",
        run: exercise_diag,
    },
    CorpusCoverage {
        schema: "fln.canon.shadow-cell",
        version: 1,
        exercise: "round trip and re-encode byte identity of a complete generic \
                   shadow-run cell binding mode/profile/epoch roots, separate \
                   claim/evidence axes, fixture and Parity identities, versioned \
                   engines and policy, and a continued-sampling obligation",
        run: exercise_shadow_cell,
    },
    CorpusCoverage {
        schema: "fln.canon.shadow-semantic-ndjson",
        version: 1,
        exercise: "build a canonical shadow publication, recover its append-only frame \
                   through the independent NDJSON parser, and prove operational \
                   telemetry cannot move the semantic projection root",
        run: exercise_shadow_semantic_ndjson,
    },
    CorpusCoverage {
        schema: "fln.canon.shadow-telemetry-ndjson",
        version: 1,
        exercise: "build two publications of one semantic cell with different worker \
                   and latency observations, recover both independently, and prove \
                   telemetry moves only its own and the outer publication root",
        run: exercise_shadow_telemetry_ndjson,
    },
    CorpusCoverage {
        schema: "fln.canon.declaration-certificate",
        version: 1,
        exercise: "construct, encode, decode and byte-identically re-encode a \
                   candidate-only theorem certificate binding every producer, \
                   environment, policy and fuel root around a shared term DAG, one \
                   literal-reduction hint and one advisory extension",
        run: exercise_declaration_certificate,
    },
    CorpusCoverage {
        schema: "fln.env.module-provenance",
        version: 1,
        exercise: "round trip and re-encode byte identity of a two-module manifest with \
                   an import edge, an uncaptured import, declarations, extra \
                   declarations, one extension contribution, and a partial-capture \
                   completeness record, plus root stability across the decode",
        run: exercise_module_provenance,
    },
    CorpusCoverage {
        schema: "fln.env.module-provenance.entry-id",
        version: 1,
        exercise: "determinism and discrimination of the derivation: equal inputs give \
                   one id, and a changed payload, descriptor name or epoch each give \
                   another; a one-way content identity, so no round trip",
        run: exercise_entry_id,
    },
    CorpusCoverage {
        schema: "fln.verdict.cnf",
        version: 1,
        exercise: "round trip and re-encode byte identity of a three-variable formula, \
                   under SchemaLimits::default()",
        run: exercise_cnf,
    },
    CorpusCoverage {
        schema: "fln.verdict.sat-model",
        version: 1,
        exercise: "round trip and re-encode byte identity of a total assignment, and \
                   distinctness from the CNF encoding of the same formula",
        run: exercise_sat_model,
    },
    CorpusCoverage {
        schema: "fln.verdict.unsat-proof",
        version: 1,
        exercise: "round trip and re-encode byte identity of a resolution proof \
                   concluding the empty clause, decoded against its own CNF",
        run: exercise_unsat_proof,
    },
];

// ---------------------------------------------------------------------------
// Exercise support
// ---------------------------------------------------------------------------

/// Bind an exercise to the registry row it was handed.
///
/// Without this an exercise could sit under the wrong row — covering one format twice
/// while another goes untested — and the name join would still pass, because the join
/// checks that a row *has* an exercise, not that the exercise is about that row.
fn bind(row: &SchemaRow, declared: SchemaId) -> Result<(), String> {
    if row.id == declared {
        return Ok(());
    }
    Err(format!(
        "this exercise demonstrates {}/{} but is registered under {}/{}; a coverage row \
         and its exercise must be about the same format",
        declared.name, declared.version, row.id.name, row.id.version
    ))
}

/// Bind against a format whose owner declares its own `SchemaId` type (fln-verdict does
/// not use fln-hash's, since it sits above it in the crate map).
fn bind_foreign(row: &SchemaRow, name: &str, version: u16) -> Result<(), String> {
    if row.id.name == name && row.id.version == version {
        return Ok(());
    }
    Err(format!(
        "this exercise demonstrates {name}/{version} but is registered under {}/{}",
        row.id.name, row.id.version
    ))
}

fn ok<T, E: std::fmt::Debug>(result: Result<T, E>, what: &str) -> Result<T, String> {
    result.map_err(|error| format!("{what}: {error:?}"))
}

/// The bytes a self-describing encoding of `id` must begin with.
fn schema_prefix(id: SchemaId) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(id);
    writer.into_bytes()
}

/// Encode, decode, re-encode: value equality *and* byte identity, plus the self-
/// describing header.
///
/// Byte identity is the half that matters for a durable format. Value equality alone
/// passes for an encoder with freedom in it — two encodings of one value — which is
/// exactly what "exactly one valid byte encoding per value" forbids.
fn round_trip<T>(value: &T, label: &str) -> Result<(), String>
where
    T: Canonical + PartialEq + std::fmt::Debug,
{
    let bytes = value.to_canonical_bytes();
    let prefix = schema_prefix(T::SCHEMA);
    if !bytes.starts_with(&prefix) {
        return Err(format!(
            "{label}: the encoding does not begin with its own schema header ({}/{}), \
             so the bytes are not self-describing",
            T::SCHEMA.name,
            T::SCHEMA.version
        ));
    }
    let decoded = ok(T::from_canonical_bytes(&bytes), &format!("{label}: decode"))?;
    if decoded != *value {
        return Err(format!("{label}: decoded value differs from the original"));
    }
    if decoded.to_canonical_bytes() != bytes {
        return Err(format!(
            "{label}: re-encoding the decoded value is not byte-identical, so the \
             format has encoder freedom"
        ));
    }
    Ok(())
}

fn n(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

// ---------------------------------------------------------------------------
// The term plane (fln-hash)
// ---------------------------------------------------------------------------

fn exercise_name(row: &SchemaRow) -> Result<(), String> {
    bind(row, <Name as Canonical>::SCHEMA)?;
    let cases = [
        ("anonymous", Name::anonymous()),
        ("string", Name::from_components(["Lean", "Meta"])),
        ("numeric", Name::num(n("_uniq"), 231)),
        // Beyond UInt64.size: the shape that made a display-form witness collide in
        // bead franken_lean-f6br.
        (
            "overflowing",
            Name::num_overflowing(Name::anonymous(), u64::MAX),
        ),
    ];
    for (label, value) in cases {
        round_trip(&value, label)?;
    }
    Ok(())
}

fn exercise_level(row: &SchemaRow) -> Result<(), String> {
    bind(row, <Level as Canonical>::SCHEMA)?;
    let u = Level::param(n("u"));
    let v = Level::param(n("v"));
    let cases = [
        ("zero", Level::zero()),
        ("param", u.clone()),
        ("succ", ok(u.clone().succ(), "succ")?),
        ("max", ok(Level::max(u.clone(), v.clone()), "max")?),
        ("imax", ok(Level::imax(u.clone(), v), "imax")?),
        ("mvar", Level::mvar(LMVarId(Name::num(n("_lmvar"), 1)))),
    ];
    for (label, value) in cases {
        round_trip(&value, label)?;
    }
    Ok(())
}

fn exercise_expr(row: &SchemaRow) -> Result<(), String> {
    bind(row, <Expr as Canonical>::SCHEMA)?;
    let nat = Expr::const_(n("Nat"), Vec::new());
    let zero = ok(Expr::bvar(0), "bvar")?;
    let mut data = KVMap::new();
    data.insert(n("pp.unicode"), DataValue::OfBool(true));
    // One value per ExprNode variant. The registry row says "a term-plane expression";
    // a corpus that exercised eight of twelve shapes would be claiming that row while
    // leaving four encodings unwitnessed.
    let cases = [
        ("bvar", zero.clone()),
        ("fvar", Expr::fvar(FVarId(n("x")))),
        ("mvar", Expr::mvar(MVarId(n("m")))),
        ("sort", Expr::sort(Level::zero())),
        ("const", Expr::const_(n("Foo"), vec![Level::zero()])),
        ("app", Expr::app(nat.clone(), zero.clone())),
        (
            "lam",
            Expr::lam(n("y"), nat.clone(), zero.clone(), BinderInfo::Default),
        ),
        (
            "forall",
            Expr::forall_e(n("y"), nat.clone(), zero.clone(), BinderInfo::Implicit),
        ),
        (
            "let",
            Expr::let_e(n("y"), nat.clone(), zero.clone(), zero.clone(), false),
        ),
        ("lit_nat", Expr::lit(Literal::Nat(NatLit::from_u64(7)))),
        ("lit_str", Expr::lit(Literal::Str("seven".to_string()))),
        ("mdata", Expr::mdata(data, nat.clone())),
        ("proj", Expr::proj(n("Prod"), 1, nat)),
    ];
    for (label, value) in cases {
        round_trip(&value, label)?;
    }
    Ok(())
}

fn kvmap(pairs: [(&str, DataValue); 6]) -> KVMap {
    let mut map = KVMap::new();
    for (key, value) in pairs {
        map.insert(n(key), value);
    }
    map
}

fn six_values() -> [(&'static str, DataValue); 6] {
    [
        ("s", DataValue::OfString("text".to_string())),
        ("b", DataValue::OfBool(true)),
        ("n", DataValue::OfName(Name::from_components(["A", "B"]))),
        ("nat", DataValue::OfNat(u64::MAX)),
        ("int", DataValue::OfInt(i64::MIN)),
        ("i", DataValue::OfInt(0)),
    ]
}

fn exercise_kvmap(row: &SchemaRow) -> Result<(), String> {
    bind(row, <KVMap as Canonical>::SCHEMA)?;
    let map = kvmap(six_values());
    round_trip(&map, "all six DataValue constructors")?;

    // Order is part of the value. If it were not, this format and the set projection
    // below would be the same format, and one of the two registry rows would be a lie.
    let mut reversed = six_values();
    reversed.reverse();
    let flipped = kvmap(reversed);
    round_trip(&flipped, "reversed")?;
    if map.to_canonical_bytes() == flipped.to_canonical_bytes() {
        return Err(
            "two maps with the same pairs in different insertion order encoded \
             identically, so the ordered format is not order-sensitive"
                .to_string(),
        );
    }
    Ok(())
}

fn exercise_kvmap_set(row: &SchemaRow) -> Result<(), String> {
    bind(row, SCHEMA_KVMAP_SET)?;
    let map = kvmap(six_values());
    let mut reversed = six_values();
    reversed.reverse();
    let flipped = kvmap(reversed);

    let Some(set_bytes) = kvmap_canonical_set_bytes(&map) else {
        return Err("the set projection refused a duplicate-free map".to_string());
    };
    let Some(flipped_bytes) = kvmap_canonical_set_bytes(&flipped) else {
        return Err("the set projection refused a duplicate-free map".to_string());
    };
    if set_bytes != flipped_bytes {
        return Err(
            "the set projection is not permutation invariant, which is the whole \
             property it exists to provide"
                .to_string(),
        );
    }
    if !set_bytes.starts_with(&schema_prefix(SCHEMA_KVMAP_SET)) {
        return Err(
            "the set projection does not carry its own schema header, so its preimages \
             could be confused with the ordered encoding's"
                .to_string(),
        );
    }
    if set_bytes == map.to_canonical_bytes() {
        return Err(
            "the set projection and the ordered encoding agree byte-for-byte, \
                    so they are one format wearing two registry rows"
                .to_string(),
        );
    }

    // Duplicate keys are representable and have no honest set view; the projection must
    // refuse rather than pick a winner.
    let mut duplicated = KVMap::new();
    duplicated.insert(n("k"), DataValue::OfNat(1));
    duplicated.insert(n("k"), DataValue::OfNat(2));
    if duplicated.len() == 2 && kvmap_canonical_set_bytes(&duplicated).is_some() {
        return Err(
            "the set projection accepted a duplicate-keyed map instead of refusing; \
             two maps the ordered format separates would share a set identity"
                .to_string(),
        );
    }
    Ok(())
}

fn exercise_diag(row: &SchemaRow) -> Result<(), String> {
    bind(row, <Diagnostic as Canonical>::SCHEMA)?;
    let diagnostic = Diagnostic {
        file_name: "Corpus.lean".to_string(),
        pos: Position {
            line: 12,
            column: 3,
        },
        end_pos: Some(Position {
            line: 12,
            column: 19,
        }),
        severity: Severity::Error,
        error_name: Some(Name::from_components(["Lean", "kernelException"])),
        caption: "type mismatch".to_string(),
        value: ErrorValue::KernelRejection {
            decl: Name::from_components(["Corpus", "thm"]),
            stable_error_class: "type_mismatch".to_string(),
            message: "expected Nat".to_string(),
        },
    };
    round_trip(&diagnostic, "kernel rejection")?;

    // The structural-budget resource tag is what forced v1 -> v2. Covering the row
    // without covering the value that moved it would leave the corpus asserting a
    // version it has not actually exercised.
    let inconclusive = Diagnostic {
        value: ErrorValue::KernelInconclusive {
            decl: Name::from_components(["Corpus", "thm"]),
            resource: ResourceReason::StructuralBudget {
                unit: StructuralUnit::ProducedNodes,
            },
        },
        end_pos: None,
        error_name: None,
        caption: String::new(),
        severity: Severity::Information,
        ..diagnostic
    };
    round_trip(
        &inconclusive,
        "kernel inconclusive under a structural budget",
    )?;

    // Version 3 added the distinct execution-step tag. A version-only update above
    // would make the projection join green while leaving the new encoding unexercised.
    let execution_steps = Diagnostic {
        value: ErrorValue::KernelInconclusive {
            decl: Name::from_components(["Corpus", "thm"]),
            resource: ResourceReason::ExecutionSteps,
        },
        ..inconclusive
    };
    round_trip(
        &execution_steps,
        "kernel inconclusive under an execution-step budget",
    )
}

// ---------------------------------------------------------------------------
// Generic shadow promotion authority (fln-hash)
// ---------------------------------------------------------------------------

fn shadow_root(seed: u8) -> ContentRoot {
    ContentRoot::new([seed; 32])
}

fn shadow_engine(id: u128, version: u64, seed: u8) -> EngineVersionV1 {
    EngineVersionV1 {
        engine_id: id,
        version,
        binary_root: shadow_root(seed),
    }
}

fn shadow_policy() -> PolicyVersionV1 {
    PolicyVersionV1 {
        policy_id: CgsePolicyId::new(300),
        version: 2,
        policy_root: shadow_root(30),
    }
}

fn shadow_cell() -> Result<ShadowCellV1, String> {
    let policy = shadow_policy();
    let fixture_manifest = FixtureManifestV1::from_fixture_ids(vec![501, 502, 503])
        .map_err(|error| format!("fixture manifest: {error:?}"))?;
    ShadowCellV1::new(ShadowCellSpecV1 {
        scope: ShadowScopeV1 {
            workload_id: 200,
            workload_root: shadow_root(20),
            epoch: EpochId::new(201),
            epoch_root: shadow_root(21),
            mode: Mode::Sound,
            reproducibility: ReproducibilityProfile::Certified,
            build_profile: BuildProfileId::new(202),
            profile_root: shadow_root(22),
            target: TargetId::new(203),
            target_root: shadow_root(23),
        },
        baseline: ProductV1 {
            engine: shadow_engine(210, 4, 24),
            product_root: shadow_root(25),
            semantic_result: SemanticResultV1::Accepted {
                result_root: shadow_root(26),
            },
        },
        candidate: CandidateResultV1::Complete(ProductV1 {
            engine: shadow_engine(211, 8, 27),
            product_root: shadow_root(28),
            semantic_result: SemanticResultV1::Accepted {
                result_root: shadow_root(26),
            },
        }),
        comparison_class: ComparisonClassV1::ExactParity,
        fixture_manifest,
        policy,
        claim_type: ClaimTypeV1::BoundedModel,
        parity_row: ParityRowV1 {
            row_id: 220,
            row_root: shadow_root(29),
        },
        sampling: SamplingObligationV1 {
            policy,
            seed_root: shadow_root(31),
            divisor: 16,
            required_initial_passes: 3,
        },
    })
    .map_err(|error| format!("shadow cell: {error:?}"))
}

fn recover_shadow(publication: &ShadowPublicationV1) -> Result<(), String> {
    let recovered = recover_journal(&publication.journal_frame())
        .into_complete()
        .map_err(|non_authoritative| format!("recovery non-authoritative: {non_authoritative:?}"))?
        .map_err(|error| format!("recovery refused publication: {error:?}"))?;
    let latest = recovered
        .latest
        .ok_or_else(|| "recovery returned no complete publication".to_string())?;
    if latest.publication.cell() != publication.cell() {
        return Err("recovery returned a different shadow cell".to_string());
    }
    Ok(())
}

fn exercise_shadow_cell(row: &SchemaRow) -> Result<(), String> {
    bind(row, SCHEMA_SHADOW_CELL)?;
    round_trip(&shadow_cell()?, "generic shadow cell")
}

fn exercise_shadow_semantic_ndjson(row: &SchemaRow) -> Result<(), String> {
    bind(row, SCHEMA_SHADOW_SEMANTIC_NDJSON)?;
    let cell = shadow_cell()?;
    let first = ShadowPublicationV1::build(
        cell.clone(),
        ShadowTelemetryV1 {
            attempts: 1,
            latency_micros: 10,
            worker_count: 1,
            dropped_events: 0,
        },
    )
    .map_err(|error| format!("build semantic publication: {error:?}"))?;
    let second = ShadowPublicationV1::build(
        cell,
        ShadowTelemetryV1 {
            attempts: 99,
            latency_micros: 1_000_000,
            worker_count: 32,
            dropped_events: 7,
        },
    )
    .map_err(|error| format!("build semantic publication variant: {error:?}"))?;
    if !first
        .semantic_ndjson()
        .starts_with("{\"schema\":\"fln.canon.shadow-semantic-ndjson/1\"")
    {
        return Err("semantic NDJSON does not begin with its registered schema".to_string());
    }
    if first.semantic_root() != second.semantic_root() {
        return Err("operational telemetry moved semantic shadow authority".to_string());
    }
    recover_shadow(&first)?;
    recover_shadow(&second)
}

fn exercise_shadow_telemetry_ndjson(row: &SchemaRow) -> Result<(), String> {
    bind(row, SCHEMA_SHADOW_TELEMETRY_NDJSON)?;
    let cell = shadow_cell()?;
    let first = ShadowPublicationV1::build(
        cell.clone(),
        ShadowTelemetryV1 {
            attempts: 1,
            latency_micros: 10,
            worker_count: 1,
            dropped_events: 0,
        },
    )
    .map_err(|error| format!("build telemetry publication: {error:?}"))?;
    let second = ShadowPublicationV1::build(
        cell,
        ShadowTelemetryV1 {
            attempts: 2,
            latency_micros: 11,
            worker_count: 8,
            dropped_events: 1,
        },
    )
    .map_err(|error| format!("build telemetry publication variant: {error:?}"))?;
    if !first
        .telemetry_ndjson()
        .starts_with("{\"schema\":\"fln.canon.shadow-telemetry-ndjson/1\"")
    {
        return Err("telemetry NDJSON does not begin with its registered schema".to_string());
    }
    if first.semantic_root() != second.semantic_root() {
        return Err("telemetry changed the semantic projection".to_string());
    }
    if first.telemetry_root() == second.telemetry_root()
        || first.publication_root() == second.publication_root()
    {
        return Err(
            "changed telemetry did not move its own root and the outer publication root"
                .to_string(),
        );
    }
    recover_shadow(&first)?;
    recover_shadow(&second)
}

fn exercise_declaration_certificate(row: &SchemaRow) -> Result<(), String> {
    bind(row, SCHEMA_DECLARATION_CERTIFICATE)?;

    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(3),
            },
        ],
    };
    let binding = CertificateBindingV1 {
        epoch: EpochId::new(1),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Certified,
        build_profile: BuildProfileId::new(2),
        consensus_policy: ConsensusPolicyV1::Paranoid,
        environment_root: ContentRoot::new([1; 32]),
        dependency_roots: vec![ContentRoot::new([2; 32])],
        declaration_root: ContentRoot::new([3; 32]),
        term_root: term_dag.content_root(),
        kernel_build_root: ContentRoot::new([4; 32]),
        checker_build_root: ContentRoot::new([5; 32]),
        policy_root: ContentRoot::new([6; 32]),
        engine_id: "fln-kernel-corpus".to_string(),
        engine_version: 1,
        fuel: FuelProfileV1 {
            profile_id: 7,
            heartbeats: 8,
            recursion_depth: 9,
            reduction_steps: 10,
            expanded_weight: 11,
            allocation_bytes: 12,
        },
    };
    let certificate = ok(
        DeclarationCertificateV1::new(
            binding,
            CertificateJudgmentV1::CheckDeclaration {
                name: Name::from_components(["Corpus", "certificateWitness"]),
                kind: DeclarationKindV1::Theorem,
                type_node: TermNodeId::new(0),
                value_node: Some(TermNodeId::new(1)),
            },
            ClaimedResultV1::Accepted,
            term_dag,
            vec![ReductionHintV1::NatOperation {
                operation: NatOperationV1::Add,
                inputs: [NatLit::from_u64(1), NatLit::from_u64(2)],
                result: NatHintResultV1::Nat(NatLit::from_u64(3)),
            }],
            vec![CertificateExtensionV1::advisory(
                1,
                b"corpus-preserved".to_vec(),
            )],
        ),
        "construct declaration certificate",
    )?;
    let bytes = ok(
        certificate.to_canonical_bytes(),
        "encode declaration certificate",
    )?;
    if !bytes.starts_with(&schema_prefix(SCHEMA_DECLARATION_CERTIFICATE)) {
        return Err(
            "declaration certificate does not carry its registered schema header".to_string(),
        );
    }
    let decoded = DeclarationCertificateV1::from_canonical_bytes(&bytes)
        .into_complete()
        .map_err(|outcome| format!("declaration certificate decode did not complete: {outcome:?}"))?
        .map_err(|error| format!("declaration certificate decode refused: {error:?}"))?;
    if decoded != certificate {
        return Err("decoded declaration certificate differs from its source".to_string());
    }
    if ok(
        decoded.to_canonical_bytes(),
        "re-encode declaration certificate",
    )? != bytes
    {
        return Err(
            "re-encoded declaration certificate is not byte-identical to its source".to_string(),
        );
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Grimoire's identities (fln-env)
// ---------------------------------------------------------------------------

fn epoch() -> ModuleEpoch {
    ModuleEpoch::new("v4.32.0", "0123456789abcdef0123456789abcdef01234567")
}

fn extension_descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: Name::from_components(["Corpus", "Extension"]),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

fn evidence(seed: u8) -> ArtifactEvidence {
    ArtifactEvidence {
        epoch: epoch(),
        content_digest: Digest([seed; 32]),
        producer: ArtifactProducer::Reference,
        grade: ArtifactGrade::OracleFixture,
    }
}

fn exercise_module_provenance(row: &SchemaRow) -> Result<(), String> {
    bind(row, MODULE_PROVENANCE_SCHEMA)?;
    let base = ModuleId::new(Name::from_components(["Corpus", "Base"]));
    let leaf = ModuleId::new(Name::from_components(["Corpus", "Leaf"]));
    // Imported but not captured, so the leaf's completeness record has a real missing
    // dependency to declare. The manifest cross-checks declared gaps against the graph,
    // so an invented one is refused — which is the validator being right.
    let absent = ModuleId::new(Name::from_components(["Corpus", "Absent"]));

    let base_record = ModuleContributionRecord::new(
        ModuleRecord::new(base.clone(), true, Vec::new(), evidence(1)),
        vec![Name::from_components(["Corpus", "Base", "d"])],
        Vec::new(),
        Vec::new(),
        ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            Vec::new(),
        ),
    );
    let leaf_record = ModuleContributionRecord::new(
        ModuleRecord::new(
            leaf,
            true,
            vec![
                DirectImport::new(base, true, true, false),
                DirectImport::new(absent.clone(), false, false, true),
            ],
            evidence(2),
        ),
        vec![Name::from_components(["Corpus", "Leaf", "thm"])],
        vec![Name::from_components(["Corpus", "Leaf", "thm", "aux"])],
        vec![ExtensionContribution::new(
            extension_descriptor(),
            0,
            Digest([3; 32]),
            vec![ExtensionEntryId::derive(
                &epoch(),
                &extension_descriptor(),
                b"corpus-payload",
            )],
        )],
        // The partial arm, so the encoding of a non-complete capture is witnessed too.
        // Transparency is derived from the contributions rather than asserted here —
        // the manifest cross-checks it, so `Mixed` beside one understood payload is
        // refused.
        ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
            vec![absent],
        ),
    );

    let limits = ModuleProvenanceLimits::default();
    let manifest = ok(
        ModuleProvenanceManifest::new(epoch(), vec![base_record, leaf_record], limits),
        "build manifest",
    )?;

    let bytes = manifest.to_canonical_bytes();
    if !bytes.starts_with(&schema_prefix(MODULE_PROVENANCE_SCHEMA)) {
        return Err("the manifest encoding does not begin with its schema header".to_string());
    }
    let decoded = ok(
        ModuleProvenanceManifest::from_canonical_bytes(&bytes, limits),
        "decode manifest",
    )?;
    if decoded != manifest {
        return Err("the decoded manifest differs from the original".to_string());
    }
    if decoded.to_canonical_bytes() != bytes {
        return Err("re-encoding the decoded manifest is not byte-identical".to_string());
    }
    // The root is a function of the canonical value, so a decode that preserved the
    // bytes but not the identity would be a silent fork.
    if decoded.root() != manifest.root() {
        return Err("the manifest root did not survive the round trip".to_string());
    }
    Ok(())
}

fn exercise_entry_id(row: &SchemaRow) -> Result<(), String> {
    bind(row, EXTENSION_ENTRY_ID_SCHEMA)?;
    let descriptor = extension_descriptor();
    let payload = b"corpus-payload".as_slice();
    let identity = ExtensionEntryId::derive(&epoch(), &descriptor, payload);

    if ExtensionEntryId::derive(&epoch(), &descriptor, payload) != identity {
        return Err("the derivation is not deterministic on equal inputs".to_string());
    }

    // Discrimination on each input it is permitted to depend on. A derivation that
    // ignores one of them is the lossy-projection defect of bead franken_lean-f6br.
    if ExtensionEntryId::derive(&epoch(), &descriptor, b"corpus-payloae") == identity {
        return Err("a changed payload did not change the entry id".to_string());
    }
    let renamed = ExtensionDescriptor {
        name: Name::from_components(["Corpus", "Other"]),
        ..descriptor.clone()
    };
    if ExtensionEntryId::derive(&epoch(), &renamed, payload) == identity {
        return Err("a changed descriptor name did not change the entry id".to_string());
    }
    let other_epoch = ModuleEpoch::new("v4.33.0", "0123456789abcdef0123456789abcdef01234567");
    if ExtensionEntryId::derive(&other_epoch, &descriptor, payload) == identity {
        return Err("a changed epoch did not change the entry id".to_string());
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// The Verdict wire formats (fln-verdict)
// ---------------------------------------------------------------------------

fn variable(raw: u32) -> Result<VariableId, String> {
    ok(VariableId::new(raw), "variable id")
}

fn clause_id(raw: u64) -> Result<ClauseId, String> {
    ok(ClauseId::new(raw), "clause id")
}

fn clause(dimacs: &[i64]) -> Result<Clause, String> {
    let mut literals = Vec::with_capacity(dimacs.len());
    for value in dimacs {
        literals.push(ok(SatLiteral::from_dimacs(*value), "literal")?);
    }
    ok(Clause::new(literals), "clause")
}

fn sat_formula() -> Result<Cnf, String> {
    ok(
        Cnf::new(
            3,
            vec![
                InputClause::new(clause_id(3)?, clause(&[-1, 3])?),
                InputClause::new(clause_id(1)?, clause(&[1, -2])?),
                InputClause::new(clause_id(2)?, clause(&[2])?),
            ],
            SchemaLimits::default(),
        ),
        "build CNF",
    )
}

fn unsat_formula() -> Result<Cnf, String> {
    ok(
        Cnf::new(
            1,
            vec![
                InputClause::new(clause_id(1)?, clause(&[1])?),
                InputClause::new(clause_id(2)?, clause(&[-1])?),
            ],
            SchemaLimits::default(),
        ),
        "build UNSAT CNF",
    )
}

fn exercise_cnf(row: &SchemaRow) -> Result<(), String> {
    bind_foreign(row, CNF_SCHEMA.name, CNF_SCHEMA.version)?;
    let cnf = sat_formula()?;
    let bytes = cnf.to_canonical_bytes();
    let decoded = ok(
        Cnf::from_canonical_bytes(&bytes, SchemaLimits::default()),
        "decode CNF",
    )?;
    if decoded != cnf {
        return Err("the decoded CNF differs from the original".to_string());
    }
    if decoded.to_canonical_bytes() != bytes {
        return Err("re-encoding the decoded CNF is not byte-identical".to_string());
    }
    Ok(())
}

fn exercise_sat_model(row: &SchemaRow) -> Result<(), String> {
    bind_foreign(row, SAT_MODEL_SCHEMA.name, SAT_MODEL_SCHEMA.version)?;
    let model = ok(
        SatModel::new(
            3,
            vec![
                Assignment::new(variable(3)?, true),
                Assignment::new(variable(1)?, true),
                Assignment::new(variable(2)?, true),
            ],
            SchemaLimits::default(),
        ),
        "build model",
    )?;
    let bytes = model.to_canonical_bytes();
    let decoded = ok(
        SatModel::from_canonical_bytes(&bytes, SchemaLimits::default()),
        "decode model",
    )?;
    if decoded != model {
        return Err("the decoded model differs from the original".to_string());
    }
    if decoded.to_canonical_bytes() != bytes {
        return Err("re-encoding the decoded model is not byte-identical".to_string());
    }
    // Three wire formats sharing one framing must still be distinguishable, or a
    // decoder could accept the wrong artifact.
    if bytes == sat_formula()?.to_canonical_bytes() {
        return Err("a model and a CNF encoded identically".to_string());
    }
    Ok(())
}

fn exercise_unsat_proof(row: &SchemaRow) -> Result<(), String> {
    bind_foreign(row, UNSAT_PROOF_SCHEMA.name, UNSAT_PROOF_SCHEMA.version)?;
    let cnf = unsat_formula()?;
    let proof = ok(
        UnsatProof::new(
            &cnf,
            vec![
                ProofStep::Derive {
                    id: clause_id(3)?,
                    clause: clause(&[])?,
                    rule: ProofRule::Resolution {
                        pivot: variable(1)?,
                        positive_parent: clause_id(1)?,
                        negative_parent: clause_id(2)?,
                    },
                },
                ProofStep::Conclude {
                    empty_clause: clause_id(3)?,
                },
            ],
            SchemaLimits::default(),
        ),
        "build proof",
    )?;
    let bytes = proof.to_canonical_bytes();
    let decoded = ok(
        UnsatProof::from_canonical_bytes(&bytes, &cnf, SchemaLimits::default()),
        "decode proof",
    )?;
    if decoded != proof {
        return Err("the decoded proof differs from the original".to_string());
    }
    if decoded.to_canonical_bytes() != bytes {
        return Err("re-encoding the decoded proof is not byte-identical".to_string());
    }
    Ok(())
}
