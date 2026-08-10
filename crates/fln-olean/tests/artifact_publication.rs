#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Barrier, OnceLock};
use std::time::{Duration, Instant};

use fln_core::expr::Expr;
use fln_core::name::Name;
use fln_core::scratch::{ARTIFACT_PUBLICATION_PREFIX, ScratchRoot};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_hash::canon::{Canonical, SCHEMA_NAME, SchemaId};
use fln_olean::artifact::{
    ArtifactError, ArtifactIdentityPlane, ArtifactLimits, ArtifactMemberInput, ArtifactPointer,
    ArtifactSetManifest, ArtifactStore, ArtifactStoreDirectory, PublicationControl,
    PublicationIoPoint, PublicationPoint, artifact_byte_hash, artifact_semantic_hash,
};
use fln_olean::format;
use fln_olean::ilean::{Ilean, IleanBudget, IleanImport, decode_ilean, encode_ilean};
use fln_olean::region::{ModuleImport, OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};
use fln_rt::region::AtomicWriteStep;

static ALPHA_SEMANTICS: OnceLock<Vec<u8>> = OnceLock::new();
static BETA_SEMANTICS: OnceLock<Vec<u8>> = OnceLock::new();
static DEMO_SEMANTICS: OnceLock<Vec<u8>> = OnceLock::new();

type CancellationTarget = (&'static str, fn(PublicationPoint) -> bool, bool);
type PointerFaultTarget = (
    &'static str,
    fn(PublicationIoPoint) -> bool,
    ArtifactPointer,
    bool,
);
type GenerationFaultTarget = (&'static str, fn(PublicationIoPoint) -> bool, Option<bool>);
const KILL_IO_PHASES: [&str; 23] = [
    "store-root-create",
    "generations-directory-create",
    "roots-directory-create",
    "store-root-sync",
    "generation-create",
    "generations-directory-sync",
    "member-create",
    "member-write",
    "member-sync",
    "manifest-create",
    "manifest-write",
    "manifest-sync",
    "generation-directory-sync",
    "root-pointer-create",
    "root-pointer-write",
    "root-pointer-file-sync",
    "root-pointer-rename",
    "root-pointer-directory-sync",
    "active-pointer-create",
    "active-pointer-write",
    "active-pointer-file-sync",
    "active-pointer-rename",
    "active-pointer-directory-sync",
];

struct InjectIoAt(fn(PublicationIoPoint) -> bool);

impl PublicationControl for InjectIoAt {
    fn should_cancel(&mut self, _point: PublicationPoint) -> bool {
        false
    }

    fn injected_io_error(&mut self, point: PublicationIoPoint) -> Option<std::io::ErrorKind> {
        (self.0)(point).then_some(std::io::ErrorKind::StorageFull)
    }
}

struct ParkAtIo {
    phase: String,
    ready_path: PathBuf,
}

impl PublicationControl for ParkAtIo {
    fn should_cancel(&mut self, _point: PublicationPoint) -> bool {
        false
    }

    fn injected_io_error(&mut self, point: PublicationIoPoint) -> Option<std::io::ErrorKind> {
        if publication_io_phase(point) == self.phase {
            std::fs::write(&self.ready_path, b"ready\n").expect("publish kill-drill marker");
            loop {
                std::thread::park();
            }
        }
        None
    }
}

fn publication_io_phase(point: PublicationIoPoint) -> &'static str {
    match point {
        PublicationIoPoint::StoreRootCreate => "store-root-create",
        PublicationIoPoint::StoreDirectoryCreate {
            directory: ArtifactStoreDirectory::Generations,
        } => "generations-directory-create",
        PublicationIoPoint::StoreDirectoryCreate {
            directory: ArtifactStoreDirectory::Roots,
        } => "roots-directory-create",
        PublicationIoPoint::StoreRootSync => "store-root-sync",
        PublicationIoPoint::GenerationDirectoryCreate => "generation-create",
        PublicationIoPoint::GenerationsDirectorySync => "generations-directory-sync",
        PublicationIoPoint::MemberCreate { .. } => "member-create",
        PublicationIoPoint::MemberChunkWrite { .. } => "member-write",
        PublicationIoPoint::MemberFileSync { .. } => "member-sync",
        PublicationIoPoint::ManifestCreate => "manifest-create",
        PublicationIoPoint::ManifestWrite { .. } => "manifest-write",
        PublicationIoPoint::ManifestFileSync => "manifest-sync",
        PublicationIoPoint::GenerationDirectorySync => "generation-directory-sync",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::RootBinding,
            step: AtomicWriteStep::CreateStaging,
        } => "root-pointer-create",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::RootBinding,
            step: AtomicWriteStep::WriteChunk { .. },
        } => "root-pointer-write",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::RootBinding,
            step: AtomicWriteStep::SyncStaging,
        } => "root-pointer-file-sync",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::RootBinding,
            step: AtomicWriteStep::RenameTarget,
        } => "root-pointer-rename",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::RootBinding,
            step: AtomicWriteStep::SyncDirectory,
        } => "root-pointer-directory-sync",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::Active,
            step: AtomicWriteStep::CreateStaging,
        } => "active-pointer-create",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::Active,
            step: AtomicWriteStep::WriteChunk { .. },
        } => "active-pointer-write",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::Active,
            step: AtomicWriteStep::SyncStaging,
        } => "active-pointer-file-sync",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::Active,
            step: AtomicWriteStep::RenameTarget,
        } => "active-pointer-rename",
        PublicationIoPoint::PointerAtomic {
            pointer: ArtifactPointer::Active,
            step: AtomicWriteStep::SyncDirectory,
        } => "active-pointer-directory-sync",
    }
}

struct TestStore {
    store: ArtifactStore,
    _scratch: ScratchRoot,
}

impl Deref for TestStore {
    type Target = ArtifactStore;

    fn deref(&self) -> &ArtifactStore {
        &self.store
    }
}

fn store_at(path: impl Into<PathBuf>) -> ArtifactStore {
    ArtifactStore::new(path, ArtifactLimits::default())
}

fn scratch_store(label: &str) -> TestStore {
    scratch_store_with_limits(label, ArtifactLimits::default())
}

fn scratch_store_with_limits(label: &str, limits: ArtifactLimits) -> TestStore {
    let scratch = ScratchRoot::create(ARTIFACT_PUBLICATION_PREFIX, "artifact-publication", label)
        .expect("create artifact-publication scratch root");
    let store = ArtifactStore::new(scratch.path().to_path_buf(), limits);
    TestStore {
        store,
        _scratch: scratch,
    }
}

fn alpha_semantics() -> &'static [u8] {
    ALPHA_SEMANTICS.get_or_init(|| {
        Name::str(Name::str(Name::anonymous(), "Demo"), "Alpha").to_canonical_bytes()
    })
}

fn beta_semantics() -> &'static [u8] {
    BETA_SEMANTICS.get_or_init(|| {
        Name::str(Name::str(Name::anonymous(), "Demo"), "Beta").to_canonical_bytes()
    })
}

fn demo_semantics() -> &'static [u8] {
    DEMO_SEMANTICS.get_or_init(|| Name::str(Name::anonymous(), "Demo").to_canonical_bytes())
}

fn alpha_inputs() -> [ArtifactMemberInput<'static>; 4] {
    [
        ArtifactMemberInput::new("Demo.olean", b"olean-alpha", SCHEMA_NAME, alpha_semantics()),
        ArtifactMemberInput::new("Demo.ilean", b"ilean-alpha", SCHEMA_NAME, alpha_semantics()),
        ArtifactMemberInput::new(
            "Demo.server",
            b"server-alpha",
            SCHEMA_NAME,
            alpha_semantics(),
        ),
        ArtifactMemberInput::new("Demo.ir", b"ir-alpha", SCHEMA_NAME, alpha_semantics()),
    ]
}

fn beta_inputs() -> [ArtifactMemberInput<'static>; 4] {
    [
        ArtifactMemberInput::new("Demo.olean", b"olean-beta", SCHEMA_NAME, beta_semantics()),
        ArtifactMemberInput::new("Demo.ilean", b"ilean-beta", SCHEMA_NAME, beta_semantics()),
        ArtifactMemberInput::new("Demo.server", b"server-beta", SCHEMA_NAME, beta_semantics()),
        ArtifactMemberInput::new("Demo.ir", b"ir-beta", SCHEMA_NAME, beta_semantics()),
    ]
}

fn assert_generation_bytes(generation: &Path, expected: &[(&str, &[u8])]) {
    for (name, bytes) in expected {
        assert_eq!(
            std::fs::read(generation.join(name)).expect("manifested member is readable"),
            *bytes,
            "{name}"
        );
    }
}

#[test]
fn complete_cross_file_set_activates_and_resolves_as_one_generation() {
    let store = scratch_store("complete");
    let publication = store.publish(&alpha_inputs()).expect("publish alpha");
    let resolved = store.resolve_active().expect("resolve alpha");

    assert_eq!(resolved.root(), publication.root());
    assert_eq!(resolved.generation_name(), publication.generation_name());
    let names: Vec<&str> = resolved
        .manifest()
        .members()
        .iter()
        .map(|member| member.name())
        .collect();
    assert_eq!(
        names,
        ["Demo.ilean", "Demo.ir", "Demo.olean", "Demo.server"],
        "the manifest order is canonical, not caller order"
    );
    assert_generation_bytes(
        resolved.generation_dir(),
        &[
            ("Demo.olean", b"olean-alpha"),
            ("Demo.ilean", b"ilean-alpha"),
            ("Demo.server", b"server-alpha"),
            ("Demo.ir", b"ir-alpha"),
        ],
    );

    let repeated = store
        .publish(&alpha_inputs())
        .expect("same root is idempotent");
    assert_eq!(
        repeated.generation_name(),
        publication.generation_name(),
        "an already verified root binding is reused"
    );
}

#[test]
fn real_olean_writer_and_ilean_codec_publish_through_the_same_transaction() {
    let lean_version = format::PIN_TAG
        .strip_prefix('v')
        .expect("generated pin tag carries its version prefix");
    let imports = [ModuleImport {
        module: Name::str(Name::anonymous(), "Init"),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let constants = [ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: Name::str(Name::str(Name::anonymous(), "Demo"), "freshNat"),
            level_params: Vec::new(),
            type_: Expr::const_(Name::str(Name::anonymous(), "Nat"), Vec::new()),
        },
        is_unsafe: false,
    })];
    let olean = encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version,
            githash: format::PIN_COMMIT,
            base_addr: (format::REGION_ALIGN as u64) * 2,
        },
        WriteBudget::default(),
    )
    .expect("encode complete fresh module");
    let ilean_value = Ilean {
        version: format::ILEAN_VERSION,
        module: "Demo".to_string(),
        direct_imports: vec![IleanImport {
            module: "Init".to_string(),
            is_private: false,
            is_all: false,
            is_meta: false,
        }],
        references: BTreeMap::new(),
        decls: BTreeMap::new(),
    };
    let ilean = encode_ilean(&ilean_value, IleanBudget::default()).expect("encode complete .ilean");
    let members = [
        ArtifactMemberInput::new("Demo.olean", &olean.bytes, SCHEMA_NAME, demo_semantics()),
        ArtifactMemberInput::new("Demo.ilean", &ilean, SCHEMA_NAME, demo_semantics()),
    ];

    let store = scratch_store("real-codecs");
    store.publish(&members).expect("publish real codec outputs");
    let resolved = store.resolve_active().expect("resolve real codec outputs");
    let olean_bytes = std::fs::read(
        resolved
            .member_path("Demo.olean")
            .expect("olean is manifested"),
    )
    .expect("read published olean");
    let view = OleanView::parse(&olean_bytes).expect("published olean header");
    let module = view
        .module_data(WalkBudget::default())
        .expect("published ModuleData");
    assert!(!module.is_module);
    assert_eq!(module.imports, imports);
    assert_eq!(module.constants, 1);

    let ilean_bytes = std::fs::read(
        resolved
            .member_path("Demo.ilean")
            .expect("ilean is manifested"),
    )
    .expect("read published ilean");
    assert_eq!(
        decode_ilean(&ilean_bytes, IleanBudget::default()).expect("published .ilean"),
        ilean_value
    );
}

#[test]
fn semantic_and_stored_byte_identities_move_independently() {
    let semantic_a = artifact_semantic_hash(SCHEMA_NAME, alpha_semantics());
    let semantic_b = artifact_semantic_hash(SCHEMA_NAME, beta_semantics());
    let bytes_a = artifact_byte_hash(b"encoding one");
    let bytes_b = artifact_byte_hash(b"encoding two");

    assert_eq!(
        semantic_a,
        artifact_semantic_hash(SCHEMA_NAME, alpha_semantics())
    );
    assert_ne!(semantic_a, semantic_b);
    assert_ne!(bytes_a, bytes_b);
    assert_eq!(bytes_a, artifact_byte_hash(b"encoding one"));
}

#[test]
fn manifest_decode_is_total_over_every_truncation_and_single_bit_change() {
    let store = scratch_store("manifest-totality");
    let staged = store.stage(&alpha_inputs()).expect("stage alpha");
    let bytes = staged.manifest().canonical_bytes();
    let root = staged.root();

    for end in 0..bytes.len() {
        assert!(
            ArtifactSetManifest::from_canonical_bytes(&bytes[..end], ArtifactLimits::default())
                .is_err(),
            "truncation at {end} must refuse"
        );
    }
    for bit in 0..bytes.len() * 8 {
        let mut changed = bytes.to_vec();
        changed[bit / 8] ^= 1 << (bit % 8);
        if let Ok(manifest) =
            ArtifactSetManifest::from_canonical_bytes(&changed, ArtifactLimits::default())
        {
            assert_ne!(
                manifest.root(),
                root,
                "a changed canonical manifest cannot retain its set root"
            );
        }
    }
}

#[test]
fn names_duplicates_and_structural_budgets_fail_before_publication() {
    let store = scratch_store("input-refusal");
    for name in [
        "",
        ".",
        "..",
        "part/child",
        "part\\child",
        "bad\nname",
        "ARTIFACTS.fln",
    ] {
        let input = [ArtifactMemberInput::new(
            name,
            b"bytes",
            SCHEMA_NAME,
            alpha_semantics(),
        )];
        assert!(store.stage(&input).is_err(), "{name:?}");
    }

    let duplicate = [
        ArtifactMemberInput::new("Demo.olean", b"one", SCHEMA_NAME, alpha_semantics()),
        ArtifactMemberInput::new("Demo.olean", b"two", SCHEMA_NAME, beta_semantics()),
    ];
    assert!(matches!(
        store.stage(&duplicate),
        Err(ArtifactError::DuplicateMember { .. })
    ));

    for schema in [
        SchemaId {
            name: "fln.olean.unregistered",
            version: 1,
        },
        SchemaId {
            name: SCHEMA_NAME.name,
            version: SCHEMA_NAME.version + 1,
        },
    ] {
        let input = [ArtifactMemberInput::new(
            "Demo.olean",
            b"bytes",
            schema,
            alpha_semantics(),
        )];
        assert!(matches!(
            store.stage(&input),
            Err(ArtifactError::InvalidSemanticSchema { .. })
        ));
    }

    let tiny = scratch_store_with_limits("tiny-budget", ArtifactLimits::new(1, 32, 4, 8));
    assert!(matches!(
        tiny.stage(&alpha_inputs()),
        Err(ArtifactError::ResourceLimitExceeded { .. })
    ));
}

#[test]
fn explicit_recovery_requires_the_expected_root_and_preserves_active_state() {
    let store = scratch_store("recovery");
    let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
    let staged = store.stage(&beta_inputs()).expect("stage beta");
    let generation_name = staged.generation_name().to_string();
    let beta_root = staged.root();
    drop(staged);

    let still_alpha = store.resolve_active().expect("alpha remains active");
    assert_eq!(still_alpha.root(), alpha.root());
    assert!(
        store
            .recover_staged(&generation_name, alpha.root())
            .is_err()
    );

    let recovered = store
        .recover_staged(&generation_name, beta_root)
        .expect("recover exact beta generation");
    let bound = recovered.bind().expect("bind beta");
    assert_eq!(
        store
            .resolve_active()
            .expect("alpha is still active")
            .root(),
        alpha.root(),
        "binding a verified root is not activation"
    );
    bound.activate().expect("activate beta");
    assert_eq!(
        store.resolve_active().expect("beta active").root(),
        beta_root
    );
}

#[test]
fn modified_generation_member_is_refused_on_every_resolution() {
    let store = scratch_store("member-change");
    let publication = store.publish(&alpha_inputs()).expect("publish alpha");
    std::fs::write(
        publication.generation_dir().join("Demo.olean"),
        b"olean-ALPHA",
    )
    .expect("modify private test generation");
    assert!(matches!(
        store.resolve_active(),
        Err(ArtifactError::MemberByteHashMismatch { .. })
            | Err(ArtifactError::MemberLengthMismatch { .. })
    ));
}

#[test]
fn concurrent_activations_never_resolve_a_mixed_set() {
    let store = Arc::new(scratch_store("concurrent"));
    let start = Arc::new(Barrier::new(3));
    let alpha_store = Arc::clone(&store);
    let alpha_start = Arc::clone(&start);
    let alpha = std::thread::spawn(move || {
        alpha_start.wait();
        alpha_store
            .publish(&alpha_inputs())
            .expect("publish alpha")
            .root()
    });
    let beta_store = Arc::clone(&store);
    let beta_start = Arc::clone(&start);
    let beta = std::thread::spawn(move || {
        beta_start.wait();
        beta_store
            .publish(&beta_inputs())
            .expect("publish beta")
            .root()
    });
    start.wait();
    let alpha_root = alpha.join().expect("alpha publisher");
    let beta_root = beta.join().expect("beta publisher");

    let resolved = store.resolve_active().expect("one complete active root");
    if resolved.root() == alpha_root {
        assert_generation_bytes(
            resolved.generation_dir(),
            &[
                ("Demo.olean", b"olean-alpha"),
                ("Demo.ilean", b"ilean-alpha"),
                ("Demo.server", b"server-alpha"),
                ("Demo.ir", b"ir-alpha"),
            ],
        );
    } else {
        assert_eq!(resolved.root(), beta_root);
        assert_generation_bytes(
            resolved.generation_dir(),
            &[
                ("Demo.olean", b"olean-beta"),
                ("Demo.ilean", b"ilean-beta"),
                ("Demo.server", b"server-beta"),
                ("Demo.ir", b"ir-beta"),
            ],
        );
    }
}

#[test]
fn cancellation_at_every_observation_point_preserves_old_or_unreachable_state() {
    let targets: [CancellationTarget; 21] = [
        (
            "before-preparation",
            |point| matches!(point, PublicationPoint::BeforePreparation),
            false,
        ),
        (
            "semantic-hash-chunk",
            |point| {
                matches!(
                    point,
                    PublicationPoint::MemberHashChunk {
                        plane: ArtifactIdentityPlane::Semantic,
                        ..
                    }
                )
            },
            false,
        ),
        (
            "stored-byte-hash-chunk",
            |point| {
                matches!(
                    point,
                    PublicationPoint::MemberHashChunk {
                        plane: ArtifactIdentityPlane::StoredBytes,
                        ..
                    }
                )
            },
            false,
        ),
        (
            "manifest-prepared",
            |point| matches!(point, PublicationPoint::ManifestPrepared { .. }),
            false,
        ),
        (
            "generation-created",
            |point| matches!(point, PublicationPoint::GenerationCreated),
            false,
        ),
        (
            "member-chunk-written",
            |point| matches!(point, PublicationPoint::MemberChunkWritten { .. }),
            false,
        ),
        (
            "member-synced",
            |point| matches!(point, PublicationPoint::MemberSynced { .. }),
            false,
        ),
        (
            "manifest-synced",
            |point| matches!(point, PublicationPoint::ManifestSynced),
            true,
        ),
        (
            "generation-verified",
            |point| matches!(point, PublicationPoint::GenerationVerified),
            true,
        ),
        (
            "before-root-binding",
            |point| matches!(point, PublicationPoint::BeforeRootBinding),
            true,
        ),
        (
            "root-binding-create",
            |point| {
                matches!(
                    point,
                    PublicationPoint::RootBindingAtomic {
                        step: AtomicWriteStep::CreateStaging
                    }
                )
            },
            true,
        ),
        (
            "root-binding-write",
            |point| {
                matches!(
                    point,
                    PublicationPoint::RootBindingAtomic {
                        step: AtomicWriteStep::WriteChunk { .. }
                    }
                )
            },
            true,
        ),
        (
            "root-binding-file-sync",
            |point| {
                matches!(
                    point,
                    PublicationPoint::RootBindingAtomic {
                        step: AtomicWriteStep::SyncStaging
                    }
                )
            },
            true,
        ),
        (
            "root-binding-rename",
            |point| {
                matches!(
                    point,
                    PublicationPoint::RootBindingAtomic {
                        step: AtomicWriteStep::RenameTarget
                    }
                )
            },
            true,
        ),
        (
            "root-binding-directory-sync",
            |point| {
                matches!(
                    point,
                    PublicationPoint::RootBindingAtomic {
                        step: AtomicWriteStep::SyncDirectory
                    }
                )
            },
            true,
        ),
        (
            "root-bound",
            |point| matches!(point, PublicationPoint::RootBound),
            true,
        ),
        (
            "before-activation",
            |point| matches!(point, PublicationPoint::BeforeActivation),
            true,
        ),
        (
            "active-create",
            |point| {
                matches!(
                    point,
                    PublicationPoint::ActivePointerAtomic {
                        step: AtomicWriteStep::CreateStaging
                    }
                )
            },
            true,
        ),
        (
            "active-write",
            |point| {
                matches!(
                    point,
                    PublicationPoint::ActivePointerAtomic {
                        step: AtomicWriteStep::WriteChunk { .. }
                    }
                )
            },
            true,
        ),
        (
            "active-file-sync",
            |point| {
                matches!(
                    point,
                    PublicationPoint::ActivePointerAtomic {
                        step: AtomicWriteStep::SyncStaging
                    }
                )
            },
            true,
        ),
        (
            "active-rename",
            |point| {
                matches!(
                    point,
                    PublicationPoint::ActivePointerAtomic {
                        step: AtomicWriteStep::RenameTarget
                    }
                )
            },
            true,
        ),
    ];

    for (label, target, complete_generation) in targets {
        let store = scratch_store(label);
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let mut control = target;
        let error = store
            .publish_with_control(&beta_inputs(), &mut control)
            .expect_err("beta publication is cancelled");
        let (point, root, generation_name) = match error {
            ArtifactError::Cancelled {
                point,
                root,
                generation_name,
            } => (point, root, generation_name),
            other => {
                assert!(
                    matches!(other, ArtifactError::Cancelled { .. }),
                    "publication returned a non-cancellation error: {other}"
                );
                continue;
            }
        };
        assert!(target(point), "{label}: stopped at {point}");
        assert_eq!(
            store
                .resolve_active()
                .expect("old generation remains active")
                .root(),
            alpha.root(),
            "{label}"
        );

        match (complete_generation, root, generation_name) {
            (true, Some(root), Some(generation_name)) => {
                store
                    .recover_staged(&generation_name, root)
                    .expect("a complete cancelled generation is explicitly recoverable");
            }
            (false, Some(root), Some(generation_name)) => {
                assert!(
                    store.recover_staged(&generation_name, root).is_err(),
                    "{label}: an incomplete generation must not become authoritative"
                );
            }
            (false, _, None) => {}
            state => assert!(
                matches!(state, (true, Some(_), Some(_)) | (false, _, None)),
                "unexpected cancellation state for {label}: {state:?}"
            ),
        }
    }
}

#[test]
fn pointer_storage_faults_report_linearization_and_never_expose_a_mixed_set() {
    let targets: [PointerFaultTarget; 10] = [
        (
            "root-create-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::RootBinding,
                        step: AtomicWriteStep::CreateStaging
                    }
                )
            },
            ArtifactPointer::RootBinding,
            false,
        ),
        (
            "root-write-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::RootBinding,
                        step: AtomicWriteStep::WriteChunk { .. }
                    }
                )
            },
            ArtifactPointer::RootBinding,
            false,
        ),
        (
            "root-file-sync-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::RootBinding,
                        step: AtomicWriteStep::SyncStaging
                    }
                )
            },
            ArtifactPointer::RootBinding,
            false,
        ),
        (
            "root-rename-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::RootBinding,
                        step: AtomicWriteStep::RenameTarget
                    }
                )
            },
            ArtifactPointer::RootBinding,
            false,
        ),
        (
            "root-directory-sync-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::RootBinding,
                        step: AtomicWriteStep::SyncDirectory
                    }
                )
            },
            ArtifactPointer::RootBinding,
            true,
        ),
        (
            "active-create-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::Active,
                        step: AtomicWriteStep::CreateStaging
                    }
                )
            },
            ArtifactPointer::Active,
            false,
        ),
        (
            "active-write-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::Active,
                        step: AtomicWriteStep::WriteChunk { .. }
                    }
                )
            },
            ArtifactPointer::Active,
            false,
        ),
        (
            "active-file-sync-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::Active,
                        step: AtomicWriteStep::SyncStaging
                    }
                )
            },
            ArtifactPointer::Active,
            false,
        ),
        (
            "active-rename-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::Active,
                        step: AtomicWriteStep::RenameTarget
                    }
                )
            },
            ArtifactPointer::Active,
            false,
        ),
        (
            "active-directory-sync-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::PointerAtomic {
                        pointer: ArtifactPointer::Active,
                        step: AtomicWriteStep::SyncDirectory
                    }
                )
            },
            ArtifactPointer::Active,
            true,
        ),
    ];

    for (label, target, expected_pointer, expected_replaced) in targets {
        let store = scratch_store(label);
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let mut control = InjectIoAt(target);
        let error = store
            .publish_with_control(&beta_inputs(), &mut control)
            .expect_err("selected pointer operation reports storage full");
        let (pointer, step, target_replaced, root, generation_name, source) = match error {
            ArtifactError::AtomicPointer {
                pointer,
                step,
                target_replaced,
                root,
                generation_name,
                source,
                ..
            } => (
                pointer,
                step,
                target_replaced,
                root,
                generation_name,
                source,
            ),
            other => {
                assert!(
                    matches!(other, ArtifactError::AtomicPointer { .. }),
                    "{label}: unexpected error {other}"
                );
                continue;
            }
        };
        assert_eq!(pointer, expected_pointer, "{label}");
        assert_eq!(target_replaced, expected_replaced, "{label}");
        let observed = PublicationIoPoint::PointerAtomic { pointer, step };
        assert!(target(observed), "{label}: stopped at {observed}");
        assert_eq!(source.kind(), std::io::ErrorKind::StorageFull, "{label}");
        store
            .recover_staged(&generation_name, root)
            .expect("pointer faults leave a complete recoverable generation");

        let active = store
            .resolve_active()
            .expect("a pointer fault leaves one complete active set");
        if pointer == ArtifactPointer::Active && target_replaced {
            assert_eq!(active.root(), root, "{label}: new complete set linearized");
        } else {
            assert_eq!(
                active.root(),
                alpha.root(),
                "{label}: old complete set remains active"
            );
        }
    }
}

#[test]
fn transaction_body_storage_faults_preserve_old_active_and_classify_staging() {
    let targets: [GenerationFaultTarget; 13] = [
        (
            "store-root-create-full",
            |point| matches!(point, PublicationIoPoint::StoreRootCreate),
            None,
        ),
        (
            "generations-directory-create-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::StoreDirectoryCreate {
                        directory: ArtifactStoreDirectory::Generations
                    }
                )
            },
            None,
        ),
        (
            "roots-directory-create-full",
            |point| {
                matches!(
                    point,
                    PublicationIoPoint::StoreDirectoryCreate {
                        directory: ArtifactStoreDirectory::Roots
                    }
                )
            },
            None,
        ),
        (
            "store-root-sync-full",
            |point| matches!(point, PublicationIoPoint::StoreRootSync),
            None,
        ),
        (
            "generation-create-full",
            |point| matches!(point, PublicationIoPoint::GenerationDirectoryCreate),
            None,
        ),
        (
            "generations-sync-full",
            |point| matches!(point, PublicationIoPoint::GenerationsDirectorySync),
            Some(false),
        ),
        (
            "member-create-full",
            |point| matches!(point, PublicationIoPoint::MemberCreate { .. }),
            Some(false),
        ),
        (
            "member-write-full",
            |point| matches!(point, PublicationIoPoint::MemberChunkWrite { .. }),
            Some(false),
        ),
        (
            "member-sync-full",
            |point| matches!(point, PublicationIoPoint::MemberFileSync { .. }),
            Some(false),
        ),
        (
            "manifest-create-full",
            |point| matches!(point, PublicationIoPoint::ManifestCreate),
            Some(false),
        ),
        (
            "manifest-write-full",
            |point| matches!(point, PublicationIoPoint::ManifestWrite { .. }),
            Some(false),
        ),
        (
            "manifest-sync-full",
            |point| matches!(point, PublicationIoPoint::ManifestFileSync),
            Some(true),
        ),
        (
            "generation-sync-full",
            |point| matches!(point, PublicationIoPoint::GenerationDirectorySync),
            Some(true),
        ),
    ];

    for (label, target, recoverable) in targets {
        let store = scratch_store(label);
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let mut control = InjectIoAt(target);
        let error = store
            .publish_with_control(&beta_inputs(), &mut control)
            .expect_err("selected transaction-body operation reports storage full");
        let (point, root, generation_name, source) = match error {
            ArtifactError::InjectedIo(error) => {
                let error = *error;
                (error.point, error.root, error.generation_name, error.source)
            }
            other => {
                assert!(
                    matches!(other, ArtifactError::InjectedIo(_)),
                    "{label}: unexpected error {other}"
                );
                continue;
            }
        };
        assert!(target(point), "{label}: stopped at {point}");
        assert_eq!(source.kind(), std::io::ErrorKind::StorageFull, "{label}");
        assert_eq!(
            store
                .resolve_active()
                .expect("old generation remains active")
                .root(),
            alpha.root(),
            "{label}"
        );

        match (recoverable, root, generation_name) {
            (None, Some(_), None) => {}
            (Some(expected), Some(root), Some(generation_name)) => {
                assert_eq!(
                    store.recover_staged(&generation_name, root).is_ok(),
                    expected,
                    "{label}"
                );
            }
            state => assert!(
                matches!(state, (None, Some(_), None) | (Some(_), Some(_), Some(_))),
                "{label}: unexpected recovery coordinates {state:?}"
            ),
        }
    }
}

#[test]
fn member_storage_full_after_one_chunk_leaves_only_partial_unreachable_staging() {
    const FIRST_CHUNK_END: u64 = 64 * 1024;
    let large = vec![0x3Cu8; (2 * FIRST_CHUNK_END + 17) as usize];
    let member = [ArtifactMemberInput::new(
        "Large.olean",
        &large,
        SCHEMA_NAME,
        alpha_semantics(),
    )];
    let store = scratch_store("member-second-chunk-full");
    let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
    let mut control = InjectIoAt(|point| {
        matches!(
            point,
            PublicationIoPoint::MemberChunkWrite {
                offset: FIRST_CHUNK_END,
                ..
            }
        )
    });
    let error = store
        .publish_with_control(&member, &mut control)
        .expect_err("the second member chunk reports storage full");
    let (root, generation_name, path, source) = match error {
        ArtifactError::InjectedIo(error) => {
            let error = *error;
            match (error.root, error.generation_name) {
                (Some(root), Some(generation_name)) => {
                    (root, generation_name, error.path, error.source)
                }
                state => {
                    assert!(
                        matches!(state, (Some(_), Some(_))),
                        "missing recovery coordinates: {state:?}"
                    );
                    return;
                }
            }
        }
        other => {
            assert!(
                matches!(other, ArtifactError::InjectedIo(_)),
                "unexpected error {other}"
            );
            return;
        }
    };
    assert_eq!(source.kind(), std::io::ErrorKind::StorageFull);
    assert_eq!(
        std::fs::metadata(path)
            .expect("partial staged member remains inspectable")
            .len(),
        FIRST_CHUNK_END
    );
    assert!(
        store.recover_staged(&generation_name, root).is_err(),
        "partial member staging is never recoverable"
    );
    assert_eq!(
        store.resolve_active().expect("alpha remains active").root(),
        alpha.root()
    );
}

#[test]
fn cancellation_is_never_observed_after_active_pointer_linearization() {
    let store = scratch_store("no-post-active-cancel");
    store.publish(&alpha_inputs()).expect("activate alpha");
    let mut observed = false;
    let mut control = |point| {
        if matches!(
            point,
            PublicationPoint::ActivePointerAtomic {
                step: AtomicWriteStep::SyncDirectory
            }
        ) {
            observed = true;
            true
        } else {
            false
        }
    };
    let beta = store
        .publish_with_control(&beta_inputs(), &mut control)
        .expect("post-rename cancellation is not queried");
    assert!(!observed);
    assert_eq!(
        store.resolve_active().expect("beta resolves").root(),
        beta.root()
    );
}

#[test]
fn large_member_hashing_and_writing_poll_cancellation_between_chunks() {
    const SECOND_CHUNK_END: u64 = 2 * 64 * 1024;
    let large = vec![0x5au8; SECOND_CHUNK_END as usize + 17];
    let member = [ArtifactMemberInput::new(
        "Large.olean",
        &large,
        SCHEMA_NAME,
        alpha_semantics(),
    )];

    for (label, target) in [
        (
            "large-hash",
            (|point| {
                matches!(
                    point,
                    PublicationPoint::MemberHashChunk {
                        plane: ArtifactIdentityPlane::StoredBytes,
                        bytes_hashed: SECOND_CHUNK_END,
                        ..
                    }
                )
            }) as fn(PublicationPoint) -> bool,
        ),
        (
            "large-write",
            (|point| {
                matches!(
                    point,
                    PublicationPoint::MemberChunkWritten {
                        bytes_written: SECOND_CHUNK_END,
                        ..
                    }
                )
            }) as fn(PublicationPoint) -> bool,
        ),
    ] {
        let store = scratch_store(label);
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let mut control = target;
        let error = store
            .publish_with_control(&member, &mut control)
            .expect_err("large publication is cancelled on its second chunk");
        let ArtifactError::Cancelled {
            point,
            root,
            generation_name,
        } = error
        else {
            assert!(matches!(error, ArtifactError::Cancelled { .. }));
            continue;
        };
        assert!(target(point), "{label}: {point}");
        assert_eq!(
            store.resolve_active().expect("alpha remains active").root(),
            alpha.root()
        );
        if let (Some(root), Some(generation_name)) = (root, generation_name) {
            assert!(
                store.recover_staged(&generation_name, root).is_err(),
                "a member cancelled mid-write is incomplete"
            );
        }
    }
}

#[test]
fn sigkill_at_every_controlled_io_step_never_exposes_a_mixed_generation() {
    for phase in KILL_IO_PHASES {
        let root = ScratchRoot::create(ARTIFACT_PUBLICATION_PREFIX, "artifact-publication", phase)
            .expect("create kill-drill scratch root");
        let ready_path = root.join("kill-ready");
        let store = store_at(root.path().to_path_buf());
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let mut child = Command::new(std::env::current_exe().expect("current test binary"))
            .arg("--exact")
            .arg("publication_kill_child")
            .arg("--nocapture")
            .env("FLN_ARTIFACT_KILL_PHASE", phase)
            .env("FLN_ARTIFACT_KILL_READY", &ready_path)
            .env("FLN_ARTIFACT_KILL_STORE", &root)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("spawn kill-drill child");

        let deadline = Instant::now() + Duration::from_secs(5);
        while !ready_path.exists() && Instant::now() < deadline {
            if child.try_wait().expect("poll kill-drill child").is_some() {
                break;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        if !ready_path.exists() {
            if child
                .try_wait()
                .expect("re-poll kill-drill child")
                .is_none()
            {
                let _ = child.kill();
            }
            let output = child
                .wait_with_output()
                .expect("reap failed kill-drill child");
            assert!(
                ready_path.exists(),
                "{phase}: child never reached the requested step; status={:?}, stdout={}, stderr={}",
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            continue;
        }

        child.kill().expect("send SIGKILL to parked child");
        let output = child.wait_with_output().expect("reap killed child");
        assert!(!output.status.success(), "{phase}: killed child succeeded");
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            assert_eq!(output.status.signal(), Some(9), "{phase}");
        }

        let resolved = store
            .resolve_active()
            .expect("restart resolves one complete generation");
        if phase == "active-pointer-directory-sync" {
            assert_generation_bytes(
                resolved.generation_dir(),
                &[
                    ("Demo.olean", b"olean-beta"),
                    ("Demo.ilean", b"ilean-beta"),
                    ("Demo.server", b"server-beta"),
                    ("Demo.ir", b"ir-beta"),
                ],
            );
        } else {
            assert_eq!(resolved.root(), alpha.root(), "{phase}");
            assert_generation_bytes(
                resolved.generation_dir(),
                &[
                    ("Demo.olean", b"olean-alpha"),
                    ("Demo.ilean", b"ilean-alpha"),
                    ("Demo.server", b"server-alpha"),
                    ("Demo.ir", b"ir-alpha"),
                ],
            );
        }
    }
}

#[test]
fn process_exit_before_activation_preserves_the_previous_complete_set() {
    for phase in ["after-stage", "after-bind"] {
        let root = ScratchRoot::create(ARTIFACT_PUBLICATION_PREFIX, "artifact-publication", phase)
            .expect("create process-exit scratch root");
        let store = store_at(root.path().to_path_buf());
        let alpha = store.publish(&alpha_inputs()).expect("activate alpha");
        let status = Command::new(std::env::current_exe().expect("current test binary"))
            .arg("--exact")
            .arg("publication_child")
            .arg("--nocapture")
            .env("FLN_ARTIFACT_CHILD_PHASE", phase)
            .env("FLN_ARTIFACT_CHILD_STORE", &root)
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .expect("spawn publication child");
        assert!(!status.success(), "child exits at its deliberate boundary");

        let resolved = store.resolve_active().expect("old root remains complete");
        assert_eq!(resolved.root(), alpha.root(), "{phase}");
        assert_generation_bytes(
            resolved.generation_dir(),
            &[
                ("Demo.olean", b"olean-alpha"),
                ("Demo.ilean", b"ilean-alpha"),
                ("Demo.server", b"server-alpha"),
                ("Demo.ir", b"ir-alpha"),
            ],
        );
    }
}

#[test]
fn publication_child() {
    let Ok(phase) = std::env::var("FLN_ARTIFACT_CHILD_PHASE") else {
        return;
    };
    let root = std::env::var_os("FLN_ARTIFACT_CHILD_STORE").expect("child store path");
    let store = store_at(PathBuf::from(root));
    let staged = store.stage(&beta_inputs()).expect("child stages beta");
    match phase.as_str() {
        "after-stage" => std::process::exit(71),
        "after-bind" => {
            let _bound = staged.bind().expect("child binds beta");
            std::process::exit(72);
        }
        _ => std::process::exit(73),
    }
}

#[test]
fn publication_kill_child() {
    let Ok(phase) = std::env::var("FLN_ARTIFACT_KILL_PHASE") else {
        return;
    };
    let ready_path = std::env::var_os("FLN_ARTIFACT_KILL_READY").expect("kill-drill marker path");
    let root = std::env::var_os("FLN_ARTIFACT_KILL_STORE").expect("kill-drill store path");
    let store = store_at(PathBuf::from(root));
    let mut control = ParkAtIo {
        phase,
        ready_path: PathBuf::from(ready_path),
    };
    let result = store.publish_with_control(&beta_inputs(), &mut control);
    eprintln!("kill-drill phase was not reached: {result:?}");
    std::process::exit(74);
}
