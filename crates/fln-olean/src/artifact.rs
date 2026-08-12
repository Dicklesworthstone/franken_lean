//! Crash-consistent publication of one module's cross-file artifact set.
//!
//! The operating-system primitive available to safe Rust is an atomic rename of
//! one directory entry, not an atomic rename of several unrelated files. This
//! module therefore publishes immutable generations through one `ACTIVE` pointer:
//!
//! 1. write every member into a fresh, unreachable generation directory;
//! 2. fsync every member, write the canonical manifest last, and fsync the
//!    generation;
//! 3. re-read the manifest and every stored byte, then atomically bind its root to
//!    that generation;
//! 4. atomically replace `ACTIVE` with the verified root.
//!
//! A crash before step 4 leaves the old active root untouched. A crash during
//! steps 1–3 can leave an incomplete or complete generation on disk, but no active
//! consumer can resolve it. [`ArtifactStore::recover_staged`] admits an explicitly
//! named generation only when its caller also supplies the expected root and every
//! byte re-verifies.
//!
//! The guarantee applies to consumers that resolve through [`ArtifactStore`].
//! This module does not claim that independently opening several conventional flat
//! paths is atomic; a Reference process must be handed the resolved generation
//! directory as one search-path root.

use std::ffi::OsStr;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use fln_hash::canon::{CanonReader, CanonWriter, SchemaId, registered};
use fln_hash::domain::{Digest, Domain, DomainHasher};
pub use fln_rt::region::{AtomicCreateError, AtomicCreateStep};
use fln_rt::region::{AtomicWriteError, AtomicWriteStep, write_file_atomic_controlled};

/// Atomically replace one conventional artifact path with complete bytes.
///
/// This is the single-file publication primitive for products such as FLBC.
/// Multi-file `.olean`/`.ilean` sets must use [`ArtifactStore`] instead so one
/// manifest and active pointer bind the complete generation.
pub fn publish_file_atomic(bytes: &[u8], path: &Path) -> io::Result<()> {
    fln_rt::region::write_file_atomic(bytes, path)
}

/// Atomically publish one new conventional artifact path without clobbering an
/// existing file, symlink, directory, or concurrent publisher.
pub fn publish_file_atomic_new(
    bytes: &[u8],
    path: &Path,
) -> Result<(), AtomicCreateError<std::convert::Infallible>> {
    fln_rt::region::write_file_atomic_new(bytes, path)
}

/// The one durable manifest encoding used by artifact generations.
///
/// This identity is joined in both directions against
/// `fln_hash::canon::SCHEMA_REGISTRY`.
pub const SCHEMA_ARTIFACT_SET_MANIFEST: SchemaId = SchemaId {
    name: "fln.olean.artifact-set-manifest",
    version: 1,
};

const MANIFEST_FILE: &str = "ARTIFACTS.fln";
const ACTIVE_FILE: &str = "ACTIVE";
const GENERATIONS_DIR: &str = "generations";
const ROOTS_DIR: &str = "roots";
const MAX_COMPONENT_BYTES: u64 = 255;
const POINTER_LIMIT: u64 = 512;
const HASH_CHUNK_BYTES: usize = 64 * 1024;
const SEMANTIC_HASH_PREFIX: &[u8] = b"fln.olean.artifact-semantic/1\0";
const BYTE_HASH_PREFIX: &[u8] = b"fln.olean.artifact-byte/1\0";
const SET_ROOT_PREFIX: &[u8] = b"fln.olean.artifact-set-root/1\0";

static GENERATION_SEQUENCE: AtomicU64 = AtomicU64::new(0);

/// Semantic identity under a named, versioned canonical schema.
///
/// Its constructor is intentionally separate from [`ArtifactByteHash`]'s: callers
/// cannot accidentally pass a stored-byte identity where canonical meaning is
/// required.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArtifactSemanticHash(Digest);

impl ArtifactSemanticHash {
    pub fn to_hex(self) -> String {
        self.0.to_hex()
    }
}

impl std::fmt::Display for ArtifactSemanticHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Identity of the exact bytes stored for one artifact member.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArtifactByteHash(Digest);

impl ArtifactByteHash {
    pub fn to_hex(self) -> String {
        self.0.to_hex()
    }
}

impl std::fmt::Display for ArtifactByteHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Content identity of one complete canonical artifact-set manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArtifactSetRoot(Digest);

impl ArtifactSetRoot {
    pub fn to_hex(self) -> String {
        self.0.to_hex()
    }

    /// Parse the canonical lowercase rendering used by journals and `ACTIVE`.
    pub fn from_hex(text: &str) -> Result<Self, ArtifactError> {
        Ok(Self(Digest(parse_digest_hex(text)?)))
    }
}

impl std::fmt::Display for ArtifactSetRoot {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Compute semantic identity from canonical meaning, not stored bytes.
pub fn artifact_semantic_hash(
    schema: SchemaId,
    canonical_semantic_bytes: &[u8],
) -> ArtifactSemanticHash {
    let mut hasher = semantic_hasher(schema, canonical_semantic_bytes.len() as u64);
    hasher.update(canonical_semantic_bytes);
    ArtifactSemanticHash(hasher.finalize())
}

fn semantic_hasher(schema: SchemaId, byte_len: u64) -> DomainHasher {
    let mut hasher = DomainHasher::new(Domain::ModuleProvenance);
    hasher
        .update(SEMANTIC_HASH_PREFIX)
        .update(&(schema.name.len() as u64).to_le_bytes())
        .update(schema.name.as_bytes())
        .update(&schema.version.to_le_bytes())
        .update(&byte_len.to_le_bytes());
    hasher
}

/// Compute identity of the exact stored encoding.
pub fn artifact_byte_hash(stored_bytes: &[u8]) -> ArtifactByteHash {
    let mut hasher = byte_hasher(stored_bytes.len() as u64);
    hasher.update(stored_bytes);
    ArtifactByteHash(hasher.finalize())
}

fn byte_hasher(byte_len: u64) -> DomainHasher {
    let mut hasher = DomainHasher::new(Domain::ModuleProvenance);
    hasher
        .update(BYTE_HASH_PREFIX)
        .update(&byte_len.to_le_bytes());
    hasher
}

fn artifact_set_root(canonical_manifest: &[u8]) -> ArtifactSetRoot {
    let mut hasher = DomainHasher::new(Domain::ModuleProvenance);
    hasher
        .update(SET_ROOT_PREFIX)
        .update(&(canonical_manifest.len() as u64).to_le_bytes())
        .update(canonical_manifest);
    ArtifactSetRoot(hasher.finalize())
}

/// One member supplied for publication.
#[derive(Debug, Clone, Copy)]
pub struct ArtifactMemberInput<'a> {
    name: &'a str,
    stored_bytes: &'a [u8],
    semantic_schema: SchemaId,
    canonical_semantic_bytes: &'a [u8],
}

impl<'a> ArtifactMemberInput<'a> {
    pub const fn new(
        name: &'a str,
        stored_bytes: &'a [u8],
        semantic_schema: SchemaId,
        canonical_semantic_bytes: &'a [u8],
    ) -> Self {
        Self {
            name,
            stored_bytes,
            semantic_schema,
            canonical_semantic_bytes,
        }
    }
}

/// Caller-supplied structural limits for publication and resolution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ArtifactLimits {
    max_members: u64,
    max_manifest_bytes: u64,
    max_member_bytes: u64,
    max_total_bytes: u64,
}

impl ArtifactLimits {
    pub const fn new(
        max_members: u64,
        max_manifest_bytes: u64,
        max_member_bytes: u64,
        max_total_bytes: u64,
    ) -> Self {
        Self {
            max_members,
            max_manifest_bytes,
            max_member_bytes,
            max_total_bytes,
        }
    }

    pub const fn max_members(self) -> u64 {
        self.max_members
    }

    pub const fn max_manifest_bytes(self) -> u64 {
        self.max_manifest_bytes
    }

    pub const fn max_member_bytes(self) -> u64 {
        self.max_member_bytes
    }

    pub const fn max_total_bytes(self) -> u64 {
        self.max_total_bytes
    }
}

impl Default for ArtifactLimits {
    fn default() -> Self {
        Self::new(
            128,
            1024 * 1024,
            16 * 1024 * 1024 * 1024,
            64 * 1024 * 1024 * 1024,
        )
    }
}

/// Which structural allowance refused work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactResource {
    Members,
    ManifestBytes,
    PointerBytes,
    MemberBytes,
    TotalBytes,
    ComponentBytes,
    GenerationEntries,
}

impl std::fmt::Display for ArtifactResource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::Members => "members",
            Self::ManifestBytes => "manifest bytes",
            Self::PointerBytes => "pointer bytes",
            Self::MemberBytes => "member bytes",
            Self::TotalBytes => "total bytes",
            Self::ComponentBytes => "path-component bytes",
            Self::GenerationEntries => "generation entries",
        };
        f.write_str(name)
    }
}

/// Which structurally distinct member identity is being computed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArtifactIdentityPlane {
    Semantic,
    StoredBytes,
}

impl std::fmt::Display for ArtifactIdentityPlane {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Semantic => f.write_str("semantic"),
            Self::StoredBytes => f.write_str("stored-byte"),
        }
    }
}

/// Which authoritative pointer an atomic replacement is publishing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArtifactPointer {
    RootBinding,
    Active,
}

impl std::fmt::Display for ArtifactPointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RootBinding => f.write_str("root binding"),
            Self::Active => f.write_str("ACTIVE"),
        }
    }
}

/// Durable store directory named by a layout operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArtifactStoreDirectory {
    Generations,
    Roots,
}

impl std::fmt::Display for ArtifactStoreDirectory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Generations => f.write_str("generations"),
            Self::Roots => f.write_str("roots"),
        }
    }
}

/// Filesystem step at which a deterministic storage fault may be injected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PublicationIoPoint {
    StoreRootCreate,
    StoreDirectoryCreate {
        directory: ArtifactStoreDirectory,
    },
    StoreRootSync,
    GenerationDirectoryCreate,
    GenerationsDirectorySync,
    MemberCreate {
        member_index: u64,
        member_count: u64,
    },
    MemberChunkWrite {
        member_index: u64,
        member_count: u64,
        offset: u64,
        chunk_len: u64,
        total_len: u64,
    },
    MemberFileSync {
        member_index: u64,
        member_count: u64,
    },
    ManifestCreate,
    ManifestWrite {
        byte_len: u64,
    },
    ManifestFileSync,
    GenerationDirectorySync,
    PointerAtomic {
        pointer: ArtifactPointer,
        step: AtomicWriteStep,
    },
}

impl std::fmt::Display for PublicationIoPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StoreRootCreate => f.write_str("create store root"),
            Self::StoreDirectoryCreate { directory } => {
                write!(f, "create {directory} store directory")
            }
            Self::StoreRootSync => f.write_str("sync store root"),
            Self::GenerationDirectoryCreate => f.write_str("create generation directory"),
            Self::GenerationsDirectorySync => f.write_str("sync generations directory"),
            Self::MemberCreate {
                member_index,
                member_count,
            } => write!(f, "create member {member_index}/{member_count}"),
            Self::MemberChunkWrite {
                member_index,
                member_count,
                offset,
                chunk_len,
                total_len,
            } => write!(
                f,
                "write {chunk_len} bytes at offset {offset} of {total_len} for member \
                 {member_index}/{member_count}"
            ),
            Self::MemberFileSync {
                member_index,
                member_count,
            } => write!(f, "sync member {member_index}/{member_count}"),
            Self::ManifestCreate => f.write_str("create generation manifest"),
            Self::ManifestWrite { byte_len } => {
                write!(f, "write {byte_len} manifest bytes")
            }
            Self::ManifestFileSync => f.write_str("sync generation manifest"),
            Self::GenerationDirectorySync => f.write_str("sync generation directory"),
            Self::PointerAtomic { pointer, step } => {
                write!(f, "perform {pointer} atomic step `{step}`")
            }
        }
    }
}

/// Deterministic cancellation observation points before group activation.
///
/// There is deliberately no point after the `ACTIVE` rename: returning
/// cancellation after the transaction has linearized would falsely report that
/// publication did not happen.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PublicationPoint {
    BeforePreparation,
    MemberHashChunk {
        member_index: u64,
        member_count: u64,
        plane: ArtifactIdentityPlane,
        bytes_hashed: u64,
    },
    ManifestPrepared {
        members: u64,
    },
    GenerationCreated,
    MemberChunkWritten {
        member_index: u64,
        member_count: u64,
        bytes_written: u64,
    },
    MemberSynced {
        member_index: u64,
        member_count: u64,
    },
    ManifestSynced,
    GenerationVerified,
    BeforeRootBinding,
    RootBindingAtomic {
        step: AtomicWriteStep,
    },
    RootBound,
    BeforeActivation,
    ActivePointerAtomic {
        step: AtomicWriteStep,
    },
}

impl std::fmt::Display for PublicationPoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BeforePreparation => f.write_str("before preparation"),
            Self::MemberHashChunk {
                member_index,
                member_count,
                plane,
                bytes_hashed,
            } => write!(
                f,
                "after hashing {bytes_hashed} {plane} bytes for member \
                 {member_index}/{member_count}"
            ),
            Self::ManifestPrepared { members } => {
                write!(f, "after preparing a {members}-member manifest")
            }
            Self::GenerationCreated => f.write_str("after creating the generation"),
            Self::MemberChunkWritten {
                member_index,
                member_count,
                bytes_written,
            } => write!(
                f,
                "after writing {bytes_written} bytes of member {member_index}/{member_count}"
            ),
            Self::MemberSynced {
                member_index,
                member_count,
            } => write!(f, "after syncing member {member_index}/{member_count}"),
            Self::ManifestSynced => f.write_str("after syncing the manifest"),
            Self::GenerationVerified => f.write_str("after verifying the generation"),
            Self::BeforeRootBinding => f.write_str("before publishing the root binding"),
            Self::RootBindingAtomic { step } => {
                write!(f, "before root-binding atomic step `{step}`")
            }
            Self::RootBound => f.write_str("after publishing the root binding"),
            Self::BeforeActivation => f.write_str("before activating the root"),
            Self::ActivePointerAtomic { step } => {
                write!(f, "before ACTIVE atomic step `{step}`")
            }
        }
    }
}

/// Cancellation source for a publication operation.
///
/// A closure `FnMut(PublicationPoint) -> bool` implements this trait directly;
/// returning `true` requests cancellation at that observation point.
pub trait PublicationControl {
    fn should_cancel(&mut self, point: PublicationPoint) -> bool;

    /// Deterministic fault-drill hook consulted before controlled filesystem
    /// operations. Production controls normally retain the default `None`.
    fn injected_io_error(&mut self, _point: PublicationIoPoint) -> Option<io::ErrorKind> {
        None
    }
}

impl<F> PublicationControl for F
where
    F: FnMut(PublicationPoint) -> bool,
{
    fn should_cancel(&mut self, point: PublicationPoint) -> bool {
        self(point)
    }
}

struct NeverCancel;

impl PublicationControl for NeverCancel {
    fn should_cancel(&mut self, _point: PublicationPoint) -> bool {
        false
    }
}

/// Recovery-bearing payload for a deterministically injected storage failure.
#[derive(Debug)]
pub struct InjectedIoError {
    pub point: PublicationIoPoint,
    pub root: Option<ArtifactSetRoot>,
    pub generation_name: Option<String>,
    pub path: PathBuf,
    pub source: io::Error,
}

/// Typed publication or resolution failure.
#[derive(Debug)]
pub enum ArtifactError {
    EmptyArtifactSet,
    InvalidMemberName {
        name: String,
        reason: &'static str,
    },
    InvalidSemanticSchema {
        name: String,
        reason: &'static str,
    },
    DuplicateMember {
        name: String,
    },
    ResourceLimitExceeded {
        resource: ArtifactResource,
        allowed: u64,
        observed: u64,
    },
    Cancelled {
        point: PublicationPoint,
        root: Option<ArtifactSetRoot>,
        generation_name: Option<String>,
    },
    AtomicPointer {
        pointer: ArtifactPointer,
        step: AtomicWriteStep,
        target_replaced: bool,
        root: ArtifactSetRoot,
        generation_name: String,
        path: PathBuf,
        source: io::Error,
    },
    InjectedIo(Box<InjectedIoError>),
    MalformedManifest {
        detail: String,
    },
    NonCanonicalManifest,
    InvalidRootHex,
    RootMismatch {
        expected: ArtifactSetRoot,
        actual: ArtifactSetRoot,
    },
    RootCollision {
        root: ArtifactSetRoot,
    },
    RootNotBound {
        root: ArtifactSetRoot,
    },
    NoActiveGeneration,
    MalformedPointer {
        kind: &'static str,
    },
    InvalidGenerationName {
        name: String,
    },
    NonRegularEntry {
        path: PathBuf,
    },
    GenerationInventoryMismatch {
        expected: Vec<String>,
        actual: Vec<String>,
    },
    MemberLengthMismatch {
        name: String,
        expected: u64,
        actual: u64,
    },
    MemberByteHashMismatch {
        name: String,
        expected: ArtifactByteHash,
        actual: ArtifactByteHash,
    },
    Io {
        operation: &'static str,
        path: PathBuf,
        source: io::Error,
    },
}

impl std::fmt::Display for ArtifactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyArtifactSet => {
                f.write_str("an artifact set must contain at least one member")
            }
            Self::InvalidMemberName { name, reason } => {
                write!(f, "invalid artifact member name `{name}`: {reason}")
            }
            Self::InvalidSemanticSchema { name, reason } => {
                write!(f, "invalid artifact semantic schema `{name}`: {reason}")
            }
            Self::DuplicateMember { name } => {
                write!(f, "duplicate artifact member `{name}`")
            }
            Self::ResourceLimitExceeded {
                resource,
                allowed,
                observed,
            } => write!(
                f,
                "artifact {resource} limit exceeded: allowed {allowed}, observed {observed}"
            ),
            Self::Cancelled {
                point,
                root,
                generation_name,
            } => write!(
                f,
                "artifact publication cancelled {point}; root={}, generation={}",
                root.map_or_else(|| "not prepared".to_string(), |root| root.to_hex()),
                generation_name.as_deref().unwrap_or("not created")
            ),
            Self::AtomicPointer {
                pointer,
                step,
                target_replaced,
                root,
                generation_name,
                path,
                source,
            } => write!(
                f,
                "artifact {pointer} write failed during `{step}` after target \
                 replacement={target_replaced}; root={root}, generation={generation_name}, \
                 path={}: {source}",
                path.display()
            ),
            Self::InjectedIo(error) => write!(
                f,
                "artifact storage fault injected before `{point}`; root={}, generation={}, \
                 path={}: {source}",
                error
                    .root
                    .map_or_else(|| "not prepared".to_string(), |root| root.to_hex()),
                error.generation_name.as_deref().unwrap_or("not created"),
                error.path.display(),
                point = error.point,
                source = error.source
            ),
            Self::MalformedManifest { detail } => {
                write!(f, "malformed artifact-set manifest: {detail}")
            }
            Self::NonCanonicalManifest => {
                f.write_str("artifact-set manifest is not in its canonical encoding")
            }
            Self::InvalidRootHex => f.write_str("artifact-set root is not 64 lowercase hex digits"),
            Self::RootMismatch { expected, actual } => {
                write!(
                    f,
                    "artifact-set root mismatch: expected {expected}, got {actual}"
                )
            }
            Self::RootCollision { root } => write!(
                f,
                "artifact-set root {root} resolves to different canonical manifest bytes"
            ),
            Self::RootNotBound { root } => {
                write!(f, "artifact-set root {root} has no generation binding")
            }
            Self::NoActiveGeneration => f.write_str("artifact store has no ACTIVE generation"),
            Self::MalformedPointer { kind } => {
                write!(f, "artifact store has a malformed {kind} pointer")
            }
            Self::InvalidGenerationName { name } => {
                write!(f, "invalid artifact generation name `{name}`")
            }
            Self::NonRegularEntry { path } => {
                write!(
                    f,
                    "artifact entry is not a regular file or real directory: {}",
                    path.display()
                )
            }
            Self::GenerationInventoryMismatch { expected, actual } => write!(
                f,
                "artifact generation inventory differs: expected {expected:?}, got {actual:?}"
            ),
            Self::MemberLengthMismatch {
                name,
                expected,
                actual,
            } => write!(
                f,
                "artifact member `{name}` length differs: expected {expected}, got {actual}"
            ),
            Self::MemberByteHashMismatch {
                name,
                expected,
                actual,
            } => write!(
                f,
                "artifact member `{name}` byte hash differs: expected {expected}, got {actual}"
            ),
            Self::Io {
                operation,
                path,
                source,
            } => write!(
                f,
                "artifact I/O failed while {operation} {}: {source}",
                path.display()
            ),
        }
    }
}

impl std::error::Error for ArtifactError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::AtomicPointer { source, .. } | Self::Io { source, .. } => Some(source),
            Self::InjectedIo(error) => Some(&error.source),
            _ => None,
        }
    }
}

fn io_error(operation: &'static str, path: &Path, source: io::Error) -> ArtifactError {
    ArtifactError::Io {
        operation,
        path: path.to_path_buf(),
        source,
    }
}

/// One immutable member row in a manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactMemberRecord {
    name: String,
    byte_len: u64,
    semantic_schema_name: String,
    semantic_schema_version: u16,
    semantic_hash: ArtifactSemanticHash,
    byte_hash: ArtifactByteHash,
}

impl ArtifactMemberRecord {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn byte_len(&self) -> u64 {
        self.byte_len
    }

    pub fn semantic_schema_name(&self) -> &str {
        &self.semantic_schema_name
    }

    pub const fn semantic_schema_version(&self) -> u16 {
        self.semantic_schema_version
    }

    pub const fn semantic_hash(&self) -> ArtifactSemanticHash {
        self.semantic_hash
    }

    pub const fn byte_hash(&self) -> ArtifactByteHash {
        self.byte_hash
    }
}

/// Canonical description of one complete artifact generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactSetManifest {
    members: Vec<ArtifactMemberRecord>,
    canonical_bytes: Vec<u8>,
    root: ArtifactSetRoot,
}

impl ArtifactSetManifest {
    pub fn members(&self) -> &[ArtifactMemberRecord] {
        &self.members
    }

    pub fn canonical_bytes(&self) -> &[u8] {
        &self.canonical_bytes
    }

    pub const fn root(&self) -> ArtifactSetRoot {
        self.root
    }

    /// Decode under caller limits and reject every non-canonical representation.
    pub fn from_canonical_bytes(
        bytes: &[u8],
        limits: ArtifactLimits,
    ) -> Result<Self, ArtifactError> {
        check_limit(
            ArtifactResource::ManifestBytes,
            limits.max_manifest_bytes,
            bytes.len() as u64,
        )?;
        let mut reader = CanonReader::new(bytes);
        reader
            .expect_schema(SCHEMA_ARTIFACT_SET_MANIFEST)
            .map_err(manifest_decode_error)?;
        let count = reader.u64().map_err(manifest_decode_error)?;
        check_limit(ArtifactResource::Members, limits.max_members, count)?;
        let count = usize::try_from(count).map_err(|_| ArtifactError::ResourceLimitExceeded {
            resource: ArtifactResource::Members,
            allowed: limits.max_members,
            observed: u64::MAX,
        })?;

        let mut members = Vec::new();
        members
            .try_reserve_exact(count)
            .map_err(|_| ArtifactError::ResourceLimitExceeded {
                resource: ArtifactResource::Members,
                allowed: limits.max_members,
                observed: count as u64,
            })?;
        let mut total = 0u64;
        let mut previous_name: Option<String> = None;
        for _ in 0..count {
            let name = reader.str().map_err(manifest_decode_error)?.to_string();
            validate_member_name(&name)?;
            if let Some(previous) = &previous_name {
                if previous == &name {
                    return Err(ArtifactError::DuplicateMember { name });
                }
                if previous > &name {
                    return Err(ArtifactError::NonCanonicalManifest);
                }
            }
            previous_name = Some(name.clone());

            let byte_len = reader.u64().map_err(manifest_decode_error)?;
            check_limit(
                ArtifactResource::MemberBytes,
                limits.max_member_bytes,
                byte_len,
            )?;
            total = total
                .checked_add(byte_len)
                .ok_or(ArtifactError::ResourceLimitExceeded {
                    resource: ArtifactResource::TotalBytes,
                    allowed: limits.max_total_bytes,
                    observed: u64::MAX,
                })?;
            check_limit(ArtifactResource::TotalBytes, limits.max_total_bytes, total)?;

            let semantic_schema_name = reader.str().map_err(manifest_decode_error)?.to_string();
            let semantic_schema_version = reader.u16().map_err(manifest_decode_error)?;
            validate_semantic_schema(&semantic_schema_name, semantic_schema_version)?;
            let semantic_hash = ArtifactSemanticHash(read_digest(&mut reader)?);
            let byte_hash = ArtifactByteHash(read_digest(&mut reader)?);
            members.push(ArtifactMemberRecord {
                name,
                byte_len,
                semantic_schema_name,
                semantic_schema_version,
                semantic_hash,
                byte_hash,
            });
        }
        reader.finish().map_err(manifest_decode_error)?;

        let canonical_bytes = encode_manifest(&members);
        if canonical_bytes != bytes {
            return Err(ArtifactError::NonCanonicalManifest);
        }
        let root = artifact_set_root(&canonical_bytes);
        Ok(Self {
            members,
            canonical_bytes,
            root,
        })
    }

    fn from_records(
        members: Vec<ArtifactMemberRecord>,
        limits: ArtifactLimits,
    ) -> Result<Self, ArtifactError> {
        let canonical_bytes = encode_manifest(&members);
        check_limit(
            ArtifactResource::ManifestBytes,
            limits.max_manifest_bytes,
            canonical_bytes.len() as u64,
        )?;
        let root = artifact_set_root(&canonical_bytes);
        Ok(Self {
            members,
            canonical_bytes,
            root,
        })
    }
}

fn manifest_decode_error(error: fln_hash::canon::CanonError) -> ArtifactError {
    ArtifactError::MalformedManifest {
        detail: error.to_string(),
    }
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, ArtifactError> {
    let bytes = reader.bytes().map_err(manifest_decode_error)?;
    let array: [u8; 32] = bytes
        .try_into()
        .map_err(|_| ArtifactError::MalformedManifest {
            detail: "digest is not 32 bytes".to_string(),
        })?;
    Ok(Digest(array))
}

fn encode_manifest(members: &[ArtifactMemberRecord]) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(SCHEMA_ARTIFACT_SET_MANIFEST);
    writer.u64(members.len() as u64);
    for member in members {
        writer.str(&member.name);
        writer.u64(member.byte_len);
        writer.str(&member.semantic_schema_name);
        writer.u16(member.semantic_schema_version);
        writer.bytes(&member.semantic_hash.0.0);
        writer.bytes(&member.byte_hash.0.0);
    }
    writer.into_bytes()
}

struct PreparedMember<'a> {
    record: ArtifactMemberRecord,
    stored_bytes: &'a [u8],
}

struct PreparedSet<'a> {
    members: Vec<PreparedMember<'a>>,
    manifest: ArtifactSetManifest,
}

fn hash_member_plane_controlled<C: PublicationControl + ?Sized>(
    mut hasher: DomainHasher,
    bytes: &[u8],
    member_index: u64,
    member_count: u64,
    plane: ArtifactIdentityPlane,
    control: &mut C,
) -> Result<Digest, ArtifactError> {
    let mut bytes_hashed = 0u64;
    if bytes.is_empty() {
        cancellation_checkpoint(
            control,
            PublicationPoint::MemberHashChunk {
                member_index,
                member_count,
                plane,
                bytes_hashed,
            },
            None,
            None,
        )?;
    } else {
        for chunk in bytes.chunks(HASH_CHUNK_BYTES) {
            hasher.update(chunk);
            bytes_hashed = bytes_hashed.saturating_add(chunk.len() as u64);
            cancellation_checkpoint(
                control,
                PublicationPoint::MemberHashChunk {
                    member_index,
                    member_count,
                    plane,
                    bytes_hashed,
                },
                None,
                None,
            )?;
        }
    }
    Ok(hasher.finalize())
}

fn prepare_members<'a, C: PublicationControl + ?Sized>(
    inputs: &'a [ArtifactMemberInput<'a>],
    limits: ArtifactLimits,
    control: &mut C,
) -> Result<PreparedSet<'a>, ArtifactError> {
    if inputs.is_empty() {
        return Err(ArtifactError::EmptyArtifactSet);
    }
    check_limit(
        ArtifactResource::Members,
        limits.max_members,
        inputs.len() as u64,
    )?;

    let mut total = 0u64;
    let mut members = Vec::new();
    members
        .try_reserve_exact(inputs.len())
        .map_err(|_| ArtifactError::ResourceLimitExceeded {
            resource: ArtifactResource::Members,
            allowed: limits.max_members,
            observed: inputs.len() as u64,
        })?;
    let member_count = inputs.len() as u64;
    for (index, input) in inputs.iter().enumerate() {
        let member_index = index as u64 + 1;
        validate_member_name(input.name)?;
        validate_semantic_schema(input.semantic_schema.name, input.semantic_schema.version)?;
        check_limit(
            ArtifactResource::MemberBytes,
            limits.max_member_bytes,
            input.stored_bytes.len() as u64,
        )?;
        check_limit(
            ArtifactResource::MemberBytes,
            limits.max_member_bytes,
            input.canonical_semantic_bytes.len() as u64,
        )?;
        total = total
            .checked_add(input.stored_bytes.len() as u64)
            .and_then(|sum| sum.checked_add(input.canonical_semantic_bytes.len() as u64))
            .ok_or(ArtifactError::ResourceLimitExceeded {
                resource: ArtifactResource::TotalBytes,
                allowed: limits.max_total_bytes,
                observed: u64::MAX,
            })?;
        check_limit(ArtifactResource::TotalBytes, limits.max_total_bytes, total)?;

        let semantic_hash = ArtifactSemanticHash(hash_member_plane_controlled(
            semantic_hasher(
                input.semantic_schema,
                input.canonical_semantic_bytes.len() as u64,
            ),
            input.canonical_semantic_bytes,
            member_index,
            member_count,
            ArtifactIdentityPlane::Semantic,
            control,
        )?);
        let byte_hash = ArtifactByteHash(hash_member_plane_controlled(
            byte_hasher(input.stored_bytes.len() as u64),
            input.stored_bytes,
            member_index,
            member_count,
            ArtifactIdentityPlane::StoredBytes,
            control,
        )?);
        members.push(PreparedMember {
            record: ArtifactMemberRecord {
                name: input.name.to_string(),
                byte_len: input.stored_bytes.len() as u64,
                semantic_schema_name: input.semantic_schema.name.to_string(),
                semantic_schema_version: input.semantic_schema.version,
                semantic_hash,
                byte_hash,
            },
            stored_bytes: input.stored_bytes,
        });
    }
    members.sort_by(|left, right| left.record.name.cmp(&right.record.name));
    for pair in members.windows(2) {
        if pair[0].record.name == pair[1].record.name {
            return Err(ArtifactError::DuplicateMember {
                name: pair[0].record.name.clone(),
            });
        }
    }
    let manifest = ArtifactSetManifest::from_records(
        members.iter().map(|member| member.record.clone()).collect(),
        limits,
    )?;
    Ok(PreparedSet { members, manifest })
}

fn check_limit(
    resource: ArtifactResource,
    allowed: u64,
    observed: u64,
) -> Result<(), ArtifactError> {
    if observed > allowed {
        return Err(ArtifactError::ResourceLimitExceeded {
            resource,
            allowed,
            observed,
        });
    }
    Ok(())
}

fn cancellation_checkpoint<C: PublicationControl + ?Sized>(
    control: &mut C,
    point: PublicationPoint,
    root: Option<ArtifactSetRoot>,
    generation_name: Option<&str>,
) -> Result<(), ArtifactError> {
    if control.should_cancel(point) {
        return Err(ArtifactError::Cancelled {
            point,
            root,
            generation_name: generation_name.map(str::to_string),
        });
    }
    Ok(())
}

fn injected_io_checkpoint<C: PublicationControl + ?Sized>(
    control: &mut C,
    point: PublicationIoPoint,
    root: Option<ArtifactSetRoot>,
    generation_name: Option<&str>,
    path: &Path,
) -> Result<(), ArtifactError> {
    if let Some(kind) = control.injected_io_error(point) {
        return Err(ArtifactError::InjectedIo(Box::new(InjectedIoError {
            point,
            root,
            generation_name: generation_name.map(str::to_string),
            path: path.to_path_buf(),
            source: io::Error::from(kind),
        })));
    }
    Ok(())
}

#[derive(Debug)]
enum PointerControlStop {
    Cancelled(Box<ArtifactError>),
    Injected(io::Error),
}

fn write_pointer_controlled<C: PublicationControl + ?Sized>(
    bytes: &[u8],
    path: &Path,
    pointer: ArtifactPointer,
    root: ArtifactSetRoot,
    generation_name: &str,
    control: &mut C,
) -> Result<(), ArtifactError> {
    let mut pointer_control = |step| {
        let cancellation_point = match pointer {
            ArtifactPointer::RootBinding => PublicationPoint::RootBindingAtomic { step },
            ArtifactPointer::Active => PublicationPoint::ActivePointerAtomic { step },
        };
        let io_point = PublicationIoPoint::PointerAtomic { pointer, step };
        if let Some(kind) = control.injected_io_error(io_point) {
            return Err(PointerControlStop::Injected(io::Error::from(kind)));
        }
        if pointer == ArtifactPointer::Active && step == AtomicWriteStep::SyncDirectory {
            return Ok(());
        }
        cancellation_checkpoint(
            control,
            cancellation_point,
            Some(root),
            Some(generation_name),
        )
        .map_err(|error| PointerControlStop::Cancelled(Box::new(error)))
    };

    match write_file_atomic_controlled(bytes, path, &mut pointer_control) {
        Ok(()) => Ok(()),
        Err(AtomicWriteError::Control {
            source: PointerControlStop::Cancelled(error),
            ..
        }) => Err(*error),
        Err(AtomicWriteError::Control {
            step,
            target_replaced,
            source: PointerControlStop::Injected(source),
        })
        | Err(AtomicWriteError::Io {
            step,
            target_replaced,
            source,
        }) => Err(ArtifactError::AtomicPointer {
            pointer,
            step,
            target_replaced,
            root,
            generation_name: generation_name.to_string(),
            path: path.to_path_buf(),
            source,
        }),
    }
}

fn validate_member_name(name: &str) -> Result<(), ArtifactError> {
    if name.is_empty() {
        return Err(ArtifactError::InvalidMemberName {
            name: name.to_string(),
            reason: "name is empty",
        });
    }
    check_limit(
        ArtifactResource::ComponentBytes,
        MAX_COMPONENT_BYTES,
        name.len() as u64,
    )?;
    if name == MANIFEST_FILE {
        return Err(ArtifactError::InvalidMemberName {
            name: name.to_string(),
            reason: "name is reserved for the transaction manifest",
        });
    }
    if name.contains(['/', '\\', '\0']) || name.chars().any(char::is_control) {
        return Err(ArtifactError::InvalidMemberName {
            name: name.to_string(),
            reason: "name contains a separator or control character",
        });
    }
    let mut components = Path::new(name).components();
    if !matches!(components.next(), Some(Component::Normal(_))) || components.next().is_some() {
        return Err(ArtifactError::InvalidMemberName {
            name: name.to_string(),
            reason: "name is not one normal path component",
        });
    }
    Ok(())
}

fn validate_semantic_schema(name: &str, version: u16) -> Result<(), ArtifactError> {
    if version == 0 {
        return Err(ArtifactError::InvalidSemanticSchema {
            name: name.to_string(),
            reason: "version zero is reserved",
        });
    }
    if name.len() as u64 > MAX_COMPONENT_BYTES {
        return Err(ArtifactError::InvalidSemanticSchema {
            name: name.to_string(),
            reason: "name exceeds 255 bytes",
        });
    }
    if !name.starts_with("fln.")
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || b".-".contains(&byte))
    {
        return Err(ArtifactError::InvalidSemanticSchema {
            name: name.to_string(),
            reason: "name must be a lowercase `fln.*` schema identifier",
        });
    }
    let Some(row) = registered(name) else {
        return Err(ArtifactError::InvalidSemanticSchema {
            name: name.to_string(),
            reason: "schema is absent from the canonical registry",
        });
    };
    if row.id.version != version {
        return Err(ArtifactError::InvalidSemanticSchema {
            name: name.to_string(),
            reason: "version differs from the canonical registry",
        });
    }
    Ok(())
}

fn parse_digest_hex(text: &str) -> Result<[u8; 32], ArtifactError> {
    if text.len() != 64
        || !text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(ArtifactError::InvalidRootHex);
    }
    let mut bytes = [0u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        let high = hex_nibble(text.as_bytes()[index * 2]);
        let low = hex_nibble(text.as_bytes()[index * 2 + 1]);
        *byte = (high << 4) | low;
    }
    Ok(bytes)
}

fn hex_nibble(byte: u8) -> u8 {
    match byte {
        b'0'..=b'9' => byte - b'0',
        b'a'..=b'f' => byte - b'a' + 10,
        _ => 0,
    }
}

/// One filesystem-backed artifact transaction root.
#[derive(Debug, Clone)]
pub struct ArtifactStore {
    root: PathBuf,
    limits: ArtifactLimits,
}

impl ArtifactStore {
    pub fn new(root: impl Into<PathBuf>, limits: ArtifactLimits) -> Self {
        Self {
            root: root.into(),
            limits,
        }
    }

    pub fn root_path(&self) -> &Path {
        &self.root
    }

    pub const fn limits(&self) -> ArtifactLimits {
        self.limits
    }

    /// Write and verify an unreachable generation, without changing any pointer.
    pub fn stage<'a>(
        &self,
        inputs: &'a [ArtifactMemberInput<'a>],
    ) -> Result<StagedArtifactSet, ArtifactError> {
        let mut control = NeverCancel;
        self.stage_with_control(inputs, &mut control)
    }

    /// [`ArtifactStore::stage`] with deterministic cancellation observations.
    pub fn stage_with_control<'a, C: PublicationControl + ?Sized>(
        &self,
        inputs: &'a [ArtifactMemberInput<'a>],
        control: &mut C,
    ) -> Result<StagedArtifactSet, ArtifactError> {
        cancellation_checkpoint(control, PublicationPoint::BeforePreparation, None, None)?;
        let prepared = prepare_members(inputs, self.limits, control)?;
        cancellation_checkpoint(
            control,
            PublicationPoint::ManifestPrepared {
                members: prepared.members.len() as u64,
            },
            Some(prepared.manifest.root()),
            None,
        )?;
        self.stage_prepared(prepared, control)
    }

    /// Publish a complete set, reusing an already verified root binding when one
    /// exists. Activation has one linearization point: replacement of `ACTIVE`.
    pub fn publish<'a>(
        &self,
        inputs: &'a [ArtifactMemberInput<'a>],
    ) -> Result<ArtifactPublication, ArtifactError> {
        let mut control = NeverCancel;
        self.publish_with_control(inputs, &mut control)
    }

    /// [`ArtifactStore::publish`] with deterministic cancellation observations.
    pub fn publish_with_control<'a, C: PublicationControl + ?Sized>(
        &self,
        inputs: &'a [ArtifactMemberInput<'a>],
        control: &mut C,
    ) -> Result<ArtifactPublication, ArtifactError> {
        cancellation_checkpoint(control, PublicationPoint::BeforePreparation, None, None)?;
        let prepared = prepare_members(inputs, self.limits, control)?;
        cancellation_checkpoint(
            control,
            PublicationPoint::ManifestPrepared {
                members: prepared.members.len() as u64,
            },
            Some(prepared.manifest.root()),
            None,
        )?;
        let root = prepared.manifest.root();
        self.ensure_layout(root, control)?;
        let bound = match self.resolve_root(root) {
            Ok(existing) => {
                if existing.manifest.canonical_bytes() != prepared.manifest.canonical_bytes() {
                    return Err(ArtifactError::RootCollision { root });
                }
                BoundArtifactSet {
                    store: self.clone(),
                    resolved: existing,
                }
            }
            Err(ArtifactError::RootNotBound { .. }) => self
                .stage_prepared(prepared, control)?
                .bind_with_control(control)?,
            Err(error) => return Err(error),
        };
        bound.activate_with_control(control)
    }

    /// Resolve the complete currently active generation and re-verify all bytes.
    pub fn resolve_active(&self) -> Result<ResolvedArtifactSet, ArtifactError> {
        let active_path = self.root.join(ACTIVE_FILE);
        let bytes =
            match read_bounded_regular(&active_path, POINTER_LIMIT, ArtifactResource::PointerBytes)
            {
                Ok(bytes) => bytes,
                Err(ArtifactError::Io { source, .. })
                    if source.kind() == io::ErrorKind::NotFound =>
                {
                    return Err(ArtifactError::NoActiveGeneration);
                }
                Err(error) => return Err(error),
            };
        let text = std::str::from_utf8(&bytes)
            .map_err(|_| ArtifactError::MalformedPointer { kind: "ACTIVE" })?;
        let Some(hex) = text.strip_suffix('\n') else {
            return Err(ArtifactError::MalformedPointer { kind: "ACTIVE" });
        };
        let root = ArtifactSetRoot::from_hex(hex)
            .map_err(|_| ArtifactError::MalformedPointer { kind: "ACTIVE" })?;
        self.resolve_root(root)
    }

    /// Recover an unreachable generation only when its exact expected root is
    /// supplied by the caller's journal or build receipt.
    pub fn recover_staged(
        &self,
        generation_name: &str,
        expected_root: ArtifactSetRoot,
    ) -> Result<StagedArtifactSet, ArtifactError> {
        let resolved = self.validate_generation(generation_name, expected_root)?;
        Ok(StagedArtifactSet {
            store: self.clone(),
            generation_name: generation_name.to_string(),
            manifest: resolved.manifest,
        })
    }

    fn ensure_layout<C: PublicationControl + ?Sized>(
        &self,
        root: ArtifactSetRoot,
        control: &mut C,
    ) -> Result<(), ArtifactError> {
        injected_io_checkpoint(
            control,
            PublicationIoPoint::StoreRootCreate,
            Some(root),
            None,
            &self.root,
        )?;
        fs::create_dir_all(&self.root)
            .map_err(|error| io_error("creating store root", &self.root, error))?;
        ensure_real_directory(&self.root)?;
        for (directory, child) in [
            (ArtifactStoreDirectory::Generations, self.generations_dir()),
            (ArtifactStoreDirectory::Roots, self.roots_dir()),
        ] {
            injected_io_checkpoint(
                control,
                PublicationIoPoint::StoreDirectoryCreate { directory },
                Some(root),
                None,
                &child,
            )?;
            match fs::create_dir(&child) {
                Ok(()) => {}
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    ensure_real_directory(&child)?;
                }
                Err(error) => return Err(io_error("creating store directory", &child, error)),
            }
        }
        injected_io_checkpoint(
            control,
            PublicationIoPoint::StoreRootSync,
            Some(root),
            None,
            &self.root,
        )?;
        sync_directory(&self.root)
    }

    fn generations_dir(&self) -> PathBuf {
        self.root.join(GENERATIONS_DIR)
    }

    fn roots_dir(&self) -> PathBuf {
        self.root.join(ROOTS_DIR)
    }

    fn stage_prepared<C: PublicationControl + ?Sized>(
        &self,
        prepared: PreparedSet<'_>,
        control: &mut C,
    ) -> Result<StagedArtifactSet, ArtifactError> {
        let root = prepared.manifest.root();
        self.ensure_layout(root, control)?;
        let (generation_name, generation_dir) = self.create_generation(root, control)?;
        cancellation_checkpoint(
            control,
            PublicationPoint::GenerationCreated,
            Some(root),
            Some(&generation_name),
        )?;
        let member_count = prepared.members.len() as u64;
        for (index, member) in prepared.members.iter().enumerate() {
            write_generation_member_controlled(
                &generation_dir.join(&member.record.name),
                member.stored_bytes,
                index as u64 + 1,
                member_count,
                root,
                &generation_name,
                control,
            )?;
        }
        write_generation_manifest_controlled(
            &generation_dir.join(MANIFEST_FILE),
            prepared.manifest.canonical_bytes(),
            root,
            &generation_name,
            control,
        )?;
        injected_io_checkpoint(
            control,
            PublicationIoPoint::GenerationDirectorySync,
            Some(root),
            Some(&generation_name),
            &generation_dir,
        )?;
        sync_directory(&generation_dir)?;
        cancellation_checkpoint(
            control,
            PublicationPoint::ManifestSynced,
            Some(root),
            Some(&generation_name),
        )?;

        let verified = self.validate_generation(&generation_name, root)?;
        if verified.manifest.canonical_bytes() != prepared.manifest.canonical_bytes() {
            return Err(ArtifactError::RootCollision { root });
        }
        cancellation_checkpoint(
            control,
            PublicationPoint::GenerationVerified,
            Some(root),
            Some(&generation_name),
        )?;
        Ok(StagedArtifactSet {
            store: self.clone(),
            generation_name,
            manifest: verified.manifest,
        })
    }

    fn create_generation<C: PublicationControl + ?Sized>(
        &self,
        root: ArtifactSetRoot,
        control: &mut C,
    ) -> Result<(String, PathBuf), ArtifactError> {
        let thread = thread_token();
        for _ in 0..1024 {
            let sequence = GENERATION_SEQUENCE.fetch_add(1, Ordering::Relaxed);
            let name = format!(
                "g-{}-{}-{thread}-{sequence}",
                root.to_hex(),
                std::process::id()
            );
            let generation = self.generations_dir().join(&name);
            injected_io_checkpoint(
                control,
                PublicationIoPoint::GenerationDirectoryCreate,
                Some(root),
                None,
                &generation,
            )?;
            match fs::create_dir(&generation) {
                Ok(()) => {
                    injected_io_checkpoint(
                        control,
                        PublicationIoPoint::GenerationsDirectorySync,
                        Some(root),
                        Some(&name),
                        &self.generations_dir(),
                    )?;
                    sync_directory(&self.generations_dir())?;
                    return Ok((name, generation));
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                Err(error) => {
                    return Err(io_error("creating artifact generation", &generation, error));
                }
            }
        }
        Err(ArtifactError::ResourceLimitExceeded {
            resource: ArtifactResource::GenerationEntries,
            allowed: 1024,
            observed: 1025,
        })
    }

    fn resolve_root(
        &self,
        expected_root: ArtifactSetRoot,
    ) -> Result<ResolvedArtifactSet, ArtifactError> {
        let binding_path = self.roots_dir().join(expected_root.to_hex());
        let bytes = match read_bounded_regular(
            &binding_path,
            POINTER_LIMIT,
            ArtifactResource::PointerBytes,
        ) {
            Ok(bytes) => bytes,
            Err(ArtifactError::Io { source, .. }) if source.kind() == io::ErrorKind::NotFound => {
                return Err(ArtifactError::RootNotBound {
                    root: expected_root,
                });
            }
            Err(error) => return Err(error),
        };
        let text = std::str::from_utf8(&bytes).map_err(|_| ArtifactError::MalformedPointer {
            kind: "root binding",
        })?;
        let Some(generation_name) = text.strip_suffix('\n') else {
            return Err(ArtifactError::MalformedPointer {
                kind: "root binding",
            });
        };
        validate_generation_name(generation_name)?;
        self.validate_generation(generation_name, expected_root)
    }

    fn validate_generation(
        &self,
        generation_name: &str,
        expected_root: ArtifactSetRoot,
    ) -> Result<ResolvedArtifactSet, ArtifactError> {
        validate_generation_name(generation_name)?;
        let generation_dir = self.generations_dir().join(generation_name);
        ensure_real_directory(&generation_dir)?;
        let manifest_path = generation_dir.join(MANIFEST_FILE);
        let manifest_bytes = read_bounded_regular(
            &manifest_path,
            self.limits.max_manifest_bytes,
            ArtifactResource::ManifestBytes,
        )?;
        let manifest = ArtifactSetManifest::from_canonical_bytes(&manifest_bytes, self.limits)?;
        if manifest.root() != expected_root {
            return Err(ArtifactError::RootMismatch {
                expected: expected_root,
                actual: manifest.root(),
            });
        }

        verify_generation_inventory(&generation_dir, &manifest, self.limits)?;
        for member in manifest.members() {
            verify_member(&generation_dir.join(member.name()), member, self.limits)?;
        }
        Ok(ResolvedArtifactSet {
            root: manifest.root(),
            generation_name: generation_name.to_string(),
            generation_dir,
            manifest,
        })
    }
}

/// A fully verified generation that is not yet bound or active.
#[derive(Debug)]
pub struct StagedArtifactSet {
    store: ArtifactStore,
    generation_name: String,
    manifest: ArtifactSetManifest,
}

impl StagedArtifactSet {
    pub fn generation_name(&self) -> &str {
        &self.generation_name
    }

    pub const fn root(&self) -> ArtifactSetRoot {
        self.manifest.root()
    }

    pub fn manifest(&self) -> &ArtifactSetManifest {
        &self.manifest
    }

    /// Atomically bind this verified generation to its content root. This still
    /// does not change `ACTIVE`.
    pub fn bind(self) -> Result<BoundArtifactSet, ArtifactError> {
        let mut control = NeverCancel;
        self.bind_with_control(&mut control)
    }

    /// [`StagedArtifactSet::bind`] with deterministic cancellation observations.
    pub fn bind_with_control<C: PublicationControl + ?Sized>(
        self,
        control: &mut C,
    ) -> Result<BoundArtifactSet, ArtifactError> {
        let verified = self
            .store
            .validate_generation(&self.generation_name, self.manifest.root())?;
        if verified.manifest.canonical_bytes() != self.manifest.canonical_bytes() {
            return Err(ArtifactError::RootCollision {
                root: self.manifest.root(),
            });
        }
        cancellation_checkpoint(
            control,
            PublicationPoint::BeforeRootBinding,
            Some(self.manifest.root()),
            Some(&self.generation_name),
        )?;
        let binding_path = self.store.roots_dir().join(self.manifest.root().to_hex());
        let pointer = format!("{}\n", self.generation_name);
        write_pointer_controlled(
            pointer.as_bytes(),
            &binding_path,
            ArtifactPointer::RootBinding,
            self.manifest.root(),
            &self.generation_name,
            control,
        )?;
        cancellation_checkpoint(
            control,
            PublicationPoint::RootBound,
            Some(self.manifest.root()),
            Some(&self.generation_name),
        )?;
        let resolved = self.store.resolve_root(self.manifest.root())?;
        if resolved.manifest.canonical_bytes() != self.manifest.canonical_bytes() {
            return Err(ArtifactError::RootCollision {
                root: self.manifest.root(),
            });
        }
        Ok(BoundArtifactSet {
            store: self.store,
            resolved,
        })
    }
}

/// A verified root binding that has not necessarily been made active.
#[derive(Debug)]
pub struct BoundArtifactSet {
    store: ArtifactStore,
    resolved: ResolvedArtifactSet,
}

impl BoundArtifactSet {
    pub const fn root(&self) -> ArtifactSetRoot {
        self.resolved.root
    }

    pub fn resolved(&self) -> &ResolvedArtifactSet {
        &self.resolved
    }

    /// Atomically make the whole bound generation active.
    ///
    /// Another publisher may supersede it after this call's rename, just as with
    /// any atomic register; at the linearization point, consumers see this complete
    /// root and never a mixture.
    pub fn activate(self) -> Result<ArtifactPublication, ArtifactError> {
        let mut control = NeverCancel;
        self.activate_with_control(&mut control)
    }

    /// [`BoundArtifactSet::activate`] with a final pre-linearization
    /// cancellation observation.
    pub fn activate_with_control<C: PublicationControl + ?Sized>(
        self,
        control: &mut C,
    ) -> Result<ArtifactPublication, ArtifactError> {
        let current = self.store.resolve_root(self.resolved.root)?;
        if current.manifest.canonical_bytes() != self.resolved.manifest.canonical_bytes() {
            return Err(ArtifactError::RootCollision {
                root: self.resolved.root,
            });
        }
        cancellation_checkpoint(
            control,
            PublicationPoint::BeforeActivation,
            Some(current.root),
            Some(&current.generation_name),
        )?;
        let active_path = self.store.root.join(ACTIVE_FILE);
        let pointer = format!("{}\n", self.resolved.root);
        write_pointer_controlled(
            pointer.as_bytes(),
            &active_path,
            ArtifactPointer::Active,
            current.root,
            &current.generation_name,
            control,
        )?;
        Ok(ArtifactPublication {
            root: current.root,
            generation_name: current.generation_name,
            generation_dir: current.generation_dir,
            manifest: current.manifest,
        })
    }
}

/// Result of one successful activation.
#[derive(Debug, Clone)]
pub struct ArtifactPublication {
    root: ArtifactSetRoot,
    generation_name: String,
    generation_dir: PathBuf,
    manifest: ArtifactSetManifest,
}

impl ArtifactPublication {
    pub const fn root(&self) -> ArtifactSetRoot {
        self.root
    }

    pub fn generation_name(&self) -> &str {
        &self.generation_name
    }

    pub fn generation_dir(&self) -> &Path {
        &self.generation_dir
    }

    pub fn manifest(&self) -> &ArtifactSetManifest {
        &self.manifest
    }
}

/// A complete generation returned by the resolver.
#[derive(Debug, Clone)]
pub struct ResolvedArtifactSet {
    root: ArtifactSetRoot,
    generation_name: String,
    generation_dir: PathBuf,
    manifest: ArtifactSetManifest,
}

impl ResolvedArtifactSet {
    pub const fn root(&self) -> ArtifactSetRoot {
        self.root
    }

    pub fn generation_name(&self) -> &str {
        &self.generation_name
    }

    pub fn generation_dir(&self) -> &Path {
        &self.generation_dir
    }

    pub fn manifest(&self) -> &ArtifactSetManifest {
        &self.manifest
    }

    /// The verified path of one manifested member.
    pub fn member_path(&self, name: &str) -> Option<PathBuf> {
        self.manifest
            .members()
            .iter()
            .any(|member| member.name() == name)
            .then(|| self.generation_dir.join(name))
    }
}

fn write_generation_member_controlled<C: PublicationControl + ?Sized>(
    path: &Path,
    bytes: &[u8],
    member_index: u64,
    member_count: u64,
    root: ArtifactSetRoot,
    generation_name: &str,
    control: &mut C,
) -> Result<(), ArtifactError> {
    injected_io_checkpoint(
        control,
        PublicationIoPoint::MemberCreate {
            member_index,
            member_count,
        },
        Some(root),
        Some(generation_name),
        path,
    )?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| io_error("creating generation manifest", path, error))?;
    let mut bytes_written = 0u64;
    for chunk in bytes.chunks(HASH_CHUNK_BYTES) {
        injected_io_checkpoint(
            control,
            PublicationIoPoint::MemberChunkWrite {
                member_index,
                member_count,
                offset: bytes_written,
                chunk_len: chunk.len() as u64,
                total_len: bytes.len() as u64,
            },
            Some(root),
            Some(generation_name),
            path,
        )?;
        file.write_all(chunk)
            .map_err(|error| io_error("writing generation member", path, error))?;
        bytes_written = bytes_written.saturating_add(chunk.len() as u64);
        cancellation_checkpoint(
            control,
            PublicationPoint::MemberChunkWritten {
                member_index,
                member_count,
                bytes_written,
            },
            Some(root),
            Some(generation_name),
        )?;
    }
    injected_io_checkpoint(
        control,
        PublicationIoPoint::MemberFileSync {
            member_index,
            member_count,
        },
        Some(root),
        Some(generation_name),
        path,
    )?;
    file.sync_all()
        .map_err(|error| io_error("syncing generation member", path, error))?;
    cancellation_checkpoint(
        control,
        PublicationPoint::MemberSynced {
            member_index,
            member_count,
        },
        Some(root),
        Some(generation_name),
    )
}

fn write_generation_manifest_controlled<C: PublicationControl + ?Sized>(
    path: &Path,
    bytes: &[u8],
    root: ArtifactSetRoot,
    generation_name: &str,
    control: &mut C,
) -> Result<(), ArtifactError> {
    injected_io_checkpoint(
        control,
        PublicationIoPoint::ManifestCreate,
        Some(root),
        Some(generation_name),
        path,
    )?;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| io_error("creating generation member", path, error))?;
    injected_io_checkpoint(
        control,
        PublicationIoPoint::ManifestWrite {
            byte_len: bytes.len() as u64,
        },
        Some(root),
        Some(generation_name),
        path,
    )?;
    file.write_all(bytes)
        .map_err(|error| io_error("writing generation manifest", path, error))?;
    injected_io_checkpoint(
        control,
        PublicationIoPoint::ManifestFileSync,
        Some(root),
        Some(generation_name),
        path,
    )?;
    file.sync_all()
        .map_err(|error| io_error("syncing generation manifest", path, error))
}

fn ensure_real_directory(path: &Path) -> Result<(), ArtifactError> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| io_error("inspecting directory", path, error))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(ArtifactError::NonRegularEntry {
            path: path.to_path_buf(),
        });
    }
    Ok(())
}

fn sync_directory(path: &Path) -> Result<(), ArtifactError> {
    File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| io_error("syncing directory", path, error))
}

fn read_bounded_regular(
    path: &Path,
    max_bytes: u64,
    resource: ArtifactResource,
) -> Result<Vec<u8>, ArtifactError> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| io_error("inspecting file", path, error))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(ArtifactError::NonRegularEntry {
            path: path.to_path_buf(),
        });
    }
    check_limit(resource, max_bytes, metadata.len())?;
    let file = File::open(path).map_err(|error| io_error("opening file", path, error))?;
    let mut bytes = Vec::new();
    let mut bounded = file.take(max_bytes.saturating_add(1));
    bounded
        .read_to_end(&mut bytes)
        .map_err(|error| io_error("reading file", path, error))?;
    check_limit(resource, max_bytes, bytes.len() as u64)?;
    Ok(bytes)
}

fn verify_generation_inventory(
    generation_dir: &Path,
    manifest: &ArtifactSetManifest,
    limits: ArtifactLimits,
) -> Result<(), ArtifactError> {
    let mut actual = Vec::new();
    let entries = fs::read_dir(generation_dir)
        .map_err(|error| io_error("reading generation directory", generation_dir, error))?;
    for entry in entries {
        let entry =
            entry.map_err(|error| io_error("reading generation entry", generation_dir, error))?;
        let name = entry.file_name().into_string().map_err(|_| {
            ArtifactError::GenerationInventoryMismatch {
                expected: Vec::new(),
                actual: Vec::new(),
            }
        })?;
        actual.push(name);
        check_limit(
            ArtifactResource::GenerationEntries,
            limits.max_members.saturating_add(1),
            actual.len() as u64,
        )?;
    }
    actual.sort();
    let mut expected: Vec<String> = manifest
        .members()
        .iter()
        .map(|member| member.name().to_string())
        .collect();
    expected.push(MANIFEST_FILE.to_string());
    expected.sort();
    if actual != expected {
        return Err(ArtifactError::GenerationInventoryMismatch { expected, actual });
    }
    Ok(())
}

fn verify_member(
    path: &Path,
    member: &ArtifactMemberRecord,
    limits: ArtifactLimits,
) -> Result<(), ArtifactError> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| io_error("inspecting artifact member", path, error))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(ArtifactError::NonRegularEntry {
            path: path.to_path_buf(),
        });
    }
    if metadata.len() != member.byte_len {
        return Err(ArtifactError::MemberLengthMismatch {
            name: member.name.clone(),
            expected: member.byte_len,
            actual: metadata.len(),
        });
    }
    check_limit(
        ArtifactResource::MemberBytes,
        limits.max_member_bytes,
        metadata.len(),
    )?;
    let mut file =
        File::open(path).map_err(|error| io_error("opening artifact member", path, error))?;
    let mut hasher = byte_hasher(member.byte_len);
    let mut buffer = [0u8; HASH_CHUNK_BYTES];
    let mut observed = 0u64;
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| io_error("reading artifact member", path, error))?;
        if read == 0 {
            break;
        }
        observed =
            observed
                .checked_add(read as u64)
                .ok_or(ArtifactError::ResourceLimitExceeded {
                    resource: ArtifactResource::MemberBytes,
                    allowed: limits.max_member_bytes,
                    observed: u64::MAX,
                })?;
        check_limit(
            ArtifactResource::MemberBytes,
            limits.max_member_bytes,
            observed,
        )?;
        hasher.update(&buffer[..read]);
    }
    if observed != member.byte_len {
        return Err(ArtifactError::MemberLengthMismatch {
            name: member.name.clone(),
            expected: member.byte_len,
            actual: observed,
        });
    }
    let actual = ArtifactByteHash(hasher.finalize());
    if actual != member.byte_hash {
        return Err(ArtifactError::MemberByteHashMismatch {
            name: member.name.clone(),
            expected: member.byte_hash,
            actual,
        });
    }
    Ok(())
}

fn validate_generation_name(name: &str) -> Result<(), ArtifactError> {
    if !name.starts_with("g-")
        || name.len() as u64 > MAX_COMPONENT_BYTES
        || name.contains(['/', '\\', '\0'])
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-')
    {
        return Err(ArtifactError::InvalidGenerationName {
            name: name.to_string(),
        });
    }
    let mut components = Path::new(name).components();
    if !matches!(components.next(), Some(Component::Normal(component)) if component == OsStr::new(name))
        || components.next().is_some()
    {
        return Err(ArtifactError::InvalidGenerationName {
            name: name.to_string(),
        });
    }
    Ok(())
}

fn thread_token() -> String {
    let digits: String = format!("{:?}", std::thread::current().id())
        .chars()
        .filter(char::is_ascii_digit)
        .collect();
    if digits.is_empty() {
        "0".to_string()
    } else {
        digits
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_hex_parser_is_canonical() {
        let root = artifact_set_root(b"manifest");
        assert_eq!(ArtifactSetRoot::from_hex(&root.to_hex()).unwrap(), root);
        assert!(ArtifactSetRoot::from_hex(&root.to_hex().to_uppercase()).is_err());
        assert!(ArtifactSetRoot::from_hex("00").is_err());
    }

    #[test]
    fn generation_names_are_one_bounded_component() {
        let root = artifact_set_root(b"manifest");
        let name = format!("g-{}-1-2-3", root.to_hex());
        assert!(validate_generation_name(&name).is_ok());
        assert!(validate_generation_name("../outside").is_err());
        assert!(validate_generation_name("g-part/child").is_err());
    }
}
