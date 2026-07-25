//! The epoch laboratory's append-only revision chain (bead `fln-q3u4`, carved
//! out of the `fln-euo` Tribunal bootstrap epic; plan §18).
//!
//! # What this exists to fix
//!
//! `tribunal/epochs/<tag>/MANIFEST.txt` opens by saying "Immutable once
//! published: revisions are reviewed, hashed regenerations." Before this crate
//! that sentence was the entire mechanism: the file carried no revision id, no
//! parent link and no root, and nothing anywhere would have noticed a published
//! manifest being edited. Every other vocabulary in the epic binds to an epoch
//! revision, so an unenforced revision identity is load-bearing in the worst
//! way — everything above it inherits an assumption nobody checks.
//!
//! # The model
//!
//! A chain is a sequence of revisions. Each names its parent's root, the
//! content digest of the manifest it publishes, and its own root — and the root
//! is always RECOMPUTED on read, never trusted. Appending is the only mutation:
//! there is no API that edits or removes a published revision, and
//! [`Chain::verify`] rejects a chain whose history has been rewritten even if
//! the rewrite is internally consistent, because the parent linkage pins it.
//!
//! # Failure atomicity
//!
//! [`publish`] writes a candidate, verifies the chain that candidate would
//! produce, syncs it, and only then atomically renames it into place. An
//! interruption at any point leaves the PRIOR revision authoritative, and a
//! leftover candidate is refused as [`ChainError::CandidatePresent`] rather
//! than consumed — the same discipline the kernel-ownership publisher uses, for
//! the same reason: a half-published identity that looks complete is worse than
//! an absent one.

#![forbid(unsafe_code)]

pub mod corpus;
pub mod derive;
pub mod g0;
pub mod normalize;
pub mod oracle;
pub mod parity;
pub mod poison;

use fln_hash::domain::{Digest, Domain, DomainHasher};
use std::path::{Path, PathBuf};

/// Schema line of the chain file. Versioned: a semantic change to what a
/// revision covers registers a NEW schema rather than reinterpreting history.
pub const CHAIN_SCHEMA: &str = "fln-epoch-revisions/1";

/// Domain tag for a revision root.
const REVISION_TAG: &[u8] = b"fln.epoch-lab.revision/1";
/// Domain tag for the content digest of a published manifest.
const CONTENT_TAG: &[u8] = b"fln.epoch-lab.content/1";

/// The chain file's name inside an epoch directory.
pub const CHAIN_FILE: &str = "REVISIONS.txt";
/// The staging name used during publication.
pub const CANDIDATE_FILE: &str = "REVISIONS.txt.candidate";

/// Every way a chain can fail to be authoritative. Total and typed: parsing or
/// verifying a hostile file yields one of these, never a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChainError {
    /// Missing or unrecognised schema line.
    BadSchema { found: String },
    /// Missing epoch line, or one naming a different epoch than the directory.
    BadEpoch { expected: String, found: String },
    /// A line that is not a well-formed revision record.
    Malformed { line: usize, reason: &'static str },
    /// Revision indices must be 1, 2, 3 … with no gaps and no reordering.
    IndexNotSequential { expected: u64, found: u64 },
    /// A revision whose recorded parent is not its predecessor's root. This is
    /// what makes a rewritten history detectable even when each record is
    /// internally consistent.
    ParentMismatch { index: u64 },
    /// A revision whose recorded root is not the recomputed one.
    RootMismatch { index: u64 },
    /// The head revision does not bind the manifest actually on disk — the
    /// "mutable revision" mutation: someone edited a published manifest.
    ContentMismatch { expected: String, found: String },
    /// A chain with no revisions at all.
    Empty,
    /// A staging candidate exists, so a previous publication was interrupted.
    /// Typed inconclusive: the PRIOR revision remains authoritative and is not
    /// silently replaced by whatever the candidate happens to contain.
    CandidatePresent { path: String },
    /// I/O, carried as a string so the error type stays comparable.
    Io { what: &'static str, detail: String },
}

impl std::fmt::Display for ChainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BadSchema { found } => write!(f, "unrecognised chain schema {found:?}"),
            Self::BadEpoch { expected, found } => {
                write!(f, "chain names epoch {found:?}, expected {expected:?}")
            }
            Self::Malformed { line, reason } => {
                write!(f, "malformed record at line {line}: {reason}")
            }
            Self::IndexNotSequential { expected, found } => {
                write!(
                    f,
                    "revision index {found} breaks the sequence (expected {expected})"
                )
            }
            Self::ParentMismatch { index } => {
                write!(f, "revision {index} does not name its predecessor's root")
            }
            Self::RootMismatch { index } => {
                write!(
                    f,
                    "revision {index}'s recorded root is not the recomputed one"
                )
            }
            Self::ContentMismatch { expected, found } => write!(
                f,
                "the head revision binds content {expected}, but the manifest on disk hashes to {found}"
            ),
            Self::Empty => write!(f, "chain contains no revisions"),
            Self::CandidatePresent { path } => write!(
                f,
                "a publication candidate remains at {path}; the prior revision stays authoritative"
            ),
            Self::Io { what, detail } => write!(f, "{what}: {detail}"),
        }
    }
}

impl std::error::Error for ChainError {}

/// The digest of a manifest's bytes, domain-separated so a manifest digest can
/// never be confused with a revision root.
pub fn content_digest(manifest: &[u8]) -> Digest {
    let mut h = DomainHasher::new(Domain::Fixture);
    h.update(CONTENT_TAG);
    h.update(&[0]);
    h.update(&(manifest.len() as u64).to_le_bytes());
    h.update(manifest);
    h.finalize()
}

/// One published revision.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Revision {
    pub index: u64,
    /// `None` for the genesis revision.
    pub parent: Option<Digest>,
    pub content: Digest,
    pub root: Digest,
}

/// Recompute a revision root from its inputs. Every field that identifies the
/// revision participates, length-prefixed where variable, so two different
/// histories cannot collide by concatenation.
fn compute_root(epoch: &str, index: u64, parent: Option<&Digest>, content: &Digest) -> Digest {
    let mut h = DomainHasher::new(Domain::Fixture);
    h.update(REVISION_TAG);
    h.update(&[0]);
    h.update(&(epoch.len() as u64).to_le_bytes());
    h.update(epoch.as_bytes());
    h.update(&index.to_le_bytes());
    // The presence of a parent is itself hashed, so a genesis revision can
    // never be re-read as a child of an all-zero root.
    match parent {
        Some(p) => {
            h.update(&[1]);
            h.update(&p.0);
        }
        None => {
            h.update(&[0]);
        }
    }
    h.update(&content.0);
    h.finalize()
}

/// An append-only revision chain for one epoch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Chain {
    pub epoch: String,
    revisions: Vec<Revision>,
}

impl Chain {
    /// The genesis chain publishing `content` for `epoch`.
    pub fn genesis(epoch: &str, content: Digest) -> Chain {
        let root = compute_root(epoch, 1, None, &content);
        Chain {
            epoch: epoch.to_string(),
            revisions: vec![Revision {
                index: 1,
                parent: None,
                content,
                root,
            }],
        }
    }

    /// A NEW chain with one more revision. Takes `&self` and returns an owned
    /// chain rather than mutating in place: appending is the only way history
    /// grows, and there is deliberately no API that edits or truncates it.
    pub fn appended(&self, content: Digest) -> Chain {
        let head = self.revisions.last().expect("a chain is never empty");
        let index = head.index + 1;
        let parent = head.root;
        let root = compute_root(&self.epoch, index, Some(&parent), &content);
        let mut revisions = self.revisions.clone();
        revisions.push(Revision {
            index,
            parent: Some(parent),
            content,
            root,
        });
        Chain {
            epoch: self.epoch.clone(),
            revisions,
        }
    }

    pub fn revisions(&self) -> &[Revision] {
        &self.revisions
    }

    pub fn head(&self) -> &Revision {
        self.revisions.last().expect("a chain is never empty")
    }

    /// Render the canonical file text.
    pub fn render(&self) -> String {
        let mut out = format!("schema {CHAIN_SCHEMA}\nepoch {}\n", self.epoch);
        for r in &self.revisions {
            out.push_str(&format!(
                "revision {} parent={} content={} root={}\n",
                r.index,
                match &r.parent {
                    Some(p) => p.to_hex(),
                    None => "genesis".to_string(),
                },
                r.content.to_hex(),
                r.root.to_hex()
            ));
        }
        out
    }

    /// Parse a chain file. Total: any input yields a `Chain` or a typed error.
    pub fn parse(text: &str, expected_epoch: &str) -> Result<Chain, ChainError> {
        let mut epoch: Option<String> = None;
        let mut revisions: Vec<Revision> = Vec::new();
        let mut saw_schema = false;

        for (i, raw) in text.lines().enumerate() {
            let line = raw.trim();
            let no = i + 1;
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if let Some(rest) = line.strip_prefix("schema ") {
                if rest.trim() != CHAIN_SCHEMA {
                    return Err(ChainError::BadSchema {
                        found: rest.trim().to_string(),
                    });
                }
                saw_schema = true;
                continue;
            }
            if let Some(rest) = line.strip_prefix("epoch ") {
                epoch = Some(rest.trim().to_string());
                continue;
            }
            let Some(rest) = line.strip_prefix("revision ") else {
                return Err(ChainError::Malformed {
                    line: no,
                    reason: "expected schema, epoch, or revision",
                });
            };
            let fields: Vec<&str> = rest.split_whitespace().collect();
            let [idx, parent, content, root] = fields.as_slice() else {
                return Err(ChainError::Malformed {
                    line: no,
                    reason: "a revision needs index, parent=, content=, root=",
                });
            };
            let index = idx.parse::<u64>().map_err(|_| ChainError::Malformed {
                line: no,
                reason: "revision index is not a number",
            })?;
            let parent = match parent.strip_prefix("parent=") {
                Some("genesis") => None,
                Some(hex) => Some(parse_digest(hex).ok_or(ChainError::Malformed {
                    line: no,
                    reason: "parent is not a digest",
                })?),
                None => {
                    return Err(ChainError::Malformed {
                        line: no,
                        reason: "missing parent=",
                    });
                }
            };
            let content = content
                .strip_prefix("content=")
                .and_then(parse_digest)
                .ok_or(ChainError::Malformed {
                    line: no,
                    reason: "missing or malformed content=",
                })?;
            let root =
                root.strip_prefix("root=")
                    .and_then(parse_digest)
                    .ok_or(ChainError::Malformed {
                        line: no,
                        reason: "missing or malformed root=",
                    })?;
            revisions.push(Revision {
                index,
                parent,
                content,
                root,
            });
        }

        if !saw_schema {
            return Err(ChainError::BadSchema {
                found: String::new(),
            });
        }
        let epoch = epoch.unwrap_or_default();
        if epoch != expected_epoch {
            return Err(ChainError::BadEpoch {
                expected: expected_epoch.to_string(),
                found: epoch,
            });
        }
        if revisions.is_empty() {
            return Err(ChainError::Empty);
        }
        Ok(Chain { epoch, revisions })
    }

    /// Recompute every root and check every parent link.
    ///
    /// Nothing recorded in the file is trusted: the roots are derived again
    /// from the epoch, index, parent and content, and compared. A rewritten
    /// history is caught by the parent linkage even when each individual record
    /// is internally consistent, because changing any revision changes its root
    /// and therefore every later revision's parent.
    pub fn verify(&self) -> Result<(), ChainError> {
        for (i, r) in self.revisions.iter().enumerate() {
            let expected_index = i as u64 + 1;
            if r.index != expected_index {
                return Err(ChainError::IndexNotSequential {
                    expected: expected_index,
                    found: r.index,
                });
            }
            let expected_parent = if i == 0 {
                None
            } else {
                Some(self.revisions[i - 1].root)
            };
            if r.parent != expected_parent {
                return Err(ChainError::ParentMismatch { index: r.index });
            }
            if compute_root(&self.epoch, r.index, r.parent.as_ref(), &r.content) != r.root {
                return Err(ChainError::RootMismatch { index: r.index });
            }
        }
        Ok(())
    }

    /// Verify the chain AND that its head binds the manifest actually on disk.
    ///
    /// The second half is what catches an edited published manifest: the chain
    /// can be perfectly well-formed and still no longer describe reality.
    pub fn verify_against(&self, manifest: &[u8]) -> Result<(), ChainError> {
        self.verify()?;
        let actual = content_digest(manifest);
        if actual != self.head().content {
            return Err(ChainError::ContentMismatch {
                expected: self.head().content.to_hex(),
                found: actual.to_hex(),
            });
        }
        Ok(())
    }
}

fn parse_digest(hex: &str) -> Option<Digest> {
    if hex.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(hex.get(i * 2..i * 2 + 2)?, 16).ok()?;
    }
    Some(Digest(out))
}

/// What a publication did.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublishReport {
    pub epoch: String,
    pub index: u64,
    pub root: String,
    /// True when the manifest already matched the head, so nothing was written.
    pub already_current: bool,
}

fn io<E: std::fmt::Display>(what: &'static str) -> impl Fn(E) -> ChainError {
    move |e| ChainError::Io {
        what,
        detail: e.to_string(),
    }
}

/// Publish `manifest_name`'s current bytes as the next revision of the epoch
/// laboratory at `epoch_dir`, failure-atomically.
///
/// Order matters and is the whole point:
/// 1. refuse outright if a candidate remains — a previous run was interrupted,
///    and the prior revision stays authoritative rather than being replaced by
///    whatever that candidate holds;
/// 2. read and verify the existing chain BEFORE writing anything, so a corrupt
///    chain cannot be extended;
/// 3. write the candidate, sync it, and re-parse and verify what was actually
///    written rather than what we intended to write;
/// 4. atomic rename, then sync the directory.
///
/// A crash at any point leaves either the prior chain or the prior chain plus a
/// refused candidate. It never leaves a half-written authoritative file.
pub fn publish(
    epoch_dir: &Path,
    epoch: &str,
    manifest_name: &str,
) -> Result<PublishReport, ChainError> {
    let chain_path = epoch_dir.join(CHAIN_FILE);
    let candidate_path = epoch_dir.join(CANDIDATE_FILE);
    if candidate_path.exists() {
        return Err(ChainError::CandidatePresent {
            path: candidate_path.display().to_string(),
        });
    }
    let manifest = std::fs::read(epoch_dir.join(manifest_name)).map_err(io("read manifest"))?;
    let content = content_digest(&manifest);

    let next = if chain_path.exists() {
        let text = std::fs::read_to_string(&chain_path).map_err(io("read chain"))?;
        let existing = Chain::parse(&text, epoch)?;
        existing.verify()?;
        if existing.head().content == content {
            return Ok(PublishReport {
                epoch: epoch.to_string(),
                index: existing.head().index,
                root: existing.head().root.to_hex(),
                already_current: true,
            });
        }
        existing.appended(content)
    } else {
        Chain::genesis(epoch, content)
    };

    write_synced(&candidate_path, next.render().as_bytes())?;

    // Verify what LANDED, not what we meant to write. A truncated or partially
    // flushed candidate is caught here, while the prior chain is still the
    // authoritative one.
    let written = std::fs::read_to_string(&candidate_path).map_err(io("read candidate"))?;
    let parsed = Chain::parse(&written, epoch)?;
    parsed.verify_against(&manifest)?;

    std::fs::rename(&candidate_path, &chain_path).map_err(io("rename candidate"))?;
    if let Ok(dir) = std::fs::File::open(epoch_dir) {
        let _ = dir.sync_all();
    }
    Ok(PublishReport {
        epoch: epoch.to_string(),
        index: parsed.head().index,
        root: parsed.head().root.to_hex(),
        already_current: false,
    })
}

fn write_synced(path: &PathBuf, bytes: &[u8]) -> Result<(), ChainError> {
    use std::io::Write;
    let mut f = std::fs::File::create(path).map_err(io("create candidate"))?;
    f.write_all(bytes).map_err(io("write candidate"))?;
    f.sync_all().map_err(io("sync candidate"))?;
    Ok(())
}

/// Load and fully verify the authoritative chain for an epoch directory.
pub fn verify_epoch(
    epoch_dir: &Path,
    epoch: &str,
    manifest_name: &str,
) -> Result<Chain, ChainError> {
    let candidate_path = epoch_dir.join(CANDIDATE_FILE);
    if candidate_path.exists() {
        return Err(ChainError::CandidatePresent {
            path: candidate_path.display().to_string(),
        });
    }
    let text = std::fs::read_to_string(epoch_dir.join(CHAIN_FILE)).map_err(io("read chain"))?;
    let manifest = std::fs::read(epoch_dir.join(manifest_name)).map_err(io("read manifest"))?;
    let chain = Chain::parse(&text, epoch)?;
    chain.verify_against(&manifest)?;
    Ok(chain)
}
