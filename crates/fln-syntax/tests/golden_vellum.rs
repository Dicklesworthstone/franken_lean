//! Byte-exact goldens for Vellum's green trees and token streams (bead pending; plan §9).
//!
//! How this suite composes with the other Vellum test mechanisms — and the measured gap
//! between them — is written up in `crates/fln-syntax/TESTING_COMPOSITION.md`. Read it before
//! adding a suite here: the two mechanisms do NOT back each other up in the direction one
//! would assume, and their blind spots overlap.
//!
//! ## No update mode, by construction
//!
//! These tests **never write** the corpus or its provenance. There is no `UPDATE_GOLDENS`
//! environment variable to set, because a golden that can regenerate its own expectation is not a
//! golden — it is a mirror. A tree-shape change must FAIL here and stay failed until a human reads
//! the diff and edits the corpus deliberately.
//!
//! The regeneration path is [`emit_corpus_for_review`], which is `#[ignore]`d and only ever prints
//! to stdout. A human runs it, reads what it produced, and pastes the rows in. That is the ceremony,
//! and it is the same one `fln-verdict`'s certificate goldens use.
//!
//! ## The golden is of the RECOVERABLE form, not the raw bytes
//!
//! Inherited from bead franken_lean-tkr2 and held literally. The lexer runs on the crlfToLf-
//! normalized *view*, so a tree reconstructs the **view**, and recovering the file is
//! `SourceView::reconstruct_original`'s job. A golden frozen against raw bytes would either fail on
//! every CRLF row or be quietly relaxed until it passed.
//!
//! So each row freezes **both** forms and the chain between them:
//!
//! ```text
//! raw_hex   the input bytes, CRLF and all
//! view_hex  the normalized bytes the lexer consumed and the tree reconstructs
//! tokens    the token stream, one entry per token, with view offsets
//! tree      the green tree's shape and spans
//! ```
//!
//! and the tests assert `tree.reconstruct(view) == view_hex` **and**
//! `view.reconstruct_original() == raw_hex`. Freezing only one form would leave the map untested;
//! freezing both makes the recoverability itself part of the artifact.
//!
//! ## Why hand-rolled and not `insta`
//!
//! The dependency universe is closed (D1): `std` plus the FrankenSuite. No snapshot crate, no regex
//! crate. The comparison is therefore a byte loop that reports the first differing offset, which is
//! what a reviewer needs anyway — "mismatch" is not a diff.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_core::scratch::{ScratchRoot, VDI4_PREFIX};
use fln_syntax::attach::{TokenExtent, attach};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{ByteSpan, SourceInfo, SourceText};
use fln_syntax::token::{TokenKind, TokenTable};
use fln_syntax::tree::Syntax;
use fln_syntax::view::SourceView;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const CORPUS: &str = include_str!("corpus/vellum_goldens.hex");
const PROVENANCE: &str = include_str!("corpus/VELLUM_GOLDENS_PROVENANCE.md");
const PRODUCER: &str = "fln-syntax@0.0.0";
const PRODUCER_COMMIT: &str = "d5ecb96659c5830449c5f000d9d9a4b9cb320dc8";
const SUPERSEDED_PRODUCER_COMMIT: &str = "d64218a954f8447b3f29c4ca230ae5d158d56dc9";
const LEXER_SCHEMA: &str = "fln.vellum.token-stream/1";
const TREE_SCHEMA: &str = "fln.vellum.green-tree/1";
const GOLDEN_ROWS: usize = 8;
const REPOSITORY_EVIDENCE_SCOPE: &[&str] = &[
    ".beads/issues.jsonl",
    "ci/VERIFICATION_MANIFEST.jsonl",
    "AGENTS.md",
    "README.md",
    "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
    "ci",
    "crates",
    "scripts",
    "tools",
];

/// Exact backup-only anchor identities reviewed after the 2026-07-25 history rewrite, and after
/// the 2026-08-04T00:12Z rebase onto `origin/main`.
///
/// Every hex run is at most five characters so this declaration cannot satisfy the scanner it
/// governs. [`decode_segmented_allowance`] removes the separators and refuses malformed rows.
/// Exact-set equality, not this population count, is the law; the count is retained as an
/// independently reviewed anti-vacuity witness and must shrink with a repaired row.
///
/// **This population GREW once, 168 -> 172, and the reason is the whole justification.** The
/// 2026-08-04 rebase replayed five commits and left every original dangling — unlike 2026-07-25,
/// no backup ref retains them. Anchors that rebase orphaned inside *mutable* evidence were
/// repaired to their content-identical main twins instead of declared: `franken_lean-gii.19`'s
/// coverage row moved to `cd758687…` at `d138c6e5`, which is why no manifest token appears here.
/// The four added entries are the ones no repair can reach, because they sit in **immutable bead
/// comments** — `franken_lean-gii.19` comment 1880 and `franken_lean-j8h` comment 1879. Declaring
/// an anchor is the treatment of last resort for an immutable citation, never an alternative to
/// repairing a mutable one, and a token that becomes repairable must leave this list.
///
/// Declaring survives garbage collection: a dangling object that is pruned is counted through the
/// `missing_objects` intersection rather than dropping out, so no backup ref is needed to keep
/// these rows honest — and one was deliberately not created, since an undeclared locally
/// resolvable backup commit is itself a refusal.
const REVIEWED_BACKUP_ONLY_ALLOWANCE_COUNT: usize = 172;
const LOCAL_BACKUP_ONLY_ALLOWANCE: &[&str] = &[
    "0382d-7b",
    "041ad-4e0",
    "059eb-dcd",
    "05d9e-ad",
    "08c89-48f64-764f4-b719b-355a3-bb60f-cb19d-afae9",
    "0bfde-75b",
    "0c297-df4",
    "0d37e-f7e",
    "0ef65-091",
    "0effc-5b2",
    "0f014-54",
    "0f857-f20",
    "1061f-875",
    "10c9a-2e3",
    "1144d-e53",
    "1210a-2ed2a-9d307-439f4-67276-c9d7a-57fd9-eea4a",
    "12e1c-205",
    "13b9a-c63",
    "14153-28",
    "15be2-98b",
    "18d60-c53",
    "19580-7a9",
    "195e9-7d7",
    "199c3-76",
    "1a1f6-b8d",
    "1a3cb-dc0",
    "1b4b8-472",
    "1caa3-69e",
    "1eec9-dad",
    "22817-01",
    "24b16-eeb",
    "25c02-44",
    "25c02-44fc5-f6823-f5dbb-cf935-7e7ba-34d9c-32e15",
    "265ba-c5c",
    "26bac-b3e",
    "26cb2-add",
    "28577-270",
    "2a5ec-8ca",
    "2a7b1-66e",
    "2b0b1-b24",
    "2bb41-8c9",
    "2cba4-c79",
    "2cba4-c79d0-897df-981b0-b0880-a788e-ccb77-c5247",
    "2ddde-9eb",
    "35558-15",
    "35b39-e16",
    "35cf9-a6",
    "35cf9-a63",
    "368cd-df",
    "37df8-a3",
    "3847f-b04",
    "3ae1f-95",
    "3ae1f-959",
    "3c766-88",
    "3c766-88e",
    "3ceb3-711",
    "40558-4bb",
    "46186-f6",
    "46186-f67",
    "4747c-803",
    "4ad44-02",
    "4c406-1a",
    "50d92-55b",
    "50f65-ba4",
    "52c3b-bb",
    "54168-10c",
    "54603-f69",
    "54d61-c88",
    "554f6-bb249-40686-dae48-f9691-2e64c-4b4d9-062d8",
    "55fe7-108",
    "564b3-ae",
    "570fd-57b",
    "58053-019",
    "5df2f-968",
    "5fe33-68e",
    "5fe33-68e8b-84722-c551e-91bf8-593c6-d42d7-dd388",
    "61774-1b5",
    "65a20-263",
    "66e56-721",
    "6960d-068",
    "6b61d-76",
    "6c0e4-06",
    "6c0e4-064",
    "73e68-1cf",
    "74aed-94a",
    "768a3-6c4",
    "76d2e-1ed",
    "7882e-312",
    "7a493-32a",
    "7b788-f7d",
    "7e07d-6d",
    "8177e-ccd",
    "828d9-488",
    "86035-037",
    "8773d-2d0",
    "8bca8-3aa",
    "8d31a-d5d",
    "8f129-69b",
    "8ffaa-15b",
    "91eba-aea",
    "93c34-753",
    "94f56-38d",
    "97c33-34",
    "99291-ba6",
    "a1a69-aabb4-c3038-17c2b-7053c-95e36-c4987-2cc8e",
    "a21ac-783",
    "a368e-a0b",
    "a4251-e7d",
    "a7bc1-60",
    "a873e-73c",
    "a90fa-dad",
    "aa5d3-44",
    "ad2aa-8e1",
    "ad82f-b45",
    "ae906-30b",
    "ae906-30b9c-c825f-08c80-095dd-15602-2edb5-44475",
    "ae967-368",
    "af265-46a",
    "b0611-5fc",
    "b364e-d1c",
    "b364e-d1c9e-2497a-d1392-32163-e979a-56703-a1974",
    "b3863-54",
    "b3863-547",
    "b6b80-e98",
    "b825e-aa",
    "bb561-892",
    "bb665-b0b",
    "be14e-e9",
    "be14e-e9b",
    "bf693-bb2",
    "bf9ef-450",
    "c0add-37a",
    "c30b4-9e0",
    "c4990-9b3",
    "c4b13-364",
    "c500d-385",
    "c500d-3850a-62465-6c81f-e9601-d2cc2-4ccba-18990",
    "c584e-470db-a1e49-a12ee-17a53-cec9d-87bbc-e14a5",
    "c821d-9c",
    "cc8d7-469",
    "ccde9-57f",
    "cece9-f1",
    "d1850-d7",
    "d5cc0-84b",
    "d5e69-023",
    "d6421-8a9",
    "d6421-8a954-f8447-b3f29-c4ca2-30ae5-d158d-56dc9",
    "d927b-7d",
    "d954a-a9f",
    "d98ed-115c3-f7ffb-ccc01-b1edd-a044e-70a8f-ba09b",
    "dc4e8-1e6",
    "dd447-7bf",
    "df2c9-75d",
    "e14fe-98",
    "e14fe-98b",
    "e165d-db1",
    "e1a59-ac",
    "e2e19-fb2",
    "e3164-55e",
    "e3add-54c",
    "e493c-7d0",
    "ea21d-b0e",
    "f0fc6-718",
    "f1b25-fa",
    "f2190-330",
    "f2578-87",
    "f3b98-d22",
    "f4860-03f17-73a0d-950c0-e28f3-34ff2-e00a4-8b4a9",
    "f4c22-a2d",
    "f4db9-1f6b8-90785-2e03a-988ea-0d8ca-bf5cb-812c6",
    "fbe5d-be4",
    "fce6c-58c",
];
#[derive(Debug, Clone, PartialEq, Eq)]
enum AnchorReachability {
    MainReachable { commit: String },
    LocalBackupOnly { commit: String },
    Unresolved(AnchorRefusal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AnchorRefusal {
    InvalidShape,
    GitInvocation {
        operation: &'static str,
        kind: std::io::ErrorKind,
    },
    GitRefusal {
        operation: &'static str,
        exit_code: Option<i32>,
    },
    MalformedGitOutput {
        operation: &'static str,
    },
    NoMatchingObject,
    AmbiguousAbbreviation {
        matches: usize,
    },
    NotCommit {
        object_type: String,
    },
    RepositoryChanged {
        before: String,
        after: String,
    },
    AncestryIndeterminate {
        exit_code: Option<i32>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum AnchorInventoryRefusal {
    Git(AnchorRefusal),
    EmptyTrackedScope,
    DuplicateTrackedPath {
        path: String,
    },
    NonUtf8TrackedPath,
    ScopeContractMissing {
        entries: Vec<String>,
    },
    AllowanceMalformed {
        entry: String,
    },
    AllowanceDuplicate {
        anchor: String,
    },
    AllowancePopulationDrift {
        declared: usize,
        reviewed: usize,
    },
    AnchorUndecidable {
        anchor: String,
        origins: Vec<String>,
        reason: AnchorRefusal,
    },
    RepositoryChanged {
        before: String,
        after: String,
    },
    AllowanceMismatch {
        undeclared: Vec<String>,
        stale: Vec<String>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct AnchorInventory {
    tracked_paths: Vec<String>,
    candidate_origins: BTreeMap<String, BTreeSet<String>>,
    main_reachable: BTreeSet<String>,
    local_backup_only: BTreeSet<String>,
    missing_objects: BTreeSet<String>,
    non_anchors: BTreeSet<String>,
}

fn git_output<I, S>(repo: &Path, operation: &'static str, args: I) -> Result<Output, AnchorRefusal>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(["-c", "maintenance.auto=false"])
        .args(args)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", repo.join(".fln-no-global-gitconfig"))
        .env("GIT_OPTIONAL_LOCKS", "0")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("LC_ALL", "C")
        .output()
        .map_err(|error| AnchorRefusal::GitInvocation {
            operation,
            kind: error.kind(),
        })
}

fn successful_git_bytes<I, S>(
    repo: &Path,
    operation: &'static str,
    args: I,
) -> Result<Vec<u8>, AnchorRefusal>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let output = git_output(repo, operation, args)?;
    if !output.status.success() {
        return Err(AnchorRefusal::GitRefusal {
            operation,
            exit_code: output.status.code(),
        });
    }
    Ok(output.stdout)
}

fn successful_git_lines<I, S>(
    repo: &Path,
    operation: &'static str,
    args: I,
) -> Result<Vec<String>, AnchorRefusal>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let stdout = successful_git_bytes(repo, operation, args)?;
    let stdout = std::str::from_utf8(&stdout)
        .map_err(|_| AnchorRefusal::MalformedGitOutput { operation })?;
    Ok(stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect())
}

fn one_object_id(operation: &'static str, matches: Vec<String>) -> Result<String, AnchorRefusal> {
    match matches.as_slice() {
        [] => Err(AnchorRefusal::NoMatchingObject),
        [object] if object.len() == 40 && object.bytes().all(|byte| byte.is_ascii_hexdigit()) => {
            Ok(object.to_ascii_lowercase())
        }
        [_] => Err(AnchorRefusal::MalformedGitOutput { operation }),
        many => Err(AnchorRefusal::AmbiguousAbbreviation {
            matches: many.len(),
        }),
    }
}

fn main_commit(repo: &Path, operation: &'static str) -> Result<String, AnchorRefusal> {
    let lines = successful_git_lines(
        repo,
        operation,
        ["rev-parse", "--verify", "refs/heads/main^{commit}"],
    )?;
    one_object_id(operation, lines)
}

fn finish_reachability(
    commit: String,
    ancestry: bool,
    main_before: String,
    main_after: String,
) -> AnchorReachability {
    if main_before != main_after {
        return AnchorReachability::Unresolved(AnchorRefusal::RepositoryChanged {
            before: main_before,
            after: main_after,
        });
    }
    if ancestry {
        AnchorReachability::MainReachable { commit }
    } else {
        AnchorReachability::LocalBackupOnly { commit }
    }
}

fn classify_anchor_against(repo: &Path, anchor: &str, main: &str) -> AnchorReachability {
    if !(7..=40).contains(&anchor.len()) || !anchor.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return AnchorReachability::Unresolved(AnchorRefusal::InvalidShape);
    }

    let disambiguate = format!("--disambiguate={}", anchor.to_ascii_lowercase());
    let object =
        match successful_git_lines(repo, "resolve-anchor", ["rev-parse", disambiguate.as_str()])
            .and_then(|matches| one_object_id("resolve-anchor", matches))
        {
            Ok(object) => object,
            Err(reason) => return AnchorReachability::Unresolved(reason),
        };
    let object_type =
        match successful_git_lines(repo, "read-object-type", ["cat-file", "-t", &object]) {
            Ok(lines) if lines.len() == 1 => lines[0].clone(),
            Ok(_) => {
                return AnchorReachability::Unresolved(AnchorRefusal::MalformedGitOutput {
                    operation: "read-object-type",
                });
            }
            Err(reason) => return AnchorReachability::Unresolved(reason),
        };
    if object_type != "commit" {
        return AnchorReachability::Unresolved(AnchorRefusal::NotCommit { object_type });
    }

    let ancestry = match git_output(
        repo,
        "check-main-ancestry",
        ["merge-base", "--is-ancestor", &object, main],
    ) {
        Ok(output) if output.status.success() => true,
        Ok(output) if output.status.code() == Some(1) => false,
        Ok(output) => {
            return AnchorReachability::Unresolved(AnchorRefusal::AncestryIndeterminate {
                exit_code: output.status.code(),
            });
        }
        Err(reason) => return AnchorReachability::Unresolved(reason),
    };
    if ancestry {
        AnchorReachability::MainReachable { commit: object }
    } else {
        AnchorReachability::LocalBackupOnly { commit: object }
    }
}

fn classify_anchor(repo: &Path, anchor: &str) -> AnchorReachability {
    let main_before = match main_commit(repo, "read-main-before") {
        Ok(main) => main,
        Err(reason) => return AnchorReachability::Unresolved(reason),
    };
    let classification = classify_anchor_against(repo, anchor, &main_before);
    let main_after = match main_commit(repo, "read-main-after") {
        Ok(main) => main,
        Err(reason) => return AnchorReachability::Unresolved(reason),
    };
    if main_before == main_after {
        classification
    } else {
        AnchorReachability::Unresolved(AnchorRefusal::RepositoryChanged {
            before: main_before,
            after: main_after,
        })
    }
}

fn commit_anchor_candidates_bytes(bytes: &[u8]) -> Vec<String> {
    let mut candidates = Vec::new();
    let mut at = 0usize;
    while at < bytes.len() {
        if !bytes[at].is_ascii_hexdigit() {
            at += 1;
            continue;
        }
        let start = at;
        while at < bytes.len() && bytes[at].is_ascii_hexdigit() {
            at += 1;
        }
        let before_is_word = start
            .checked_sub(1)
            .and_then(|index| bytes.get(index))
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_');
        let after_is_word = bytes
            .get(at)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_');
        if (7..=40).contains(&(at - start)) && !before_is_word && !after_is_word {
            candidates.push(
                std::str::from_utf8(&bytes[start..at])
                    .expect("a run of ASCII hexadecimal digits is UTF-8")
                    .to_ascii_lowercase(),
            );
        }
    }
    candidates
}

fn commit_anchor_candidates(text: &str) -> Vec<String> {
    commit_anchor_candidates_bytes(text.as_bytes())
}

fn scan_evidence_file(path: &Path) -> Result<Vec<String>, std::io::ErrorKind> {
    fs::read_to_string(path)
        .map(|text| commit_anchor_candidates(&text))
        .map_err(|error| error.kind())
}

fn tracked_scope_paths(
    repo: &Path,
    revision: &str,
    scope: &[&str],
) -> Result<Vec<String>, AnchorInventoryRefusal> {
    let mut args = vec!["ls-tree", "-r", "-z", "--name-only", revision, "--"];
    args.extend_from_slice(scope);
    let stdout = successful_git_bytes(repo, "list-tracked-evidence-scope", args)
        .map_err(AnchorInventoryRefusal::Git)?;
    let mut seen = BTreeSet::new();
    let mut paths = Vec::new();
    for raw_path in stdout
        .split(|byte| *byte == b'\0')
        .filter(|path| !path.is_empty())
    {
        let path = std::str::from_utf8(raw_path)
            .map_err(|_| AnchorInventoryRefusal::NonUtf8TrackedPath)?
            .to_string();
        if !seen.insert(path.clone()) {
            return Err(AnchorInventoryRefusal::DuplicateTrackedPath { path });
        }
        paths.push(path);
    }
    if paths.is_empty() {
        return Err(AnchorInventoryRefusal::EmptyTrackedScope);
    }
    Ok(paths)
}

fn read_tracked_blob(
    repo: &Path,
    revision: &str,
    path: &str,
) -> Result<Vec<u8>, AnchorInventoryRefusal> {
    let object = format!("{revision}:{path}");
    successful_git_bytes(
        repo,
        "read-tracked-evidence-blob",
        ["cat-file", "blob", &object],
    )
    .map_err(AnchorInventoryRefusal::Git)
}

fn decode_segmented_allowance(
    allowance: &[&str],
) -> Result<BTreeSet<String>, AnchorInventoryRefusal> {
    let mut decoded = BTreeSet::new();
    for entry in allowance {
        let segments: Vec<&str> = entry.split('-').collect();
        if segments.len() < 2
            || segments.iter().any(|segment| {
                segment.is_empty()
                    || segment.len() > 5
                    || !segment.bytes().all(|byte| byte.is_ascii_hexdigit())
            })
        {
            return Err(AnchorInventoryRefusal::AllowanceMalformed {
                entry: (*entry).to_string(),
            });
        }
        let anchor = segments.concat().to_ascii_lowercase();
        if !(7..=40).contains(&anchor.len()) {
            return Err(AnchorInventoryRefusal::AllowanceMalformed {
                entry: (*entry).to_string(),
            });
        }
        if !decoded.insert(anchor.clone()) {
            return Err(AnchorInventoryRefusal::AllowanceDuplicate { anchor });
        }
    }
    Ok(decoded)
}

fn segment_anchor_for_fixture(anchor: &str) -> String {
    anchor
        .as_bytes()
        .chunks(5)
        .map(|chunk| std::str::from_utf8(chunk).expect("fixture anchor is ASCII"))
        .collect::<Vec<_>>()
        .join("-")
}

fn scan_repository_anchor_inventory(
    repo: &Path,
    revision: &str,
    scope: &[&str],
) -> Result<AnchorInventory, AnchorInventoryRefusal> {
    let tracked_paths = tracked_scope_paths(repo, revision, scope)?;
    let mut candidate_origins: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for path in &tracked_paths {
        let blob = read_tracked_blob(repo, revision, path)?;
        for candidate in commit_anchor_candidates_bytes(&blob) {
            candidate_origins
                .entry(candidate)
                .or_default()
                .insert(path.clone());
        }
    }

    let mut main_reachable = BTreeSet::new();
    let mut local_backup_only = BTreeSet::new();
    let mut missing_objects = BTreeSet::new();
    let mut non_anchors = BTreeSet::new();
    for (anchor, origins) in &candidate_origins {
        match classify_anchor_against(repo, anchor, revision) {
            AnchorReachability::MainReachable { .. } => {
                main_reachable.insert(anchor.clone());
            }
            AnchorReachability::LocalBackupOnly { .. } => {
                local_backup_only.insert(anchor.clone());
            }
            AnchorReachability::Unresolved(AnchorRefusal::NoMatchingObject) => {
                missing_objects.insert(anchor.clone());
                non_anchors.insert(anchor.clone());
            }
            AnchorReachability::Unresolved(AnchorRefusal::NotCommit { .. }) => {
                non_anchors.insert(anchor.clone());
            }
            AnchorReachability::Unresolved(reason) => {
                return Err(AnchorInventoryRefusal::AnchorUndecidable {
                    anchor: anchor.clone(),
                    origins: origins.iter().cloned().collect(),
                    reason,
                });
            }
        }
    }

    Ok(AnchorInventory {
        tracked_paths,
        candidate_origins,
        main_reachable,
        local_backup_only,
        missing_objects,
        non_anchors,
    })
}

/// Audit retained historical anchors without requiring a clone to carry local forensic refs.
///
/// A reviewed token that is still present in tracked evidence may be unavailable in a transport
/// clone, but it never becomes current authority: only main ancestry does that. The allowance
/// remains bidirectional because removing the token from the tracked scope, resolving it to a
/// current commit, or resolving it to a non-commit makes the declaration stale. A locally
/// resolvable backup-only commit that is not declared remains an immediate refusal.
fn audit_anchor_inventory(
    repo: &Path,
    scope: &[&str],
    allowance: &[&str],
) -> Result<AnchorInventory, AnchorInventoryRefusal> {
    let main_before =
        main_commit(repo, "inventory-main-before").map_err(AnchorInventoryRefusal::Git)?;
    let inventory = scan_repository_anchor_inventory(repo, &main_before, scope)?;
    let main_after =
        main_commit(repo, "inventory-main-after").map_err(AnchorInventoryRefusal::Git)?;
    if main_before != main_after {
        return Err(AnchorInventoryRefusal::RepositoryChanged {
            before: main_before,
            after: main_after,
        });
    }

    let declared = decode_segmented_allowance(allowance)?;
    let unavailable_but_retained: BTreeSet<String> = inventory
        .missing_objects
        .intersection(&declared)
        .cloned()
        .collect();
    let retained: BTreeSet<String> = inventory
        .local_backup_only
        .union(&unavailable_but_retained)
        .cloned()
        .collect();
    let undeclared: Vec<String> = inventory
        .local_backup_only
        .difference(&declared)
        .cloned()
        .collect();
    let stale: Vec<String> = declared.difference(&retained).cloned().collect();
    if !undeclared.is_empty() || !stale.is_empty() {
        return Err(AnchorInventoryRefusal::AllowanceMismatch { undeclared, stale });
    }
    Ok(inventory)
}

fn validate_repository_scope(paths: &[String]) -> Result<(), AnchorInventoryRefusal> {
    let present: BTreeSet<&str> = paths.iter().map(String::as_str).collect();
    let mut missing = Vec::new();
    for required in [
        ".beads/issues.jsonl",
        "ci/VERIFICATION_MANIFEST.jsonl",
        "AGENTS.md",
        "README.md",
        "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
    ] {
        if !present.contains(required) {
            missing.push(required.to_string());
        }
    }
    for prefix in ["ci/", "crates/", "scripts/", "tools/"] {
        if !paths.iter().any(|path| path.starts_with(prefix)) {
            missing.push(format!("{prefix}**"));
        }
    }
    if missing.is_empty() {
        Ok(())
    } else {
        Err(AnchorInventoryRefusal::ScopeContractMissing { entries: missing })
    }
}

fn audit_checked_in_repository(repo: &Path) -> Result<AnchorInventory, AnchorInventoryRefusal> {
    let declared = decode_segmented_allowance(LOCAL_BACKUP_ONLY_ALLOWANCE)?;
    if declared.len() != REVIEWED_BACKUP_ONLY_ALLOWANCE_COUNT {
        return Err(AnchorInventoryRefusal::AllowancePopulationDrift {
            declared: declared.len(),
            reviewed: REVIEWED_BACKUP_ONLY_ALLOWANCE_COUNT,
        });
    }
    let inventory =
        audit_anchor_inventory(repo, REPOSITORY_EVIDENCE_SCOPE, LOCAL_BACKUP_ONLY_ALLOWANCE)?;
    validate_repository_scope(&inventory.tracked_paths)?;
    Ok(inventory)
}

/// One scratch workspace per cell, reclaimed when the cell passes and retained when it
/// fails (franken_lean-eir2 routes this producer through the workspace fence). The
/// both-directions retention proof for this family lives in fln-conformance's
/// scratch_reclamation_census: this file is a pin-dependent surface, and the
/// CI-execution join reads any citation into it as evidence CI never executed.
fn unique_temp_workspace(label: &str) -> Result<ScratchRoot, std::io::Error> {
    ScratchRoot::create(VDI4_PREFIX, "golden-vellum", label)
}

/// Resolve the tree Cargo invoked this test from without baking a checkout path into the binary.
///
/// The repository-wide audit is Git-backed, so the invocation tree is the authority it must read.
/// A compile-time `env!` here would make a shared target directory capable of running a binary
/// built in another checkout against that other checkout's evidence.
fn invoking_workspace_root() -> PathBuf {
    let manifest_dir = std::env::var_os("CARGO_MANIFEST_DIR")
        .map(PathBuf::from)
        .expect("Cargo must identify the invoking crate directory");
    manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("the workspace root is two levels above the invoking crate directory")
}

fn must_git_with_input(repo: &Path, args: &[&str], input: &[u8]) -> String {
    let mut child = Command::new("git")
        .arg("-C")
        .arg(repo)
        .args(args)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", repo.join(".fln-no-global-gitconfig"))
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("LC_ALL", "C")
        .env("GIT_AUTHOR_DATE", "2001-01-01T00:00:00Z")
        .env("GIT_COMMITTER_DATE", "2001-01-01T00:00:00Z")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("temporary Git command starts");
    child
        .stdin
        .take()
        .expect("piped Git stdin exists")
        .write_all(input)
        .expect("temporary Git command accepts its bounded input");
    let output = child
        .wait_with_output()
        .expect("temporary Git command completes");
    assert!(
        output.status.success(),
        "git {args:?} failed in {repo:?} with {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("Git fixture output is UTF-8")
        .trim()
        .to_string()
}

fn must_git(repo: &Path, args: &[&str]) -> String {
    must_git_with_input(repo, args, &[])
}

/// The token table the goldens were produced with. Frozen here because the table is a *parameter*
/// of the lexer — the same source lexes differently under a different table, so a golden without
/// its table is not reproducible.
fn table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "theorem", "fun", "=>", ":=", "+", "*", "(", ")", "λ", "→", "/--", "/-!",
    ])
}

/// The corpus inputs, by name. The raw bytes live here rather than in the golden file so a reviewer
/// can see what was fed in without decoding hex.
fn inputs() -> Vec<(&'static str, &'static str)> {
    vec![
        ("empty", ""),
        ("bare-ident", "x"),
        ("lf-simple", "def f := 1\n"),
        ("crlf-simple", "def f := 1\r\n"),
        ("crlf-two-lines", "def f := 1\r\ndef g := 2\r\n"),
        ("lone-cr-preserved", "def f := 1\rdef g := 2\n"),
        ("comment-and-trivia", "-- c\r\ndef f := (1 + 2)\r\n"),
        ("unicode-and-doc", "/-- d -/\ndef α := λ x => x\n"),
    ]
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Row {
    name: String,
    raw_hex: String,
    view_hex: String,
    tokens: String,
    tree: String,
    producer: String,
    producer_commit: String,
    lexer_schema: String,
    tree_schema: String,
}

/// Where two byte strings first differ — a reviewer needs the offset, not the word "mismatch".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mismatch {
    Byte { at: usize, expected: u8, actual: u8 },
    Length { expected: usize, actual: usize },
}

fn first_difference(expected: &[u8], actual: &[u8]) -> Option<Mismatch> {
    for (at, (e, a)) in expected.iter().zip(actual.iter()).enumerate() {
        if e != a {
            return Some(Mismatch::Byte {
                at,
                expected: *e,
                actual: *a,
            });
        }
    }
    if expected.len() != actual.len() {
        return Some(Mismatch::Length {
            expected: expected.len(),
            actual: actual.len(),
        });
    }
    None
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn from_hex(text: &str) -> Vec<u8> {
    text.as_bytes()
        .chunks(2)
        .filter_map(|pair| {
            let hi = (pair[0] as char).to_digit(16)?;
            let lo = (*pair.get(1)? as char).to_digit(16)?;
            Some((hi * 16 + lo) as u8)
        })
        .collect()
}

/// What the lexer produced, rendered one token per entry with **view** offsets.
fn render_tokens(text: &SourceText, table: &TokenTable) -> String {
    let run = lex_run(text, table);
    let mut out = Vec::new();
    for event in &run.events {
        match event {
            Event::Token(token) => {
                let kind = match &token.kind {
                    TokenKind::Symbol(symbol) => format!("sym({symbol})"),
                    TokenKind::Ident(name) => format!("ident({})", name.to_display_string()),
                    TokenKind::Literal(kind) => format!("lit({kind:?})"),
                };
                out.push(format!(
                    "{}:{}..{}",
                    kind,
                    token.extent.start().0,
                    token.extent.end().0
                ));
            }
            Event::Refused { error, .. } => {
                out.push(format!("refused({}):{}", error.message(), error.at().0));
            }
            Event::Trivia(_) => {}
        }
    }
    out.join(" ")
}

/// The green tree's shape and spans, rendered so a shape change is a text change.
///
/// Includes each leaf's `pos..end_pos` and the byte length of its leading and trailing trivia, so a
/// misattachment shows up here even though it would not change a reconstruction.
fn render_tree(text: &SourceText, table: &TokenTable) -> (String, Option<Syntax>, ByteSpan) {
    let run = lex_run(text, table);
    let extents: Vec<TokenExtent> = run
        .token_extents()
        .into_iter()
        .map(TokenExtent::Present)
        .collect();
    let Ok(attachment) = attach(text, &extents) else {
        return (
            "<attach refused>".to_string(),
            None,
            ByteSpan::empty_at(fln_syntax::source::BytePos(0)),
        );
    };

    let leaves: Vec<Syntax> = attachment
        .entries()
        .iter()
        .zip(run.token_extents())
        .map(|(entry, extent)| match entry {
            fln_syntax::attach::Attached::Token(info) => {
                Syntax::atom(*info, format!("t{}", extent.start().0))
            }
            fln_syntax::attach::Attached::Missing { .. } => Syntax::Missing,
        })
        .collect();

    let tree = Syntax::node(Name::str(Name::anonymous(), "file"), leaves);
    let mut out = vec![format!("file[{}]", tree_child_count(&tree))];
    for leaf in tree_children(&tree) {
        match leaf.info() {
            SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } => out.push(format!(
                "leaf {}..{} lead{} trail{}",
                pos.0,
                end_pos.0,
                leading.len_bytes(),
                trailing.len_bytes()
            )),
            other => out.push(format!("leaf {other:?}")),
        }
    }
    out.push(format!("epilogue{}", attachment.epilogue().len_bytes()));
    (out.join(" "), Some(tree), attachment.epilogue())
}

fn tree_children(tree: &Syntax) -> Vec<Syntax> {
    match tree {
        Syntax::Node { args, .. } => args.clone(),
        _ => Vec::new(),
    }
}

fn tree_child_count(tree: &Syntax) -> usize {
    tree_children(tree).len()
}

/// Produce the row for one input.
fn produce(name: &str, raw: &str, commit: &str) -> Row {
    let original = SourceText::from_utf8(raw.as_bytes()).expect("corpus inputs are valid UTF-8");
    let view = SourceView::of(&original);
    let table = table();
    let (tree, _, _) = render_tree(view.normalized(), &table);
    Row {
        name: name.to_string(),
        raw_hex: to_hex(raw.as_bytes()),
        view_hex: to_hex(view.normalized().as_bytes()),
        tokens: render_tokens(view.normalized(), &table),
        tree,
        producer: PRODUCER.to_string(),
        producer_commit: commit.to_string(),
        lexer_schema: LEXER_SCHEMA.to_string(),
        tree_schema: TREE_SCHEMA.to_string(),
    }
}

fn frozen_rows() -> Vec<Row> {
    CORPUS
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let f: Vec<&str> = line.split('|').collect();
            assert_eq!(
                f.len(),
                9,
                "a golden row has nine fields; found {} in {line:?}",
                f.len()
            );
            Row {
                name: f[0].to_string(),
                raw_hex: f[1].to_string(),
                view_hex: f[2].to_string(),
                tokens: f[3].to_string(),
                tree: f[4].to_string(),
                producer: f[5].to_string(),
                producer_commit: f[6].to_string(),
                lexer_schema: f[7].to_string(),
                tree_schema: f[8].to_string(),
            }
        })
        .collect()
}

/// **THE GOLDEN COMPARISON.** Every frozen row must be reproduced exactly.
///
/// No update path. A difference fails and keeps failing until a human edits the corpus.
#[test]
fn every_frozen_golden_is_reproduced_byte_for_byte() {
    let frozen = frozen_rows();
    assert_eq!(
        frozen.len(),
        GOLDEN_ROWS,
        "the corpus must hold exactly {GOLDEN_ROWS} reviewed rows"
    );

    for row in &frozen {
        let found = inputs().into_iter().find(|(name, _)| *name == row.name);
        assert!(
            found.is_some(),
            "frozen row {:?} has no matching input; the corpus has drifted from the input set",
            row.name
        );
        let (_, raw) = found.unwrap_or(("", ""));
        let produced = produce(&row.name, raw, &row.producer_commit);

        // The raw bytes, and the VIEW bytes — both frozen, because the recoverable form is what
        // losslessness is defined against.
        assert_eq!(
            first_difference(&from_hex(&row.raw_hex), &from_hex(&produced.raw_hex)),
            None,
            "{}: raw bytes differ from the golden",
            row.name
        );
        assert_eq!(
            first_difference(&from_hex(&row.view_hex), &from_hex(&produced.view_hex)),
            None,
            "{}: the normalized VIEW differs from the golden. The view is what the lexer consumed \
             and what the tree reconstructs, so this is the form losslessness is defined against.",
            row.name
        );
        assert_eq!(
            first_difference(row.tokens.as_bytes(), produced.tokens.as_bytes()),
            None,
            "{}: the TOKEN STREAM differs.\n  golden:   {}\n  produced: {}",
            row.name,
            row.tokens,
            produced.tokens
        );
        assert_eq!(
            first_difference(row.tree.as_bytes(), produced.tree.as_bytes()),
            None,
            "{}: the GREEN TREE SHAPE differs. This is the assertion that must never be quietly \
             regenerated.\n  golden:   {}\n  produced: {}",
            row.name,
            row.tree,
            produced.tree
        );
        assert_eq!(row.lexer_schema, LEXER_SCHEMA, "{}: lexer schema", row.name);
        assert_eq!(row.tree_schema, TREE_SCHEMA, "{}: tree schema", row.name);
        assert_eq!(row.producer, PRODUCER, "{}: producer", row.name);
        assert_eq!(
            row.producer_commit, PRODUCER_COMMIT,
            "{}: producer commit",
            row.name
        );
    }
}

/// **THE RECOVERABILITY CHAIN**, frozen alongside the artifacts rather than assumed.
///
/// The tree reconstructs the VIEW; the view reconstructs the FILE. And for any row the view actually
/// normalized, the tree's reconstruction is asserted to DIFFER from the raw bytes — so a golden
/// frozen against raw bytes could not pass, which is what keeps tkr2's constraint from being
/// quietly relaxed.
#[test]
fn every_golden_row_recovers_its_file_through_the_map() {
    let mut normalized_rows = 0usize;
    for row in frozen_rows() {
        let (_, raw) = inputs()
            .into_iter()
            .find(|(name, _)| *name == row.name)
            .expect("row has an input");
        let original = SourceText::from_utf8(raw.as_bytes()).expect("valid");
        let view = SourceView::of(&original);
        let table = table();
        let (_, tree, epilogue) = render_tree(view.normalized(), &table);

        assert_eq!(
            view.reconstruct_original(),
            raw.as_bytes(),
            "{}: the view must recover the file",
            row.name
        );
        if let Some(tree) = tree {
            let reconstructed = tree
                .reconstruct(view.normalized(), epilogue)
                .unwrap_or_default();
            assert_eq!(
                first_difference(view.normalized().as_bytes(), &reconstructed),
                None,
                "{}: the tree must reconstruct the view",
                row.name
            );
            if view.normalized_anything() {
                normalized_rows += 1;
                assert_ne!(
                    reconstructed,
                    raw.as_bytes(),
                    "{}: this row WAS normalized, so the tree's reconstruction must differ from the \
                     raw bytes. A golden frozen against raw bytes would be wrong here.",
                    row.name
                );
            }
        }
    }
    assert!(
        normalized_rows >= 3,
        "only {normalized_rows} rows exercise the crlfToLf map; the corpus needs CRLF inputs or \
         the recoverability half is untested"
    );
}

/// **The golden FAILS on a tree-shape change.** Demonstrated, not asserted in prose.
///
/// A shape change is simulated by perturbing the produced rendering — one leaf's trivia length —
/// and confirming the comparison rejects it. Without this the suite could be a mirror and nobody
/// would know.
#[test]
fn a_changed_tree_shape_fails_the_comparison() {
    let row = frozen_rows()
        .into_iter()
        .find(|row| row.name == "crlf-two-lines")
        .expect("the corpus has a CRLF row");

    // Perturb exactly one character of the frozen shape, the way a real attachment change would.
    let mut perturbed = row.tree.clone();
    let at = perturbed
        .find("lead0")
        .expect("the row has a zero-length leading trivia to perturb");
    perturbed.replace_range(at..at + 5, "lead9");

    assert_ne!(perturbed, row.tree, "the perturbation must change the text");
    assert!(
        first_difference(row.tree.as_bytes(), perturbed.as_bytes()).is_some(),
        "a changed tree shape MUST be reported as a difference. If this passed, the golden would \
         accept any shape and the suite would be decorative."
    );

    // And the mismatch names the offset, which is what a reviewer needs.
    let difference = first_difference(row.tree.as_bytes(), perturbed.as_bytes());
    assert!(
        matches!(difference, Some(Mismatch::Byte { at, .. }) if at > 0),
        "the mismatch must name a byte offset, which is what a reviewer needs: {difference:?}"
    );
}

/// The provenance document exists, names the producer and the ceremony, and states that the tests
/// never write it. A golden suite without recorded provenance cannot be reproduced once it goes
/// stale.
#[test]
fn the_provenance_document_records_what_a_reviewer_needs() {
    for required in [
        "no update mode",
        PRODUCER,
        PRODUCER_COMMIT,
        SUPERSEDED_PRODUCER_COMMIT,
        "local-backup-only",
        LEXER_SCHEMA,
        TREE_SCHEMA,
        "crlfToLf",
        "recoverable",
    ] {
        assert!(
            PROVENANCE.contains(required),
            "the provenance must mention {required:?}"
        );
    }
    // Every frozen row is named in the provenance table, so a reviewer can see the set at a glance.
    for row in frozen_rows() {
        assert!(
            PROVENANCE.contains(&row.name),
            "row {:?} is not listed in the provenance",
            row.name
        );
    }
}

/// Every input has a frozen row and every frozen row has an input — a corpus that drifted from its
/// inputs would silently stop testing whatever fell out.
#[test]
fn the_corpus_and_the_input_set_agree() {
    let frozen: Vec<String> = frozen_rows().into_iter().map(|row| row.name).collect();
    let declared: Vec<String> = inputs()
        .into_iter()
        .map(|(name, _)| name.to_string())
        .collect();
    assert_eq!(frozen.len(), declared.len(), "row count vs input count");
    for name in &declared {
        assert!(frozen.contains(name), "input {name:?} has no frozen row");
    }
    for name in &frozen {
        assert!(declared.contains(name), "frozen row {name:?} has no input");
    }
}

/// The mutable Vellum provenance now names a producer that a reader of `main` can reach.
///
/// The pre-rewrite producer remains in the prose as labeled historical context, never as current
/// authority. Object existence is deliberately not the test: the old object still exists in this
/// clone through backup refs.
#[test]
fn the_checked_in_producer_anchor_is_reachable_from_main() {
    let repo = invoking_workspace_root();
    assert_eq!(
        classify_anchor(&repo, PRODUCER_COMMIT),
        AnchorReachability::MainReachable {
            commit: PRODUCER_COMMIT.to_string()
        },
        "the checked-in producer must resolve to exactly one commit reachable from refs/heads/main"
    );
    assert!(
        PROVENANCE.contains("superseded"),
        "the old pre-rewrite anchor must remain labeled as superseded history"
    );
}

#[test]
fn binary_blobs_are_scanned_for_ascii_anchors_without_lossy_decoding() {
    let mut blob = vec![0xff, 0x00];
    blob.extend_from_slice(PRODUCER_COMMIT.as_bytes());
    blob.extend_from_slice(&[0x00, 0xfe]);

    assert_eq!(
        commit_anchor_candidates_bytes(&blob),
        vec![PRODUCER_COMMIT.to_string()],
        "a binary tracked artifact remains inside the repository-wide evidence census"
    );
}

/// The repository-wide half of vdi4 runs in plain `cargo test`, over the committed evidence
/// surfaces rather than over a hand-built substitute.
///
/// A concurrent main movement is an environmental refusal, so one wholly fresh attempt is
/// permitted. Two consecutive moving snapshots remain a failure rather than being rendered clean.
#[test]
fn the_repository_wide_anchor_allowance_matches_main_in_both_directions() {
    let repo = invoking_workspace_root();
    let first = audit_checked_in_repository(&repo);
    let result = if matches!(first, Err(AnchorInventoryRefusal::RepositoryChanged { .. })) {
        audit_checked_in_repository(&repo)
    } else {
        first
    };
    let inventory =
        result.expect("the committed repository anchor inventory must be decidable and reviewed");

    let declared = decode_segmented_allowance(LOCAL_BACKUP_ONLY_ALLOWANCE)
        .expect("the production audit already accepted this allowance");
    let reviewed_but_unavailable = inventory.missing_objects.intersection(&declared).count();
    assert_eq!(
        inventory.local_backup_only.len() + reviewed_but_unavailable,
        REVIEWED_BACKUP_ONLY_ALLOWANCE_COUNT,
        "the exact-set audit passed, so its independently reviewed retained population must \
         agree even in a transport clone that lacks forensic refs"
    );
    assert_eq!(
        inventory.candidate_origins.len(),
        inventory.main_reachable.len()
            + inventory.local_backup_only.len()
            + inventory.non_anchors.len(),
        "every scanned candidate must land in exactly one terminal class"
    );
    assert!(
        !inventory.main_reachable.is_empty(),
        "a repository scan finding no current commit anchor is a broken scan, not a clean tree"
    );
    assert!(
        !inventory.non_anchors.is_empty(),
        "the live scope must retain incidental digest-shaped controls so commit promotion stays \
         discriminating"
    );
    assert!(
        inventory
            .candidate_origins
            .values()
            .all(|origins| !origins.is_empty()),
        "every candidate must retain at least one tracked origin"
    );
}

/// R2/R5: exercise the history-rewrite shape, not merely a missing-object substitute.
///
/// The old commit remains a real object under backup refs after `main` is replaced by an
/// unrelated root. Only `merge-base --is-ancestor` distinguishes it from current evidence. A
/// transport clone then proves that current validity does not depend on either backup ref.
#[test]
fn rewritten_history_separates_current_backup_only_and_unresolved_anchors() {
    let workspace =
        unique_temp_workspace("rewritten-history").expect("create rewritten-history workspace");
    let origin = workspace.join("origin");
    fs::create_dir(&origin).expect("temporary origin directory");
    must_git(
        &origin,
        &[
            "init",
            "--quiet",
            "--initial-branch=main",
            "--object-format=sha1",
            ".",
        ],
    );
    must_git(&origin, &["config", "user.name", "Vellum Fixture"]);
    must_git(&origin, &["config", "user.email", "vellum-fixture.invalid"]);
    fs::write(origin.join("evidence.txt"), "pre-rewrite evidence\n")
        .expect("write bounded fixture input");
    must_git(&origin, &["add", "evidence.txt"]);
    must_git(&origin, &["commit", "--quiet", "-m", "pre-rewrite"]);
    let old_commit = must_git(&origin, &["rev-parse", "refs/heads/main^{commit}"]);
    must_git(
        &origin,
        &["update-ref", "refs/original/refs/heads/main", &old_commit],
    );
    must_git(&origin, &["tag", "pre-filter-branch-backup", &old_commit]);

    let empty_tree = must_git_with_input(&origin, &["mktree"], &[]);
    let current_commit = must_git_with_input(
        &origin,
        &["commit-tree", &empty_tree],
        b"replacement main\n",
    );
    must_git(
        &origin,
        &[
            "update-ref",
            "refs/heads/main",
            &current_commit,
            &old_commit,
        ],
    );
    assert_ne!(
        current_commit, old_commit,
        "the replacement root must be unrelated"
    );
    assert_eq!(
        must_git(&origin, &["cat-file", "-t", &old_commit]),
        "commit",
        "the negative control must be a real local commit, not a missing object"
    );

    let missing = "0000000000000000000000000000000000000000";
    let content_digest = "ab".repeat(32);
    let evidence_path = origin.join("anchors.txt");
    fs::write(
        &evidence_path,
        format!(
            "current {current_commit}\nlegacy {old_commit}\nmissing {missing}\ndigest \
             {content_digest}\n"
        ),
    )
    .expect("write bounded anchor fixture");
    assert_eq!(
        scan_evidence_file(&evidence_path).expect("fixture scanner succeeds"),
        vec![
            current_commit.clone(),
            old_commit.clone(),
            missing.to_string()
        ],
        "a 64-hex content digest is not a Git commit candidate"
    );
    must_git(&origin, &["add", "anchors.txt"]);
    must_git(&origin, &["commit", "--quiet", "-m", "record anchors"]);

    let segmented_old = segment_anchor_for_fixture(&old_commit);
    let reviewed_allowance = [segmented_old.as_str()];
    let inventory = audit_anchor_inventory(&origin, &["anchors.txt"], &reviewed_allowance)
        .expect("the reviewed fixture inventory passes");
    assert_eq!(inventory.tracked_paths, vec!["anchors.txt"]);
    assert_eq!(inventory.candidate_origins.len(), 3);
    assert_eq!(
        inventory.main_reachable,
        BTreeSet::from([current_commit.clone()])
    );
    assert_eq!(
        inventory.local_backup_only,
        BTreeSet::from([old_commit.clone()])
    );
    assert_eq!(
        inventory.missing_objects,
        BTreeSet::from([missing.to_string()])
    );
    assert_eq!(inventory.non_anchors, BTreeSet::from([missing.to_string()]));

    assert_eq!(
        audit_anchor_inventory(&origin, &["anchors.txt"], &[]),
        Err(AnchorInventoryRefusal::AllowanceMismatch {
            undeclared: vec![old_commit.clone()],
            stale: Vec::new(),
        }),
        "a newly observed backup-only anchor must fail until it is reviewed"
    );
    let segmented_current = segment_anchor_for_fixture(&current_commit);
    let stale_allowance = [segmented_old.as_str(), segmented_current.as_str()];
    assert_eq!(
        audit_anchor_inventory(&origin, &["anchors.txt"], &stale_allowance),
        Err(AnchorInventoryRefusal::AllowanceMismatch {
            undeclared: Vec::new(),
            stale: vec![current_commit.clone()],
        }),
        "an allowance entry must fail as soon as its anchor is current rather than backup-only"
    );

    assert_eq!(
        classify_anchor(&origin, &current_commit),
        AnchorReachability::MainReachable {
            commit: current_commit.clone()
        }
    );
    assert_eq!(
        classify_anchor(&origin, &old_commit),
        AnchorReachability::LocalBackupOnly {
            commit: old_commit.clone()
        },
        "object existence under backup refs must not earn current authority"
    );
    assert_eq!(
        classify_anchor(&origin, missing),
        AnchorReachability::Unresolved(AnchorRefusal::NoMatchingObject)
    );

    let fresh = workspace.join("fresh");
    let origin_text = origin.to_str().expect("temporary path is UTF-8");
    let fresh_text = fresh.to_str().expect("temporary path is UTF-8");
    must_git(
        &workspace,
        &[
            "clone",
            "--quiet",
            "--no-local",
            "--no-tags",
            "--single-branch",
            "--branch",
            "main",
            origin_text,
            fresh_text,
        ],
    );
    for backup_ref in [
        "refs/original/refs/heads/main",
        "refs/tags/pre-filter-branch-backup",
    ] {
        let output = git_output(
            &fresh,
            "probe-absent-backup-ref",
            ["show-ref", "--verify", "--quiet", backup_ref],
        )
        .expect("the fresh clone can run Git");
        assert_eq!(
            output.status.code(),
            Some(1),
            "fresh --no-tags clone unexpectedly retained {backup_ref}"
        );
    }
    assert_eq!(
        classify_anchor(&fresh, &current_commit),
        AnchorReachability::MainReachable {
            commit: current_commit.clone()
        },
        "current evidence remains valid without local backup refs"
    );
    assert_eq!(
        classify_anchor(&fresh, &old_commit),
        AnchorReachability::Unresolved(AnchorRefusal::NoMatchingObject),
        "the old object is a local forensic aid and must not cross the transport clone"
    );
    let fresh_inventory = audit_anchor_inventory(&fresh, &["anchors.txt"], &reviewed_allowance)
        .expect("the reviewed historical token remains retained in a main-only clone");
    assert!(
        fresh_inventory.local_backup_only.is_empty(),
        "a transport clone must not invent the local backup ref"
    );
    assert!(
        fresh_inventory.missing_objects.contains(&old_commit),
        "the reviewed token remains present in tracked evidence but its old object is unavailable"
    );
    must_git(&fresh, &["config", "user.name", "Vellum Fixture"]);
    must_git(&fresh, &["config", "user.email", "vellum-fixture.invalid"]);
    fs::write(
        fresh.join("anchors.txt"),
        format!("current {current_commit}\nmissing {missing}\ndigest {content_digest}\n"),
    )
    .expect("remove only the reviewed historical token from the bounded fixture");
    must_git(&fresh, &["add", "anchors.txt"]);
    must_git(
        &fresh,
        &["commit", "--quiet", "-m", "repair historical anchor"],
    );
    assert_eq!(
        audit_anchor_inventory(&fresh, &["anchors.txt"], &reviewed_allowance),
        Err(AnchorInventoryRefusal::AllowanceMismatch {
            undeclared: Vec::new(),
            stale: vec![old_commit.clone()],
        }),
        "a reviewed unavailable token must become stale when tracked evidence stops naming it"
    );
}

/// R6: ambiguity, scanner inability, and changing or unusable repository state refuse.
#[test]
fn ambiguous_or_inconclusive_anchor_probes_never_turn_green() {
    let first = "1111111111111111111111111111111111111111".to_string();
    let second = "2222222222222222222222222222222222222222".to_string();
    assert_eq!(
        one_object_id("synthetic-ambiguity", vec![first, second]),
        Err(AnchorRefusal::AmbiguousAbbreviation { matches: 2 })
    );

    let changed = finish_reachability(
        "3333333333333333333333333333333333333333".to_string(),
        true,
        "4444444444444444444444444444444444444444".to_string(),
        "5555555555555555555555555555555555555555".to_string(),
    );
    assert!(matches!(
        changed,
        AnchorReachability::Unresolved(AnchorRefusal::RepositoryChanged { .. })
    ));

    let not_a_repo =
        unique_temp_workspace("not-a-repository").expect("create non-repository workspace");
    assert!(matches!(
        classify_anchor(&not_a_repo, "6666666666666666666666666666666666666666"),
        AnchorReachability::Unresolved(AnchorRefusal::GitRefusal {
            operation: "read-main-before",
            ..
        })
    ));
    assert_eq!(
        scan_evidence_file(&not_a_repo.join("missing-evidence.txt")),
        Err(std::io::ErrorKind::NotFound),
        "scanner inability is a refusal, not an empty clean inventory"
    );
}

/// The regeneration ceremony. `#[ignore]`d, and it **only prints** — it never writes the corpus or
/// the provenance.
///
/// Run it deliberately, read what it produced, and paste the rows in by hand:
///
/// ```text
/// cargo test -p fln-syntax --test golden_vellum -- --ignored --nocapture emit_corpus
/// ```
///
/// Printing rather than writing is the whole point. A suite that can rewrite its own expectation
/// will eventually do so on a run nobody read, and the first bug it accepts will be invisible.
#[test]
#[ignore = "regeneration ceremony: prints rows for a human to review and paste"]
fn emit_corpus_for_review() {
    println!("# Frozen Vellum goldens. Tests compile this file in and never rewrite it.");
    println!("# Provenance and the reviewed change ceremony live in VELLUM_GOLDENS_PROVENANCE.md.");
    println!(
        "# fields: name|raw_hex|view_hex|tokens|tree|producer|producer_commit|lexer_schema|tree_schema"
    );
    let commit = std::env::var("GOLDEN_COMMIT").unwrap_or_else(|_| "UNSET".to_string());
    for (name, raw) in inputs() {
        let row = produce(name, raw, &commit);
        println!(
            "{}|{}|{}|{}|{}|{}|{}|{}|{}",
            row.name,
            row.raw_hex,
            row.view_hex,
            row.tokens,
            row.tree,
            row.producer,
            row.producer_commit,
            row.lexer_schema,
            row.tree_schema
        );
    }
}
