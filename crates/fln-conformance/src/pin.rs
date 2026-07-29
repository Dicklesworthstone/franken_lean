//! Locating the pinned Reference, once, from the lock that pins it.
//!
//! Every rig that consults the oracle needs the same two facts: which tag `SUITE.lock`
//! pins, and where that toolchain lives. Before this module each rig answered them
//! separately — `kernel_replay.rs` hard-codes the elan path, `leanchecker_witness.sh`
//! builds its own, and a third spelling would have shipped with the next rig.
//!
//! That duplication is not merely untidy. A hard-coded path can probe a toolchain the lock
//! does not pin, and the run would look **exactly** as green: the oracle answers, the
//! comparison passes, and the answer is about a different Reference than the one this epoch
//! is defined against. Resolving the tag from `SUITE.lock` — the single pin ceremony
//! (D15) — makes that state unrepresentable rather than unlikely.
//!
//! Absence is never a pass. Callers get [`None`] and use [`RigRun::typed_skip`] to emit both
//! the human notice and, when a collector is configured, a structured record saying what
//! was *not* established. A successful rig consumes the same [`RigRun`] through
//! [`RigRun::executed`]. That one-owner shape prevents the skip and success branches from
//! accidentally naming different rigs, and lets the pin-bearing CI lane distinguish an
//! assertion-bearing execution from libtest's indistinguishable `ok` after an early return
//! (beads `fln-rgha` and `fln-log-derived-disposition-not-execution-xes2`).

use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The directory into which pin-dependent rigs emit their execution records.
///
/// The variable is intentionally opt-in: a developer without the 4 GiB Reference
/// installation still gets the typed human skip and an ordinary test run remains useful.
/// The pin-bearing workflow sets it and refuses unless the complete expected record set is
/// present. Each rig owns one file, avoiding the cross-thread append race a shared NDJSON
/// file would introduce.
pub const RIG_EXECUTION_DIR_ENV: &str = "FLN_RIG_EXECUTION_DIR";

/// The on-disk record schema emitted by [`RigRun`].
pub const RIG_EXECUTION_SCHEMA: &str = "fln.rig-execution/1";

/// Every `fln-conformance` test in the pin-bearing contract-drift job whose
/// assertion-bearing half depends on the pinned Reference.
///
/// This is a closed, compiled registry rather than a hand-maintained CI list. Each variant
/// names the exact test-function citation the verification manifest understands. The
/// CI-execution join checks that every variant occurs in exactly that function, that no
/// legacy free-form `SKIP` site remains, and that the registry and collected record set
/// agree in both directions. It is deliberately not a suite-wide type: lower crates cannot
/// depend upward on `fln-conformance`, and their pin-reaching surfaces remain governed by
/// the source-derived reach/allowance half of the join.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PinRig {
    ExtObservableCapture,
    PinCtorInventory,
    PinOptionDefaults,
    PresentOleanCorpusInventory,
    PresentOleanImportContexts,
    PresentOleanCorpusThreadMatrix,
    PreludeKernelReplay,
    AdmissionFaultMatrix,
    LspCensusNoMockE2e,
    G04NoMockE2e,
}

impl PinRig {
    pub const ALL: &[Self] = &[
        Self::ExtObservableCapture,
        Self::PinCtorInventory,
        Self::PinOptionDefaults,
        Self::PresentOleanCorpusInventory,
        Self::PresentOleanImportContexts,
        Self::PresentOleanCorpusThreadMatrix,
        Self::PreludeKernelReplay,
        Self::AdmissionFaultMatrix,
        Self::LspCensusNoMockE2e,
        Self::G04NoMockE2e,
    ];

    /// The exact executable unit this record describes.
    pub const fn identity(self) -> &'static str {
        match self {
            Self::ExtObservableCapture => {
                "test:fln-conformance::ext_observable_capture::the_checked_in_capture_is_what_the_pinned_binary_produces_today"
            }
            Self::PinCtorInventory => {
                "test:fln-conformance::pin_ctor_inventory::every_constructor_inventory_fln_core_claims_is_the_one_the_pinned_binary_declares"
            }
            Self::PinOptionDefaults => {
                "test:fln-conformance::pin_option_defaults::every_option_default_fln_core_claims_is_the_one_the_pinned_binary_reports"
            }
            Self::PresentOleanCorpusInventory => {
                "test:fln-conformance::kernel_replay::present_olean_corpus_inventory_is_closed_and_honest"
            }
            Self::PresentOleanImportContexts => {
                "test:fln-conformance::kernel_replay::present_olean_import_contexts_accept_reference_extended_duplicates"
            }
            Self::PresentOleanCorpusThreadMatrix => {
                "test:fln-conformance::kernel_replay::present_olean_corpus_thread_matrix_compares_stream_digests"
            }
            Self::PreludeKernelReplay => {
                "test:fln-conformance::kernel_replay::prelude_replays_through_the_kernel"
            }
            Self::AdmissionFaultMatrix => {
                "test:fln-conformance::kernel_replay::admission_fault_matrix_is_typed_and_atomic"
            }
            Self::LspCensusNoMockE2e => {
                "test:fln-conformance::lsp_census_no_mock_e2e::lsp_census_no_mock_e2e"
            }
            Self::G04NoMockE2e => "test:fln-conformance::g0_4_no_mock_e2e::g0_4_no_mock_e2e",
        }
    }

    /// The Rust spelling used at the call site, for the structural source join.
    pub const fn variant_name(self) -> &'static str {
        match self {
            Self::ExtObservableCapture => "ExtObservableCapture",
            Self::PinCtorInventory => "PinCtorInventory",
            Self::PinOptionDefaults => "PinOptionDefaults",
            Self::PresentOleanCorpusInventory => "PresentOleanCorpusInventory",
            Self::PresentOleanImportContexts => "PresentOleanImportContexts",
            Self::PresentOleanCorpusThreadMatrix => "PresentOleanCorpusThreadMatrix",
            Self::PreludeKernelReplay => "PreludeKernelReplay",
            Self::AdmissionFaultMatrix => "AdmissionFaultMatrix",
            Self::LspCensusNoMockE2e => "LspCensusNoMockE2e",
            Self::G04NoMockE2e => "G04NoMockE2e",
        }
    }

    const fn notice_name(self) -> &'static str {
        match self {
            Self::ExtObservableCapture => "ext_observable_capture",
            Self::PinCtorInventory => "pin_ctor_inventory",
            Self::PinOptionDefaults => "pin_option_defaults",
            Self::PresentOleanCorpusInventory => "present_olean_corpus_inventory",
            Self::PresentOleanImportContexts => "present_olean_import_contexts",
            Self::PresentOleanCorpusThreadMatrix => "present_olean_corpus_thread_matrix",
            Self::PreludeKernelReplay => "kernel_replay",
            Self::AdmissionFaultMatrix => "admission_fault_matrix",
            Self::LspCensusNoMockE2e => "lsp_census_no_mock_e2e",
            Self::G04NoMockE2e => "g0_4_no_mock_e2e",
        }
    }

    fn from_identity(identity: &str) -> Option<Self> {
        Self::ALL
            .iter()
            .copied()
            .find(|rig| rig.identity() == identity)
    }
}

/// What the assertion-bearing portion of a pin-dependent rig did.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RigDisposition {
    Executed,
    TypedSkipNoPin,
}

impl RigDisposition {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Executed => "executed",
            Self::TypedSkipNoPin => "typed_skip_no_pin",
        }
    }

    fn parse(text: &str) -> Option<Self> {
        match text {
            "executed" => Some(Self::Executed),
            "typed_skip_no_pin" => Some(Self::TypedSkipNoPin),
            _ => None,
        }
    }
}

/// One durable, exact-unit execution record.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RigExecutionRecord {
    rig: PinRig,
    disposition: RigDisposition,
    reference_tag: String,
    reference_commit: String,
}

impl RigExecutionRecord {
    pub fn rig(&self) -> PinRig {
        self.rig
    }

    pub fn disposition(&self) -> RigDisposition {
        self.disposition
    }

    pub fn reference_tag(&self) -> &str {
        &self.reference_tag
    }

    pub fn reference_commit(&self) -> &str {
        &self.reference_commit
    }

    /// The canonical five-line representation. Values cannot contain newlines because the
    /// rig identity is compiled and the pin fields come from one whitespace-delimited lock
    /// row.
    pub fn to_text(&self) -> String {
        format!(
            "schema={RIG_EXECUTION_SCHEMA}\nrig={}\ndisposition={}\nreference_tag={}\nreference_commit={}\n",
            self.rig.identity(),
            self.disposition.as_str(),
            self.reference_tag,
            self.reference_commit,
        )
    }

    /// Parse one record fail-closed: exact keys, exact order, a registered rig, a version
    /// shaped tag, and the full lowercase commit from `SUITE.lock`.
    pub fn parse(text: &str) -> Result<Self, String> {
        let lines = text.lines().collect::<Vec<_>>();
        if lines.len() != 5 {
            return Err(format!(
                "rig execution record has {} lines, expected exactly 5",
                lines.len()
            ));
        }
        if lines[0] != format!("schema={RIG_EXECUTION_SCHEMA}") {
            return Err(format!(
                "unsupported rig execution schema line {:?}",
                lines[0]
            ));
        }
        let identity = field(lines[1], "rig")?;
        let rig = PinRig::from_identity(identity)
            .ok_or_else(|| format!("rig execution record names unregistered unit {identity:?}"))?;
        let disposition_text = field(lines[2], "disposition")?;
        let disposition = RigDisposition::parse(disposition_text)
            .ok_or_else(|| format!("unsupported rig execution disposition {disposition_text:?}"))?;
        let reference_tag = field(lines[3], "reference_tag")?;
        if !reference_tag.starts_with('v') || reference_tag.len() < 2 {
            return Err(format!(
                "rig execution record has malformed Reference tag {reference_tag:?}"
            ));
        }
        let reference_commit = field(lines[4], "reference_commit")?;
        if reference_commit.len() != 40
            || !reference_commit
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(format!(
                "rig execution record has malformed Reference commit {reference_commit:?}"
            ));
        }
        let record = Self {
            rig,
            disposition,
            reference_tag: reference_tag.to_string(),
            reference_commit: reference_commit.to_string(),
        };
        if record.to_text() != text {
            return Err(
                "rig execution record is not in canonical five-line representation".to_string(),
            );
        }
        Ok(record)
    }
}

fn field<'a>(line: &'a str, key: &str) -> Result<&'a str, String> {
    let prefix = format!("{key}=");
    let value = line
        .strip_prefix(&prefix)
        .ok_or_else(|| format!("rig execution record expected {key}=..., found {line:?}"))?;
    if value.is_empty() {
        return Err(format!("rig execution record field {key} is empty"));
    }
    Ok(value)
}

/// A single-use witness joining the skip and executed branches of one rig.
#[derive(Debug)]
#[must_use = "a pin-dependent rig must finish as executed or typed_skip_no_pin"]
pub struct RigRun {
    rig: PinRig,
}

impl RigRun {
    pub const fn new(rig: PinRig) -> Self {
        Self { rig }
    }

    /// Record absence and return the typed human notice. Failure to persist a configured
    /// record is a test failure, never a silently lost disclosure.
    pub fn typed_skip(self) -> Result<String, String> {
        emit_record(self.rig, RigDisposition::TypedSkipNoPin)?;
        Ok(skip_notice(self.rig.notice_name()))
    }

    /// Record only after the rig's assertion-bearing body completed.
    pub fn executed(self) -> Result<(), String> {
        emit_record(self.rig, RigDisposition::Executed)
    }
}

fn emit_record(rig: PinRig, disposition: RigDisposition) -> Result<(), String> {
    let Some(root) = std::env::var_os(RIG_EXECUTION_DIR_ENV) else {
        return Ok(());
    };
    let root = PathBuf::from(root);
    match std::fs::symlink_metadata(&root) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(format!(
                "{RIG_EXECUTION_DIR_ENV} path {} is not a real directory",
                root.display()
            ));
        }
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            std::fs::create_dir_all(&root).map_err(|error| {
                format!("create rig execution directory {}: {error}", root.display())
            })?;
            let metadata = std::fs::symlink_metadata(&root).map_err(|error| {
                format!(
                    "inspect created rig execution directory {}: {error}",
                    root.display()
                )
            })?;
            if metadata.file_type().is_symlink() || !metadata.is_dir() {
                return Err(format!(
                    "created {RIG_EXECUTION_DIR_ENV} path {} is not a real directory",
                    root.display()
                ));
            }
        }
        Err(error) => {
            return Err(format!(
                "inspect rig execution directory {}: {error}",
                root.display()
            ));
        }
    }

    let tag = pinned_tag().ok_or_else(|| "SUITE.lock has no Reference tag".to_string())?;
    let commit = pinned_commit().ok_or_else(|| "SUITE.lock has no Reference commit".to_string())?;
    let record = RigExecutionRecord {
        rig,
        disposition,
        reference_tag: tag,
        reference_commit: commit,
    };
    let text = record.to_text();
    let path = root.join(record_filename(rig.identity()));
    match OpenOptions::new().create_new(true).write(true).open(&path) {
        Ok(mut file) => {
            file.write_all(text.as_bytes()).map_err(|error| {
                format!("write rig execution record {}: {error}", path.display())
            })?;
            file.sync_all().map_err(|error| {
                format!("sync rig execution record {}: {error}", path.display())
            })?;
            std::fs::File::open(&root)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| {
                    format!("sync rig execution directory {}: {error}", root.display())
                })?;
            Ok(())
        }
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => Err(format!(
            "rig execution record {} already exists; a duplicate, stale or contradictory \
                 disposition cannot be reused or overwritten",
            path.display()
        )),
        Err(error) => Err(format!(
            "create rig execution record {}: {error}",
            path.display()
        )),
    }
}

fn record_filename(identity: &str) -> String {
    // FNV-1a is only a compact filename partition. The complete identity remains inside
    // the record and the parser rejects a collision rather than trusting this hash.
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in identity.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("rig-{hash:016x}.record")
}

/// The workspace root, two levels above this crate's manifest — of the checkout this run
/// was actually launched from.
///
/// The tree check is not decoration. This module's own doc comment above says a rig that
/// consults the wrong Reference "would look **exactly** as green"; resolving the root
/// from a manifest dir baked in by a *different checkout* is the same failure one level
/// out, and it has been observed live (bead `fln-cross-tree-baked-root-k60n`).
pub fn workspace_root() -> PathBuf {
    crate::checked_workspace_root!()
}

/// The Reference tag `SUITE.lock` pins, e.g. `v4.32.0`.
pub fn pinned_tag() -> Option<String> {
    let lock = std::fs::read_to_string(workspace_root().join("SUITE.lock")).ok()?;
    tag_from_lock(&lock)
}

/// The commit `SUITE.lock` pins for the Reference.
pub fn pinned_commit() -> Option<String> {
    let lock = std::fs::read_to_string(workspace_root().join("SUITE.lock")).ok()?;
    field_from_lock(&lock, "commit=")
}

/// Split out so the parse is testable without a filesystem, and so a lock that stops
/// naming a reference row fails loudly here rather than silently returning a default.
fn tag_from_lock(lock: &str) -> Option<String> {
    field_from_lock(lock, "tag=")
}

fn field_from_lock(lock: &str, prefix: &str) -> Option<String> {
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))?
        .split_whitespace()
        .find_map(|field| field.strip_prefix(prefix).map(str::to_string))
}

/// The pinned `lean` binary. `FLN_REFERENCE_BIN` overrides for hosts that install the
/// toolchain elsewhere; otherwise the elan layout for the tag the lock pins.
pub fn pinned_lean() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_BIN") {
        let p = PathBuf::from(path);
        return p.is_file().then_some(p);
    }
    let home = std::env::var("HOME").ok()?;
    let tag = pinned_tag()?;
    let p = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin/lean");
    p.is_file().then_some(p)
}

/// What the pinned binary said when it was asked a question.
///
/// `success` is kept alongside `code` because a probe killed by a signal has no exit code,
/// and a rig that only inspected `code` would read that as "no failure reported".
#[derive(Debug)]
pub struct Answer {
    pub stdout: String,
    pub stderr: String,
    pub code: Option<i32>,
    pub success: bool,
}

/// Ask the pinned binary a question, as a Lean file it elaborates and reports on.
///
/// This is the *oracle* capacity D8 reserves for the Reference: the binary is asked and its
/// answer compared, never linked, patched, or executed as a component. Every rig that needs
/// an answer rather than a reading should come through here — the duplication this module's
/// header warns about is exactly the shape where one rig grows a scratch path, a cleanup or
/// an exit-code reading that the others do not have.
///
/// `Err` is a broken oracle, never an absent one: callers decide absence with
/// [`pinned_lean`] and use [`RigRun::typed_skip`]. A pin that was located but will not run
/// has produced no evidence *and* is a defect, and those are different outcomes from a pin
/// that is not installed.
pub fn ask(lean: &Path, rig: &str, probe: &str) -> Result<Answer, String> {
    let dir = std::env::temp_dir().join(format!("fln-probe-{rig}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|error| format!("probe scratch {dir:?}: {error}"))?;
    let file = dir.join(format!("{rig}.lean"));
    std::fs::write(&file, probe).map_err(|error| format!("writing {file:?}: {error}"))?;

    let out = Command::new(lean)
        .arg(&file)
        .output()
        .map_err(|error| format!("running {}: {error}", lean.display()));
    // Best-effort: a scratch directory that outlives a failed probe is untidy, never wrong,
    // and must not mask the probe's own error.
    let _ = std::fs::remove_dir_all(&dir);
    let out = out?;

    Ok(Answer {
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        code: out.status.code(),
        success: out.status.success(),
    })
}

/// A typed skip line naming what was NOT established, for rigs whose oracle is absent.
///
/// Kept private so every real skip passes through [`RigRun::typed_skip`] and therefore
/// cannot forget the structured record while retaining only the human message.
fn skip_notice(rig: &str) -> String {
    format!(
        "SKIP {rig}: the pinned Reference toolchain ({}) was not found. Install it with \
         `elan toolchain install leanprover/lean4:{}` or set FLN_REFERENCE_BIN. This is a \
         typed skip: NOTHING this rig checks has been established by this run.",
        pinned_tag().unwrap_or_else(|| "<unreadable SUITE.lock>".into()),
        pinned_tag().unwrap_or_else(|| "<tag>".into()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_tag_comes_from_the_reference_row_and_nowhere_else() {
        let lock = "\
# comment\n\
rust-commit deadbeef\n\
suite frankensqlite commit=abc path=/dp/frankensqlite\n\
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b tree=ba16913\n\
corpus leanprover-community/mathlib4 tag=nightly commit=999\n";
        assert_eq!(tag_from_lock(lock).as_deref(), Some("v4.32.0"));
        assert_eq!(field_from_lock(lock, "commit=").as_deref(), Some("8c9756b"));
    }

    /// A lock with no reference row yields None rather than a default: a rig that
    /// defaulted would probe whatever happened to be installed.
    #[test]
    fn a_lock_without_a_reference_row_names_no_tag() {
        assert_eq!(tag_from_lock("rust-commit deadbeef\n"), None);
        // The corpus row must not be mistaken for the reference row.
        assert_eq!(
            tag_from_lock("corpus leanprover-community/mathlib4 tag=nightly commit=1\n"),
            None
        );
    }

    #[test]
    fn the_real_lock_pins_a_reference_tag_and_commit() {
        assert!(pinned_tag().is_some_and(|tag| tag.starts_with('v')));
        assert!(pinned_commit().is_some_and(|commit| commit.len() >= 7));
    }

    #[test]
    fn the_rig_registry_is_unique_and_uses_exact_test_citations() {
        let identities = PinRig::ALL
            .iter()
            .map(|rig| rig.identity())
            .collect::<std::collections::BTreeSet<_>>();
        let variants = PinRig::ALL
            .iter()
            .map(|rig| rig.variant_name())
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(identities.len(), PinRig::ALL.len());
        assert_eq!(variants.len(), PinRig::ALL.len());
        assert!(
            identities
                .iter()
                .all(|identity| identity.starts_with("test:fln-conformance::"))
        );
    }

    #[test]
    fn a_rig_execution_record_round_trips_and_refuses_shape_drift() {
        let record = RigExecutionRecord {
            rig: PinRig::PreludeKernelReplay,
            disposition: RigDisposition::Executed,
            reference_tag: "v4.32.0".to_string(),
            reference_commit: "8c9756b28d64dab099da31a4c09229a9e6a2ef35".to_string(),
        };
        let text = record.to_text();
        assert_eq!(RigExecutionRecord::parse(&text), Ok(record.clone()));

        let unknown = text.replace(
            "test:fln-conformance::kernel_replay::prelude_replays_through_the_kernel",
            "test:fln-conformance::kernel_replay::a_name_that_is_not_registered",
        );
        assert!(
            RigExecutionRecord::parse(&unknown)
                .expect_err("an unknown rig must be refused")
                .contains("unregistered")
        );
        assert!(
            RigExecutionRecord::parse(&(text.clone() + "extra=field\n"))
                .expect_err("a sixth field must be refused")
                .contains("exactly 5")
        );
        assert!(
            RigExecutionRecord::parse(text.trim_end())
                .expect_err("a noncanonical missing newline must be refused")
                .contains("canonical")
        );
    }

    #[test]
    fn record_filenames_are_stable_but_never_the_execution_identity() {
        let first = record_filename(PinRig::PreludeKernelReplay.identity());
        assert_eq!(
            first,
            record_filename(PinRig::PreludeKernelReplay.identity())
        );
        assert_ne!(
            first,
            record_filename(PinRig::AdmissionFaultMatrix.identity())
        );
        assert!(!first.contains("kernel_replay"));
    }
}
