//! The build profile the kernel's stack calibration assumes must be the one
//! cargo actually produces (bead `franken_lean-4o3n`).
//!
//! # The hazard, stated exactly
//!
//! `fln-kernel` selects which measured per-depth stack cost to derive its depth
//! ceiling from by asking [`Profile::current()`], which is `cfg!(debug_assertions)`
//! (`crates/fln-kernel/src/verdict.rs`). Two measurements exist, taken on
//! 2026-07-25 under bead `franken_lean-kxbj`:
//!
//! | pair produced by cargo         | measured cost | ceiling for 64 MiB |
//! |--------------------------------|---------------|--------------------|
//! | `opt-level = 0`, assertions on  | 5,935 B/depth | ~4,096             |
//! | `opt-level = 3`, assertions off | 640 B/depth   | ~38,000            |
//!
//! `debug_assertions` is a **proxy** for "unoptimised", and `verdict.rs` says so
//! in terms. This suite is what makes the proxy true here rather than hoped for,
//! because the failure is not a wrong number — it is a process abort:
//!
//! * A profile pairing `debug-assertions = false` with `opt-level = 0` is
//!   classified `Release`, so the kernel derives a ceiling from the 640-byte
//!   figure while the frames it actually gets are the 5,935-byte ones. The
//!   descent then runs about 9.3x deeper than the stack can hold. A native stack
//!   overflow is the one exhaustion FL-INV-07 cannot convert into a typed
//!   `Inconclusive`, because it aborts the process uncatchably — there is no
//!   "after the fact" in which to type it. The compile-time assertions in
//!   `verdict.rs` cannot see this: they check the ceiling against the floor
//!   *under the measurement they were handed*, and here the wrong measurement is
//!   handed over.
//! * The mirror pairing — `debug-assertions = true` with optimisation on — is
//!   *safe* to run, because it takes the more expensive figure. It is still
//!   refused: the bound's provenance would name a configuration it was not taken
//!   in, and 4o3n's whole finding is that a bound whose provenance is wrong in
//!   the safe direction is a bound nobody can compare. Certifying parity between
//!   two engines requires each number to describe the build it ran in.
//!
//! # Why it is a constraint and why now
//!
//! There is no `[profile.*]` table anywhere in this workspace today, so this
//! costs nothing and refuses nothing. That is the point: a constraint has to
//! precede the code it governs, because afterwards there is a working profile
//! override, a build-time complaint it was solving, and a deadline. Adding it
//! now means the next agent who wants `[profile.dev] opt-level = 2` is told,
//! at the moment of the edit, that the calibration has to move with it.
//!
//! # What this does NOT check
//!
//! It reads manifests. It does not observe codegen, so `RUSTFLAGS`, a
//! `config.toml` `[build] rustflags`, or a `-C opt-level` passed by a wrapper can
//! still produce a pair no manifest declares. Those are outside a manifest scan
//! by construction, and the in-binary behavioural guards
//! (`fln-kernel/tests/depth_stack_calibration.rs`) are what would catch the
//! consequence. This closes the declarable half; it is a floor, not coverage.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};

/// The two `(opt-level, debug-assertions)` pairs a `StackMeasurement` exists for.
///
/// Kept as data rather than as a condition, so adding a third measurement to
/// `fln-kernel` is a visible edit here rather than a loosened comparison.
const MEASURED_PAIRS: [(OptLevel, bool); 2] = [
    // `cargo test`: what the Tribunal and every kernel replay run under.
    (OptLevel::Numeric(0), true),
    // `cargo test --release`: 9.3x cheaper per unit of depth.
    (OptLevel::Numeric(3), false),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OptLevel {
    Numeric(u8),
    /// `"s"` / `"z"`: optimised for size. Never measured, and deliberately not
    /// mapped onto a numeric level — a size-optimised build has its own frame
    /// layout and guessing which measurement covers it is the defect this file
    /// exists to prevent.
    Size(&'static str),
}

impl OptLevel {
    fn parse(raw: &str) -> Option<OptLevel> {
        let raw = raw.trim().trim_matches('"');
        match raw {
            "s" => Some(OptLevel::Size("s")),
            "z" => Some(OptLevel::Size("z")),
            _ => raw.parse::<u8>().ok().map(OptLevel::Numeric),
        }
    }

    fn describe(self) -> String {
        match self {
            OptLevel::Numeric(level) => level.to_string(),
            OptLevel::Size(which) => format!("\"{which}\""),
        }
    }
}

/// One `[profile...]` table found in a manifest, with the keys this suite reads.
#[derive(Debug, Clone)]
struct ProfileTable {
    /// The header as written, e.g. `profile.release` or `profile.dev.package.*`.
    header: String,
    opt_level: Option<OptLevel>,
    debug_assertions: Option<bool>,
    inherits: Option<String>,
    /// An `opt-level` or `debug-assertions` line this parser could not read.
    /// Never ignored: an undecidable input is a refusal, not a pass.
    unreadable: Vec<String>,
}

/// Why a manifest is refused. One variant per distinguishable cause, because a
/// single "bad profile" string would make the abort case and the provenance case
/// look like the same finding, and only one of them kills the process.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Finding {
    /// The pair is classified `Release` by the proxy and is not optimised: the
    /// kernel would derive a ceiling ~9.3x above what the stack holds.
    CeilingAboveFrames {
        manifest: String,
        header: String,
        opt_level: String,
    },
    /// Safe to run, and the provenance would name a configuration the build is
    /// not. Nothing derived under it can be established comparable.
    ProvenanceWouldLie {
        manifest: String,
        header: String,
        opt_level: String,
        debug_assertions: bool,
    },
    /// A custom profile with no `inherits`, or a key this parser cannot read.
    /// Undecidable, therefore refused.
    Undecidable {
        manifest: String,
        header: String,
        detail: String,
    },
}

impl Finding {
    fn render(&self) -> String {
        match self {
            Finding::CeilingAboveFrames {
                manifest,
                header,
                opt_level,
            } => format!(
                "{manifest} [{header}]: debug-assertions are OFF at opt-level {opt_level}. \
                 fln-kernel's Profile::current() reads cfg!(debug_assertions), so it would \
                 classify this build `release` and derive its depth ceiling from the 640 \
                 bytes/depth release measurement — while unoptimised frames cost 5,935. The \
                 descent would run ~9.3x deeper than the stack holds, and a native stack \
                 overflow aborts the process uncatchably: FL-INV-07 cannot type it, so the \
                 guarantee has to be structural and this is where it is structural. Either \
                 restore the pairing, or measure this configuration \
                 (cargo test -p fln-kernel --test depth_stack_calibration -- --ignored \
                 calibrate_stack_bytes_per_depth), add the StackMeasurement to \
                 fln-kernel/src/verdict.rs, and add the pair to MEASURED_PAIRS here."
            ),
            Finding::ProvenanceWouldLie {
                manifest,
                header,
                opt_level,
                debug_assertions,
            } => format!(
                "{manifest} [{header}]: opt-level {opt_level} with debug-assertions \
                 {debug_assertions} is not a measured configuration. This pairing is SAFE to \
                 run — the proxy picks the more expensive figure — but every budget derived \
                 under it would carry provenance naming a build it was not taken in, and \
                 franken_lean-4o3n's finding is that a bound whose provenance is wrong in the \
                 safe direction is still a bound nobody can compare. Measure the \
                 configuration and register it, or leave the pairing alone."
            ),
            Finding::Undecidable {
                manifest,
                header,
                detail,
            } => format!(
                "{manifest} [{header}]: {detail}. This scan never exits clean on a question it \
                 could not answer — an unreadable profile is refused, not assumed harmless."
            ),
        }
    }
}

/// Split a manifest into its `[profile...]` tables.
///
/// A hand-rolled reader because the dependency universe is closed (D1): there is
/// no TOML crate and there will not be one. It reads only the four keys this
/// property needs and records anything it cannot read, so the narrowness is
/// visible in the output rather than silently permissive. The same approach the
/// poison compile-out suite already uses on this manifest.
fn profile_tables(manifest: &str) -> Vec<ProfileTable> {
    let mut tables: Vec<ProfileTable> = Vec::new();
    let mut current: Option<ProfileTable> = None;
    for raw in manifest.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.starts_with('[') && line.ends_with(']') {
            if let Some(table) = current.take() {
                tables.push(table);
            }
            let header = line.trim_matches(['[', ']']).trim().to_string();
            if header == "profile" || header.starts_with("profile.") {
                current = Some(ProfileTable {
                    header,
                    opt_level: None,
                    debug_assertions: None,
                    inherits: None,
                    unreadable: Vec::new(),
                });
            }
            continue;
        }
        let Some(table) = current.as_mut() else {
            continue;
        };
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let (key, value) = (key.trim(), value.trim().trim_end_matches(','));
        match key {
            "opt-level" => match OptLevel::parse(value) {
                Some(level) => table.opt_level = Some(level),
                None => table.unreadable.push(format!("opt-level = {value}")),
            },
            "debug-assertions" => match value.trim() {
                "true" => table.debug_assertions = Some(true),
                "false" => table.debug_assertions = Some(false),
                other => table.unreadable.push(format!("debug-assertions = {other}")),
            },
            "inherits" => table.inherits = Some(value.trim_matches('"').to_string()),
            _ => {}
        }
    }
    if let Some(table) = current.take() {
        tables.push(table);
    }
    tables
}

/// Cargo's built-in pairs. `test` inherits `dev` and `bench` inherits `release`,
/// which is why both appear.
fn built_in_pair(name: &str) -> Option<(OptLevel, bool)> {
    match name {
        "dev" | "test" => Some((OptLevel::Numeric(0), true)),
        "release" | "bench" => Some((OptLevel::Numeric(3), false)),
        _ => None,
    }
}

/// The profile a table's header belongs to: `profile.dev.package.*` resolves to
/// `dev`, because a package override adjusts that profile rather than being one.
fn base_profile_name(header: &str) -> Option<&str> {
    header.strip_prefix("profile.")?.split('.').next()
}

/// The effective pair a table produces, following `inherits` for custom profiles
/// and applying package-override keys on top of the profile they adjust.
fn effective_pair(
    table: &ProfileTable,
    tables: &[ProfileTable],
) -> Result<(OptLevel, bool), String> {
    let name = base_profile_name(&table.header)
        .ok_or_else(|| "a [profile] table with no profile name".to_string())?;
    let (mut opt_level, mut debug_assertions) = match built_in_pair(name) {
        Some(pair) => pair,
        None => {
            // A custom profile. Cargo requires `inherits`; a table without one
            // is rejected by cargo, and a table whose parent we cannot resolve
            // is rejected here.
            let declaration = tables
                .iter()
                .find(|candidate| candidate.header == format!("profile.{name}"))
                .ok_or_else(|| {
                    format!("custom profile `{name}` is adjusted here but declared nowhere")
                })?;
            let parent = declaration.inherits.as_deref().ok_or_else(|| {
                format!("custom profile `{name}` declares no `inherits`, so its pair is unknown")
            })?;
            built_in_pair(parent).ok_or_else(|| {
                format!(
                    "custom profile `{name}` inherits `{parent}`, which this scan cannot resolve \
                     to a built-in pair"
                )
            })?
        }
    };
    // The declaring table's own keys, then this table's, so a package override
    // sits on top of the profile it adjusts.
    if let Some(declaration) = tables
        .iter()
        .find(|candidate| candidate.header == format!("profile.{name}"))
    {
        if let Some(level) = declaration.opt_level {
            opt_level = level;
        }
        if let Some(flag) = declaration.debug_assertions {
            debug_assertions = flag;
        }
    }
    if let Some(level) = table.opt_level {
        opt_level = level;
    }
    if let Some(flag) = table.debug_assertions {
        debug_assertions = flag;
    }
    Ok((opt_level, debug_assertions))
}

/// Audit one manifest's profile tables. Findings come back in table order, so
/// the report is a diffable artifact rather than a set that reshuffles.
fn audit(manifest_path: &str, manifest: &str) -> Vec<Finding> {
    let tables = profile_tables(manifest);
    let mut findings = Vec::new();
    for table in &tables {
        for detail in &table.unreadable {
            findings.push(Finding::Undecidable {
                manifest: manifest_path.to_string(),
                header: table.header.clone(),
                detail: format!("cannot read `{detail}`"),
            });
        }
        let pair = match effective_pair(table, &tables) {
            Ok(pair) => pair,
            Err(detail) => {
                findings.push(Finding::Undecidable {
                    manifest: manifest_path.to_string(),
                    header: table.header.clone(),
                    detail,
                });
                continue;
            }
        };
        if MEASURED_PAIRS.contains(&pair) {
            continue;
        }
        let (opt_level, debug_assertions) = pair;
        // The abort case is exactly "the proxy says release and the build is
        // not optimised". Everything else that is unmeasured is the safe-but-
        // unquotable case.
        if !debug_assertions && opt_level == OptLevel::Numeric(0) {
            findings.push(Finding::CeilingAboveFrames {
                manifest: manifest_path.to_string(),
                header: table.header.clone(),
                opt_level: opt_level.describe(),
            });
        } else {
            findings.push(Finding::ProvenanceWouldLie {
                manifest: manifest_path.to_string(),
                header: table.header.clone(),
                opt_level: opt_level.describe(),
                debug_assertions,
            });
        }
    }
    findings
}

fn workspace_root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

/// Every manifest cargo can read in this workspace.
///
/// Profiles are only honoured in the ROOT manifest — cargo warns and ignores one
/// in a member. They are scanned anyway, and refused anyway: a profile table
/// that looks effective and is not is worse than one that is, because the reader
/// who added it believes the calibration moved with it.
fn workspace_manifests(root: &Path) -> Vec<PathBuf> {
    let mut manifests = vec![root.join("Cargo.toml")];
    for parent in ["crates", "tools"] {
        let Ok(entries) = fs::read_dir(root.join(parent)) else {
            continue;
        };
        let mut found: Vec<PathBuf> = entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|path| path.is_dir())
            .flat_map(|dir| {
                let mut here = vec![dir.join("Cargo.toml")];
                // One level deeper covers nested members such as
                // tools/structure-guard/kernel-ownership-publisher.
                if let Ok(nested) = fs::read_dir(&dir) {
                    for entry in nested.filter_map(Result::ok) {
                        let path = entry.path();
                        if path.is_dir() {
                            here.push(path.join("Cargo.toml"));
                        }
                    }
                }
                here
            })
            .filter(|path| path.exists())
            .collect();
        found.sort();
        manifests.append(&mut found);
    }
    manifests
}

fn render(findings: &[Finding]) -> String {
    findings
        .iter()
        .map(Finding::render)
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ---------------------------------------------------------------------------
// The live tree
// ---------------------------------------------------------------------------

#[test]
fn every_declared_build_profile_is_one_the_kernel_has_measured() {
    let root = workspace_root();
    let manifests = workspace_manifests(&root);
    assert!(
        manifests.len() > 10,
        "the manifest walk found only {} files, which means it stopped walking rather than \
         found a clean tree",
        manifests.len()
    );

    let mut findings = Vec::new();
    for manifest in &manifests {
        // An unreadable manifest fails the run rather than being skipped: a scan
        // that cannot read one of its inputs has not established anything about
        // the tree, and skipping would turn that into a pass.
        let text = fs::read_to_string(manifest)
            .map_err(|error| format!("cannot read {}: {error}", manifest.display()))
            .expect("every workspace manifest is readable");
        let relative = manifest
            .strip_prefix(&root)
            .unwrap_or(manifest)
            .to_string_lossy()
            .into_owned();
        findings.extend(audit(&relative, &text));
    }

    assert!(
        findings.is_empty(),
        "a build profile would put fln-kernel's depth ceiling out of step with the frames \
         cargo actually produces:\n\n{}",
        render(&findings)
    );
}

/// The state this constraint was written in, recorded so its later loss is
/// visible. Today no manifest declares a profile at all, so the two built-in
/// pairs are the only ones in play and both are measured.
#[test]
fn the_workspace_declares_no_profile_overrides_today() {
    let root = workspace_root();
    let declaring: Vec<String> = workspace_manifests(&root)
        .into_iter()
        .filter(|manifest| {
            fs::read_to_string(manifest)
                .map(|text| !profile_tables(&text).is_empty())
                .unwrap_or(false)
        })
        .map(|manifest| manifest.to_string_lossy().into_owned())
        .collect();
    assert!(
        declaring.is_empty(),
        "profile tables now exist ({declaring:?}). That is not itself wrong — the audit above \
         decides it — but this test recorded that none existed when the constraint was \
         written. Update it deliberately rather than deleting it."
    );
}

// ---------------------------------------------------------------------------
// Planted violations — both directions
// ---------------------------------------------------------------------------

/// THE ABORT CASE. Assertions off, optimisation off: classified `release`, given
/// the 640-byte ceiling, running on 5,935-byte frames.
#[test]
fn a_profile_that_would_abort_the_kernel_is_refused() {
    let findings = audit(
        "planted/Cargo.toml",
        "[profile.release]\nopt-level = 0\ndebug-assertions = false\n",
    );
    assert!(
        matches!(findings.as_slice(), [Finding::CeilingAboveFrames { .. }]),
        "the abort pairing must be refused as an abort, not as a provenance nit: {findings:?}"
    );
    assert!(
        render(&findings).contains("aborts the process uncatchably"),
        "the refusal must say why this one is not a style question"
    );
}

/// THE SAME CASE ARRIVING THROUGH A PACKAGE OVERRIDE, which is how it would
/// actually happen: someone turns optimisation off for one crate to get a usable
/// backtrace, and the profile name still says `release`.
#[test]
fn a_package_override_that_would_abort_the_kernel_is_refused() {
    let findings = audit(
        "planted/Cargo.toml",
        "[profile.release.package.fln-kernel]\nopt-level = 0\n",
    );
    assert!(
        matches!(findings.as_slice(), [Finding::CeilingAboveFrames { .. }]),
        "a package override inherits its profile's debug-assertions, so this is the abort \
         pairing wearing a different header: {findings:?}"
    );
}

/// THE PROVENANCE CASE. Safe to run, refused anyway, and refused as a DIFFERENT
/// finding — collapsing the two would make the abort look like a nit.
#[test]
fn an_optimised_dev_profile_is_refused_as_a_provenance_defect_not_an_abort() {
    let findings = audit("planted/Cargo.toml", "[profile.dev]\nopt-level = 2\n");
    assert!(
        matches!(findings.as_slice(), [Finding::ProvenanceWouldLie { .. }]),
        "an optimised dev build is safe and unquotable, which is its own finding: {findings:?}"
    );
    assert!(
        render(&findings).contains("SAFE to run"),
        "the refusal must not imply this one aborts"
    );
}

/// A size-optimised profile is neither measured pair and is never guessed into
/// one.
#[test]
fn a_size_optimised_profile_is_not_mapped_onto_a_measured_pair() {
    let findings = audit(
        "planted/Cargo.toml",
        "[profile.release]\nopt-level = \"z\"\n",
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(render(&findings).contains("\"z\""), "{findings:?}");
}

/// An undecidable table is refused rather than assumed harmless — the posture
/// the projection guard and the structure guard already take.
#[test]
fn a_profile_this_scan_cannot_read_is_refused_rather_than_passed() {
    let unresolvable = audit(
        "planted/Cargo.toml",
        "[profile.fast-check]\ncodegen-units = 1\n",
    );
    assert!(
        matches!(unresolvable.as_slice(), [Finding::Undecidable { .. }]),
        "a custom profile with no inherits has an unknown pair: {unresolvable:?}"
    );

    let unreadable = audit(
        "planted/Cargo.toml",
        "[profile.release]\ndebug-assertions = maybe\n",
    );
    assert!(
        unreadable
            .iter()
            .any(|finding| matches!(finding, Finding::Undecidable { .. })),
        "an unparseable value must not be silently skipped: {unreadable:?}"
    );
}

/// THE PERMISSION HALF. A constraint that refuses every profile table is a wall,
/// and a wall gets deleted the first time someone needs a legitimate override.
#[test]
fn the_measured_pairs_and_unrelated_profile_keys_are_permitted() {
    assert!(
        audit(
            "planted/Cargo.toml",
            "[profile.release]\nlto = true\ncodegen-units = 1\nstrip = true\n",
        )
        .is_empty(),
        "keys that do not touch the calibration must pass untouched"
    );
    assert!(
        audit(
            "planted/Cargo.toml",
            "[profile.dev]\nopt-level = 0\ndebug-assertions = true\ndebug = 2\n",
        )
        .is_empty(),
        "restating the measured dev pair must pass"
    );
    assert!(
        audit(
            "planted/Cargo.toml",
            "[profile.perf]\ninherits = \"release\"\nlto = \"fat\"\n",
        )
        .is_empty(),
        "a custom profile inheriting a measured pair and changing nothing about it must pass"
    );
    assert!(
        audit(
            "planted/Cargo.toml",
            "[profile.release.package.\"*\"]\ncodegen-units = 16\n",
        )
        .is_empty(),
        "a package override that leaves both axes alone must pass"
    );
}

/// THE LIVE PATH DISCRIMINATES. The planted cases above prove `audit` refuses;
/// this proves the file the live test actually reads would carry a refusal
/// through the same path. The real root manifest is read from disk and the
/// hazard is appended in memory — the tree is never touched, because a guard
/// that has to mutate a shared manifest to test itself is a guard nobody runs.
#[test]
fn the_real_root_manifest_would_refuse_a_hazard_appended_to_it() {
    let root = workspace_root();
    let manifest = fs::read_to_string(root.join("Cargo.toml")).expect("root Cargo.toml");
    assert!(
        audit("Cargo.toml", &manifest).is_empty(),
        "the live manifest must be clean before this test means anything"
    );

    let planted =
        format!("{manifest}\n[profile.release]\nopt-level = 0\ndebug-assertions = false\n");
    let findings = audit("Cargo.toml", &planted);
    assert!(
        matches!(findings.as_slice(), [Finding::CeilingAboveFrames { .. }]),
        "the real manifest plus one hazard must be refused, or the live test is scanning \
         something it cannot judge: {findings:?}"
    );
}

/// The comment is not the guard. If `#` stopped being stripped, a commented-out
/// hazard would be read as a live one and this file would fail on a clean tree —
/// which is the direction that gets a guard deleted.
#[test]
fn commented_out_profile_lines_are_not_read_as_settings() {
    assert!(
        audit(
            "planted/Cargo.toml",
            "[profile.release]\n# opt-level = 0\nlto = true\n",
        )
        .is_empty(),
        "a comment must not be parsed as a setting"
    );
}
