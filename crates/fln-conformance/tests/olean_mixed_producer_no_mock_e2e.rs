//! No-mock seed for the W2 mixed-producer matrix (`franken_lean-0nz`).
//!
//! This is intentionally one narrow production path, not the full codec claim:
//! FrankenLean writes a basic `Demo` module which imports the pinned Reference
//! `Init`, publishes its `.olean` and `.ilean` together through the atomic
//! artifact store, and then the pinned `leanchecker` plus `lean --stdin`
//! consume that exact generation. It is the "Reference toolchain loads and
//! checks our written oleans" half of `franken_lean-0nz`'s acceptance, which
//! `franken_lean-z8j.1.20` records as having no per-commit evidence.
//!
//! An acceptance is only worth something if the same checker, on the same path,
//! can refuse: a second fresh module whose one axiom has an ill-typed type is
//! published the same way and must be rejected by the pinned kernel.
//!
//! What it does NOT establish: environment-extension payloads, module-system
//! (`.olean.server`/`.olean.private`) emission, full-Corpus fresh emission,
//! the opposite direction of the matrix, or byte identity against a separately
//! elaborated Reference module. Those remain owned by `franken_lean-0nz`.
//!
//! Provenance: ported from FoggyForge's unlanded "conformance: seed fresh olean
//! mixed-producer path" and "test(olean): reclaim artifact fixture roots"
//! (archived at tag `archive/foggyforge/kernel-corpus-fixes-20260730`),
//! adapted to the current scratch fence and pin-rig registry.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

use fln_conformance::pin;
use fln_core::expr::Expr;
use fln_core::name::Name;
use fln_core::scratch::{OLEAN_MIXED_PRODUCER_PREFIX, ScratchRoot};
use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};
use fln_hash::canon::{Canonical, SCHEMA_NAME};
use fln_olean::artifact::{ArtifactLimits, ArtifactMemberInput, ArtifactStore};
use fln_olean::format;
use fln_olean::ilean::{Ilean, IleanBudget, IleanImport, encode_ilean};
use fln_olean::region::{ModuleImport, OleanHeader, OleanView};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

fn command_output(command: &mut Command, context: &str) -> Result<std::process::Output, String> {
    command
        .output()
        .map_err(|error| format!("{context}: {error}"))
}

/// One fresh FrankenLean module importing the Reference's `Init`, holding one axiom.
fn axiom_module(module: &str, axiom: &str, type_: Expr) -> (Name, ConstantInfo) {
    let name = Name::from_components([module, axiom]);
    let constant = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    });
    (name, constant)
}

/// Encode `module` with its `.ilean`, publish both through the atomic artifact store,
/// and return the scratch guard (which owns the store) plus a `LEAN_PATH` that puts the
/// published generation ahead of the Reference library.
fn publish_fresh_module(
    module: &str,
    constant: ConstantInfo,
    init: &OleanHeader,
    reference_commit: &str,
    reference_lib: &Path,
) -> Result<(ScratchRoot, OsString), String> {
    let imports = [ModuleImport {
        module: Name::from_components(["Init"]),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let olean = encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &[constant],
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: init.version,
            flags: init.flags,
            lean_version: &init.lean_version,
            githash: reference_commit,
            base_addr: (format::REGION_ALIGN as u64) * 2,
        },
        WriteBudget::default(),
    )
    .map_err(|error| format!("encode fresh {module}.olean: {error}"))?;
    let ilean = encode_ilean(
        &Ilean {
            version: format::ILEAN_VERSION,
            module: module.to_string(),
            direct_imports: vec![IleanImport {
                module: "Init".to_string(),
                is_private: false,
                is_all: false,
                is_meta: false,
            }],
            references: BTreeMap::new(),
            decls: BTreeMap::new(),
        },
        IleanBudget::default(),
    )
    .map_err(|error| format!("encode fresh {module}.ilean: {error}"))?;

    let semantic_bytes = Name::from_components([module]).to_canonical_bytes();
    let olean_member = format!("{module}.olean");
    let ilean_member = format!("{module}.ilean");
    let members = [
        ArtifactMemberInput::new(&olean_member, &olean.bytes, SCHEMA_NAME, &semantic_bytes),
        ArtifactMemberInput::new(&ilean_member, &ilean, SCHEMA_NAME, &semantic_bytes),
    ];
    let scratch = ScratchRoot::create(OLEAN_MIXED_PRODUCER_PREFIX, "mixed-producer", module)
        .map_err(|error| format!("create mixed-producer scratch root for {module}: {error}"))?;
    let store = ArtifactStore::new(scratch.path(), ArtifactLimits::default());
    store
        .publish(&members)
        .map_err(|error| format!("publish fresh {module} generation: {error}"))?;
    let resolved = store
        .resolve_active()
        .map_err(|error| format!("resolve fresh {module} generation: {error}"))?;
    if resolved.member_path(&olean_member).is_none() {
        return Err(format!(
            "the active {module} generation does not manifest {olean_member}"
        ));
    }
    if reference_lib.join(&olean_member).exists() {
        return Err(format!(
            "pinned Reference library unexpectedly supplies {olean_member}"
        ));
    }
    let lean_path = std::env::join_paths([resolved.generation_dir(), reference_lib])
        .map_err(|error| format!("join mixed-producer LEAN_PATH for {module}: {error}"))?;
    Ok((scratch, lean_path))
}

fn run_leanchecker(
    leanchecker: &Path,
    module: &str,
    lean_path: &OsString,
) -> Result<std::process::Output, String> {
    // `-v` makes the checker name each module it replays, so an exit 0 that never
    // reached our module cannot pass for an acceptance of it.
    command_output(
        Command::new(leanchecker)
            .arg("-v")
            .arg(module)
            .env("LEAN_PATH", lean_path)
            .env_remove("LEAN_SYSROOT")
            .env("LC_ALL", "C")
            .env("TZ", "UTC"),
        &format!("run pinned leanchecker over fresh {module}.olean"),
    )
}

#[test]
fn olean_mixed_producer_no_mock_e2e() -> Result<(), String> {
    let run = pin::RigRun::new(pin::PinRig::OleanMixedProducerNoMockE2e);
    let Some(lean) = pin::pinned_lean() else {
        let notice = run.typed_skip()?;
        eprintln!("{notice}");
        return Ok(());
    };
    let reference_commit =
        pin::pinned_commit().ok_or_else(|| "SUITE.lock has no Reference commit".to_string())?;
    let bin_dir = lean
        .parent()
        .ok_or_else(|| format!("pinned lean has no binary directory: {}", lean.display()))?;
    let toolchain_root = bin_dir
        .parent()
        .ok_or_else(|| format!("pinned lean has no toolchain root: {}", lean.display()))?;
    let reference_lib = toolchain_root.join("lib/lean");
    let leanchecker = bin_dir.join(format!("leanchecker{}", std::env::consts::EXE_SUFFIX));
    // Once the pinned `lean` exists, a missing sibling is a broken installation of the
    // pin, not an absent pin: it fails rather than taking the typed skip.
    if !reference_lib.is_dir() {
        return Err(format!(
            "pinned Reference library is absent: {}",
            reference_lib.display()
        ));
    }
    if !leanchecker.is_file() {
        return Err(format!(
            "pinned Reference checker is absent: {}",
            leanchecker.display()
        ));
    }

    let identity = command_output(
        Command::new(&lean)
            .arg("--githash")
            .env_remove("LEAN_PATH")
            .env_remove("LEAN_SYSROOT")
            .env("LC_ALL", "C")
            .env("TZ", "UTC"),
        "run pinned lean --githash",
    )?;
    if !identity.status.success()
        || String::from_utf8_lossy(&identity.stdout).trim() != reference_commit
    {
        return Err(format!(
            "pinned lean identity differs from SUITE.lock: status={:?}, stdout={:?}, stderr={:?}",
            identity.status,
            String::from_utf8_lossy(&identity.stdout),
            String::from_utf8_lossy(&identity.stderr)
        ));
    }

    // The fresh modules' headers are taken from the Reference's own Init so the
    // loader's version/githash gate is exercised against the real pin rather than a
    // transcription of it.
    let init_bytes = std::fs::read(reference_lib.join("Init.olean"))
        .map_err(|error| format!("read pinned Init.olean: {error}"))?;
    let init_view = OleanView::parse(&init_bytes)
        .map_err(|error| format!("parse pinned Init.olean header: {error}"))?;
    if init_view.header.githash != reference_commit {
        return Err("pinned Init.olean and SUITE.lock name different commits".to_string());
    }
    let nat = Expr::const_(Name::from_components(["Nat"]), Vec::new());

    // ACCEPTANCE: `Nat` resolves only through the imported Reference-built `Init`, so
    // the checked environment is genuinely mixed-producer.
    let (_, good) = axiom_module("Demo", "freshNat", nat.clone());
    let (_good_scratch, good_path) = publish_fresh_module(
        "Demo",
        good,
        &init_view.header,
        &reference_commit,
        &reference_lib,
    )?;
    let checked = run_leanchecker(&leanchecker, "Demo", &good_path)?;
    let checked_stdout = String::from_utf8_lossy(&checked.stdout);
    if !checked.status.success() || !checked_stdout.contains("replaying Demo") {
        return Err(format!(
            "pinned leanchecker did not replay and accept fresh Demo.olean: status={:?}, \
             stdout={checked_stdout:?}, stderr={:?}",
            checked.status,
            String::from_utf8_lossy(&checked.stderr)
        ));
    }

    let mut child = Command::new(&lean)
        .arg("--stdin")
        .env("LEAN_PATH", &good_path)
        .env_remove("LEAN_SYSROOT")
        .env("LC_ALL", "C")
        .env("TZ", "UTC")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("start pinned lean consumer: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "pinned lean consumer has no stdin".to_string())?
        .write_all(b"import Demo\n#check Demo.freshNat\n")
        .map_err(|error| format!("write pinned lean probe: {error}"))?;
    let consumed = child
        .wait_with_output()
        .map_err(|error| format!("wait for pinned lean consumer: {error}"))?;
    let stdout = String::from_utf8_lossy(&consumed.stdout);
    let stderr = String::from_utf8_lossy(&consumed.stderr);
    if !consumed.status.success()
        || stdout.trim() != "Demo.freshNat : Nat"
        || !stderr.trim().is_empty()
    {
        return Err(format!(
            "pinned lean did not consume the fresh module exactly: status={:?}, \
             stdout={stdout:?}, stderr={stderr:?}",
            consumed.status
        ));
    }

    // REFUSAL CONTROL: the same writer, store and checker over `Nat Nat`, which is not a
    // type. A leanchecker that accepted this would make the acceptance above vacuous.
    let (_, bad) = axiom_module("DemoBad", "freshNat", Expr::app(nat.clone(), nat));
    let (_bad_scratch, bad_path) = publish_fresh_module(
        "DemoBad",
        bad,
        &init_view.header,
        &reference_commit,
        &reference_lib,
    )?;
    let refused = run_leanchecker(&leanchecker, "DemoBad", &bad_path)?;
    let refused_stderr = String::from_utf8_lossy(&refused.stderr);
    if refused.status.success()
        || !refused_stderr.contains("(kernel)")
        || !refused_stderr.contains("DemoBad.freshNat")
    {
        return Err(format!(
            "pinned leanchecker did not refuse the ill-typed fresh DemoBad.olean with a \
             kernel error naming it: status={:?}, stdout={:?}, stderr={refused_stderr:?}",
            refused.status,
            String::from_utf8_lossy(&refused.stdout)
        ));
    }

    run.executed()
}
