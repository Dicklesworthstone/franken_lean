//! Shared file-scale T2/T3 differential runner consumed by both the
//! `t2-differential` CLI binary and the `PinRig::FileScaleT2Differential` test
//! (bead `fln-file-scale-t2-differential-5f1b`).
//!
//! Takes the pinned Reference `lean` path explicitly from the caller so this
//! library module contains zero pin-locator coordinates.

use std::collections::BTreeMap;
use std::fs;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use fln::{OleanDecodeLimits, VmExecutionLimits};
use fln_cli::{LeanImportBaseCache, LeanSourceCaptureOutcome, capture_lean_source_with_cache};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;

use super::{
    CheckpointJournal, ModuleSnapshot, ObservedFileRow, SideVerdict, SnapshotError, T2LedgerRow,
    T2NormalizerId, T2RatchetLedger, TierStatus, compare_modules, fixture_digest_hex, scratch_root,
};

pub const LEDGER_REL: &str = "crates/fln-conformance/evidence/t2_differential/ledger.tsv";
const REF_DIFF_LADDER_DIR: &str = "crates/fln-cli/tests/fixtures/source_ladder";
const ORDINARY_PROBE_DIR: &str = "crates/fln-cli/tests/fixtures/ordinary_lean_probe";
const LOCAL_IMPORTS_DIR: &str = "crates/fln-conformance/tests/fixtures/t2_local_imports";
const UPSTREAM_LEDGER_REL: &str = "crates/fln-cli/tests/fixtures/upstream_suite/ledger.tsv";

pub const FLOOR_SOURCE_LADDER: usize = 100;
pub const FLOOR_ORDINARY_PROBE: usize = 37;
pub const FLOOR_LOCAL_IMPORTS: usize = 3;
pub const FLOOR_UPSTREAM_ELAB: usize = 20;

const MAX_SOURCE_BYTES: usize = 4 * 1024 * 1024;
const DEFAULT_WORKERS: usize = 4;

#[derive(Debug, Clone)]
pub struct RunOptions {
    pub workers: usize,
    pub write_ledger: bool,
    pub log_path: Option<PathBuf>,
}

impl Default for RunOptions {
    fn default() -> Self {
        Self {
            workers: DEFAULT_WORKERS,
            write_ledger: false,
            log_path: None,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FamilySummary {
    pub total: usize,
    pub both_accept: usize,
    pub both_reject: usize,
    pub native_rejects: usize,
    pub false_accept: usize,
    pub inconclusive: usize,
    pub primary_t2_identical: usize,
    pub full_t2_identical: usize,
    pub t3_identical: usize,
}

#[derive(Debug, Clone)]
pub struct RunSummary {
    pub pin_tag: String,
    pub pin_commit: String,
    pub binary_digest: String,
    pub observed: Vec<ObservedFileRow>,
    pub per_family: BTreeMap<String, FamilySummary>,
    pub improvements: Vec<String>,
}

#[derive(Debug, Clone)]
struct TargetFile {
    family: &'static str,
    rel_key: String,
    abs_path: PathBuf,
    module_name: String,
}

fn collect_population(root: &Path) -> Result<Vec<TargetFile>, String> {
    let mut targets = Vec::new();

    for dir in ["examples", REF_DIFF_LADDER_DIR] {
        let full_dir = root.join(dir);
        let mut files: Vec<PathBuf> = fs::read_dir(&full_dir)
            .map_err(|e| format!("read {}: {e}", full_dir.display()))?
            .flatten()
            .map(|entry| entry.path())
            .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("lean"))
            .collect();
        files.sort();
        for path in files {
            let rel = path
                .strip_prefix(root)
                .map_err(|e| format!("strip root {}: {e}", path.display()))?
                .to_string_lossy()
                .replace('\\', "/");
            let stem = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("Main")
                .to_owned();
            targets.push(TargetFile {
                family: "source_ladder",
                rel_key: rel,
                abs_path: path,
                module_name: stem,
            });
        }
    }

    let probe_dir = root.join(ORDINARY_PROBE_DIR);
    let manifest_text = fs::read_to_string(probe_dir.join("manifest.tsv"))
        .map_err(|e| format!("read ordinary_lean_probe/manifest.tsv: {e}"))?;
    let mut probe_files = Vec::new();
    for line in manifest_text.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let Some(file) = line.split('\t').next() else {
            continue;
        };
        probe_files.push(file.to_owned());
    }
    probe_files.sort();
    for file in probe_files {
        let abs = probe_dir.join(&file);
        let stem = abs
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("Main")
            .to_owned();
        targets.push(TargetFile {
            family: "ordinary_probe",
            rel_key: format!("{ORDINARY_PROBE_DIR}/{file}"),
            abs_path: abs,
            module_name: stem,
        });
    }

    let upstream_ledger = fs::read_to_string(root.join(UPSTREAM_LEDGER_REL))
        .map_err(|e| format!("read upstream_suite/ledger.tsv: {e}"))?;
    let mut upstream_files = Vec::new();
    for line in upstream_ledger.lines() {
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() >= 2 && fields[1] == "0" && fields[0].starts_with("elab/") {
            let abs = root.join("vendor/lean4-src/tests").join(fields[0]);
            if abs.is_file() {
                upstream_files.push((fields[0].to_owned(), abs));
            }
        }
    }
    upstream_files.sort_by(|a, b| a.0.cmp(&b.0));
    for (rel_under_tests, abs) in upstream_files {
        let stem = abs
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("Main")
            .to_owned();
        targets.push(TargetFile {
            family: "upstream_elab",
            rel_key: format!("vendor/lean4-src/tests/{rel_under_tests}"),
            abs_path: abs,
            module_name: stem,
        });
    }

    Ok(targets)
}

fn pin_compile_olean(
    pin_lean: &Path,
    root_dir: &Path,
    source_path: &Path,
    olean_out: &Path,
    extra_lean_path: Option<&Path>,
) -> Result<bool, String> {
    let mut cmd = Command::new(pin_lean);
    cmd.arg("-R")
        .arg(root_dir)
        .arg("-o")
        .arg(olean_out)
        .arg(source_path);
    if let Some(dir) = extra_lean_path {
        let mut lean_path = dir.as_os_str().to_os_string();
        if let Ok(existing) = std::env::var("LEAN_PATH")
            && !existing.is_empty()
        {
            lean_path.push(":");
            lean_path.push(existing);
        }
        cmd.env("LEAN_PATH", lean_path);
    }
    let output = cmd
        .output()
        .map_err(|error| format!("invoke pinned lean -o: {error}"))?;
    Ok(output.status.success())
}

fn owner_for_diff(
    pin_verdict: SideVerdict,
    native_verdict: SideVerdict,
    diff_class: &str,
    first_difference: &str,
) -> String {
    if pin_verdict == SideVerdict::Reject && native_verdict == SideVerdict::Reject {
        return "negative_control:both_reject".to_owned();
    }
    if pin_verdict == SideVerdict::Accept && native_verdict == SideVerdict::Reject {
        return "fln-upstream-suite-scoreboard-n04o".to_owned();
    }
    if diff_class == "identical" {
        return "verified".to_owned();
    }
    if first_difference.contains("match_") || first_difference.contains("_sparseCasesOn_") {
        return "fln-matcher-auxiliary-definitions-lzxm".to_owned();
    }
    if first_difference.contains("_sunfold")
        || first_difference.contains("._f")
        || first_difference.contains(".eq_")
        || first_difference.contains("._unsafe_rec")
    {
        return "fln-fln-definition-auxiliary-names-lv0n".to_owned();
    }
    if first_difference.contains("sizeof")
        || first_difference.contains("ctorIdx")
        || first_difference.contains("_flat_ctor")
        || first_difference.contains("inductive_construction")
        || first_difference.contains(".brecOn.eq")
        || first_difference.contains(".below.")
        || first_difference.contains("._autoParam")
    {
        return "franken_lean-z8j.1.12:inductive_auxiliaries".to_owned();
    }
    if first_difference.contains("pin_only_primary: term") {
        return "fln-macro-rung-e1rk:syntax_parser_descr".to_owned();
    }
    if first_difference.contains("attributes:") {
        return "fln-j0hb:attribute_journal_parity".to_owned();
    }
    if first_difference.contains("LetE(") {
        return "fln-j0hb:let_e_in_type".to_owned();
    }
    if first_difference.contains("_proof_") {
        return "fln-j0hb:proof_aux".to_owned();
    }
    if first_difference.contains("native_only_primary: 1") {
        return "fln-j0hb:eval_numeric_leak".to_owned();
    }
    if first_difference.contains("App vs Lit(") {
        return "fln-j0hb:ofnat_lit_index".to_owned();
    }
    "fln-j0hb:t2_elab_parity".to_owned()
}

#[allow(clippy::too_many_arguments)]
fn observe_single_file(
    root: &Path,
    pin_lean: &Path,
    pin_tag: &str,
    pin_commit: &str,
    binary_digest: &str,
    scratch: &Path,
    index: usize,
    target: &TargetFile,
    base_cache: &Arc<LeanImportBaseCache>,
) -> ObservedFileRow {
    let source_bytes = fs::read(&target.abs_path).unwrap_or_default();
    let source_digest = fixture_digest_hex(&source_bytes);

    let olean_out = scratch.join(format!("single_{index}.olean"));
    let pin_verdict = match pin_compile_olean(pin_lean, root, &target.abs_path, &olean_out, None) {
        Ok(true) => SideVerdict::Accept,
        Ok(false) => SideVerdict::Reject,
        Err(_) => SideVerdict::Inconclusive,
    };

    let capture = capture_lean_source_with_cache(
        &target.abs_path,
        MAX_SOURCE_BYTES,
        NonZeroUsize::new(4).unwrap_or(NonZeroUsize::MIN),
        VmExecutionLimits::default(),
        base_cache,
    );
    let native_verdict = match capture.outcome {
        LeanSourceCaptureOutcome::Accepted => SideVerdict::Accept,
        LeanSourceCaptureOutcome::Rejected => SideVerdict::Reject,
        LeanSourceCaptureOutcome::Inconclusive { .. }
        | LeanSourceCaptureOutcome::InternalFault { .. } => SideVerdict::Inconclusive,
    };

    if pin_verdict == SideVerdict::Accept && native_verdict == SideVerdict::Accept {
        let decode_limits = OleanDecodeLimits::new(32 * 1024 * 1024);
        let mod_name = Name::from_components([target.module_name.as_str()]);
        let pin_snap = match ModuleSnapshot::from_olean_file(mod_name, &olean_out, decode_limits) {
            Ok(snap) => snap,
            Err(error) => {
                return ObservedFileRow {
                    family: target.family.to_owned(),
                    file: target.rel_key.clone(),
                    source_digest,
                    pin_tag: pin_tag.to_owned(),
                    pin_commit: pin_commit.to_owned(),
                    binary_digest: binary_digest.to_owned(),
                    normalizer: T2NormalizerId::V1.as_str().to_owned(),
                    pin_verdict: SideVerdict::Inconclusive,
                    native_verdict,
                    primary_t2: TierStatus::NotApplicable,
                    full_t2: TierStatus::NotApplicable,
                    t3: TierStatus::NotApplicable,
                    diff_class: "pin_olean_decode_error".to_owned(),
                    first_difference: error.to_string(),
                    native_decls: 0,
                    pin_decls: 0,
                };
            }
        };
        let Some(native_mod) = capture.modules.last() else {
            return ObservedFileRow {
                family: target.family.to_owned(),
                file: target.rel_key.clone(),
                source_digest,
                pin_tag: pin_tag.to_owned(),
                pin_commit: pin_commit.to_owned(),
                binary_digest: binary_digest.to_owned(),
                normalizer: T2NormalizerId::V1.as_str().to_owned(),
                pin_verdict,
                native_verdict: SideVerdict::Inconclusive,
                primary_t2: TierStatus::NotApplicable,
                full_t2: TierStatus::NotApplicable,
                t3: TierStatus::NotApplicable,
                diff_class: "native_capture_empty".to_owned(),
                first_difference: "accepted native run captured zero modules".to_owned(),
                native_decls: 0,
                pin_decls: pin_snap.constants.len(),
            };
        };
        let native_snap = ModuleSnapshot::from_captured_module(native_mod);
        match compare_modules(&native_snap, &pin_snap, T2NormalizerId::V1) {
            Ok(cmp) => ObservedFileRow {
                family: target.family.to_owned(),
                file: target.rel_key.clone(),
                source_digest,
                pin_tag: pin_tag.to_owned(),
                pin_commit: pin_commit.to_owned(),
                binary_digest: binary_digest.to_owned(),
                normalizer: T2NormalizerId::V1.as_str().to_owned(),
                pin_verdict,
                native_verdict,
                primary_t2: if cmp.primary_t2_identical {
                    TierStatus::Identical
                } else {
                    TierStatus::Diff
                },
                full_t2: if cmp.full_t2_identical {
                    TierStatus::Identical
                } else {
                    TierStatus::Diff
                },
                t3: if cmp.t3_identical {
                    TierStatus::Identical
                } else {
                    TierStatus::Diff
                },
                diff_class: cmp.diff_class().to_owned(),
                first_difference: cmp.first_difference.unwrap_or_default(),
                native_decls: cmp.native_declaration_count,
                pin_decls: cmp.pin_declaration_count,
            },
            Err(error) => ObservedFileRow {
                family: target.family.to_owned(),
                file: target.rel_key.clone(),
                source_digest,
                pin_tag: pin_tag.to_owned(),
                pin_commit: pin_commit.to_owned(),
                binary_digest: binary_digest.to_owned(),
                normalizer: T2NormalizerId::V1.as_str().to_owned(),
                pin_verdict,
                native_verdict: SideVerdict::Inconclusive,
                primary_t2: TierStatus::NotApplicable,
                full_t2: TierStatus::NotApplicable,
                t3: TierStatus::NotApplicable,
                diff_class: "normalizer_budget".to_owned(),
                first_difference: error.to_string(),
                native_decls: native_snap.constants.len(),
                pin_decls: pin_snap.constants.len(),
            },
        }
    } else {
        let diff_class = match (pin_verdict, native_verdict) {
            (SideVerdict::Reject, SideVerdict::Reject) => "both_reject",
            (SideVerdict::Accept, SideVerdict::Reject) => "native_rejects",
            (SideVerdict::Reject, SideVerdict::Accept) => "false_accept",
            _ => "inconclusive",
        };
        ObservedFileRow {
            family: target.family.to_owned(),
            file: target.rel_key.clone(),
            source_digest,
            pin_tag: pin_tag.to_owned(),
            pin_commit: pin_commit.to_owned(),
            binary_digest: binary_digest.to_owned(),
            normalizer: T2NormalizerId::V1.as_str().to_owned(),
            pin_verdict,
            native_verdict,
            primary_t2: TierStatus::NotApplicable,
            full_t2: TierStatus::NotApplicable,
            t3: TierStatus::NotApplicable,
            diff_class: diff_class.to_owned(),
            first_difference: String::new(),
            native_decls: 0,
            pin_decls: 0,
        }
    }
}

fn observe_local_import_chain(
    root: &Path,
    pin_lean: &Path,
    pin_tag: &str,
    pin_commit: &str,
    binary_digest: &str,
    scratch: &Path,
    base_cache: &Arc<LeanImportBaseCache>,
) -> Result<(Vec<ObservedFileRow>, ModuleSnapshot, ModuleSnapshot), String> {
    let fixture_dir = root.join(LOCAL_IMPORTS_DIR);
    let olean_dir = scratch.join("local_imports_olean");
    fs::create_dir_all(&olean_dir).map_err(|e| format!("create local_imports_olean dir: {e}"))?;

    let chain = ["Lib", "Main", "Consumer"];
    let mut pin_snaps: BTreeMap<String, ModuleSnapshot> = BTreeMap::new();
    let decode_limits = OleanDecodeLimits::new(32 * 1024 * 1024);
    for module in chain {
        let src = fixture_dir.join(format!("{module}.lean"));
        let out = olean_dir.join(format!("{module}.olean"));
        let ok = pin_compile_olean(pin_lean, &fixture_dir, &src, &out, Some(&olean_dir))?;
        if !ok {
            return Err(format!("pinned lean rejected local_imports {module}.lean"));
        }
        let snap =
            ModuleSnapshot::from_olean_file(Name::from_components([module]), &out, decode_limits)
                .map_err(|e| format!("decode pinned {module}.olean: {e}"))?;
        pin_snaps.insert(module.to_owned(), snap);
    }

    let consumer_src = fixture_dir.join("Consumer.lean");
    let capture = capture_lean_source_with_cache(
        &consumer_src,
        MAX_SOURCE_BYTES,
        NonZeroUsize::new(4).unwrap_or(NonZeroUsize::MIN),
        VmExecutionLimits::default(),
        base_cache,
    );
    if capture.outcome != LeanSourceCaptureOutcome::Accepted {
        return Err(format!(
            "FrankenLean did not accept Consumer.lean local-import chain: outcome={:?} stdout={} stderr={}",
            capture.outcome, capture.output.stdout, capture.output.stderr
        ));
    }
    if capture.modules.len() != 3 {
        return Err(format!(
            "expected 3 modules (Lib, Main, Consumer) in capture, found {}",
            capture.modules.len()
        ));
    }

    let mut native_snaps: BTreeMap<String, ModuleSnapshot> = BTreeMap::new();
    for (idx, captured) in capture.modules.iter().enumerate() {
        // `lean_entry_module_name` derives the entry module's dotted path
        // relative to cwd (e.g. `crates.fln-conformance...Consumer`), while
        // local imports keep their imported names (`Lib`, `Main`).
        let key = if idx + 1 == capture.modules.len() {
            "Consumer".to_owned()
        } else {
            captured.module.to_display_string()
        };
        native_snaps.insert(key, ModuleSnapshot::from_captured_module(captured));
    }

    let mut rows = Vec::new();
    for module in chain {
        let src_path = fixture_dir.join(format!("{module}.lean"));
        let source_bytes =
            fs::read(&src_path).map_err(|e| format!("read {}: {e}", src_path.display()))?;
        let source_digest = fixture_digest_hex(&source_bytes);
        let pin_snap = pin_snaps
            .get(module)
            .ok_or_else(|| format!("missing pin snap for {module}"))?;
        let native_snap = native_snaps
            .get(module)
            .ok_or_else(|| format!("missing native snap for {module}"))?;
        let cmp = compare_modules(native_snap, pin_snap, T2NormalizerId::V1)
            .map_err(|e| format!("compare {module}: {e}"))?;
        rows.push(ObservedFileRow {
            family: "local_imports".to_owned(),
            file: format!("{LOCAL_IMPORTS_DIR}/{module}.lean"),
            source_digest,
            pin_tag: pin_tag.to_owned(),
            pin_commit: pin_commit.to_owned(),
            binary_digest: binary_digest.to_owned(),
            normalizer: T2NormalizerId::V1.as_str().to_owned(),
            pin_verdict: SideVerdict::Accept,
            native_verdict: SideVerdict::Accept,
            primary_t2: if cmp.primary_t2_identical {
                TierStatus::Identical
            } else {
                TierStatus::Diff
            },
            full_t2: if cmp.full_t2_identical {
                TierStatus::Identical
            } else {
                TierStatus::Diff
            },
            t3: if cmp.t3_identical {
                TierStatus::Identical
            } else {
                TierStatus::Diff
            },
            diff_class: cmp.diff_class().to_owned(),
            first_difference: cmp.first_difference.unwrap_or_default(),
            native_decls: cmp.native_declaration_count,
            pin_decls: cmp.pin_declaration_count,
        });
    }

    let main_native = native_snaps
        .remove("Main")
        .ok_or_else(|| "missing native Main snapshot".to_owned())?;
    let main_pin = pin_snaps
        .remove("Main")
        .ok_or_else(|| "missing pin Main snapshot".to_owned())?;
    Ok((rows, main_native, main_pin))
}

fn flip_first_implicit_binder(expr: &Expr) -> Expr {
    match expr.node() {
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info: BinderInfo::Implicit,
        } => Expr::forall_e(
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            BinderInfo::Default,
        ),
        _ => expr.clone(),
    }
}

/// Run the full file-scale T2/T3 differential suite against the live pinned
/// Reference `pin_lean`, execute all four live negative/trivia/corruption/resume
/// controls, and verify (or write, when `options.write_ledger`) the ratchet ledger.
pub fn run_file_scale_differential(
    root: &Path,
    pin_lean: &Path,
    pin_tag: &str,
    pin_commit: &str,
    options: &RunOptions,
) -> Result<RunSummary, String> {
    let exe_bytes = std::env::current_exe()
        .and_then(fs::read)
        .unwrap_or_else(|_| b"unknown-binary".to_vec());
    let binary_digest = fixture_digest_hex(&exe_bytes);
    let scratch = scratch_root("file-scale").map_err(|e| format!("create scratch root: {e}"))?;
    let targets = collect_population(root)?;
    let workers = options.workers.max(1);

    let base_cache = Arc::new(LeanImportBaseCache::new());
    let next_index = AtomicUsize::new(0);
    let results: Mutex<Vec<(usize, ObservedFileRow)>> = Mutex::new(Vec::new());
    let binary_digest_ref = binary_digest.as_str();
    std::thread::scope(|scope| {
        for _ in 0..workers {
            let scratch_path = scratch.path();
            let targets = &targets;
            let next_index = &next_index;
            let results = &results;
            let base_cache = &base_cache;
            scope.spawn(move || {
                loop {
                    let idx = next_index.fetch_add(1, Ordering::Relaxed);
                    if idx >= targets.len() {
                        break;
                    }
                    let row = observe_single_file(
                        root,
                        pin_lean,
                        pin_tag,
                        pin_commit,
                        binary_digest_ref,
                        scratch_path,
                        idx,
                        &targets[idx],
                        base_cache,
                    );
                    if let Ok(mut guard) = results.lock() {
                        guard.push((idx, row));
                    }
                }
            });
        }
    });

    let mut indexed = results
        .into_inner()
        .map_err(|_| "worker results mutex poisoned".to_owned())?;
    indexed.sort_by_key(|(idx, _)| *idx);
    let mut observed: Vec<ObservedFileRow> = indexed.into_iter().map(|(_, row)| row).collect();

    let (chain_rows, main_native, main_pin) = observe_local_import_chain(
        root,
        pin_lean,
        pin_tag,
        pin_commit,
        &binary_digest,
        scratch.path(),
        &base_cache,
    )?;
    observed.extend(chain_rows);

    // Control 1: Planted implicit-binder mutation on live Main.wrapBox must fail T2.
    let main_clean_cmp = compare_modules(&main_native, &main_pin, T2NormalizerId::V1)
        .map_err(|e| format!("compare clean Main: {e}"))?;
    if !main_clean_cmp.primary_t2_identical {
        return Err(format!(
            "local_imports Main.lean primary declarations not T2-identical: {:?}",
            main_clean_cmp.first_difference
        ));
    }
    let mut mutated_main = main_native;
    if let Some(ConstantInfo::Defn(def)) = mutated_main
        .constants
        .get_mut(&Name::from_components(["wrapBox"]))
    {
        def.base.type_ = flip_first_implicit_binder(&def.base.type_);
    }
    let main_mut_cmp = compare_modules(&mutated_main, &main_pin, T2NormalizerId::V1)
        .map_err(|e| format!("compare mutated Main: {e}"))?;
    if main_mut_cmp.primary_t2_identical || main_mut_cmp.full_t2_identical {
        return Err(
            "planted implicit->explicit binder mutation on live Main.wrapBox did not fail T2"
                .to_owned(),
        );
    }

    // Control 2: Harmless comment & whitespace edit preserves T2 on live pin + native.
    let trivia_dir = scratch.join("trivia_control");
    fs::create_dir_all(&trivia_dir).map_err(|e| format!("create trivia dir: {e}"))?;
    let orig_lib = fs::read_to_string(root.join(LOCAL_IMPORTS_DIR).join("Lib.lean"))
        .map_err(|e| format!("read Lib.lean: {e}"))?;
    let trivia_lib_path = trivia_dir.join("LibTrivia.lean");
    let trivia_source = format!("-- leading comment\n\n{orig_lib}\n/- trailing comment -/\n\n");
    fs::write(&trivia_lib_path, &trivia_source)
        .map_err(|e| format!("write LibTrivia.lean: {e}"))?;
    let trivia_olean = trivia_dir.join("LibTrivia.olean");
    if !pin_compile_olean(pin_lean, &trivia_dir, &trivia_lib_path, &trivia_olean, None)? {
        return Err("pinned lean rejected comment/whitespace-edited LibTrivia.lean".to_owned());
    }
    let trivia_pin_snap = ModuleSnapshot::from_olean_file(
        Name::from_components(["LibTrivia"]),
        &trivia_olean,
        OleanDecodeLimits::new(32 * 1024 * 1024),
    )
    .map_err(|e| format!("decode LibTrivia.olean: {e}"))?;
    let trivia_native_cap = capture_lean_source_with_cache(
        &trivia_lib_path,
        MAX_SOURCE_BYTES,
        NonZeroUsize::new(4).unwrap_or(NonZeroUsize::MIN),
        VmExecutionLimits::default(),
        &base_cache,
    );
    if trivia_native_cap.outcome != LeanSourceCaptureOutcome::Accepted {
        return Err("FrankenLean rejected comment/whitespace-edited LibTrivia.lean".to_owned());
    }
    let trivia_native_snap = ModuleSnapshot::from_captured_module(
        trivia_native_cap
            .modules
            .last()
            .ok_or_else(|| "LibTrivia capture missing entry module".to_owned())?,
    );
    let trivia_cmp = compare_modules(&trivia_native_snap, &trivia_pin_snap, T2NormalizerId::V1)
        .map_err(|e| format!("compare trivia snapshots: {e}"))?;
    if !trivia_cmp.primary_t2_identical {
        return Err(format!(
            "comment/whitespace edit changed primary T2: {:?}",
            trivia_cmp.first_difference
        ));
    }

    // Control 3: Truncated live pin .olean returns typed Decode error; pristine recovers.
    let corrupt_olean = trivia_dir.join("LibTrivia.corrupt.olean");
    let pristine_bytes =
        fs::read(&trivia_olean).map_err(|e| format!("read pristine LibTrivia.olean: {e}"))?;
    fs::write(
        &corrupt_olean,
        &pristine_bytes[..pristine_bytes.len().min(24)],
    )
    .map_err(|e| format!("write truncated olean: {e}"))?;
    if !matches!(
        ModuleSnapshot::from_olean_file(
            Name::from_components(["LibTrivia"]),
            &corrupt_olean,
            OleanDecodeLimits::new(32 * 1024 * 1024),
        ),
        Err(SnapshotError::Decode { .. })
    ) {
        return Err("truncated live pin .olean did not return typed Decode error".to_owned());
    }
    let recovered = ModuleSnapshot::from_olean_file(
        Name::from_components(["LibTrivia"]),
        &trivia_olean,
        OleanDecodeLimits::new(32 * 1024 * 1024),
    )
    .map_err(|e| format!("pristine LibTrivia.olean recovery failed: {e}"))?;
    if recovered.constants.len() != trivia_pin_snap.constants.len() {
        return Err("pristine LibTrivia.olean recovery constant count drifted".to_owned());
    }

    // Control 4: Crash/resume checkpoint over live rows with truncated tail recovery.
    let ckpt_path = scratch.join("live_checkpoint.jsonl");
    {
        let mut journal = CheckpointJournal::load(&ckpt_path)?;
        let half = observed.len() / 2;
        for row in &observed[..half] {
            journal.record(row.clone())?;
        }
        let mut raw =
            fs::read_to_string(&ckpt_path).map_err(|e| format!("read live checkpoint: {e}"))?;
        raw.push_str("{\"schema\":\"fln.t2-differential-checkpoint/1\",\"file\":\"truncated");
        fs::write(&ckpt_path, raw).map_err(|e| format!("write simulated crash tail: {e}"))?;
    }
    let resumed = CheckpointJournal::load(&ckpt_path)?;
    if resumed.corrupted_lines() != 1 {
        return Err(format!(
            "expected exactly 1 corrupted tail line in crash/resume control, got {}",
            resumed.corrupted_lines()
        ));
    }
    for row in &observed[..observed.len() / 2] {
        let Some(cached) = resumed.reusable(
            &row.file,
            &row.source_digest,
            pin_tag,
            pin_commit,
            &binary_digest,
            T2NormalizerId::V1.as_str(),
        ) else {
            return Err(format!(
                "completed prefix row {} did not resume cleanly from checkpoint",
                row.file
            ));
        };
        if cached != row {
            return Err(format!("resumed row {} differed from original", row.file));
        }
    }

    if let Some(log_path) = &options.log_path {
        let mut log_journal = CheckpointJournal::load(log_path)?;
        for row in &observed {
            log_journal.record(row.clone())?;
        }
    }

    let mut per_family: BTreeMap<String, FamilySummary> = BTreeMap::new();
    for row in &observed {
        let entry = per_family
            .entry(row.family.clone())
            .or_insert(FamilySummary {
                total: 0,
                both_accept: 0,
                both_reject: 0,
                native_rejects: 0,
                false_accept: 0,
                inconclusive: 0,
                primary_t2_identical: 0,
                full_t2_identical: 0,
                t3_identical: 0,
            });
        entry.total += 1;
        match (row.pin_verdict, row.native_verdict) {
            (SideVerdict::Accept, SideVerdict::Accept) => entry.both_accept += 1,
            (SideVerdict::Reject, SideVerdict::Reject) => entry.both_reject += 1,
            (SideVerdict::Accept, SideVerdict::Reject) => entry.native_rejects += 1,
            (SideVerdict::Reject, SideVerdict::Accept) => entry.false_accept += 1,
            _ => entry.inconclusive += 1,
        }
        if row.primary_t2 == TierStatus::Identical {
            entry.primary_t2_identical += 1;
        }
        if row.full_t2 == TierStatus::Identical {
            entry.full_t2_identical += 1;
        }
        if row.t3 == TierStatus::Identical {
            entry.t3_identical += 1;
        }
    }

    let false_accepts: Vec<&str> = observed
        .iter()
        .filter(|r| r.pin_verdict == SideVerdict::Reject && r.native_verdict == SideVerdict::Accept)
        .map(|r| r.file.as_str())
        .collect();
    if !false_accepts.is_empty() {
        return Err(format!(
            "FALSE ACCEPTS detected (Reference rejected, FrankenLean accepted): {false_accepts:?}"
        ));
    }

    let ledger_path = root.join(LEDGER_REL);
    if options.write_ledger {
        let mut family_floors = BTreeMap::new();
        family_floors.insert("source_ladder".to_owned(), FLOOR_SOURCE_LADDER);
        family_floors.insert("ordinary_probe".to_owned(), FLOOR_ORDINARY_PROBE);
        family_floors.insert("local_imports".to_owned(), FLOOR_LOCAL_IMPORTS);
        family_floors.insert("upstream_elab".to_owned(), FLOOR_UPSTREAM_ELAB);
        let mut rows = BTreeMap::new();
        for row in &observed {
            rows.insert(
                row.file.clone(),
                T2LedgerRow {
                    family: row.family.clone(),
                    file: row.file.clone(),
                    pin_verdict: row.pin_verdict,
                    native_verdict: row.native_verdict,
                    primary_t2: row.primary_t2,
                    full_t2: row.full_t2,
                    t3: row.t3,
                    diff_class: row.diff_class.clone(),
                    owner_or_note: owner_for_diff(
                        row.pin_verdict,
                        row.native_verdict,
                        &row.diff_class,
                        &row.first_difference,
                    ),
                },
            );
        }
        let ledger = T2RatchetLedger {
            pin_tag: pin_tag.to_owned(),
            normalizer_id: T2NormalizerId::V1.as_str().to_owned(),
            family_floors,
            rows,
        };
        if let Some(parent) = ledger_path.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("create ledger dir: {e}"))?;
        }
        fs::write(&ledger_path, ledger.render())
            .map_err(|e| format!("write {}: {e}", ledger_path.display()))?;
    }

    let ledger_text = fs::read_to_string(&ledger_path)
        .map_err(|e| format!("read {}: {e}", ledger_path.display()))?;
    let ledger = T2RatchetLedger::parse(&ledger_text)?;
    let verdict = ledger.verify(&observed);
    if !verdict.is_clean() {
        return Err(format!(
            "T2 ratchet ledger verification failed ({} problem(s)):\n{}",
            verdict.problems.len(),
            verdict.problems.join("\n")
        ));
    }

    Ok(RunSummary {
        pin_tag: pin_tag.to_owned(),
        pin_commit: pin_commit.to_owned(),
        binary_digest,
        observed,
        per_family,
        improvements: verdict.improvements,
    })
}
