//! Installed-CLI E2E matrix for `fln check-olean --policy` (plan §8.3c, bead `fln-9908`).
//!
//! Exercises the real compiled `fln` binary across all four registered policies
//! (`standard`, `release`, `paranoid`, `compat-bench`) plus unknown/invalid
//! policy invocations, across single-file `.olean`, closed module-set with
//! `--receipts`, and parallel `--continue --jobs` frontier runs.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use fln::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, Level,
    Name, OLEAN_ACCEPTED_VERSIONS, OLEAN_PIN_COMMIT, OLEAN_PIN_TAG, OLEAN_REGION_ALIGN,
    OleanModuleImport, OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader,
    ReducibilityHints, TheoremVal, encode_olean_module,
};

static COUNTER: AtomicU64 = AtomicU64::new(0);

fn scratch_dir(label: &str) -> PathBuf {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "fln-policy-cli-{label}-{}-{id}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn n(parts: &[&str]) -> Name {
    Name::from_components(parts.iter().copied())
}

fn bv(idx: u32) -> Expr {
    Expr::bvar(idx).expect("small bvar")
}

fn encode(imports: &[OleanModuleImport], constants: &[ConstantInfo]) -> Vec<u8> {
    encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.trim_start_matches('v'),
            githash: OLEAN_PIN_COMMIT,
            base_addr: OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("encode olean")
    .bytes
}

fn prop_axiom(name: Name) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: Expr::sort(Level::zero()),
        },
        is_unsafe: false,
    })
}

fn id_thm(name: Name, prop: &Name) -> ConstantInfo {
    let p = Expr::const_(prop.clone(), Vec::new());
    ConstantInfo::Thm(TheoremVal {
        base: ConstantVal {
            name,
            level_params: Vec::new(),
            type_: Expr::forall_e(n(&["h"]), p.clone(), p.clone(), BinderInfo::Default),
        },
        value: Expr::lam(n(&["h"]), p, bv(0), BinderInfo::Default),
        all: Vec::new(),
    })
}

fn unsafe_def(name: Name, prop: &Name) -> ConstantInfo {
    let p = Expr::const_(prop.clone(), Vec::new());
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::forall_e(n(&["h"]), p.clone(), p.clone(), BinderInfo::Default),
        },
        value: Expr::lam(n(&["h"]), p, bv(0), BinderInfo::Default),
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Unsafe,
        all: vec![name],
    })
}

fn run_fln(args: &[&str]) -> (Option<i32>, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(args)
        .output()
        .expect("execute installed fln binary");
    (
        output.status.code(),
        String::from_utf8(output.stdout).expect("utf8 stdout"),
        String::from_utf8(output.stderr).expect("utf8 stderr"),
    )
}

fn extract_json_str<'a>(text: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\":\"");
    let rest = text.split(&needle).nth(1)?;
    rest.split('"').next()
}

fn extract_json_u64(text: &str, key: &str) -> Option<u64> {
    let needle = format!("\"{key}\":");
    let rest = text.split(&needle).nth(1)?;
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    digits.parse().ok()
}

fn write_module(root: &Path, parts: &[&str], bytes: &[u8]) -> PathBuf {
    let mut path = root.to_path_buf();
    for part in &parts[..parts.len() - 1] {
        path.push(part);
    }
    std::fs::create_dir_all(&path).expect("create module dir");
    path.push(format!("{}.olean", parts[parts.len() - 1]));
    std::fs::write(&path, bytes).expect("write module olean");
    path
}

#[test]
fn installed_cli_policy_matrix_single_file_receipts_and_frontier() {
    let root = scratch_dir("matrix");

    // 1. Standalone single-file artifact with 48 ordinary theorems + 1 high-risk unsafe def.
    let prop = n(&["CliPol", "P"]);
    let mut single_rows = vec![prop_axiom(prop.clone())];
    for i in 0..48 {
        single_rows.push(id_thm(n(&["CliPol", &format!("t{i:02}")]), &prop));
    }
    single_rows.push(unsafe_def(n(&["CliPol", "u0"]), &prop));
    let single_path = root.join("Single.olean");
    std::fs::write(&single_path, encode(&[], &single_rows)).expect("write Single.olean");
    let single = single_path.to_str().expect("utf8 path");

    // Unknown/missing/duplicate policy -> typed usage error (exit 2).
    for (args, expected_fragment) in [
        (
            vec!["check-olean", "--policy", "bogus", single],
            "unknown --policy value",
        ),
        (
            vec!["check-olean", "--policy=bogus", single],
            "unknown --policy value",
        ),
        (vec!["check-olean", "--policy"], "--policy requires a value"),
        (
            vec![
                "check-olean",
                "--policy",
                "standard",
                "--policy",
                "release",
                single,
            ],
            "--policy may be supplied at most once",
        ),
    ] {
        let (code, stdout, stderr) = run_fln(&args);
        assert_eq!(
            code,
            Some(2),
            "args={args:?} stdout={stdout} stderr={stderr}"
        );
        assert!(
            stderr.contains(expected_fragment),
            "args={args:?} stderr={stderr}"
        );
    }

    // Default (omitted --policy) == --policy release.
    let (code_def, out_def, err_def) = run_fln(&["check-olean", "--json", single]);
    assert_eq!(code_def, Some(0), "{err_def}");
    let (code_rel, out_rel, err_rel) =
        run_fln(&["check-olean", "--json", "--policy", "release", single]);
    assert_eq!(code_rel, Some(0), "{err_rel}");
    assert_eq!(
        out_def, out_rel,
        "default policy must equal --policy release"
    );
    assert_eq!(extract_json_str(&out_rel, "policy"), Some("release"));
    assert!(out_rel.contains("\"authority\":true"), "{out_rel}");
    assert!(out_rel.contains("\"attestable\":true"), "{out_rel}");
    assert!(out_rel.contains("\"g1Eligible\":true"), "{out_rel}");
    assert_eq!(extract_json_u64(&out_rel, "k1Checked"), Some(50));
    assert_eq!(extract_json_u64(&out_rel, "checkerSelected"), Some(50));
    assert_eq!(extract_json_u64(&out_rel, "skipped"), Some(0));

    // --policy standard: skips low-risk declarations outside 1/16 bucket, checks high-risk floor.
    let (code_std, out_std, err_std) =
        run_fln(&["check-olean", "--json", "--policy=standard", single]);
    assert_eq!(code_std, Some(0), "{err_std}");
    assert_eq!(extract_json_str(&out_std, "policy"), Some("standard"));
    assert!(out_std.contains("\"authority\":true"), "{out_std}");
    assert!(out_std.contains("\"attestable\":true"), "{out_std}");
    assert!(out_std.contains("\"g1Eligible\":false"), "{out_std}");
    let std_selected = extract_json_u64(&out_std, "checkerSelected").expect("checkerSelected");
    let std_skipped = extract_json_u64(&out_std, "skipped").expect("skipped");
    let std_high_risk = extract_json_u64(&out_std, "highRisk").expect("highRisk");
    assert_eq!(std_selected + std_skipped, 50, "{out_std}");
    assert!(std_skipped > 0 && std_selected < 50, "{out_std}");
    assert!(std_high_risk >= 1, "{out_std}");
    assert_eq!(
        extract_json_str(&out_std, "resultLogicalRoot"),
        extract_json_str(&out_rel, "resultLogicalRoot"),
        "standard and release must produce identical logical roots"
    );

    // --policy compat-bench: sampled, NEVER attestable, authority=false.
    let (code_cb, out_cb, err_cb) =
        run_fln(&["check-olean", "--json", "--policy", "compat-bench", single]);
    assert_eq!(code_cb, Some(0), "{err_cb}");
    assert_eq!(extract_json_str(&out_cb, "policy"), Some("compat-bench"));
    assert!(out_cb.contains("\"authority\":false"), "{out_cb}");
    assert!(out_cb.contains("\"attestable\":false"), "{out_cb}");
    assert!(out_cb.contains("\"g1Eligible\":false"), "{out_cb}");
    assert_eq!(
        extract_json_u64(&out_cb, "checkerSelected"),
        Some(std_selected)
    );
    assert_eq!(extract_json_u64(&out_cb, "skipped"), Some(std_skipped));

    // --policy paranoid: unavailable required witness -> exit 3 inconclusive, NEVER silent fallback.
    let (code_par, out_par, err_par) =
        run_fln(&["check-olean", "--json", "--policy", "paranoid", single]);
    assert_eq!(code_par, Some(3), "stdout={out_par} stderr={err_par}");
    assert!(
        out_par.is_empty(),
        "error JSON must go to stderr: {out_par}"
    );
    assert!(err_par.contains("\"class\":\"inconclusive\""), "{err_par}");
    assert_eq!(extract_json_str(&err_par, "policy"), Some("paranoid"));
    assert!(err_par.contains("paranoid-second-witness"), "{err_par}");

    // 2. Closed module-set directory: receipts preserve policy identity & chain differs per policy.
    let set_dir = root.join("modset");
    let base_name = n(&["Set", "Base"]);
    let imp = |module: &Name| OleanModuleImport {
        module: module.clone(),
        import_all: false,
        is_exported: false,
        is_meta: false,
    };
    write_module(
        &set_dir,
        &["Set", "Base"],
        &encode(&[], &[prop_axiom(prop.clone())]),
    );
    let mut leaf_a_rows: Vec<ConstantInfo> = (0..24)
        .map(|i| id_thm(n(&["Set", &format!("a{i:02}")]), &prop))
        .collect();
    leaf_a_rows.push(unsafe_def(n(&["Set", "aUnsafe"]), &prop));
    write_module(
        &set_dir,
        &["Set", "LeafA"],
        &encode(&[imp(&base_name)], &leaf_a_rows),
    );
    let leaf_b_rows: Vec<ConstantInfo> = (0..24)
        .map(|i| id_thm(n(&["Set", &format!("b{i:02}")]), &prop))
        .collect();
    write_module(
        &set_dir,
        &["Set", "LeafB"],
        &encode(&[imp(&base_name)], &leaf_b_rows),
    );
    let set_str = set_dir.to_str().expect("utf8 set_dir");

    let rcpt_rel = root.join("receipts-release.jsonl");
    let rcpt_std = root.join("receipts-standard.jsonl");
    let rcpt_cb = root.join("receipts-compat-bench.jsonl");
    for (policy, rcpt_path, expected_attestable, expected_g1) in [
        ("release", &rcpt_rel, "true", "true"),
        ("standard", &rcpt_std, "true", "false"),
        ("compat-bench", &rcpt_cb, "false", "false"),
    ] {
        let rcpt_str = rcpt_path.to_str().expect("utf8 path");
        let (code, stdout, stderr) = run_fln(&[
            "check-olean",
            "--json",
            "--policy",
            policy,
            "--receipts",
            rcpt_str,
            set_str,
        ]);
        assert_eq!(code, Some(0), "policy={policy} stderr={stderr}");
        assert_eq!(extract_json_str(&stdout, "policy"), Some(policy));
        assert!(
            stdout.contains(&format!("\"attestable\":{expected_attestable}")),
            "policy={policy} stdout={stdout}"
        );
        assert!(
            stdout.contains(&format!("\"g1Eligible\":{expected_g1}")),
            "policy={policy} stdout={stdout}"
        );
        let rcpt_text = std::fs::read_to_string(rcpt_path).expect("read receipt jsonl");
        let lines: Vec<&str> = rcpt_text.lines().collect();
        assert_eq!(lines.len(), 4, "3 module rows + 1 summary row");
        for line in &lines {
            assert_eq!(
                extract_json_str(line, "policy"),
                Some(policy),
                "every receipt row must preserve policy: {line}"
            );
            assert!(
                line.contains(&format!("\"attestable\":{expected_attestable}")),
                "every receipt row must preserve attestable: {line}"
            );
        }
        if policy == "compat-bench" {
            assert!(stdout.contains("\"authority\":false"), "{stdout}");
        }
        if policy == "standard" {
            assert!(
                rcpt_text.contains("\"policy-skipped\":"),
                "standard receipts must honestly label skipped declarations: {rcpt_text}"
            );
        }
    }
    let rel_chain = std::fs::read_to_string(&rcpt_rel).unwrap();
    let std_chain = std::fs::read_to_string(&rcpt_std).unwrap();
    let cb_chain = std::fs::read_to_string(&rcpt_cb).unwrap();
    assert_ne!(
        extract_json_str(rel_chain.lines().last().unwrap(), "chain"),
        extract_json_str(std_chain.lines().last().unwrap(), "chain"),
        "release and standard receipt chains must be cryptographically distinct"
    );
    assert_ne!(
        extract_json_str(std_chain.lines().last().unwrap(), "chain"),
        extract_json_str(cb_chain.lines().last().unwrap(), "chain"),
        "standard and compat-bench receipt chains must be cryptographically distinct"
    );

    // 3. Frontier (--continue --json --jobs 1 vs --jobs 4): schedule-independent selectionDigest.
    let (code_j1, out_j1, err_j1) = run_fln(&[
        "check-olean",
        "--continue",
        "--json",
        "--jobs",
        "1",
        "--policy",
        "standard",
        set_str,
    ]);
    assert_eq!(code_j1, Some(0), "{err_j1}");
    let (code_j4, out_j4, err_j4) = run_fln(&[
        "check-olean",
        "--continue",
        "--json",
        "--jobs",
        "4",
        "--policy",
        "standard",
        set_str,
    ]);
    assert_eq!(code_j4, Some(0), "{err_j4}");
    assert_eq!(
        extract_json_str(&out_j1, "selectionDigest"),
        extract_json_str(&out_j4, "selectionDigest"),
        "standard frontier selectionDigest must be identical across --jobs 1 and --jobs 4"
    );
    assert_eq!(
        extract_json_u64(&out_j1, "checkerSelected"),
        extract_json_u64(&out_j4, "checkerSelected")
    );
    assert_eq!(
        extract_json_u64(&out_j1, "skipped"),
        extract_json_u64(&out_j4, "skipped")
    );

    // Frontier with --policy paranoid -> exit 3 (inconclusive rows, never accepted).
    let (code_fpar, out_fpar, err_fpar) = run_fln(&[
        "check-olean",
        "--continue",
        "--json",
        "--policy",
        "paranoid",
        set_str,
    ]);
    assert_eq!(
        code_fpar,
        Some(1),
        "blocked dependents after inconclusive Base exit 1: {out_fpar} {err_fpar}"
    );
    assert!(out_fpar.contains("\"accepted\":0"), "{out_fpar}");
    assert!(out_fpar.contains("\"inconclusive\":1"), "{out_fpar}");
    assert_eq!(extract_json_str(&out_fpar, "policy"), Some("paranoid"));
}
