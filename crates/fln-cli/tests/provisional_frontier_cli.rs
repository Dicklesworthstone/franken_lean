//! Installed-binary end-to-end tests for `fln check-olean --continue --provisional`
//! (bead `fln-provisional-frontier-vf32`).
//!
//! Exercises the real `fln` executable over pinned-format `.olean` module sets
//! emitted by `fln::encode_olean_module`, logging one structured line per row
//! (phase, verdict, assumes, declaration counts, K1 steps, wall ms) plus summary
//! totals and exit codes.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use fln::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, Level,
    Name, OleanModuleImport, OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader,
    ReducibilityHints, encode_olean_module,
};

fn fln_bin() -> &'static str {
    env!("CARGO_BIN_EXE_fln")
}

fn temp_dir(label: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "fln-provisional-e2e-{label}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir_all(&dir).expect("create temp fixture dir");
    dir
}

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn axiom(name: &str, ty: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_: ty,
        },
        is_unsafe: false,
    })
}

fn safe_def(name: &str, ty: Expr, value: Expr) -> ConstantInfo {
    let decl_name = n(name);
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: decl_name.clone(),
            level_params: Vec::new(),
            type_: ty,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![decl_name],
    })
}

fn beta_chain(prop_name: &str, witness_name: &str, depth: usize) -> Expr {
    let prop = Expr::const_(n(prop_name), Vec::new());
    let mut expr = Expr::const_(n(witness_name), Vec::new());
    for _ in 0..depth {
        let id = Expr::lam(
            Name::str(Name::anonymous(), "x"),
            prop.clone(),
            Expr::bvar(0).expect("bvar 0"),
            BinderInfo::Default,
        );
        expr = Expr::app(id, expr);
    }
    expr
}

fn write_olean(root: &Path, module: &str, imports: &[&str], constants: &[ConstantInfo]) {
    let imports: Vec<OleanModuleImport> = imports
        .iter()
        .map(|dep| OleanModuleImport {
            module: n(dep),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let bytes = encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: fln::OLEAN_REGION_ALIGN as u64,
        },
        OleanWriteBudget::default(),
    )
    .expect("encode pinned-format olean")
    .bytes;
    let mut path = root.to_path_buf();
    for component in module.split('.') {
        path.push(component);
    }
    path.set_extension("olean");
    std::fs::create_dir_all(path.parent().expect("parent")).expect("mkdirs");
    std::fs::write(&path, bytes).expect("write olean");
}

fn strip_elapsed(json: &str) -> String {
    // Strip volatile `elapsedMs` integers for schedule-independence comparison across --jobs.
    let mut out = String::with_capacity(json.len());
    let mut rest = json;
    while let Some(pos) = rest.find("\"elapsedMs\":") {
        out.push_str(&rest[..pos + "\"elapsedMs\":".len()]);
        let after = &rest[pos + "\"elapsedMs\":".len()..];
        let digits = after.bytes().take_while(u8::is_ascii_digit).count();
        out.push('0');
        rest = &after[digits..];
    }
    out.push_str(rest);
    out
}

#[test]
fn cli_provisional_chain_failed_control_and_schedule_independence() {
    let dir = temp_dir("chain");
    let p_ty = Expr::const_(n("A.P"), Vec::new());
    write_olean(
        &dir,
        "A",
        &[],
        &[
            axiom("A.P", Expr::sort(Level::zero())),
            axiom("A.p", p_ty.clone()),
        ],
    );
    write_olean(
        &dir,
        "B",
        &["A"],
        &[
            safe_def("B.ok1", p_ty.clone(), Expr::const_(n("A.p"), Vec::new())),
            safe_def("B.heavy", p_ty.clone(), beta_chain("A.P", "A.p", 80)),
            safe_def("B.ok2", p_ty.clone(), Expr::const_(n("B.ok1"), Vec::new())),
        ],
    );
    write_olean(
        &dir,
        "C",
        &["B"],
        &[safe_def(
            "C.useB",
            p_ty.clone(),
            Expr::const_(n("B.heavy"), Vec::new()),
        )],
    );
    write_olean(
        &dir,
        "D",
        &["C"],
        &[safe_def(
            "D.useC",
            p_ty.clone(),
            Expr::const_(n("C.useB"), Vec::new()),
        )],
    );

    // 1. Without --provisional: B inconclusive, C and D blocked; schema unchanged.
    let plain = Command::new(fln_bin())
        .args(["check-olean", "--continue", "--json", "--max-steps", "120"])
        .arg(&dir)
        .output()
        .expect("run fln check-olean --continue");
    let plain_stdout = String::from_utf8_lossy(&plain.stdout);
    assert_eq!(
        plain.status.code(),
        Some(1),
        "blocked rows yield exit 1: {plain_stdout}"
    );
    assert!(plain_stdout.contains("\"accepted\":1"));
    assert!(plain_stdout.contains("\"inconclusive\":1"));
    assert!(plain_stdout.contains("\"blocked\":2"));
    assert!(!plain_stdout.contains("\"provisional\":true"));
    assert!(!plain_stdout.contains("\"acceptedUnderAssumptions\""));

    // 2. With --provisional at --jobs 1, 8, 32: identical rows (modulo elapsedMs).
    let mut normalized = Vec::new();
    for jobs in ["1", "8", "32"] {
        let out = Command::new(fln_bin())
            .args([
                "check-olean",
                "--continue",
                "--provisional",
                "--json",
                "--max-steps",
                "120",
                "--jobs",
                jobs,
            ])
            .arg(&dir)
            .output()
            .expect("run fln check-olean --continue --provisional");
        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
        let code = out.status.code().unwrap_or(255);
        assert_eq!(code, 3, "jobs={jobs} exit_code must be 3: {stdout}");
        assert!(
            stdout.contains("\"provisional\":true"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"authority\":false"),
            "jobs={jobs}: {stdout}"
        );
        assert!(stdout.contains("\"accepted\":1"), "jobs={jobs}: {stdout}");
        assert!(
            stdout.contains("\"acceptedUnderAssumptions\":2"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"inconclusive\":1"),
            "jobs={jobs}: {stdout}"
        );
        assert!(stdout.contains("\"blocked\":0"), "jobs={jobs}: {stdout}");
        assert!(
            stdout.contains("\"eligibleBlocked\":2"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"ineligibleBlocked\":0"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"assumes\":[\"B\"]"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"assumedDeclarations\":1"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"assumedDeclarationNames\":[\"B.heavy\"]"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"unlockValue\":2"),
            "jobs={jobs}: {stdout}"
        );
        assert!(
            stdout.contains("\"firstBlockerCount\":2"),
            "jobs={jobs}: {stdout}"
        );
        eprintln!("[e2e chain jobs={jobs}] exit={code} json={}", stdout.trim());
        normalized.push(strip_elapsed(&stdout));
    }
    assert_eq!(
        normalized[0], normalized[1],
        "--jobs 1 vs --jobs 8 mismatch"
    );
    assert_eq!(
        normalized[0], normalized[2],
        "--jobs 1 vs --jobs 32 mismatch"
    );

    // Human-readable log check: logs phase, verdict, assumes, decl counts, k1_steps, ms.
    let human = Command::new(fln_bin())
        .args([
            "check-olean",
            "--continue",
            "--provisional",
            "--max-steps",
            "120",
        ])
        .arg(&dir)
        .output()
        .expect("run human provisional");
    let human_stdout = String::from_utf8_lossy(&human.stdout);
    assert_eq!(human.status.code(), Some(3));
    assert!(
        human_stdout.contains("2 of 3 declarations accepted, 1 assumed [B.heavy]"),
        "{human_stdout}"
    );
    assert!(
        human_stdout.contains("accepted-under-assumptions C:"),
        "{human_stdout}"
    );
    assert!(human_stdout.contains("assumes=[B]"), "{human_stdout}");
    assert!(human_stdout.contains("k1_steps"), "{human_stdout}");
    assert!(human_stdout.contains("unlockValue=2"), "{human_stdout}");
    eprintln!("[e2e human]\n{human_stdout}");

    // 3. Failed-root control: B is failed -> C stays blocked in BOTH modes!
    let fail_dir = temp_dir("failed");
    write_olean(
        &fail_dir,
        "A",
        &[],
        &[axiom("A.P", Expr::sort(Level::zero()))],
    );
    write_olean(
        &fail_dir,
        "B",
        &["A"],
        &[safe_def("B.bad", p_ty.clone(), Expr::sort(Level::one()))],
    );
    write_olean(
        &fail_dir,
        "C",
        &["B"],
        &[safe_def(
            "C.useB",
            p_ty,
            Expr::const_(n("B.bad"), Vec::new()),
        )],
    );
    for extra in [&[][..], &["--provisional"][..]] {
        let mut cmd = Command::new(fln_bin());
        cmd.args(["check-olean", "--continue", "--json"])
            .args(extra)
            .arg(&fail_dir);
        let out = cmd.output().expect("run failed control");
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert_eq!(out.status.code(), Some(1), "{extra:?}: {stdout}");
        assert!(stdout.contains("\"accepted\":1"), "{extra:?}: {stdout}");
        assert!(stdout.contains("\"failed\":1"), "{extra:?}: {stdout}");
        assert!(stdout.contains("\"blocked\":1"), "{extra:?}: {stdout}");
        assert!(
            !stdout.contains("accepted-under-assumptions"),
            "{extra:?}: {stdout}"
        );
    }

    // 4. Usage error: --provisional without --continue must exit 2.
    let bad_usage = Command::new(fln_bin())
        .args(["check-olean", "--provisional"])
        .arg(&dir)
        .output()
        .expect("run bad usage");
    assert_eq!(bad_usage.status.code(), Some(2));

    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&fail_dir);
}
