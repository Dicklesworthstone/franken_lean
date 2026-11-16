#![forbid(unsafe_code)]
//! `fln check-olean --continue --progress` killed while a module is still in the
//! council keeps every row that already exists (bead
//! `fln-frontier-oom-abort-w9dx`, "survive a crash").
//!
//! The `decided` lines leave in frontier order, so a row decided early waits
//! behind any slower module before it, and a crash in that window used to lose
//! it. The `settled` line is written the moment the row exists. The run here holds
//! the pinned `Init.Prelude` (seconds in the council) at position 1 and a module
//! whose artifact cannot decode, which is decided at once, at position 2. The
//! process is killed as soon as that module's `settled` line arrives, before any
//! `decided` line can: the verdict must already be on the stream.
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn copy_module(lib: &Path, module: &str, to: &Path, as_module: &str, corrupt: bool) {
    let from = lib.join(module.replace('.', "/"));
    let target = to.join(as_module.replace('.', "/"));
    std::fs::create_dir_all(target.parent().expect("a module path has a parent"))
        .expect("create the fixture's module directory");
    for extension in ["olean", "olean.server", "olean.private"] {
        let mut bytes = std::fs::read(from.with_extension(extension))
            .unwrap_or_else(|error| panic!("read {module}.{extension}: {error}"));
        if corrupt && extension == "olean" {
            // The header stays valid; the object region does not decode.
            let middle = bytes.len() / 2;
            bytes[middle] ^= 0xFF;
            bytes[middle + 1] ^= 0xFF;
        }
        std::fs::write(target.with_extension(extension), bytes)
            .unwrap_or_else(|error| panic!("write {as_module}.{extension}: {error}"));
    }
}

#[test]
fn a_run_killed_with_a_module_in_the_council_keeps_every_settled_row() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("check_olean_progress_crash");
    copy_module(&lib, "Init.Prelude", &dir, "Init.Prelude", false);
    copy_module(&lib, "Init.Coe", &dir, "Zzz.Corrupt", true);

    let mut child = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-olean", "--continue", "--progress", "--jobs", "2"])
        .arg(&dir)
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn fln check-olean");
    let stderr = BufReader::new(child.stderr.take().expect("piped stderr"));
    let mut seen: Vec<String> = Vec::new();
    let mut killed = false;
    let settled_corrupt =
        |line: &String| line.contains("\"event\":\"settled\"") && line.contains("Zzz.Corrupt");
    let prelude_started = |line: &String| {
        line.contains("\"event\":\"started\"")
            && line.contains("\"position\":1,")
            && line.contains("Init.Prelude")
    };
    for line in stderr.lines() {
        seen.push(line.expect("a progress line"));
        // Kill once the corrupt row has settled and Init.Prelude is in the council.
        if seen.iter().any(settled_corrupt) && seen.iter().any(prelude_started) {
            child
                .kill()
                .expect("kill the run with Init.Prelude in the council");
            killed = true;
            break;
        }
    }
    let status = child.wait().expect("reap the killed run");
    assert!(
        killed,
        "the run ended before the corrupt row settled with Init.Prelude in the council: {seen:#?}"
    );
    assert!(
        !status.success(),
        "the run was killed, not finished: {status:?}"
    );
    // Init.Prelude, at position 1, was still in the council, so no `decided`
    // line could have carried the corrupt module's verdict yet.
    assert!(
        !seen
            .iter()
            .any(|line| line.contains("\"event\":\"decided\"")),
        "nothing was decided before the kill: {seen:#?}"
    );
    let settled = seen
        .iter()
        .find(|line| settled_corrupt(line))
        .expect("the corrupt row settled");
    assert!(
        settled.starts_with("{\"schema\":\"fln.check-olean-frontier-progress/2\",\"event\":\"settled\",\"position\":2,\"total\":2,"),
        "the corrupt module settles at its frontier position: {settled}"
    );
    assert!(
        settled.contains("\"verdict\":\"failed\""),
        "the settled row carries the module's verdict: {settled}"
    );
}

/// Installed-binary e2e for `fln-frontier-rows-depend-on-jobs-2g96`:
/// `fln check-olean --continue --jobs 8` under a tight `prlimit --as` (`ulimit -v`)
/// over a 4-module fixture where `Fix.HeavyA` and `Fix.HeavyB` have tiny `.olean`
/// files (~1 KiB, so admission control dispatches them together) and transiently
/// materialize ~256 MiB of `BigNat` shift buffers during council checking so both
/// cannot fit in virtual address space concurrently, while each fits solo.
#[test]
fn check_olean_continue_jobs_eight_under_small_ulimit_v_retries_solo_and_attributes_peaks() {
    use fln::{
        ConstantInfo, ConstantVal, Expr, Literal, Name, NatLit, OLEAN_ACCEPTED_VERSIONS,
        OLEAN_PIN_COMMIT, OLEAN_PIN_TAG, OLEAN_REGION_ALIGN, OleanModuleImport,
        OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader, TheoremVal,
    };
    use fln_olean::encode_module_with_extensions;

    let n = |s: &str| Name::from_components(s.split('.'));
    let c = |s: &str| Expr::const_(n(s), Vec::new());
    let nat_lit = |v: u64| Expr::lit(Literal::Nat(NatLit::from_u64(v)));

    let base_dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("check_olean_2g96_ulimit");
    let pkg_dir = base_dir.join("pkg");
    let fix_src = pkg_dir.join("Fix");
    std::fs::create_dir_all(&fix_src).expect("create package source dir");
    std::fs::write(
        pkg_dir.join("lakefile.toml"),
        "name = \"fix\"\n[[lean_lib]]\nname = \"Fix\"\n",
    )
    .expect("write lakefile.toml");
    std::fs::write(
        fix_src.join("Root.lean"),
        "\
prelude
inductive Bool where
  | false : Bool
  | true : Bool
inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
def Nat.add : Nat -> Nat -> Nat
  | a, Nat.zero => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
def Nat.shiftLeft : Nat -> Nat -> Nat
  | a, Nat.zero => a
  | a, Nat.succ b => Nat.shiftLeft (Nat.add a a) b
def Nat.beq : Nat -> Nat -> Bool
  | Nat.zero, Nat.zero => Bool.true
  | Nat.succ a, Nat.succ b => Nat.beq a b
  | _, _ => Bool.false
inductive EqB (a : Bool) : Bool -> Prop where
  | refl : EqB a a
",
    )
    .expect("write Fix/Root.lean");
    std::fs::write(
        fix_src.join("Light.lean"),
        "prelude\nimport Fix.Root\ntheorem light_ok : EqB Bool.true Bool.true := EqB.refl\n",
    )
    .expect("write Fix/Light.lean");

    let build = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["build", "+Fix.Light:olean"])
        .current_dir(&pkg_dir)
        .output()
        .expect("build Fix.Root and Fix.Light with lake");
    assert!(
        build.status.success(),
        "lake build failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );

    // 128 MiB per BigNat operand (2^30 bits = 16,777,216 u64 limbs = 128 MiB).
    // Two operands in `Nat.beq` allocate >= 256 MiB transiently per theorem check;
    // repeating across 4 theorems keeps the module in check long enough for the
    // two `--jobs 8` workers to overlap deterministically while dropping each
    // theorem's arena before the next theorem starts.
    const SHIFT_BITS: u64 = 1 << 30;
    let encode_heavy_module = |mod_stem: &str| -> Vec<u8> {
        let constants: Vec<ConstantInfo> = (0..4)
            .map(|idx| {
                let thm_name = format!("Fix.{mod_stem}.t{idx}");
                let shift_a = Expr::app(
                    Expr::app(c("Nat.shiftLeft"), nat_lit(1)),
                    nat_lit(SHIFT_BITS),
                );
                let shift_b = Expr::app(
                    Expr::app(c("Nat.shiftLeft"), nat_lit(2)),
                    nat_lit(SHIFT_BITS - 1),
                );
                let eq_lhs = Expr::app(Expr::app(c("Nat.beq"), shift_a), shift_b);
                let ty = Expr::app(Expr::app(c("EqB"), eq_lhs), c("Bool.true"));
                let val = Expr::app(c("EqB.refl"), c("Bool.true"));
                ConstantInfo::Thm(TheoremVal {
                    base: ConstantVal {
                        name: n(&thm_name),
                        level_params: Vec::new(),
                        type_: ty,
                    },
                    value: val,
                    all: vec![n(&thm_name)],
                })
            })
            .collect();
        let imports = [OleanModuleImport {
            module: n("Fix.Root"),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }];
        encode_module_with_extensions(
            OleanModuleWriteInput {
                is_module: false,
                imports: &imports,
                constants: &constants,
                extra_const_names: &[],
            },
            &[],
            OleanWriteHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: OLEAN_PIN_TAG.strip_prefix('v').expect("v tag"),
                githash: OLEAN_PIN_COMMIT,
                base_addr: 2 * OLEAN_REGION_ALIGN as u64,
            },
            OleanWriteBudget::default(),
        )
        .expect("encode heavy .olean")
        .bytes
    };

    let built_fix = pkg_dir.join(".lake/build/lib/lean/Fix");
    let one_heavy_dir = base_dir.join("one_heavy");
    let two_heavy_dir = base_dir.join("two_heavy");
    for target_root in [&one_heavy_dir, &two_heavy_dir] {
        std::fs::create_dir_all(target_root.join("Fix")).expect("create fixture Fix dir");
        for stem in ["Root", "Light"] {
            for ext in ["olean", "olean.server", "olean.private"] {
                let src = built_fix.join(format!("{stem}.{ext}"));
                if src.is_file() {
                    std::fs::copy(&src, target_root.join("Fix").join(format!("{stem}.{ext}")))
                        .expect("copy base olean");
                }
            }
        }
    }
    let heavy_a = encode_heavy_module("HeavyA");
    let heavy_b = encode_heavy_module("HeavyB");
    assert!(
        heavy_a.len() < 8192 && heavy_b.len() < 8192,
        "encoded heavy modules stay tiny so closure estimate admits them concurrently"
    );
    std::fs::write(one_heavy_dir.join("Fix/HeavyA.olean"), &heavy_a).expect("write one HeavyA");
    std::fs::write(two_heavy_dir.join("Fix/HeavyA.olean"), &heavy_a).expect("write two HeavyA");
    std::fs::write(two_heavy_dir.join("Fix/HeavyB.olean"), &heavy_b).expect("write two HeavyB");

    // Calibrate the host's `--jobs 8` address-space baseline + 1 heavy module so
    // the test adapts across debug/release binaries and libc mappings while staying
    // strictly too tight for 2 concurrent heavy modules (+ >= 256 MiB extra).
    let fln_bin = env!("CARGO_BIN_EXE_fln");
    let mut calibrated_limit_bytes = None;
    for candidate_mib in [950_u64, 1050, 1150, 1250, 1350, 1450, 1600, 1750, 1900] {
        let as_bytes = candidate_mib << 20;
        let probe = Command::new("prlimit")
            .arg(format!("--as={as_bytes}"))
            .arg("--")
            .arg(fln_bin)
            .args(["check-olean", "--continue", "--jobs", "8"])
            .arg(&one_heavy_dir)
            .env("MALLOC_ARENA_MAX", "1")
            .output()
            .expect("run calibration probe under prlimit");
        if probe.status.success() {
            calibrated_limit_bytes = Some(as_bytes + (64 << 20));
            break;
        }
    }
    let limit_bytes = calibrated_limit_bytes.expect("one heavy module fits under <= 1900 MiB");

    let human = Command::new("prlimit")
        .arg(format!("--as={limit_bytes}"))
        .arg("--")
        .arg(fln_bin)
        .args(["check-olean", "--continue", "--jobs", "8"])
        .arg(&two_heavy_dir)
        .env("MALLOC_ARENA_MAX", "1")
        .output()
        .expect("run two-heavy check-olean under prlimit");
    let human_stdout = String::from_utf8_lossy(&human.stdout);
    let human_stderr = String::from_utf8_lossy(&human.stderr);
    assert!(
        human.status.success(),
        "solo retry must recover concurrent host-memory refusal under as={limit_bytes}:\nstdout:\n{human_stdout}\nstderr:\n{human_stderr}"
    );
    assert!(
        human_stdout.contains("council modules: 4/4 accepted"),
        "row conservation must hold across solo retries:\n{human_stdout}"
    );
    assert!(
        human_stdout.contains("attempt=2")
            && human_stdout.contains("isolated retry after host-memory refusal"),
        "human log must record attempt=2 and isolated retry:\n{human_stdout}\nstderr:\n{human_stderr}"
    );
    for expected_token in [
        "accepted      Fix.Root:",
        "accepted      Fix.HeavyA:",
        "accepted      Fix.HeavyB:",
        "accepted      Fix.Light:",
        "wall=",
        "estimate=",
        "peak=",
        "k1Delta=",
        "checker=",
        "decodedOlean=",
        "admittedEntries=",
        "top memory rows (up to 20 by peak bytes):",
    ] {
        assert!(
            human_stdout.contains(expected_token),
            "missing {expected_token:?} in human output:\n{human_stdout}"
        );
    }

    let json = Command::new("prlimit")
        .arg(format!("--as={limit_bytes}"))
        .arg("--")
        .arg(fln_bin)
        .args(["check-olean", "--continue", "--jobs", "8", "--json"])
        .arg(&two_heavy_dir)
        .env("MALLOC_ARENA_MAX", "1")
        .output()
        .expect("run two-heavy --json check-olean under prlimit");
    let json_stdout = String::from_utf8_lossy(&json.stdout);
    let json_stderr = String::from_utf8_lossy(&json.stderr);
    assert!(
        json.status.success(),
        "json run failed:\nstdout:\n{json_stdout}\nstderr:\n{json_stderr}"
    );
    assert!(
        json_stdout.contains("\"modules\":4,\"accepted\":4,\"failed\":0,\"inconclusive\":0")
            && json_stdout.contains("\"attempt\":2")
            && json_stdout.contains(
                "\"attempts\":[{\"attempt\":1,\"isolated\":false,\"verdict\":\"inconclusive\""
            )
            && json_stdout.contains("\"topMemoryRows\":["),
        "json receipt missing retry or topMemoryRows attribution:\n{json_stdout}"
    );
}
