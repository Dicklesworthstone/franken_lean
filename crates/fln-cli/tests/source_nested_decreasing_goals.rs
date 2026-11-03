//! A nested recursive call (`ack x (ack (x+1) y)`) is its own decreasing goal, and its proof is an
//! argument in the outer call's goal: at the pin that argument is the nested goal's metavariable
//! (`mkDecreasingProof`, vendored `Lean/Elab/PreDefinition/WF/Fix.lean`), so a proof script that
//! proves the nested call first works on the outer goal with that proof in place, not over an open
//! hole. Through `fln check-source` over `prelude`, `Init.WFTactics` and `Init.Omega`. Every
//! program is compared with the pinned `lean` v4.32.0 whenever it is present. The same reduced
//! imports must also suffice to compile and execute the checked definitions: executable
//! recursion must not depend on importing the `Init.WFComputable` simplification lemmas.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.WFTactics\nimport Init.Omega\n";

const ACKERMANN: &str = "def ack : Nat → Nat → Nat\n  | 0,   y   => y+1\n  | x+1, 0   => ack x 1\n  \
     | x+1, y+1 => ack x (ack (x+1) y)\n";

/// Added after `ACKERMANN`: real termination proofs, nested recursive calls, fixed arguments,
/// universe-polymorphic captures, a dependent result, closures, and singleton/mutual captures.
const EXECUTABLE_SUFFIX: &str = r#"termination_by x y => (x, y)
decreasing_by all_goals decreasing_tactic

def down (n : Nat) : Nat :=
  if h : n = 0 then 0 else down (n - 1) + 1
termination_by n
decreasing_by omega

def tally (offset n : Nat) : Nat :=
  if h : n = 0 then offset else tally offset (n - 1) + 2
termination_by n
decreasing_by omega

universe u
def keep {α : Type u} (a : α) (n : Nat) : α :=
  if h : n = 0 then a else keep a (n - 1)
termination_by n
decreasing_by omega

def dependentResult (n : Nat) (p : Fin (Nat.succ n)) : Fin (Nat.succ n) := match n with
  | 0 => p
  | k + 1 =>
    let r := dependentResult k (Fin.mk 0 (Nat.succ_pos k))
    Fin.mk (Nat.succ r.val) (Nat.succ_lt_succ r.isLt)
termination_by n
decreasing_by exact Nat.lt_succ_self k

section
variable (unused : String) (offset : Nat)
def capturedSingleton (n : Nat) : Nat :=
  if h : n = 0 then offset else capturedSingleton (n - 1) + 2
termination_by n + offset
decreasing_by omega

mutual
def wfCapturedLeft (n : Nat) : Nat :=
  if h : n = 0 then wfCapturedHelper 0 else wfCapturedRight (n - 1) + 1
termination_by n + offset
decreasing_by omega
def wfCapturedRight (n : Nat) : Nat :=
  if h : n = 0 then wfCapturedHelper 1 else wfCapturedLeft (n - 1) + 2
termination_by n + offset
decreasing_by omega
def wfCapturedHelper (n : Nat) : Nat := offset + n
end
end

def applyRepeated (step : Nat → Nat) (n value : Nat) : Nat :=
  if h : n = 0 then value else applyRepeated step (n - 1) (step value)
termination_by n
decreasing_by omega

def functionResult (n : Nat) : Nat → Nat :=
  if h : n = 0 then (fun x => x + 1)
  else (fun x => functionResult (n - 1) (x + 2))
termination_by n
decreasing_by omega

#eval down 6
#eval ack 0 4
#eval ack 2 2
#eval tally 7 5
#eval let counted := tally 11; counted 3
#eval keep 23 4
#eval keep true 5
#eval (dependentResult 6 (Fin.mk 0 (Nat.succ_pos 6))).val
#eval wfCapturedLeft 7 2
#eval wfCapturedRight 7 2
#eval capturedSingleton 7 5
#eval applyRepeated (fun x => x + 3) 4 2
#eval functionResult 3 5
#eval ack 3 2
"#;

const EXECUTABLE_OUTPUT: &[u8] = b"6\n5\n7\n17\n17\n23\ntrue\n6\n10\n11\n17\n14\n12\n29\n";

const NONCOMPUTABLE_DEPENDENCY: &str = r#"noncomputable def hidden : Nat := 7
def rejected (n : Nat) : Nat :=
  if h : n = 0 then hidden else rejected (n - 1) + 1
termination_by n
decreasing_by omega
"#;

/// Accepted at the pin and here: `ACKERMANN` followed by each suffix.
const ACCEPTED: &[(&str, &str)] = &[
    ("inferred_measure", ""),
    ("default_tactic", "termination_by x y => (x, y)\n"),
    (
        "tactic_per_goal",
        "termination_by x y => (x, y)\ndecreasing_by\n  · decreasing_tactic\n  \
         · decreasing_tactic\n  · decreasing_tactic\n",
    ),
    (
        "tactic_on_all_goals",
        "termination_by x y => (x, y)\ndecreasing_by\n  all_goals decreasing_tactic\n",
    ),
    (
        "simp_on_each_goal",
        "termination_by x y => (x, y)\ndecreasing_by\n  · (try simp)\n    sorry\n  \
         · (try simp)\n    sorry\n  · (try simp)\n    sorry\n",
    ),
];

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Omega.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-nested-decreasing-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn reference_lean(lib: &Path) -> Option<PathBuf> {
    let lean = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    assert!(
        lean.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference binary is required"
    );
    lean
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let theirs = reference_lean(lib).map(|pinned| {
        Command::new(pinned)
            .arg("-j1")
            .arg(&entry)
            .env("LEAN_PATH", lib)
            .output()
            .expect("run the pinned lean")
            .status
            .code()
            .expect("normal pinned exit")
    });
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

fn execute(binary: &Path, lib: &Path, root: &Path, entry: &Path, native: bool) -> Output {
    let mut command = Command::new(binary);
    if native {
        command.env("FLN_IMPORT_REUSE_DIR", root.join("records"));
    } else {
        command.arg("-j1");
    }
    command
        .arg(entry)
        .env("LEAN_PATH", lib)
        .output()
        .expect("execute the compiler process")
}

fn assert_success(label: &str, output: &Output) {
    assert!(
        output.status.success(),
        "{label}: stdout={} stderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_execution(label: &str, output: &Output) {
    assert_success(label, output);
    assert!(
        output.stderr.is_empty(),
        "{label}: unexpected stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.stdout, EXECUTABLE_OUTPUT,
        "{label}: recursive results"
    );
}

fn execute_and_replay(lib: &Path, root: &Path, entry: &Path) {
    let artifact = root.join("Ackermann.flbc");
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("execute the source and emit its final bytecode");
    assert_success("native reduced imports", &output);
    let report = String::from_utf8(output.stdout).unwrap();
    // Check every evaluation in source order, including its raw result type. The source runner
    // emits these fields together before the per-evaluation usage counters.
    let actual: Vec<_> = report
        .split("\"event\":\"evaluation\",")
        .skip(1)
        .map(|row| {
            row.split_once(",\"steps\":")
                .expect("evaluation row with usage counters")
                .0
                .to_owned()
        })
        .collect();
    let expected: Vec<_> = std::str::from_utf8(EXECUTABLE_OUTPUT)
        .unwrap()
        .lines()
        .map(|value| {
            let kind = if matches!(value, "true" | "false") {
                "bool"
            } else {
                "nat"
            };
            format!("\"kind\":\"{kind}\",\"value\":{value}")
        })
        .collect();
    assert_eq!(actual, expected, "ordered recursive results: {report}");
    assert!(report.contains("\"emittedFlbc\":{\"path\":"), "{report}");
    assert!(std::fs::metadata(&artifact).unwrap().len() > 0);

    // Replay the final nested Ackermann call from the self-contained artifact. No source or
    // imported environment is supplied to this independent process.
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .env_remove("LEAN_PATH")
        .env_remove("FLN_IMPORT_REUSE_DIR")
        .output()
        .expect("replay the emitted recursive bytecode");
    assert_success("standalone Ackermann replay", &replay);
    let replay = String::from_utf8(replay.stdout).unwrap();
    assert!(replay.contains("\"returnValue\":29,"), "{replay}");
}

fn assert_noncomputable_dependency(label: &str, output: &Output) {
    let diagnostic = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        output.status.code(),
        Some(1),
        "{label}: must reject normally, without a resource stop or crash: {diagnostic}"
    );
    assert!(
        diagnostic.contains("failed to compile definition")
            && diagnostic.contains("noncomputable")
            && diagnostic.contains("hidden"),
        "{label}: rejected for the wrong reason: {diagnostic}"
    );
}

#[test]
fn checked_well_founded_recursion_executes_without_wfcomputable() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let pinned = reference_lean(&lib);
    let native = Path::new(env!("CARGO_BIN_EXE_lean"));
    for (name, extra_import) in [
        ("ReducedImports", ""),
        ("ExplicitWFComputable", "import Init.WFComputable\n"),
    ] {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(
            &entry,
            format!("{HEADER}{extra_import}{ACKERMANN}{EXECUTABLE_SUFFIX}"),
        )
        .unwrap();
        if let Some(pinned) = &pinned {
            let output = execute(pinned, &lib, &root, &entry, false);
            assert_execution(&format!("Reference {name}"), &output);
        }
        if extra_import.is_empty() {
            execute_and_replay(&lib, &root, &entry);
        } else {
            let output = execute(native, &lib, &root, &entry, true);
            assert_execution(&format!("native {name}"), &output);
        }
    }

    // The executable companion must retain live noncomputable dependencies, even though its
    // termination proofs and the logical WellFounded.fix implementation are erased at runtime.
    let entry = root.join("LiveNoncomputableDependency.lean");
    std::fs::write(&entry, format!("{HEADER}{NONCOMPUTABLE_DEPENDENCY}")).unwrap();
    if let Some(pinned) = &pinned {
        let output = execute(pinned, &lib, &root, &entry, false);
        assert_noncomputable_dependency("Reference", &output);
    }
    let output = execute(native, &lib, &root, &entry, true);
    assert_noncomputable_dependency("native", &output);
}

#[test]
fn a_nested_call_proof_is_its_own_goal_in_the_outer_goal() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = workspace();
    for (name, suffix) in ACCEPTED {
        let program = format!("{ACKERMANN}{suffix}");
        let (code, stderr, pinned) = check(&lib, &root, name, &program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
}
