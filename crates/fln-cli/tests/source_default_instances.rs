//! Default instances, checked over the pinned `Init.Core` closure. The pin's
//! `tryToSynthesizeUsingDefaultInstance` (Lean/Elab/SyntheticMVars.lean) assigns a goal to its
//! default instance applied to fresh holes. It registers the instance arguments as new goals, for
//! later synthesis or another default to solve. Synthesis then resumes over everything the
//! assignment decided. So `v + k`, over the pattern variables of a `match` on a numeral, is
//! `instHAdd` with `Add ?α` open until `instOfNatNat` fixes `?α`. Every program here was run
//! through the pinned `lean` v4.32.0 with the same header first (2026-10-11), with the same
//! verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

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
        .filter(|lib| lib.join("Init/Core.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace(case: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-default-instances-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `HEADER` + `program`: (exit code, stdout, stderr).
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn default_instances_leave_their_arguments_to_later_synthesis() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "match_numeral_pair",
            "def sacha : Nat :=\n  let (v, k) := match 0 with\n    | (n) => (0, 0)\n  v + k\n",
        ),
        ("sum", "def a := 2 + 3\ntheorem t : a = 5 := rfl\n"),
        ("lambda", "example : (fun x => x + 1) 2 = 3 := rfl\n"),
        ("pair", "def b := (1, 2)\ntheorem t : b.2 = 2 := rfl\n"),
        ("product", "example : 2 * 3 = 6 := rfl\n"),
        (
            "let",
            "def d := let x := 1; x + x\ntheorem t : d = 2 := rfl\n",
        ),
        ("truncated", "theorem t : 1 - 2 = 0 := rfl\n"),
        (
            "match_literal",
            "def m := match 3 with\n  | 0 => 1\n  | _ => 2\ntheorem t : m = 2 := rfl\n",
        ),
        ("condition", "def i := if 1 = 1 then 2 else 3\n"),
        // `Pow` has two defaults; the pin tries the last added first, `instPowNat` before
        // `Pow α α`, so the exponent is a `Nat`.
        ("power", "theorem t : 2 ^ 10 = 1024 := rfl\n"),
        ("power_mod", "theorem t : (2 ^ 64 + 1) % 7 = 3 := rfl\n"),
        ("power_def", "def p := 2 ^ 5\ntheorem t : p = 32 := rfl\n"),
        (
            "power_var",
            "def f (n : Nat) := 2 ^ n\ntheorem t : f 3 = 8 := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn default_instance_refusals_match_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "string",
            "def a : String := 2 + 3\n",
            "failed to synthesize instance of type class",
        ),
        ("wrong_sum", "example : 2 + 3 = 6 := rfl\n", "Type mismatch"),
        (
            "mixed",
            "def h := 1 + \"a\"\n",
            "failed to synthesize instance of type class",
        ),
        (
            "negation",
            "example : 2 - 3 = -1 := rfl\n",
            "failed to synthesize instance of type class",
        ),
        (
            "match_numeral_wrong",
            "def sacha : Nat :=\n  let (v, k) := match 0 with\n    | (n) => (0, 0)\n  v + k\ntheorem t : sacha = 1 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "bool",
            "def b : Bool := 1 + 1\n",
            "failed to synthesize instance of type class",
        ),
        (
            "power_wrong",
            "theorem t : 2 ^ 10 = 1023 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "power_string",
            "def s : String := 2 ^ 3\n",
            "failed to synthesize instance of type class",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: {pin}): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
}
