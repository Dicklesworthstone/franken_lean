//! `Std.Legacy.Range`'s range literals, `[a:b]`, `[:b]`, `[a:b:s]` and `[:b:s]`
//! (`syntax:max "[" withoutPosition(…) "]"`, vendored `Init/Data/Range/Basic.lean:69-78`), in
//! `for` loops through the installed drop-in `lean`, over `prelude` + `Init.Data.Range.Basic` +
//! `Init.Data.Repr`. Each literal is the macros' `Range` instance: the omitted `start` and `step`
//! at their defaults, `step_pos` by `Nat.zero_lt_one` or, with a written step, `by decide`.
//! Every program is compared with the pinned `lean` v4.32.0 whenever it is present.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Range.Basic\nimport Init.Data.Repr\n";

const PROGRAM: &str = "def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n+1] do
    acc := acc + i
  return acc
#eval sumTo 100
#eval sumTo 0
def upTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [:n] do
    acc := acc + i
  return acc
#eval upTo 5
def evens (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [:n:2] do
    acc := acc + i
  return acc
#eval evens 10
def stepped (a b : Nat) : Nat := Id.run do
  let mut total := 0
  for i in [a:b:3] do
    total := total + i
  return total
#eval stepped 1 10
";

/// The pin's output for [`PROGRAM`]. Every loop reads its index: a body that ignores it is refused
/// at runtime ingress here (a closure-type mismatch), which is recorded separately.
const EXPECTED: &str = "5050\n0\n10\n20\n12\n";

/// Refused at the pin, and here: a range never ends at its colon, never mixes `,` and `:`, and a
/// written step must be decidably positive.
const REFUSED: &[(&str, &str)] = &[
    ("trailing_colon", "def r := [1:]\n"),
    ("empty_range", "def r := [:]\n"),
    ("mixed_separators", "def r := [1, 2:3]\n"),
    ("zero_step", "def r := [0:5:0]\n"),
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
        .filter(|lib| lib.join("Init/Data/Range/Basic.olean").is_file());
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
        "fln-range-literals-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
fn pinned(lib: &Path, entry: &Path) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `HEADER` + `program`: its exit code, stdout and stderr. One record
/// directory per workspace, so the import closure is admitted once.
fn ours(lib: &Path, root: &Path, name: &str, program: &str) -> (Option<i32>, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
    (
        output.status.code(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn range_literals_run_their_for_loops_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, "Ranges", PROGRAM);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, EXPECTED);
    if let Some((code, stdout)) = pinned(&lib, &root.join("Ranges.lean")) {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
    for (name, program) in REFUSED {
        let (code, stdout, stderr) = ours(&lib, &root, name, program);
        assert_ne!(code, Some(0), "{name}: accepted\n{stdout}");
        assert!(!stderr.is_empty(), "{name}: refused without a reason");
        if let Some((code, _)) = pinned(&lib, &root.join(format!("{name}.lean"))) {
            assert_ne!(code, 0, "{name}: the pin accepts it");
        }
    }
}
