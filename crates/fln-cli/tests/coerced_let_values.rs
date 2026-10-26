//! A coerced value is the term the source wrote, not its reduction. The pin's `?a := b` for
//! `CoeT Bool b (Option Bool)` is `isDefEqQuickOther`'s direct assignment (vendored
//! `Lean/Meta/ExprDefEq.lean`), so a `let` variable stays a variable and `expandCoe` gives
//! `some b`. Reducing the side first zeta-delta-expanded `b` and, at instances transparency,
//! unfolded `getElem` through both instances, printing `some b'` and
//! `some (bs.getInternal n sorry)` with a spurious `declaration uses sorry` warning (upstream
//! `tests/elab/forOutParamIssue.lean`).
//!
//! Through the drop-in `lean` over `prelude` with `Init.Data.Array.Basic` and
//! `Init.Data.Option.Coe`. Every program here was run through the pinned `lean` v4.32.0 with the
//! same header first (2026-10-24), and is compared with the pinned binary again when present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.Data.Array.Basic\nimport Init.Data.Option.Coe\n";

/// The upstream test's class and instance, whose `sorry` is the one warning the pin prints,
/// then `let` values coerced from `Bool` to `Option Bool` in a term and in a definition body.
const LET_VALUES: &str = "namespace Ex
class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) where
  getElem (xs : Cont) (i : Idx) : Elem
export GetElem (getElem)
instance : GetElem (Array α) Nat α where
  getElem xs i := xs[i]'sorry
#check fun (b' : Bool) => (let b := b'; (b : Option Bool))
#check fun (bs : Array Bool) (n : Nat) => (let b : Bool := getElem bs n; (b : Option Bool))
#check fun (b' : Bool) => (let b := id b'; (b : Option Bool))
def c6 (b' : Bool) : Option Bool := let b := b'; b
def c7 (bs : Array Bool) (n : Nat) : Option Bool := let b : Bool := getElem bs n; b
def c9 (b' : Bool) : Option Bool := let b := id b'; b
example (b' : Bool) : c6 b' = some b' := rfl
example (b' : Bool) : c9 b' = some b' := rfl
end Ex
";

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

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-coerced-let-values-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// This crate's `lean` on `HEADER` + `program`, and the pinned `lean` when it is present.
fn runs(lib: &Path, root: &Path, name: &str, program: &str) -> (Output, Option<Output>) {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let run = |binary: &Path| {
        Command::new(binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean")
    };
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file());
    (
        run(Path::new(env!("CARGO_BIN_EXE_lean"))),
        pinned.as_deref().map(run),
    )
}

fn stdout(name: &str, output: &Output) -> String {
    assert_eq!(
        output.status.code(),
        Some(0),
        "{name}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout.clone()).expect("UTF-8 output")
}

/// The message lines: every `<file>:<line>:<col>: <severity>:` header.
fn messages(name: &str, stdout: &str) -> Vec<String> {
    let prefix = format!("{name}.lean:");
    stdout
        .lines()
        .filter(|line| line.starts_with(&prefix))
        .map(str::to_owned)
        .collect()
}

#[test]
fn coerced_let_variables_are_assigned_as_written_without_a_spurious_sorry() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let name = "let_values";
    let (ours, pinned) = runs(&lib, &root, name, LET_VALUES);
    let ours = stdout(name, &ours);
    // The instance's own `sorry` (line 8 after the three-line header) is the only warning:
    // `c7`'s body names `b`, so it does not use `sorry`.
    assert_eq!(
        messages(name, &ours),
        [format!(
            "{name}.lean:8:0: warning: declaration uses `sorry`"
        )],
        "{ours}"
    );
    for coerced in ["let b := b';", "let b := getElem bs n;", "let b := id b';"] {
        assert!(ours.contains(coerced), "{coerced}\n{ours}");
    }
    assert_eq!(ours.matches("some b :").count(), 3, "{ours}");
    for reduced in ["some b'", "getInternal", "some (id b')"] {
        assert!(!ours.contains(reduced), "{reduced}\n{ours}");
    }
    if let Some(pinned) = pinned {
        let pinned = stdout(name, &pinned);
        assert_eq!(messages(name, &ours), messages(name, &pinned));
        // The terms, compared up to layout: this printer keeps `fun x => let …` on one line
        // where the pin breaks after `=>`, a formatter difference outside this repair.
        let words = |text: &str| text.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(
            words(&ours),
            words(&pinned),
            "\nours:\n{ours}\npinned:\n{pinned}"
        );
    }
}
