//! `#check` and `#synth` over section variables, through the installed drop-in `lean`, over
//! `prelude` + `import Init.Core`. The pin elaborates a query with every section variable in the
//! local context (`runTermElabM`) and prints the term with them free; the candidate checked here
//! is closed over the variables its term uses, and the printer opens them again under the names
//! the pin shows. Before this, any such query reached the kernel with a free variable
//! ("kernel rejected declaration (UnknownFVar)").
//!
//! The program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-21),
//! and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = "prelude
import Init.Core
structure S where
  bar : Nat
variable (s : S)
#check s.bar
#check s
universe v
variable (α : Type v) (a : α)
#check a
#check (fun (x : α) => x)
variable [Inhabited α]
#synth Inhabited α
#check (default : α)
#check (Nat.zero : Nat)
#check Nat.succ
variable (x : Nat) (h : x = x)
#check h
#check Eq.refl x
#check fun (t : Type v) (k : t) => k
#check fun (n : Nat) => Nat.add n x
#check @Eq.refl Nat x
";

/// The pin's output for [`PROGRAM`]: a section variable prints by its name, an anonymous
/// instance variable as `inst✝`, and `universe v` names a level inside a query.
const EXPECTED: &str = "s.bar : Nat
s : S
a : α
fun x => x : α → α
inst✝
default : α
Nat.zero : Nat
Nat.succ (n : Nat) : Nat
h : x = x
Eq.refl x : x = x
fun t k => k : (t : Type v) → t → t
fun n => n.add x : Nat → Nat
Eq.refl x : x = x
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
        "fln-check-section-variables-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s stdout and exit code on `entry`, when the binary is present.
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

#[test]
fn queries_over_section_variables_print_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let entry = root.join("Queries.lean");
    std::fs::write(&entry, PROGRAM).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(&root)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
    assert_eq!(
        ours.status.code(),
        Some(0),
        "stderr: {}",
        String::from_utf8_lossy(&ours.stderr)
    );
    assert_eq!(String::from_utf8(ours.stdout).unwrap(), EXPECTED);
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
}
