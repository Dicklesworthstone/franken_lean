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
#check let a := x
  let b := a
  b
#check let a := 1
  let b := a
  b
";

/// The pin's output for [`PROGRAM`]: a section variable prints by its name, an anonymous
/// instance variable as `inst✝`, and `universe v` names a level inside a query. A `let` chain at
/// the top of the line breaks after each `;`, under section variables too.
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
let a := x;
let b := a;
b : Nat
let a := 1;
let b := a;
b : Nat
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

/// A `let` (`have` when nondependent) inside another term prints in parentheses, broken after
/// its `;` at the enclosing indentation, and its hard line breaks every group around it. In a
/// goal too: `apply` assigns the `have` term itself, unreduced, as the pin's
/// `isDefEqQuickOther` assigns it.
const NESTED_LETS: &str = "prelude
import Init.Core
opaque q : Nat → Prop
opaque f : Nat → Nat → Nat
#check q (have x := 0; x + 1)
#check q (let x := 0; x + 1)
#check f (let x := 0; x + 1) 2
#check fun (n : Nat) => q (have x := n; x + 1)
#check q (let x := 0; let y := x; x + y)
#check have x := 0; x + 1
#check let x := 0; x + 1
opaque p : Nat → Prop
axiom p_of_q : q x → p x
axiom pq : q (have x := 0; x + 1)
theorem pletfun : p (have x := 0; x + 1) := by
  apply p_of_q
  trace_state
  exact pq
";

/// The pinned v4.32.0's output for [`NESTED_LETS`] (measured 2026-10-22).
const NESTED_LETS_EXPECTED: &str = "q
  (have x := 0;
  x + 1) : Prop
q
  (let x := 0;
  x + 1) : Prop
f
  (let x := 0;
  x + 1)
  2 : Nat
fun n =>
  q
    (have x := n;
    x + 1) : Nat → Prop
q
  (let x := 0;
  let y := x;
  x + y) : Prop
have x := 0;
x + 1 : Nat
let x := 0;
x + 1 : Nat
⊢ q
    (have x := 0;
    x + 1)
";

#[test]
fn nested_lets_print_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let entry = root.join("NestedLets.lean");
    std::fs::write(&entry, NESTED_LETS).unwrap();
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
    assert_eq!(
        String::from_utf8(ours.stdout).unwrap(),
        NESTED_LETS_EXPECTED
    );
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, NESTED_LETS_EXPECTED),
            "the pin moved"
        );
    }
}

/// `#synth` over a class that unfolds to a function type: the pin abstracts the instance over
/// the telescope with `etaReduce := true`, so an instance without subgoals prints as itself and
/// one whose instance arguments were still holes prints eta-expanded (measured 2026-10-22).
#[test]
fn synth_eta_reduces_unless_the_instance_had_subgoals() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let entry = root.join("Synth.lean");
    std::fs::write(
        &entry,
        "prelude\nimport Init.Core\n#synth DecidableEq (Nat × Nat)\n#synth DecidableEq Nat\n#synth Inhabited Nat\n",
    )
    .unwrap();
    let expected = "fun a b => instDecidableEqProd a b\ninstDecidableEqNat\ninstInhabitedNat\n";
    let ours = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(&root)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
    assert_eq!(
        (
            ours.status.code(),
            String::from_utf8(ours.stdout).unwrap().as_str()
        ),
        (Some(0), expected),
        "stderr: {}",
        String::from_utf8_lossy(&ours.stderr)
    );
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
}
