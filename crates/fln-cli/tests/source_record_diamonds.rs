//! Structures and classes whose parents share fields (diamonds), through the installed drop-in
//! `lean`, over `prelude` + `import Init.Core`. The pin copies a parent whose fields overlap the
//! ones already present (`withStruct`, vendored `Lean/Elab/Structure.lean:640-835`): each of its
//! fields is reused at its type or becomes a constructor field, a parent of the copied parent
//! that overlaps nothing becomes a subobject, and the copied parent's projection `D.toC` is a
//! definition over the fields (`mkCoercionToCopiedParent`), an instance between classes. A
//! copied field keeps its parent's default. Before this, such a declaration was refused
//! ("duplicate record field").
//!
//! The programs were run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-21), and are compared with the pinned binary's output again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// A diamond through a common ancestor, a class diamond whose copied parent is an instance, and
/// parents that share nothing (two subobjects).
const DIAMOND: &str = r#"prelude
import Init.Core
structure A where
  x : Nat
  y : Nat
structure B extends A where
  z : Nat
structure C extends A where
  w : Nat
set_option structureDiamondWarning false
structure D extends B, C where
  a : Nat
#check D.mk
#check @D.toC
def d : D := { x := 1, y := 2, z := 3, w := 4, a := 5 }
example : d.w = 4 := rfl
example : d.x = 1 := rfl
example : d.toC.w = 4 := rfl
example : d.toC.x = 1 := rfl
example : d.toC = { x := 1, y := 2, w := 4 } := rfl
class P (α : Type) where
  one : α
class Q (α : Type) extends P α where
  add : α → α → α
class R (α : Type) extends P α where
  mul : α → α → α
class S (α : Type) extends Q α, R α
#check @S.toR
instance : S Nat where
  one := 1
  add := Nat.add
  mul := Nat.mul
example : R.mul (α := Nat) 2 3 = 6 := rfl
example : P.one (α := Nat) = 1 := rfl
structure E where
  v : Nat
structure F extends A, E
#check F.mk
"#;

/// The pin's output for [`DIAMOND`].
const DIAMOND_EXPECTED: &str = "D.mk (toB : B) (w a : Nat) : D
D.toC : D → C
@S.toR : {α : Type} → [self : S α] → R α
F.mk (toA : A) (toE : E) : F
";

/// A copied parent whose own parent overlaps nothing, which becomes a subobject of the record
/// (`toE`), and a copied field's default (`w := 7`).
const NESTED: &str = r#"prelude
import Init.Core
structure A where
  x : Nat
structure B extends A where
  z : Nat
structure E where
  e : Nat
structure H extends E where
  x : Nat
  h : Nat
set_option structureDiamondWarning false
structure G extends B, H
#check G.mk
#check @G.toH
def g : G := { x := 1, z := 2, e := 3, h := 4 }
example : g.toH.e = 3 := rfl
example : g.e = 3 := rfl
example : g.toE.e = 3 := rfl
structure C extends A where
  w : Nat := 7
structure D extends B, C
def d : D := { x := 1, z := 3 }
example : d.w = 7 := rfl
"#;

/// The pin's output for [`NESTED`].
const NESTED_EXPECTED: &str = "G.mk (toB : B) (toE : E) (h : Nat) : G
G.toH : G → H
";

/// A field both parents declare keeps the earlier parent's default, as at the pin.
const EARLIER_DEFAULT: &str = r#"prelude
import Init.Core
structure B where
  x : Nat := 1
structure C where
  x : Nat := 2
  y : Nat
set_option structureDiamondWarning false in
structure D extends B, C
def d : D := { y := 0 }
example : d.x = 1 := rfl
"#;

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
        "fln-record-diamonds-{}-{}",
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

/// The installed `lean` on `program`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, program: &str) -> (Option<i32>, String, String) {
    let entry = root.join("Diamonds.lean");
    std::fs::write(&entry, program).unwrap();
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
fn diamonds_copy_the_overlapping_parent_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (program, expected) in [
        (DIAMOND, DIAMOND_EXPECTED),
        (NESTED, NESTED_EXPECTED),
        (EARLIER_DEFAULT, ""),
    ] {
        let (code, stdout, stderr) = ours(&lib, &root, program);
        assert_eq!(code, Some(0), "{program}\nstderr: {stderr}");
        assert_eq!(stdout, expected, "{program}");
        if let Some((code, stdout)) = pinned(&lib, &root.join("Diamonds.lean")) {
            assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
        }
    }
}

/// A shared field at two different types, which the pin refuses too ("Field type mismatch"),
/// and a field only the later parent gives a default, which the pin fills from it: here that
/// default is not carried, so an instance omitting the field is refused rather than given
/// another value.
#[test]
fn diamonds_refuse_a_mismatched_field_and_an_uncarried_default() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (program, refusal) in [
        (
            r#"prelude
import Init.Core
structure Bar (α : Type) where
  a : α
  b : Nat → α
structure Baz (α : Type) where
  a : α → α
  c : Bool → α
set_option structureDiamondWarning false in
structure Foo (α : Type) extends Bar α, Baz α
"#,
            "Field type mismatch",
        ),
        (
            r#"prelude
import Init.Core
structure B where
  x : Nat
structure C where
  x : Nat := 2
  y : Nat
set_option structureDiamondWarning false in
structure D extends B, C
def d : D := { y := 0 }
example : d.x = 2 := rfl
"#,
            "missing record field x",
        ),
    ] {
        let (code, stdout, stderr) = ours(&lib, &root, program);
        assert_ne!(code, Some(0), "{program}\nstdout: {stdout}");
        assert!(stderr.contains(refusal), "{program}\nstderr: {stderr}");
    }
}

/// `{}` is a `choice` between the empty structure instance and `∅` at the pin: with an
/// `EmptyCollection` instance in scope both elaborate, and the pin reports the term ambiguous;
/// before the instance exists only the structure instance does (`elab_fail/emptyc.lean`).
#[test]
fn empty_braces_are_ambiguous_where_an_empty_collection_exists() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let accepted = "prelude\nimport Init.Core\nstructure A where\n  x : Nat := 0\ndef foo : A := {}\n#check foo\n";
    let (code, stdout, stderr) = ours(&lib, &root, accepted);
    assert_eq!(
        (code, stdout.as_str()),
        (Some(0), "foo : A\n"),
        "stderr: {stderr}"
    );
    if let Some((code, stdout)) = pinned(&lib, &root.join("Diamonds.lean")) {
        assert_eq!((code, stdout.as_str()), (0, "foo : A\n"), "the pin moved");
    }
    let ambiguous = "prelude\nimport Init.Core\nstructure A where\n  x : Nat := 0\ndef foo : A := {}\ninstance : EmptyCollection A := ⟨{ x := 10 }⟩\ndef boo : A := {}\n";
    let (code, stdout, stderr) = ours(&lib, &root, ambiguous);
    assert_eq!(code, Some(1), "stdout: {stdout}\nstderr: {stderr}");
    assert!(stderr.contains("Ambiguous term"), "{stderr}");
    if let Some((code, _)) = pinned(&lib, &root.join("Diamonds.lean")) {
        assert_eq!(code, 1, "the pin moved");
    }
}
