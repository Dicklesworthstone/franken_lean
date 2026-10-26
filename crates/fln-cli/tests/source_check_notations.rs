//! A source file's own notations in `#check` output, through the installed drop-in `lean`, over
//! `prelude` + `import Init.Core`. The pin's `notation` and mixfix commands declare an app
//! unexpander for the constant their right-hand side applies (`mkUnexpander`, vendored
//! `Lean/Elab/Notation.lean:103-128`), and its delaborator prints an application of that constant
//! through the notation: `𝟚` for `two`, `ℕ` for `Nat` in types too, `(g ∘' f) x` for an
//! over-applied infix. `#check` of an identifier still prints the constant's signature; a
//! notation's use is not an identifier, though it expands to one.
//!
//! The program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-21),
//! and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = r#"prelude
import Init.Core
def two := 2
notation "𝟚" => two
#check 𝟚
#check two
#check (two)
def three (_ : Nat) := 3
notation "𝟛" => three
#check 𝟛 10
notation "ℕ" => Nat
#check ℕ
#check (ℕ)
#check Nat
#check Nat → ℕ
class HAdd' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hAdd : α → β → γ
instance [HAdd α β γ] : HAdd' α β γ where
  hAdd := HAdd.hAdd
notation "(+)" => HAdd'.hAdd
#check ((+) : Nat -> Nat -> Nat)
#check ((+) 2 : Nat -> Nat)
#check ((+) 2 3 : Nat)
def Function.comp' {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)
section
variable (f : α → β) (g : β → γ) (x : α)
infixr:90 " ∘' "  => Function.comp'
#check (g ∘' f) x
#check g ∘' f
#check Function.comp' g f
end
def pair (a b : Nat) : Nat := a + b
notation "⟪" a ", " b "⟫" => pair a b
#check ⟪1, 2⟫
#check pair 1
#check pair ⟪1, 2⟫ 3
notation "dup" a => pair a a
#check dup 1
infixl:65 " +++ " => pair
#check 1 +++ 2 +++ 3
#check 1 +++ (2 +++ 3)
#check ⟪1 +++ 2, 3⟫
section
local notation "loc" => two
#check loc
end
#check two
"#;

/// The pin's output for [`PROGRAM`]. An application prints through the newest notation over its
/// constant that its explicit arguments reach; `dup`'s variable occurs twice on its right-hand
/// side, so it declares no unexpander and `pair 1 1` prints through `⟪ , ⟫`; a `local` notation
/// prints only in its section.
const EXPECTED: &str = "𝟚 : Nat
two : Nat
𝟚 : Nat
𝟛 10 : Nat
ℕ : Type
ℕ : Type
Nat : Type
ℕ → ℕ : Type
(+) : ℕ → ℕ → ℕ
(+) 2 : ℕ → ℕ
(+) 2 3 : ℕ
(g ∘' f) x : γ
g ∘' f : α → γ
g ∘' f : α → γ
⟪1, 2⟫ : ℕ
pair 1 : ℕ → ℕ
⟪⟪1, 2⟫, 3⟫ : ℕ
⟪1, 1⟫ : ℕ
1 +++ 2 +++ 3 : ℕ
1 +++ (2 +++ 3) : ℕ
1 +++ 2 +++ 3 : ℕ
loc : ℕ
two : ℕ
";

/// Infixes over the builtin `+`'s token at a higher priority: where one is active (`local`, in
/// its section; `scoped`, in or after opening its namespace) `x + y` is `f x y`, and prints
/// back through it with the atom's own spacing (`"  +  "` is `1  + 2`); elsewhere `+` is
/// `HAdd.hAdd`.
const PRIORITY: &str = r#"prelude
import Init.Core
def f (x y : Nat) := x + 2*y
namespace Foo
local infix:65 (priority := high) "+" => f
theorem ex1 (x y : Nat) : x + y = f x y := rfl
#check 1 + 2
end Foo
#check 1 + 2
theorem ex2 (x y : Nat) : x + y = HAdd.hAdd x y := rfl
section
def g (x y : Nat) := 3*(x+y)
local infix:65 (priority := high) "  +  " => g
theorem ex4 (x y : Nat) : x + y = g x y := rfl
#check 1 + 2
end
theorem ex5 (x y : Nat) : x + y = HAdd.hAdd x y := rfl
#check 1 + 2
namespace Bar
scoped infix:65 (priority := high) "+" => f
theorem ex6 (x y : Nat) : x + y = f x y := rfl
#check 1 + 2
end Bar
#check 1 + 2
theorem ex7 (x y : Nat) : x + y = HAdd.hAdd x y := rfl
open Bar
theorem ex8 (x y : Nat) : x + y = f x y := rfl
#check 1 + 2
"#;

/// The pin's output for [`PRIORITY`].
const PRIORITY_EXPECTED: &str = "1+2 : Nat
1 + 2 : Nat
1  + 2 : Nat
1 + 2 : Nat
1+2 : Nat
1 + 2 : Nat
1+2 : Nat
";

/// A notation whose right-hand side passes something other than a variable: the pin's
/// unexpander matches only some delaborated arguments, which is not decided here, so an
/// application it might print is refused rather than printed another way.
const UNDECIDED: &str = "prelude
import Init.Core
def pair (a b : Nat) : Nat := a + b
notation \"one+\" a => pair 1 a
#check pair 2 3
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
        "fln-check-notations-{}-{}",
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
    let entry = root.join("Notations.lean");
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
fn applications_print_through_the_files_notations_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, PROGRAM);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, EXPECTED);
    if let Some((code, stdout)) = pinned(&lib, &root.join("Notations.lean")) {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
}

#[test]
fn an_infix_outranking_a_builtin_operator_reads_in_its_place() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, PRIORITY);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, PRIORITY_EXPECTED);
    if let Some((code, stdout)) = pinned(&lib, &root.join("Notations.lean")) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, PRIORITY_EXPECTED),
            "the pin moved"
        );
    }
}

#[test]
fn an_application_an_undecided_notation_may_print_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, UNDECIDED);
    assert_ne!(code, Some(0), "stdout: {stdout}");
    assert!(
        stderr.contains("a notation of this file may print"),
        "stderr: {stderr}"
    );
}

#[test]
fn a_section_capture_never_resolves_to_an_unrelated_global() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let source = "prelude\nimport Init.Core\ndef x : Nat := 1\nsection\nvariable (x : Nat)\nnotation \"capturedValue!\" => x\nend\n#check capturedValue!\n";
    let (code, stdout, stderr) = ours(&lib, &root, source);
    assert_eq!(code, Some(5), "stdout: {stdout}\nstderr: {stderr}");
    assert!(stdout.is_empty(), "{stdout}");
    assert!(
        stderr.contains("quotation capture of a section variable"),
        "{stderr}"
    );
    if let Some((code, output)) = pinned(&lib, &root.join("Notations.lean")) {
        assert_eq!(code, 1, "{output}");
        assert!(output.contains("Unknown constant"), "{output}");
    }
}

#[test]
#[ignore = "whole pinned Init admission; required scheduled Reference release lane"]
fn upstream_notation_printing_regressions_match_the_pin() {
    let lib = pinned_lib().expect("the pinned Reference is required for the upstream comparison");
    let reference = lib.parent().unwrap().parent().unwrap().join("bin/lean");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success(), "{version:?}");
    assert_eq!(
        String::from_utf8_lossy(&version.stdout).trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let root = workspace();
    let records = root.join("records");
    std::fs::create_dir(&records).unwrap();
    let cases = [
        ("1367", include_str!("../../../vendor/lean4-src/tests/elab/1367.lean")),
        ("2045", include_str!("../../../vendor/lean4-src/tests/elab/2045.lean")),
        ("469", include_str!("../../../vendor/lean4-src/tests/elab/469.lean")),
        ("constDelab", include_str!("../../../vendor/lean4-src/tests/elab/constDelab.lean")),
        ("scopedParsers", include_str!("../../../vendor/lean4-src/tests/elab/scopedParsers.lean")),
        ("infixprio", include_str!("../../../vendor/lean4-src/tests/elab/infixprio.lean")),
        ("localParsers", include_str!("../../../vendor/lean4-src/tests/elab/localParsers.lean")),
    ];
    for (name, source) in cases {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, source).unwrap();
        eprintln!("upstream notation comparison: elab/{name}.lean");
        let oracle = Command::new(&reference)
            .arg(&entry)
            .env("LEAN_PATH", &lib)
            .output()
            .unwrap();
        assert_eq!(oracle.status.code(), Some(0), "{name}: {oracle:?}");
        assert!(oracle.stderr.is_empty(), "{name}: {oracle:?}");
        let native = Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&entry)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", &records)
            .output()
            .unwrap();
        assert_eq!(native.status.code(), Some(0), "{name}: {native:?}");
        assert_eq!(native.stdout, oracle.stdout, "elab/{name}.lean");
        assert!(native.stderr.is_empty(), "{name}: {native:?}");
        assert_eq!(std::fs::read_to_string(&entry).unwrap(), source);
    }
}
