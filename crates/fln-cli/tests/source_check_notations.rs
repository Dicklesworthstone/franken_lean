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
