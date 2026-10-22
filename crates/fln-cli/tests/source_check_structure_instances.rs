//! Structure instances in `#check` output, through the installed drop-in `lean`, over
//! `prelude` and `import Init.Core`. The pin's `delabStructureInstance` (vendored
//! `PrettyPrinter/Delaborator/Builtins.lean:635-689`) prints a structure's constructor applied to
//! every field as `{ x := a, … }`, flattening a parent's subobject that is itself that parent's
//! constructor applied, and as `⟨a, …⟩` for a structure tagged
//! `@[pp_using_anonymous_constructor]`, which `Subtype` is in `Init.Prelude`. `Prod.mk` prints
//! as a structure instance here because `Init.Core` does not import `Init.NotationExtra`, where
//! its `(a, b)` unexpander is registered.
//!
//! The program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-22),
//! and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = r#"prelude
import Init.Core
structure P where
  a : Nat
  b : Nat
structure Q extends P where
  c : Nat
class C (α : Type) where
  x : α
  y : α
structure R where
  n : Nat
  h : n = n
structure Long where
  first_field_with_a_long_name : Nat
  second_field_with_a_long_name : Nat
  third_field_with_a_long_name : Nat
  fourth_field_with_a_long_name : Nat
#check ({ a := 1, b := 2 } : P)
#check ({ a := 1, b := 2, c := 3 } : Q)
#check (⟨1, 2⟩ : P)
#check P.mk 1
#check fun (n : Nat) => ({ a := n, b := n } : P)
#check ({ n := 1, h := rfl } : R)
#check (⟨1, rfl⟩ : Subtype (fun n : Nat => n = 1))
#check ({ x := 1, y := 2 } : C Nat)
#check (Prod.mk 1 2)
#check ({ first_field_with_a_long_name := 1000000, second_field_with_a_long_name := 2000000, third_field_with_a_long_name := 3000000, fourth_field_with_a_long_name := 4 } : Long)
#check Q.mk { a := 1, b := 2 } 3
#check fun (p : P) => Q.mk p 3
"#;

/// The pin's output for [`PROGRAM`]: a proof field prints `⋯`; `Q.mk p 3` keeps the parent
/// `p` as `toP`, which is not a constructor application to flatten.
const EXPECTED: &str = "{ a := 1, b := 2 } : P
{ a := 1, b := 2, c := 3 } : Q
{ a := 1, b := 2 } : P
P.mk 1 : Nat → P
fun n => { a := n, b := n } : Nat → P
{ n := 1, h := ⋯ } : R
⟨1, ⋯⟩ : Subtype fun n => n = 1
{ x := 1, y := 2 } : C Nat
{ fst := 1, snd := 2 } : Nat × Nat
{ first_field_with_a_long_name := 1000000, second_field_with_a_long_name := 2000000,
  third_field_with_a_long_name := 3000000, fourth_field_with_a_long_name := 4 } : Long
{ a := 1, b := 2, c := 3 } : Q
fun p => { toP := p, c := 3 } : P → Q
";

/// `fun` parses at `maxPrec`, so as an application's last argument it is left bare; an
/// application ending so is bracketed whole where a token follows it, and a field's `,` is not
/// such a token (the pin's parenthesizer, measured 2026-10-22).
const TRAILING_FUN: &str = r#"prelude
import Init.Core
def ap (f : Nat → Nat) (n : Nat) : Nat := f n
def ap2 (n : Nat) (f : Nat → Nat) : Nat := f n
#check ap (fun x => x) 1
#check ap2 1 fun x => x
#check (Subtype fun n : Nat => n = 1) → Nat
#check ap2 (ap2 1 fun x => x) fun y => y
#check ap2 1 (fun x => x) + 2
#check 2 + ap2 1 fun x => x
#check fun (g : (Nat → Nat) → Nat) => g fun x => x
#check (ap2 1 fun x => x, 3)
"#;

/// The pin's output for [`TRAILING_FUN`].
const TRAILING_FUN_EXPECTED: &str = "ap (fun x => x) 1 : Nat
ap2 1 fun x => x : Nat
(Subtype fun n => n = 1) → Nat : Type
ap2 (ap2 1 fun x => x) fun y => y : Nat
(ap2 1 fun x => x) + 2 : Nat
2 + ap2 1 fun x => x : Nat
fun g => g fun x => x : ((Nat → Nat) → Nat) → Nat
{ fst := ap2 1 fun x => x, snd := 3 } : Nat × Nat
";

/// With `Init.NotationExtra` imported, its `@[app_unexpander]`s are registered: `Prod.mk` prints
/// as a tuple, flattened to the right, `Unit.unit` as `()`, lists and `∃` as notation. Without
/// it (above) they are applications and structure instances.
const NOTATION_EXTRA: &str = r#"prelude
import Init.NotationExtra
#check Unit.unit
#check (Unit.unit, 1)
#check (1, 2, 3)
#check ((1, 2), 3)
#check [1, 2]
#check ∃ x : Nat, x = 1
"#;

/// The pin's output for [`NOTATION_EXTRA`].
const NOTATION_EXTRA_EXPECTED: &str = "Unit.unit : Unit
((), 1) : Unit × Nat
(1, 2, 3) : Nat × Nat × Nat
((1, 2), 3) : (Nat × Nat) × Nat
[1, 2] : List Nat
∃ x, x = 1 : Prop
";

/// What this door refuses rather than print another way: a local type without fields (the pin
/// prints `structure E` as `{ }` and `inductive E | mk` as `E.mk`) and a field with a default
/// value (which the pin omits when the value equals it).
///
/// With `Init.NotationExtra` imported, an application another registered unexpander prints
/// (`Subtype` as `{ n // n = 1 }`) is refused too, and so is a term holding binders this engine's
/// elaboration introduced (an `if` it compiles to `Decidable.rec`, where the pin has `ite`).
const REFUSED: &[&str] = &[
    "prelude\nimport Init.Core\nstructure E\n#check ({ } : E)\n",
    "prelude\nimport Init.Core\nstructure D where\n  x : Nat := 3\n#check ({ x := 4 } : D)\n",
    "prelude\nimport Init.NotationExtra\n#check (⟨1, rfl⟩ : Subtype (fun n : Nat => n = 1))\n",
    "prelude\nimport Init.NotationExtra\n#check fun (n : Nat) => if n = 0 then 1 else 2\n",
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
        "fln-check-structure-instances-{}-{}",
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

/// The installed `lean` on `entry`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, entry: &Path) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn structure_instances_print_as_the_pin_prints_them() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Instances.lean");
    std::fs::write(&entry, PROGRAM).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, EXPECTED, "{stderr}");
}

#[test]
fn a_last_fun_argument_is_bracketed_only_where_a_token_follows() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Funs.lean");
    std::fs::write(&entry, TRAILING_FUN).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, TRAILING_FUN_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, TRAILING_FUN_EXPECTED, "{stderr}");
}

#[test]
fn registered_unexpanders_print_tuples_lists_and_unit_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Extra.lean");
    std::fs::write(&entry, NOTATION_EXTRA).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, NOTATION_EXTRA_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, NOTATION_EXTRA_EXPECTED, "{stderr}");
}

#[test]
fn structure_instances_this_door_cannot_decide_are_refused() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (index, program) in REFUSED.iter().enumerate() {
        let entry = root.join(format!("Refused{index}.lean"));
        std::fs::write(&entry, program).unwrap();
        if let Some((code, _)) = pinned(&lib, &entry) {
            assert_eq!(code, 0, "the pin accepts {program}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(
            stderr.contains("the way the pin does"),
            "{program}: {stderr}"
        );
    }
}
