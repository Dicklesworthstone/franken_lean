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
/// such a token (the pin's parenthesizer, measured 2026-10-22). An ascribed `fun` is the root of
/// its line, grouped, so it stays on one line. An ascribed proof is the root too, so it prints in
/// full, while a proof inside an ascribed value is still `⋯` (measured 2026-10-23).
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
#check (fun (v : Nat) => v + 1 : Nat → Nat)
#check (Eq.refl 2 : 2 = 2)
#check (Subtype.mk 2 (Eq.refl 2) : Subtype fun n : Nat => n = 2)
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
fun v => v + 1 : Nat → Nat
Eq.refl 2 : 2 = 2
⟨2, ⋯⟩ : Subtype fun n => n = 2
";

/// With `Init.NotationExtra` imported, its `@[app_unexpander]`s are registered: `Prod.mk` prints
/// as a tuple, flattened to the right, `Unit.unit` as `()`, lists and `∃` as notation, `Subtype`
/// as `{ n // n = 1 }`, and its anonymous constructor with the proof elided (`pp.proofs`). Without
/// it (above) they are applications and structure instances.
const NOTATION_EXTRA: &str = r#"prelude
import Init.NotationExtra
#check Unit.unit
#check (Unit.unit, 1)
#check (1, 2, 3)
#check ((1, 2), 3)
#check [1, 2]
#check ∃ x : Nat, x = 1
#check Sigma fun (n : Nat) => Fin n
#check PSigma fun (n : Nat) => n = n
#check Sigma fun (_ : Nat) => Nat
#check (Sigma fun (n : Nat) => Fin n) → Nat
#check Nat × Sigma fun (n : Nat) => Fin n
#check (⟨1, rfl⟩ : Subtype (fun n : Nat => n = 1))
"#;

/// The pin's output for [`NOTATION_EXTRA`].
const NOTATION_EXTRA_EXPECTED: &str = "Unit.unit : Unit
((), 1) : Unit × Nat
(1, 2, 3) : Nat × Nat × Nat
((1, 2), 3) : (Nat × Nat) × Nat
[1, 2] : List Nat
∃ x, x = 1 : Prop
(n : Nat) × Fin n : Type
(n : Nat) ×' n = n : Type
(_ : Nat) × Nat : Type
(n : Nat) × Fin n → Nat : Type
Nat × (n : Nat) × Fin n : Type
⟨1, ⋯⟩ : { n // n = 1 }
";

/// `+`, `::`, `∧` and `=` are `infixl`/`infixr` notations of `Init.Notation`, which registers
/// their unexpanders. With only `Init.Prelude` imported the pin prints the applications.
const PRELUDE_OPERATORS: &str = r#"prelude
import Init.Prelude
#check fun (a b : Nat) => HAdd.hAdd a b
#check fun (a : Nat) (l : List Nat) => List.cons a l
#check fun (p q : Prop) => And p q
#check fun (a b : Nat) => Eq a b
"#;

/// The pin's output for [`PRELUDE_OPERATORS`].
const PRELUDE_OPERATORS_EXPECTED: &str = "fun a b => HAdd.hAdd a b : Nat → Nat → Nat
fun a l => List.cons a l : Nat → List Nat → List Nat
fun p q => And p q : Prop → Prop → Prop
fun a b => Eq a b : Nat → Nat → Prop
";

/// A `scoped` unexpander is in force only where its namespace is active. `Int.negSucc`'s
/// `-[n+1]` (`scoped notation` in `Init/Data/Int/Basic.lean:74`) is scoped to `Int`, so the pin
/// prints `Int.negSucc 9` outside it, and in another namespace.
const SCOPED: &str = r#"prelude
import Init.Data.Int.Basic
#reduce Int.negSucc 9
namespace Foo
#reduce Int.negSucc 9
end Foo
#reduce (Int.ofNat 3, Int.negSucc 2)
"#;

/// The pin's output for [`SCOPED`].
const SCOPED_EXPECTED: &str = "Int.negSucc 9
Int.negSucc 9
{ fst := Int.ofNat 3, snd := Int.negSucc 2 }
";

/// The object of field notation drops projections to a parent's subobject
/// (`stripParentProjections`, vendored `PrettyPrinter/Delaborator/Builtins.lean:260-270`):
/// `B.toA (D.toB d)` prints `d.toA`. `D.toC` is no subobject, since `C` shares `A` with `B`. It is
/// a definition, so `d.toC` stays. An object outside field notation keeps its projection.
const PARENT_PROJECTIONS: &str = r#"prelude
import Init.Core
structure A where
  x : Nat
structure B extends A where
  z : Nat
structure C extends A where
  w : Nat
structure D extends B, C where
  a : Nat
def B.double (b : B) : Nat := b.z
#print D.toC
#check fun (d : D) => d.x
#check fun (d : D) => d.toB
#check fun (d : D) => d.toB.toA
#check fun (d : D) => B.double d.toB
#check fun (d : D) => (D.toC d).w
#check fun (b : B) => b.toA.x
"#;

/// The pin's output for [`PARENT_PROJECTIONS`].
const PARENT_PROJECTIONS_EXPECTED: &str = "@[reducible] def D.toC : D → C :=
fun self => { toA := self.toA, w := self.w }
fun d => d.x : D → Nat
fun d => d.toB : D → B
fun d => d.toA : D → A
fun d => d.double : D → Nat
fun d => d.toC.w : D → Nat
fun b => b.x : B → Nat
";

/// The coercion arrow `↑e` (`elabCoe`): `e` elaborates without an expected type and is made to
/// have the expected type. With none known it only unifies (`up2 : Nat → Nat`, `↑(3 : Nat)` is
/// `3`); with `Int` expected a `Nat` is coerced, also as an operator's leaf, and prints `↑n`.
const COERCION_ARROW: &str = r#"prelude
import Init.Data.Int.Basic
def up (n : Nat) : Nat := ↑n
def up2 (n : Nat) := ↑n
#check up2
#check fun (n : Nat) => (↑n : Int)
#check ↑(3 : Nat)
example (n : Nat) : (↑n : Int) = Int.ofNat n := rfl
def co3 (n : Nat) : Int := ↑n + 1
#check co3
"#;

/// The pin's output for [`COERCION_ARROW`].
const COERCION_ARROW_EXPECTED: &str = "up2 (n : Nat) : Nat
fun n => ↑n : Nat → Int
3 : Nat
co3 (n : Nat) : Int
";

/// A local structure without fields: the pin prints its one instance as `{ }`.
const EMPTY_STRUCTURE: &str = "prelude\nimport Init.Core\nstructure E\n#check ({ } : E)\n";

/// The pin's output for [`EMPTY_STRUCTURE`].
const EMPTY_STRUCTURE_EXPECTED: &str = "{ } : E\n";

/// What this door refuses rather than print another way: a field the pin compares with its
/// default by a reducible `isDefEq` that is not decided here (`1 + 2` against `3`, which the pin
/// omits: `{ } : D`). A field syntactically equal to its default, or a literal other than a
/// literal default (`{ x := 4 } : D`), prints (`source_check_optional_parameters`).
///
/// Without `Init.NotationExtra`, whose macro the `Σ` notation is, the pin fails to print a `Sigma`
/// at all ("failed to pretty print expression"); this door refuses it there.
///
/// With `Init.NotationExtra` imported, a term holding binders this engine's elaboration
/// introduced (an `if` it compiles to `Decidable.rec`, where the pin has `ite`) is refused too.
/// Inside `open Int`, the pin prints `Int.negSucc 9` as `-[9+1]`, which is refused here too.
const REFUSED: &[&str] = &[
    "prelude\nimport Init.Core\nstructure D where\n  x : Nat := 3\n#check ({ x := 1 + 2 } : D)\n",
    "prelude\nimport Init.NotationExtra\n#check fun (n : Nat) => if n = 0 then 1 else 2\n",
    "prelude\nimport Init.Core\n#check Sigma fun (n : Nat) => Fin n\n",
    "prelude\nimport Init.Data.Int.Basic\nopen Int in\n#reduce Int.negSucc 9\n",
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
fn operators_print_as_applications_where_their_notation_is_not_imported() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Operators.lean");
    std::fs::write(&entry, PRELUDE_OPERATORS).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, PRELUDE_OPERATORS_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, PRELUDE_OPERATORS_EXPECTED, "{stderr}");
}

#[test]
fn a_scoped_unexpander_is_in_force_only_where_its_namespace_is_active() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Scoped.lean");
    std::fs::write(&entry, SCOPED).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, SCOPED_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, SCOPED_EXPECTED, "{stderr}");
}

#[test]
fn a_field_notation_object_drops_parent_projections_as_at_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Parents.lean");
    std::fs::write(&entry, PARENT_PROJECTIONS).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, PARENT_PROJECTIONS_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, PARENT_PROJECTIONS_EXPECTED, "{stderr}");
}

#[test]
fn the_coercion_arrow_coerces_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Coercions.lean");
    std::fs::write(&entry, COERCION_ARROW).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, COERCION_ARROW_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, COERCION_ARROW_EXPECTED, "{stderr}");
}

#[test]
fn a_structure_without_fields_prints_its_instance_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Empty.lean");
    std::fs::write(&entry, EMPTY_STRUCTURE).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, EMPTY_STRUCTURE_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, EMPTY_STRUCTURE_EXPECTED, "{stderr}");
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
