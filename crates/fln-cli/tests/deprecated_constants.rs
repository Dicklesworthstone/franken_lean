//! The pin's deprecation warnings (`Linter.checkDeprecated`, vendored
//! `src/Lean/Linter/Deprecated.lean`), through the drop-in `lean` over `prelude` with
//! `Init.Core`: `@[deprecated]` on source declarations and on `Init.Core`'s own (its `.olean`'s
//! `deprecatedAttr` entries), each use where the pin resolves the constant, the attribute's
//! own warnings, the notes on a replacement, and `#guard_msgs` over them. Each program runs
//! through the pinned `lean` v4.32.0 in the same test and must print exactly what the pin
//! prints.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const HEADER: &str = "prelude\nimport Init.Core\n";

/// The three attribute forms on source declarations, and the uses the pin reports: an
/// identifier, a field of generalized field notation (`n.inc'`, `(n).inc'`, `n |>.inc'`,
/// `n.inc'.inc'`) at the field, `@c`, an ascription, `#check (c)` and `#reduce c` but not
/// `#check c`, `rw` and `exact` arguments, nothing in the body of a deprecated declaration,
/// nothing under `set_option linter.deprecated false`, and the warning ahead of `sorry`'s.
const SOURCE: &str = r##"def a := 1
@[deprecated "Don't use `hi`." (since := "1970-01-01")]
theorem hi : a = 1 := rfl
@[deprecated]
def Foo.foo : Nat := 3
@[deprecated Foo.foo (since := "2025-01-01")]
def Foo.bar : Nat := Foo.foo
def Nat.inc (n : Nat) : Nat := n + 1
@[deprecated inc (since := "2025-10-17")]
def Nat.inc' (n : Nat) : Nat := n + 1
example : a = 1 := hi
example : Nat := Foo.foo
example : Nat := Foo.bar
example (n : Nat) : Nat := n.inc'
example (n : Nat) : Nat := (n).inc'
example (n : Nat) : Nat := n |>.inc'
example (n : Nat) : Nat := Nat.inc' n
example (n : Nat) : Nat := Nat.inc' (Nat.inc' n)
set_option linter.deprecated false in
example : Nat := Foo.foo
#check Foo.foo
#check (Foo.foo)
#reduce Foo.foo
theorem t : a = 1 := by rw [hi]
theorem t2 : a = 1 := by exact hi
def usesSorry : Nat := Foo.foo + sorry
example (n : Nat) : Nat := n.inc'.inc'
example : Nat := @Foo.foo
example := (Nat.inc' : Nat → Nat)
"##;

/// `Init.Core`'s own deprecations, read from its `.olean`, and the notes on a replacement
/// (vendored `Lean/Linter/Deprecated.lean:69-91`): a protected replacement, with and without
/// a multi-component prefix; a different namespace, its example named as the use's scope
/// names it (`foo x` under `open Foo`); a different type (`Bar.bar = Bar.bar`), compared at
/// reducible transparency, so abbreviations of one type are no different type.
const IMPORTED: &str = r##"def g := false
def g' := Lean.reduceBool g
example : PUnit.{1} = PUnit.{1} := rfl
theorem s (a b : PUnit.{1}) : a = b := PUnit.subsingleton a b
theorem s2 (p : Nat → Prop) (a b : Subtype p) (h : a.val = b.val) : a = b := Subtype.eq h
theorem s3 (p : Nat → Prop) (a b : Subtype p) (h : a.val = b.val) : a = b := by
  exact Subtype.eq h
open Subtype in
theorem s4 (p : Nat → Prop) (a b : Subtype p) (h : a.val = b.val) : a = b := Subtype.eq h
namespace X
def y := Lean.reduceBool g
end X
abbrev Foo := Nat
namespace Foo
protected def bar : Foo → Foo
  | 0 => 0
  | n + 1 => Foo.bar n + 1
theorem bar_rfl : Foo.bar = Foo.bar := rfl
@[deprecated Foo.bar (since := "2025-01-01")]
def foo : Foo → Foo := id
end Foo
open Foo in
example := foo
abbrev Bar := Nat
@[deprecated Foo.foo (since := "2025-01-01")]
def Bar.bar : Bar → Bar := id
abbrev b : Bar := 31
example := b.bar
open Foo in
example := b.bar
set_option linter.deprecated false in
@[deprecated Foo.bar_rfl (since := "2025-01-01")]
theorem Bar.bar_rfl : Bar.bar = Bar.bar := rfl
example := Bar.bar_rfl
namespace A.B
protected def C := ()
@[deprecated B.C (since := "2025-01-01")]
def D := ()
end A.B
open A B in
example := D
set_option linter.all false in
set_option linter.deprecated true in
example := A.B.D
"##;

/// `@[deprecated]`'s own two warnings at the attribute, in attribute order with an inline
/// `instance`'s, ahead of `sorry`'s and the class-typed definition's; the use warnings ahead
/// of the unused-variables linter.
const ATTRIBUTES: &str = r##"@[deprecated "x" (since := "2025-01-01")]
def a : Nat := 1
@[deprecated]
def b (n : Nat) : Nat := sorry
@[deprecated a]
def c : Inhabited Nat := ⟨a⟩
@[instance, deprecated "y"]
def d : Inhabited Nat := ⟨b 1⟩
def e (unused : Nat) : Nat := a
@[deprecated "z" (since := "1")] theorem f : True := trivial
example := f
example := (· + a)
example : Nat := .zero
"##;

/// A dotted identifier (`.mk'`), `#guard_msgs` over the warnings, `linter.all` as the
/// default of `linter.deprecated`, a term-level `set_option`, a `variable` binder, theorem,
/// `abbrev`, `axiom`, `instance` and `private` declarations, and a constant receiver of field
/// notation (`instT.default`), reported at its own component.
const KINDS: &str = r##"@[deprecated "use b" (since := "2025-01-01")]
def a : Nat := 1
structure T where
  n : Nat
@[deprecated T.mk (since := "2025-01-01")]
def T.mk' (n : Nat) : T := ⟨n⟩
example : T := .mk' 1
example : Nat := Nat.add a a
/-- warning: `a` has been deprecated: use b -/
#guard_msgs in
example : Nat := a
/--
warning: `a` has been deprecated: use b
---
warning: `a` has been deprecated: use b
-/
#guard_msgs in
example : Nat := Nat.add a a
set_option linter.all false in
example : Nat := a
example : Nat := set_option linter.deprecated false in a
variable (x : Fin a)
theorem th : a = a := rfl
@[deprecated th (since := "2025-01-01")]
theorem th' : a = a := rfl
example : a = a := th'
@[deprecated (since := "2025-01-01")]
abbrev ab := 2
example := ab
@[deprecated "no" (since := "2025-01-01")]
axiom ax : Nat
theorem tax : ax = ax := rfl
@[deprecated "inst" (since := "2025-01-01")]
instance instT : Inhabited T := ⟨⟨a⟩⟩
example : T := instT.default
private def p := 3
@[deprecated p (since := "2025-01-01")]
private def q := 3
example := q
"##;

/// Where the pin elaborates twice or out of order: a structure's field types before its
/// defaults; a `match` on an identifier, whose discriminant is elaborated once more before
/// the match (`tryPostponeIfDiscrTypeIsMVar`); instances, inductive types, default
/// arguments, binders, `let` and tactics.
const ORDER: &str = r##"@[deprecated "use b" (since := "2025-01-01")]
def a : Nat := 1
instance : Inhabited (Fin (a + 1)) := ⟨⟨0, Nat.zero_lt_succ a⟩⟩
structure S where
  x : Nat := a
  y : Fin a
inductive I where
  | mk : Fin a → I
def od (n : Nat) : Bool := a == n







def f (n : Nat := a) : Nat := n
example : Nat := f
example : Nat := (fun (x : Nat) => x + a) a
example : Nat := let y := a; y
example : Nat := match a with
  | 0 => a
  | _ => 1
theorem t (h : a = 1) : a = 1 := by
  exact h
theorem t2 : a = 1 := by
  rfl
theorem t3 : True := by
  have : a = a := rfl
  trivial
"##;

/// Structure instances, anonymous constructors, `if`, `show`, a field of a constant, `<|`; a
/// `match` on two identifiers reports both, then both again; `match c with | y => e` reports
/// once (`expandSimpleMatch`), and so does a non-atomic discriminant.
const NOTATIONS: &str = r##"@[deprecated "use b" (since := "2025-01-01")]
def a : Nat := 1
structure P where
  x : Nat
  y : Nat
example : P := { x := a, y := a }
example : P := ⟨a, a⟩
example : Nat := if a = 1 then a else 0
example : Nat := (a : Nat)
example : Nat := show Nat from a
example : Nat := a.succ
example : Nat := a |>.succ
example : Nat := Nat.succ <| a
example : Nat := match a, a with
  | 0, _ => 1
  | _, _ => 2
example : Nat := match a with
  | y => y
example : Nat := match a + 1 with
  | 0 => 1
  | _ => 2
example (n : Nat) : Nat := match n with
  | 0 => a
  | _ => 2



example : Prop := ∀ n : Fin a, n = n
example : Nat := ((fun x => x) : Nat → Nat) a
"##;

/// Each program, the deprecation warnings and the attribute warnings the pin prints for it.
const PROGRAMS: &[(&str, &str, usize, usize)] = &[
    ("source", SOURCE, 18, 2),
    ("imported", IMPORTED, 12, 0),
    ("attributes", ATTRIBUTES, 3, 4),
    ("kinds", KINDS, 14, 1),
    ("order", ORDER, 18, 0),
    ("notations", NOTATIONS, 20, 0),
];

/// `#guard_msgs` expecting each kind of warning, a note included, is judged, as at the pin
/// (upstream `tests/elab/7993.lean`, `4636.lean`): the matching guards pass and print nothing.
const GUARDED: &str = r##"abbrev Foo := Nat
namespace Foo
protected def bar : Foo → Foo
  | 0 => 0
  | n + 1 => Foo.bar n + 1
@[deprecated Foo.bar (since := "2025-01-01")]
def foo : Foo → Foo := id
end Foo
/--
warning: `Foo.foo` has been deprecated: Use `Foo.bar` instead

Note: `Foo.bar` is protected. References to this constant must include its prefix `Foo` even when inside its namespace.
-/
#guard_msgs in
open Foo in
example := foo
/--
warning: `[deprecated]` attribute should specify either a new name or a deprecation message
---
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs in
@[deprecated] def old : Nat := 1
/-- warning: `old` has been deprecated -/
#guard_msgs in
example : Nat := old
/--
warning: `Lean.reduceBool` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
-/
#guard_msgs in
def g := Lean.reduceBool false
"##;

/// A guard expecting the wrong text fails at both.
const MISGUARDED: &str = r##"@[deprecated "x" (since := "2025-01-01")] def old : Nat := 1
/-- warning: `old` has been deprecated: y -/
#guard_msgs in
example : Nat := old
"##;

fn pinned_toolchain() -> Option<PathBuf> {
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
        "fln-deprecated-constants-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The runs of this crate's `lean` and of the pinned `lean` on `HEADER` + `program`.
fn runs(lib: &Path, root: &Path, name: &str, program: &str) -> [(PathBuf, Output); 2] {
    let entry = format!("{name}.lean");
    std::fs::write(root.join(&entry), format!("{HEADER}{program}")).unwrap();
    let pinned = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .expect("the pinned toolchain's lean");
    [PathBuf::from(env!("CARGO_BIN_EXE_lean")), pinned].map(|binary| {
        let output = Command::new(&binary)
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run lean");
        (binary, output)
    })
}

/// The stdout of this crate's `lean` and of the pinned `lean` on `HEADER` + `program`, both of
/// which must accept it.
fn outputs(lib: &Path, root: &Path, name: &str, program: &str) -> (String, String) {
    let [ours, pinned] = runs(lib, root, name, program).map(|(binary, output)| {
        assert_eq!(
            output.status.code(),
            Some(0),
            "{name}: {}\n{}",
            binary.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8(output.stdout).expect("UTF-8 output")
    });
    (ours, pinned)
}

#[test]
fn deprecation_warnings_match_the_pin() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    for &(name, program, deprecated, attributes) in PROGRAMS {
        let (ours, pinned) = outputs(&lib, &root, name, program);
        assert_eq!(ours, pinned, "{name}: {program}");
        // The programs must actually exercise the warnings.
        assert_eq!(
            ours.matches("has been deprecated").count(),
            deprecated,
            "{name}: {ours}"
        );
        assert_eq!(
            ours.matches("attribute should specify").count(),
            attributes,
            "{name}: {ours}"
        );
    }
}

#[test]
fn guards_expecting_deprecation_warnings_are_judged() {
    let Some(lib) = pinned_toolchain() else {
        return;
    };
    let root = workspace();
    let (ours, pinned) = outputs(&lib, &root, "guarded", GUARDED);
    assert_eq!(ours, pinned, "guarded: {GUARDED}");
    assert_eq!(ours, "", "the matching guards print nothing");
    let [ours, pinned] =
        runs(&lib, &root, "misguarded", MISGUARDED).map(|(_, output)| output.status.code());
    assert_eq!(pinned, Some(1), "the pin refuses the mismatched guard");
    assert_eq!(ours, Some(1), "this door refuses it too: {MISGUARDED}");
}
