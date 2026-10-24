//! Optional (`optParam`) and tactic (`autoParam`) parameters in `#check` output, through the
//! installed drop-in `lean`. `#check c` for an identifier naming a constant prints its signature
//! without elaborating it (`elabCheckCore`, vendored `Lean/Elab/BuiltinCommand.lean:434-443`), with
//! a defaulted parameter as `(m : Nat := 3)` (`delabParamsAux`); an application prints in the
//! pin's explicit mode, headed by `@`, when the next parameter is implicit or a later explicit one
//! has a default (`useAppExplicit`, `needsExplicit`), and otherwise drops its trailing arguments
//! equal to their defaults (`delabAppImplicitCore`, vendored
//! `PrettyPrinter/Delaborator/Builtins.lean:160-501`). A structure instance omits a field equal to
//! its default (`collectStructFields`).
//!
//! Each program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// Defaults of a source definition, trailing, leading, dependent and grouped.
const FUNCTIONS: &str = r#"prelude
import Init.Core
def f (n : Nat) (m : Nat := 3) : Nat := n + m
#check f
#check f 1
#check @f
#check f 1 3
#check f 1 4
#check (f)
#check @f 1
#check @f 1 3
def g (a : Nat := 3) (b : Nat) : Nat := a + b
#check g
#check g 3 4
#check g 5 4
#check @g
#check g 3
def h (n : Nat) (m : Nat := n) : Nat := n + m
#check h
#check h 1
#check h 1 1
#check h 1 2
def chain (a : Nat := 3) (b : Nat := a + 1) : Nat := a + b
#check chain
#check (chain)
#check chain 5
#check chain 5 6
#check chain 3 5
def q (a b : Nat := 3) : Nat := a + b
#check q
#check q 3 4
#print f
"#;

/// The pin's output for [`FUNCTIONS`]. Only trailing arguments equal to their defaults are
/// dropped: `g 3 4` keeps its leading `3`, and `chain 3 5` its `3`.
const FUNCTIONS_EXPECTED: &str = "f (n : Nat) (m : Nat := 3) : Nat
f 1 : Nat
@f : Nat → optParam Nat 3 → Nat
f 1 : Nat
f 1 4 : Nat
fun n => f n : Nat → Nat
@f 1 : optParam Nat 3 → Nat
f 1 : Nat
g (a : Nat := 3) (b : Nat) : Nat
g 3 4 : Nat
g 5 4 : Nat
@g : optParam Nat 3 → Nat → Nat
g : Nat → Nat
h (n : Nat) (m : Nat := n) : Nat
h 1 : Nat
h 1 : Nat
h 1 2 : Nat
chain (a : Nat := 3) (b : Nat := a + 1) : Nat
chain : Nat
chain 5 : Nat
chain 5 6 : Nat
chain 3 5 : Nat
q (a b : Nat := 3) : Nat
q 3 4 : Nat
def f : Nat → optParam Nat 3 → Nat :=
fun n m => n + m
";

/// Implicit and strict implicit parameters beside defaults, explicit mode for partial
/// applications, and a signature's binder names after its colon.
const MODES: &str = r#"prelude
import Init.Core
def k {α : Type} (x : α) (y : Nat := 0) : α := (fun _ => x) y
#check k
#check k 1
#check @k
#check @k Nat
#check k 1 0
#check k 1 2
#check @k Nat 1
#check @k Nat 1 0
def s ⦃n : Nat⦄ (m : Nat) : Nat := m + n
#check @s
#check (s)
def w {α : Type} (x : α) {β : Type} (y : β) : β := (fun _ => y) x
#check @w Nat 1
#check @w Nat 1 Bool
#check @w Nat 1 Bool true
#check @w
#check @List.map Nat
def r : Nat → (k : Nat) → Nat := fun _ k => k
#check r
#check @r
def r2 (a : Nat) : Nat → (k j : Nat) → Nat := fun _ k _ => k + a
#check r2
def r4 : Nat → {k : Nat} → (h : k = k) → Nat := fun _ _ _ => 0
#check r4
"#;

/// The pin's output for [`MODES`]. A strict implicit first parameter does not select explicit
/// mode; an implicit one after the supplied arguments does (`@w Nat 1`, `@List.map Nat`). After
/// a signature's colon, a binder with an accessible name shows it (`(k : Nat) → Nat`), while the
/// term `@r` prints its type as an arrow.
const MODES_EXPECTED: &str = "k {α : Type} (x : α) (y : Nat := 0) : α
k 1 : Nat
@k : {α : Type} → α → optParam Nat 0 → α
@k Nat : Nat → optParam Nat 0 → Nat
k 1 : Nat
k 1 2 : Nat
@k Nat 1 : optParam Nat 0 → Nat
k 1 : Nat
s : ⦃n : Nat⦄ → Nat → Nat
s : ⦃n : Nat⦄ → Nat → Nat
@w Nat 1 : {β : Type} → β → β
w 1 : Bool → Bool
w 1 true : Bool
@w : {α : Type} → α → {β : Type} → β → β
@List.map Nat : {β : Type u_1} → (Nat → β) → List Nat → List β
r : Nat → (k : Nat) → Nat
r : Nat → Nat → Nat
r2 (a : Nat) : Nat → (k j : Nat) → Nat
r4 : Nat → {k : Nat} → (h : k = k) → Nat
";

/// A constructor's default, structure field defaults, and class methods.
const DATA: &str = r#"prelude
import Init.Core
inductive T where
  | a (n : Nat) (m : Nat := 3)
#check T.a
#check T.a 1
#check T.a 1 3
#check @T.a
#check T.a 1 4
#check @T.rec
structure S where
  x : Nat := 3
#check S.mk
#check ({} : S)
#check S.mk 3
#check ({ x := 4 } : S)
#check @S.mk
structure P (α : Type) where
  x : α
  y : Nat := 7
  z : Bool := true
#check ({ x := 1 } : P Nat)
#check ({ x := 1, y := 8 } : P Nat)
#check ({ x := 1, z := false } : P Nat)
structure Q where
  a : Nat
  b : Nat := a
#check ({ a := 1 } : Q)
#check ({ a := 1, b := 2 } : Q)
class D (α : Type) where
  op : α → (n : Nat := 3) → α
#check D.op
#check @D.op
class E (α : Type) where
  val : Nat := 3
#check E.val
"#;

/// The pin's output for [`DATA`]. The constructor keeps its `optParam`; its recursor's minor
/// premise does not (`consumeTypeAnnotations`). A structure's default lives beside it, not in
/// its constructor's type, and a field equal to it is omitted, a dependent one (`b := a`) at
/// the value of the field it reads.
const DATA_EXPECTED: &str = "T.a (n : Nat) (m : Nat := 3) : T
T.a 1 : T
T.a 1 : T
@T.a : Nat → optParam Nat 3 → T
T.a 1 4 : T
@T.rec : {motive : T → Sort u_1} → ((n m : Nat) → motive (T.a n m)) → (t : T) → motive t
S.mk (x : Nat) : S
{ } : S
{ } : S
{ x := 4 } : S
S.mk : Nat → S
{ x := 1 } : P Nat
{ x := 1, y := 8 } : P Nat
{ x := 1, z := false } : P Nat
{ a := 1 } : Q
{ a := 1, b := 2 } : Q
D.op {α : Type} [self : D α] : α → (n : optParam Nat 3) → α
@D.op : {α : Type} → [self : D α] → α → optParam Nat 3 → α
E.val (α : Type) [self : E α] : Nat
";

/// Imported defaults and a tactic default, from the pinned `Init`.
const IMPORTED: &str = r#"prelude
import Init.Data.Array.Basic
#check @Array.back
#check Array.extract
#check @Array.extract
#check fun (as : Array Nat) => as.extract
#check fun (as : Array Nat) => as.extract 1
#check fun (as : Array Nat) => as.extract 0 2
"#;

/// The pin's output for [`IMPORTED`].
const IMPORTED_EXPECTED: &str = "@Array.back : {α : Type u_1} → (xs : Array α) → autoParam (0 < xs.size) Array.back._auto_1 → α
Array.extract.{u_1} {α : Type u_1} (as : Array α) (start : Nat := 0) (stop : Nat := as.size) : Array α
@Array.extract : {α : Type u_1} → (as : Array α) → optParam Nat 0 → optParam Nat as.size → Array α
fun as => as.extract : Array Nat → Array Nat
fun as => as.extract 1 : Array Nat → Array Nat
fun as => as.extract 0 2 : Array Nat → Array Nat
";

/// A signature with a tactic default: the pin prints `(h : 0 < xs.size := by get_elem_tactic)`,
/// reading the tactic by evaluating `Array.back._auto_1`, which this door does not do.
const TACTIC_SIGNATURE: &str = "prelude
import Init.Data.Array.Basic
#check Array.back
";

/// A field the pin compares with its default by a reducible `isDefEq` (`1 + 2` against `3`:
/// the pin prints `{ } : S`), which is not decided here.
const UNDECIDED_DEFAULT: &str = "prelude
import Init.Core
structure S where
  x : Nat := 3
#check ({ x := 1 + 2 } : S)
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
        "fln-check-optional-{}-{}",
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
    let entry = root.join("Optional.lean");
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

/// `program` prints `expected`, as the pinned binary does when it is present.
fn prints_as_the_pin(program: &str, expected: &str) {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, program);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, expected);
    if let Some((code, stdout)) = pinned(&lib, &root.join("Optional.lean")) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
}

/// `program` is refused as a capability the door lacks, naming `what`, where the pin prints.
fn is_refused(program: &str, what: &str) {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, program);
    assert_ne!(code, Some(0), "stdout: {stdout}");
    assert!(stdout.is_empty(), "stdout: {stdout}");
    assert!(stderr.contains(what), "stderr: {stderr}");
    if let Some((code, _)) = pinned(&lib, &root.join("Optional.lean")) {
        assert_eq!(code, 0, "the pin prints this program");
    }
}

#[test]
fn defaulted_parameters_print_their_signatures_and_omit_trailing_defaults_as_at_the_pin() {
    prints_as_the_pin(FUNCTIONS, FUNCTIONS_EXPECTED);
}

#[test]
fn implicit_and_defaulted_parameters_choose_the_pins_application_mode() {
    prints_as_the_pin(MODES, MODES_EXPECTED);
}

#[test]
fn constructor_structure_and_class_defaults_print_as_at_the_pin() {
    prints_as_the_pin(DATA, DATA_EXPECTED);
}

#[test]
fn imported_defaults_and_tactic_parameters_print_as_at_the_pin() {
    prints_as_the_pin(IMPORTED, IMPORTED_EXPECTED);
}

#[test]
fn a_signature_with_a_tactic_default_is_refused() {
    is_refused(TACTIC_SIGNATURE, "a parameter whose default is a tactic");
}

#[test]
fn a_field_only_definitionally_equal_to_its_default_is_refused() {
    is_refused(
        UNDECIDED_DEFAULT,
        "a structure field that may be definitionally equal to its default",
    );
}
