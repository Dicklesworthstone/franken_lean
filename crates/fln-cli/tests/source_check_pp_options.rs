//! The pin's pretty-printer options (`set_option pp.… in`), through the installed drop-in
//! `lean`. The options are the ones the pin's delaborator reads (`getPP*`, vendored
//! `Lean/PrettyPrinter/Delaborator/Options.lean`), with the defaults `pp.all` gives them, and
//! each holds only in its command's scope. An option combination the printer does not
//! reproduce is refused, typed, rather than printed another way.
//!
//! Each program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-25), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// `pp.explicit`, `pp.universes`, `pp.notation`, `pp.coercions`, `pp.natLit`,
/// `pp.numericTypes`, `pp.proofs` and `pp.beta`, each in a `set_option … in` scope.
const EXPLICIT: &str = r##"prelude
import Init.Core
set_option linter.unusedVariables false
variable (n k : Nat) (p q : Prop)
set_option pp.explicit true in
#check n + k
set_option pp.explicit true in
#check (2 : Nat)
set_option pp.explicit true in
#check fun (x : Nat) => x + 1
set_option pp.explicit true in
#check p ∧ ¬q
set_option pp.explicit true in
#check Nat.succ n
set_option pp.explicit true in
#check @id
set_option pp.universes true in
#check n = k
set_option pp.universes true in
#check p ↔ q
set_option pp.universes true in
#check Nat.succ n
set_option pp.universes true in
#check (2 : Nat)
set_option pp.universes true in
#check @Nat.rec
set_option pp.universes true in
set_option pp.explicit true in
#check Nat.succ n
set_option pp.notation false in
#check n + k
set_option pp.notation false in
#check p ∧ ¬q
set_option pp.notation false in
#check ∀ x : Nat, x = x
set_option pp.notation false in
#check (2 : Nat)
set_option pp.coercions false in
#check (2 : Nat) + n
set_option pp.natLit true in
#check nat_lit 2
set_option pp.natLit true in
#check 2
set_option pp.numericTypes true in
#check 2 + 1 = 3
set_option pp.proofs true in
#check (⟨Nat.le_refl 0, Nat.le_refl 1⟩ : 0 ≤ 0 ∧ 1 ≤ 1)
#check (⟨Nat.le_refl 0, Nat.le_refl 1⟩ : 0 ≤ 0 ∧ 1 ≤ 1)
set_option pp.proofs false in
#check (⟨Nat.le_refl 0, Nat.le_refl 1⟩ : 0 ≤ 0 ∧ 1 ≤ 1)
set_option pp.beta true in
#check (fun x => x) Nat
"##;

/// The pinned `lean` v4.32.0's output for [`EXPLICIT`] (2026-10-25).
const EXPLICIT_EXPECTED: &str = r##"@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n k : Nat
@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)) : Nat
fun x =>
  @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) x
    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) : Nat → Nat
And p (Not q) : Prop
n.succ : Nat
@id : {α : Sort u_1} → α → α
Eq.{1} n k : Prop
p ↔ q : Prop
n.succ : Nat
2 : Nat
@Nat.rec.{u_1} : {motive : Nat → Sort u_1} →
  motive Nat.zero → ((n : Nat) → motive n → motive n.succ) → (t : Nat) → motive t
n.succ : Nat
HAdd.hAdd n k : Nat
And p (Not q) : Prop
∀ (x : Nat), Eq x x : Prop
2 : Nat
OfNat.ofNat 2 + n : Nat
nat_lit 2 : Nat
2 : Nat
(2 : Nat) + (1 : Nat) = (3 : Nat) : Prop
⟨Nat.le_refl 0, Nat.le_refl 1⟩ : 0 ≤ 0 ∧ 1 ≤ 1
⟨Nat.le_refl 0, Nat.le_refl 1⟩ : 0 ≤ 0 ∧ 1 ≤ 1
⋯ : 0 ≤ 0 ∧ 1 ≤ 1
Nat : Type
"##;

/// `pp.all` and the options it implies (`pp.funBinderTypes`, `pp.letVarTypes`,
/// `pp.piBinderNames`, `pp.fullNames`, `pp.structureInstanceTypes`, …), each one alone, and
/// `pp.foralls`, over terms, signatures, structure instances and `#print`.
const ALL: &str = r##"prelude
import Init.Core
set_option linter.unusedVariables false
variable (n k : Nat)
set_option pp.all true in
#check n + k
set_option pp.all true in
#check fun {α : Type} [inst : Inhabited α] (x : α) => (default : α)
set_option pp.all true in
#check ∀ {α : Type} (x y : α), x = y
set_option pp.all true in
#check (n : Nat) → Fin n → Nat
set_option pp.all true in
#check let x := 1; x + x
set_option pp.all true in
#check "abc"
set_option pp.all true in
#check 'a'
set_option pp.all true in
#check Nat.succ
set_option pp.all true in
#check @Nat.rec
set_option pp.funBinderTypes true in
#check fun {α : Type} (x y : α) => x
set_option pp.funBinderTypes true in
#check fun (a b : Nat) (c : Nat) => a + b + c
set_option pp.letVarTypes true in
#check let x := 1; x + x
set_option pp.piBinderNames true in
#check @Nat.rec
set_option pp.piBinderNames true in
#check Nat → Type
set_option pp.piBinderNames true in
set_option pp.piBinderNames.hygienic true in
#check Nat → Type
set_option pp.foralls false in
#check ∀ (i : Nat), i = i
set_option pp.foralls false in
#check (i : Nat) → True
structure Foo where
  x : Nat
  b : Bool
set_option pp.all true in
#check { x := 10, b := true : Foo }
set_option pp.all true in
set_option pp.universes false in
set_option pp.explicit false in
set_option pp.structureInstances true in
#check { x := 10, b := true : Foo }
set_option pp.fieldNotation false in
#check fun (f : Foo) => f.x
class A (α : Type) where
  one : α
class B (α : Type) extends A α where
  two : α
class C (α : Type) extends A α where
  three : α
class D (α : Type) extends B α, C α
set_option pp.all true in
#print D.toB
set_option pp.all true in
#print D.toC
set_option pp.all true in
def foo [D α] : A α := inferInstance
set_option pp.all true in
#print foo
"##;

/// The pinned `lean` v4.32.0's output for [`ALL`] (2026-10-25).
const ALL_EXPECTED: &str = r##"@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n k : Nat
fun {α : Type} [inst : Inhabited.{1} α] (x : α) =>
  @Inhabited.default.{1} α inst : {α : Type} → [inst : Inhabited.{1} α] → (x : α) → α
∀ {α : Type} (x y : α), @Eq.{1} α x y : Prop
(n : Nat) → Fin n → Nat : Type
let x : Nat := @OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1));
@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) x x : Nat
"abc" : String
'a' : Char
Nat.succ (n : Nat) : Nat
@Nat.rec.{u_1} : {motive : (t : Nat) → Sort u_1} →
  (zero : motive Nat.zero) → (succ : (n : Nat) → (n_ih : motive n) → motive (Nat.succ n)) → (t : Nat) → motive t
fun {α : Type} (x y : α) => x : {α : Type} → α → α → α
fun (a b c : Nat) => a + b + c : Nat → Nat → Nat → Nat
let x : Nat := 1;
x + x : Nat
@Nat.rec : {motive : (t : Nat) → Sort u_1} →
  (zero : motive Nat.zero) → (succ : (n : Nat) → (n_ih : motive n) → motive n.succ) → (t : Nat) → motive t
Nat → Type : Type 1
(a : Nat) → Type : Type 1
(i : Nat) → i = i : Prop
Nat → True : Prop
Foo.mk (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) Bool.true : Foo
{ x := OfNat.ofNat 10, b := Bool.true : Foo } : Foo
fun f => Foo.x f : Foo → Nat
@[implicit_reducible] def D.toB : {α : Type} → [self : D α] → B α :=
fun (α : Type) [self : D α] => self.1
@[implicit_reducible] def D.toC : {α : Type} → [self : D α] → C α :=
fun (α : Type) (self : D α) => @C.mk α (@B.toA α (@D.toB α self)) (@D.three α self)
All.lean:64:0: warning: Definition `foo` of class type must be marked with `@[reducible]` or `@[implicit_reducible]`
def foo : {α : Type} → [D α] → A α :=
fun {α : Type} [inst : D α] => @inferInstance.{1} (A α) (@C.toA α (@D.toC α inst))
"##;

/// Instance arguments in explicit mode under `pp.instances` and `pp.instanceTypes`, with
/// `pp.all` on for the file (the upstream `PPInstances` test, reduced).
const INSTANCES: &str = r##"prelude
import Init.Core
set_option linter.unusedVariables false
class Semiring (α : Type) where add : α → α → α
class Ring (α : Type) where add : α → α → α
class AddCommMonoid (α : Type) where
class Module (α β : Type) [Semiring α] [AddCommMonoid β] where
class SemiNormedGroup (α : Type) where
instance SemiNormedGroup.toAddCommMonoid [SemiNormedGroup α] : AddCommMonoid α := {}
instance Ring.toSemiring [instR : Ring α] : Semiring α := { add := instR.add }
opaque R : Type := Unit
opaque foo (a b : R) : R := a
instance R.Ring : Ring R := { add := foo }
variable {E : Type} [instSNG : SemiNormedGroup E]
set_option pp.all true
set_option pp.instances false in
set_option pp.instanceTypes false in
#check Module R E
set_option pp.instances false in
set_option pp.instanceTypes true in
#check Module R E
set_option pp.instances true in
set_option pp.instanceTypes true in
#check Module R E
"##;

/// The pinned `lean` v4.32.0's output for [`INSTANCES`] (2026-10-25).
const INSTANCES_EXPECTED: &str = r##"@Module R E _ _ : Type
@Module R E (_ : Semiring R) (_ : AddCommMonoid E) : Type
@Module R E (@Ring.toSemiring R (R.Ring : Ring R) : Semiring R)
  (@SemiNormedGroup.toAddCommMonoid E (instSNG : SemiNormedGroup E) : AddCommMonoid E) : Type
"##;

/// Coercions, negative numerals, `∃` and subtypes under `pp.coercions`,
/// `pp.coercions.types`, `pp.universes`, `pp.notation`, `pp.explicit`, `pp.numericTypes` and
/// `pp.funBinderTypes`.
const COERCIONS: &str = r##"prelude
import Init.Data.Int.Basic
import Init.NotationExtra
set_option linter.unusedVariables false
variable (n k : Nat) (i : Int)
set_option pp.all true in
#check (n + k : Int)
set_option pp.coercions false in
#check (n : Int) + 1
set_option pp.coercions.types true in
#check (n : Int) + 1
set_option pp.coercions false in
#check (-2 : Int)
set_option pp.universes true in
#check (-2 : Int)
set_option pp.universes true in
#check -i
set_option pp.notation false in
#check -i
set_option pp.explicit true in
#check (n : Int)
set_option pp.coercions false in
set_option pp.explicit true in
#check (1 : Int) + 3 ^ 2
set_option pp.numericTypes true in
#check (-2 : Int)
set_option pp.all true in
#check (n : Int) = i
set_option pp.funBinderTypes true in
#check ∃ x, x = n
#check ∃ x y : Nat, x = y
set_option pp.funBinderTypes true in
#check ∃ x y : Nat, x = y
set_option pp.funBinderTypes true in
#check { x : Nat // x < 10 }
#check { x : Nat // x < 10 }
set_option pp.notation false in
#check { x : Nat // x < 10 }
"##;

/// The pinned `lean` v4.32.0's output for [`COERCIONS`] (2026-10-25).
const COERCIONS_EXPECTED: &str = r##"@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt n)
  (@Nat.cast.{0} Int instNatCastInt k) : Int
n.cast + OfNat.ofNat 1 : Int
(↑n : Int) + 1 : Int
-OfNat.ofNat 2 : Int
-2 : Int
Neg.neg.{0} i : Int
Neg.neg i : Int
@Nat.cast Int instNatCastInt n : Int
@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (@OfNat.ofNat Int (nat_lit 1) (@instOfNat (nat_lit 1)))
  (@HPow.hPow Int Nat Int (@instHPow Int Nat (@instPowNat Int Int.instNatPow))
    (@OfNat.ofNat Int (nat_lit 3) (@instOfNat (nat_lit 3)))
    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) : Int
(-2 : Int) : Int
@Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt n) i : Prop
∃ (x : Nat), x = n : Prop
∃ x y, x = y : Prop
∃ (x : Nat), ∃ (y : Nat), x = y : Prop
{ x : Nat // x < 10 } : Type
{ x // x < 10 } : Type
Subtype fun x => LT.lt x 10 : Type
"##;

/// A private name under `pp.privateNames`: the pin prints its internal form,
/// `_private.Refused.0.secret`, which this door does not reproduce.
const PRIVATE_NAMES: &str = "prelude
import Init.Core
private def secret : Nat := 42
set_option pp.privateNames true in
#check @secret
";

/// `pp.analyze` switched on: the pin's analyzer is not implemented here.
const ANALYZE: &str = "prelude
import Init.Core
set_option pp.analyze true in
#check Nat.succ
";

/// `pp.raw`: the pin's raw printer is not implemented here, and the option has no row.
const RAW: &str = "prelude
import Init.Core
set_option pp.raw true in
#check Nat.succ
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
        "fln-check-pp-options-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s stdout and exit code on `root/name.lean`, when the binary is present.
fn pinned(lib: &Path, root: &Path, name: &str) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(format!("{name}.lean"))
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `program`, written to `root/name.lean`: its exit code, stdout and
/// stderr. Every program of one test shares `root`'s import records.
fn ours(lib: &Path, root: &Path, name: &str, program: &str) -> (Option<i32>, String, String) {
    std::fs::write(root.join(format!("{name}.lean")), program).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(format!("{name}.lean"))
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
fn prints_as_the_pin(name: &str, program: &str, expected: &str) {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let (code, stdout, stderr) = ours(&lib, &root, name, program);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!(stdout, expected);
    if let Some((code, stdout)) = pinned(&lib, &root, name) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
}

#[test]
fn explicit_universes_notation_coercions_and_literals_print_as_the_pin() {
    prints_as_the_pin("Explicit", EXPLICIT, EXPLICIT_EXPECTED);
}

#[test]
fn pp_all_its_implied_options_and_print_commands_print_as_the_pin() {
    prints_as_the_pin("All", ALL, ALL_EXPECTED);
}

#[test]
fn instance_arguments_under_pp_instances_and_instance_types_print_as_the_pin() {
    prints_as_the_pin("Instances", INSTANCES, INSTANCES_EXPECTED);
}

#[test]
fn coercions_numerals_exists_and_subtypes_print_as_the_pin() {
    prints_as_the_pin("Coercions", COERCIONS, COERCIONS_EXPECTED);
}

/// Each program is refused, naming `what`, where the pin prints it.
#[test]
fn an_option_this_door_does_not_reproduce_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, program, what) in [
        (
            "Refused",
            PRIVATE_NAMES,
            "a private name under `pp.privateNames`",
        ),
        ("Analyze", ANALYZE, "only the pin's default is admitted"),
        ("Raw", RAW, "set_option `pp.raw`: no option row"),
    ] {
        let (code, stdout, stderr) = ours(&lib, &root, name, program);
        assert_ne!(code, Some(0), "{name}: stdout: {stdout}");
        assert!(stdout.is_empty(), "{name}: stdout: {stdout}");
        assert!(stderr.contains(what), "{name}: stderr: {stderr}");
        if let Some((code, _)) = pinned(&lib, &root, name) {
            assert_eq!(code, 0, "{name}: the pin prints this program");
        }
    }
}
