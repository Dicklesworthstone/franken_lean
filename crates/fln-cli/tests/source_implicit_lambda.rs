//! The implicit lambda, through the installed drop-in `lean` over `prelude` with `Init.Tactics`.
//! The pin elaborates a term whose expected type starts with an implicit or instance-implicit
//! binder inside `fun {a…} =>`, against the type that remains (`useImplicitLambda`,
//! `elabImplicitLambda`, vendored `Lean/Elab/Term/TermElabM.lean:1704-1793`), so
//! `example : ∀ {a : Nat}, a = a := rfl` is accepted. Here such a term was elaborated against the
//! whole type, and every accepted program in the first test was refused.
//!
//! `@f`, `@f a`, `fun` with an implicit binder, holes, `by` and type ascriptions get no implicit
//! lambda (`blockImplicitLambda`). Neither does a term elaborated as `no_implicit_lambda% t`, which
//! the `have`, `let`, `suffices`, `let rec` and `match` tactics are built on (`refine_lift`,
//! vendored `src/Init/Tactics.lean:832-941`, `Lean/Elab/Tactic/Match.lean:58`). The annotation
//! stays on the goal those tactics leave, so `exact rfl` against `∀ {a : Nat}, a = a` is refused
//! after them and accepted after `show`.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-29),
//! and the pin is consulted again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Tactics\n";

const EQ: &str = "inductive EQ {α : Type} (a : α) : α → Type where\n  | refl : EQ a a\n\
def EQ.trans {α : Type} {a b c : α} (h₁ : EQ a b) (h₂ : EQ b c) : EQ a c := by\n  \
cases h₁; cases h₂; constructor\n";

/// Programs the pin accepts, printing nothing, each needing the implicit lambda: a constant whose
/// implicit binders do not line up with the expected ones, an argument, an instance binder, a
/// structure field, an instance field (`tests/elab/calcInType.lean`), `exact` and `refine`.
const ACCEPTED: &[&str] = &[
    "example : ∀ {a : Nat}, a = a := rfl\n",
    "example : ∀ {a : Nat}, a = a := (rfl)\n",
    "example : ∀ {a b : Nat}, a = b → b = a := Eq.symm\n",
    "def f (g : ∀ {α : Type}, α → α) : Nat := g 1\nexample : Nat := f (Function.comp id id)\n",
    "theorem h (k : ∀ {a b : Nat}, a = b → b = a) : 0 = 0 := k rfl\nexample : 0 = 0 := h Eq.symm\n",
    "example : ∀ {α : Type} [Inhabited α], Inhabited α := inferInstance\n",
    "example : ∀ [Inhabited Nat], Nat := default\n",
    "structure S where\n  f : ∀ {n : Nat}, n = n\nexample : S := ⟨rfl⟩\nexample : S := { f := rfl }\n",
    "example : ∀ {a : Nat}, a = a := by exact rfl\n",
    "example : ∀ {a : Nat}, a = a := by refine rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  show ∀ {a : Nat}, a = a\n  exact rfl\n",
    "def foo2mk (_ : ∀ {α : Type} (a : α), a = a) : Nat := 37\n\
     example (x) : foo2mk x = foo2mk x := rfl\n",
    "example : ∀ {a b : Nat}, a + b = a + b := fun {_} => rfl\n",
];

/// Programs the pin accepts, printing nothing, whose terms need the implicit lambda after a
/// definition made earlier in the program.
const ACCEPTED_AFTER_EQ: &[&str] = &[
    "example : ∀ {a b c : Nat}, EQ a b → EQ b c → EQ a c := EQ.trans\n",
    "instance : Trans (@EQ α) (@EQ α) (@EQ α) where\n  trans := EQ.trans\n",
];

/// Programs the pin rejects: the blocked forms, a strict-implicit binder (which does not trigger
/// the feature), and a body that fails under the binders.
const REFUSED: &[&str] = &[
    "example : ∀ {a : Nat}, a = a := @rfl\n",
    "example : ∀ {a : Nat}, a = a := (rfl : _)\n",
    "example : ∀ {a : Nat}, a = a := _\n",
    "example : ∀ ⦃a : Nat⦄, a = a := rfl\n",
    "example : ∀ {a : Nat}, a = a + 1 := rfl\n",
];

/// Tactic proofs the pin accepts: the goal a `refine_lift` tactic leaves keeps its binders, which
/// `intro` then introduces.
const TACTICS_ACCEPTED: &[&str] = &[
    "example (n : Nat) : ∀ {a : Nat}, a = a := by\n  match n with\n  | _ => intro a; rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  suffices h : True by intro a; rfl\n  trivial\n",
    "example : ∀ {a : Nat}, a = a := by\n  let rec f : Nat := 0\n  intro a; rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  have _h : True := True.intro\n  intro a\n  exact rfl\n",
    "example (n : Nat) : ∀ {a : Nat}, n + a = n + a := by\n  match n with\n  | _ => intro a; exact rfl\n",
    "example (b : Bool) : ∀ {a : Bool}, (b || a) = (b || a) := by\n  match b with\n  \
     | true => intro a; exact rfl\n  | false => intro a; exact rfl\n",
];

/// Tactic proofs the pin rejects: after a `refine_lift` tactic, `exact` and `refine` get no
/// implicit lambda, and `rfl` meets the binders. A `match` alternative whose type the motive
/// changed (`x✝ + a`, `true || a`) keeps the annotation too.
const TACTICS_REFUSED: &[&str] = &[
    "example (n : Nat) : ∀ {a : Nat}, n + a = n + a := by\n  match n with\n  | _ => exact rfl\n",
    "example (b : Bool) : ∀ {a : Bool}, (b || a) = (b || a) := by\n  match b with\n  \
     | true => exact rfl\n  | false => exact rfl\n",
    "example (n : Nat) : ∀ {a : Nat}, a = a := by\n  match n with\n  | _ => rfl\n",
    "example (n : Nat) : ∀ {a : Nat}, a = a := by\n  match n with\n  | _ => exact rfl\n",
    "example (n : Nat) : ∀ {a : Nat}, a = a := by\n  match n with\n  | _ => ?r\n  case r => exact rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  suffices h : True by exact rfl\n  trivial\n",
    "example : ∀ {a : Nat}, a = a := by\n  let rec f : Nat := 0\n  exact rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  have _h : True := True.intro\n  exact rfl\n",
    "example : ∀ {a : Nat}, a = a := by\n  let _x := 1\n  refine rfl\n",
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
        "fln-implicit-lambda-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s exit code and stdout on `entry`, when the binary is present.
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

/// Each program, after `prelude`, must be accepted with `stdout` by the pin and here.
fn accepted(lib: &Path, root: &Path, tag: &str, programs: &[&str], prefix: &str, stdout: &str) {
    for (index, program) in programs.iter().enumerate() {
        let entry = root.join(format!("{tag}{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{prefix}{program}")).unwrap();
        if let Some((code, out)) = pinned(lib, &entry) {
            assert_eq!(
                (code, out.as_str()),
                (0, stdout),
                "the pin moved: {program}"
            );
        }
        let (code, out, stderr) = ours(lib, root, &entry);
        assert_eq!((code, out.as_str()), (0, stdout), "{program}: {stderr}");
    }
}

/// Each program, after `prelude`, must be rejected by the pin and refused here.
fn refused(lib: &Path, root: &Path, tag: &str, programs: &[&str]) {
    for (index, program) in programs.iter().enumerate() {
        let entry = root.join(format!("{tag}{index}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        if let Some((code, _)) = pinned(lib, &entry) {
            assert_eq!(code, 1, "the pin rejects {program}");
        }
        let (code, stdout, stderr) = ours(lib, root, &entry);
        assert_ne!(code, 0, "{program}: {stdout}");
        assert!(stderr.contains("refused"), "{program}: {stderr}");
    }
}

#[test]
fn terms_against_leading_implicit_binders_get_an_implicit_lambda() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Accepted", ACCEPTED, "", "");
    accepted(&lib, &root, "AfterEq", ACCEPTED_AFTER_EQ, EQ, "");
    // The binder is the expected type's, under a fresh macro scope, printed as the pin prints it.
    accepted(
        &lib,
        &root,
        "Printed",
        &["theorem g : ∀ {a : Nat}, a = a := rfl\n#print g\n"],
        "",
        "@[defeq] theorem g : ∀ {a : Nat}, a = a :=\nfun {a} => rfl\n",
    );
    refused(&lib, &root, "Refused", REFUSED);
}

#[test]
fn goals_left_by_refine_lift_tactics_get_no_implicit_lambda() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Tactics", TACTICS_ACCEPTED, "", "");
    refused(&lib, &root, "TacticsRefused", TACTICS_REFUSED);
}
