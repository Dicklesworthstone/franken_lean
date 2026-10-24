//! Equation theorems `f.eq_<n>`, `f.eq_def` and `f.eq_unfold`, generated when a command names
//! them, and `rw [f]` through them (the pin's `Lean.Meta.Eqns` reserved-name action and
//! `withRWRulesSeq`, vendored `Lean/Meta/Eqns.lean`, `Lean/Elab/Tactic/Rewrite.lean`).
//!
//! Through the installed `lean` over `prelude` with `Init.Core`. Every program was run through
//! the pinned `lean` v4.32.0 first (2026-10-24): the expected output below is the pin's stdout,
//! and each program is compared with the pinned binary again when it is present. A program
//! the pin accepts and this engine does not generate the equations for is refused with the
//! capability exit, never accepted with other statements.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

/// Programs the pin accepts, and its stdout.
const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "nonrecursive_statements",
        "def dist (n m : Nat) := n - m + (m - n)
#check @dist.eq_1
#check @dist.eq_def
#check @dist.eq_unfold
#check dist.eq_1
def answer := 42
#check @answer.eq_1
#check @answer.eq_def
#check @answer.eq_unfold
def withLet (n : Nat) : Nat := let k := n + 1; k * k
#check @withLet.eq_1
#check @withLet.eq_def
#check @withLet.eq_unfold
def poly {α : Type} (x : α) (xs : List α) : List α := x :: xs
#check @poly.eq_1
#check @poly.eq_def
#check @poly.eq_unfold
def poly2 (x : α) (xs : List α) : List α := x :: xs
#check @poly2.eq_1
#check poly2.eq_unfold
",
        "dist.eq_1 : ∀ (n m : Nat), dist n m = n - m + (m - n)
dist.eq_def : ∀ (n m : Nat), dist n m = n - m + (m - n)
dist.eq_unfold : dist = fun n m => n - m + (m - n)
dist.eq_1 (n m : Nat) : dist n m = n - m + (m - n)
answer.eq_1 : answer = 42
answer.eq_def : answer = 42
answer.eq_unfold : answer = 42
withLet.eq_1 : ∀ (n : Nat), withLet n = (n + 1) * (n + 1)
withLet.eq_def : ∀ (n : Nat),
  withLet n =
    have k := n + 1;
    k * k
withLet.eq_unfold : withLet = fun n =>
  have k := n + 1;
  k * k
@poly.eq_1 : ∀ {α : Type} (x : α) (xs : List α), poly x xs = x :: xs
@poly.eq_def : ∀ {α : Type} (x : α) (xs : List α), poly x xs = x :: xs
poly.eq_unfold : @poly = fun {α} x xs => x :: xs
@poly2.eq_1 : ∀ {α : Type u_1} (x : α) (xs : List α), poly2 x xs = x :: xs
poly2.eq_unfold.{u_1} : @poly2 = fun {α} x xs => x :: xs
",
    ),
    (
        "terms_and_rewrites",
        "def dist (n m : Nat) := n - m + (m - n)
def answer := 42
def withLet (n : Nat) : Nat := let k := n + 1; k * k
theorem t1 (n m : Nat) : dist n m = n - m + (m - n) := dist.eq_1 n m
theorem t2 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist]
theorem t3 (n : Nat) : withLet n = (n + 1) * (n + 1) := by rw [withLet]
theorem t4 : answer + 0 = 42 := by rw [answer]
theorem t5 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist.eq_def]
theorem t6 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist.eq_unfold]
example : dist 3 5 = 2 := by rw [dist]
namespace Foo
def twice (n : Nat) : Nat := n + n
theorem t7 (n : Nat) : twice n = n + n := twice.eq_1 n
end Foo
#check @Foo.twice.eq_1
",
        "Foo.twice.eq_1 : ∀ (n : Nat), Foo.twice n = n + n\n",
    ),
    (
        "locations_scopes_and_privacy",
        "def wrap (n : Nat) : Nat := n + 1
theorem h1 (n : Nat) (h : wrap n = 5) : n + 1 = 5 := by rw [wrap] at h; exact h
theorem h2 (n : Nat) : wrap (wrap n) = n + 1 + 1 := by rw [wrap, wrap]
theorem h3 (n : Nat) : n + 1 = wrap n := by rw [← wrap]
private def pw (n : Nat) : Nat := n * 2
theorem h4 (n : Nat) : pw n = n * 2 := pw.eq_1 n
#check @pw.eq_1
namespace A
def g (n : Nat) := n + 3
end A
open A in
theorem h5 : g 1 = 1 + 3 := g.eq_1 1
theorem h6 : A.g 1 = 1 + 3 := by rw [A.g]
",
        "pw.eq_1 : ∀ (n : Nat), pw n = n * 2\n",
    ),
    (
        "operands_ending_in_fun_or_have",
        "#check ∀ n : Nat, n = (have k := n + 1; k * k)
#check fun n : Nat => n = (have k := n + 1; k * k)
#check (id = fun x : Nat => x)
#check ((fun x : Nat => x) = id)
#check (id = fun x : Nat => x) ∧ True
",
        "∀ (n : Nat),
  n =
    have k := n + 1;
    k * k : Prop
fun n =>
  n =
    have k := n + 1;
    k * k : Nat → Prop
id = fun x => x : Prop
(fun x => x) = id : Prop
(id = fun x => x) ∧ True : Prop
",
    ),
];

/// Programs the pin refuses, and a line of this engine's refusal.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "beyond_the_equations",
        "def dist (n m : Nat) := n - m + (m - n)\n#check dist.eq_2\n",
        "Unknown identifier `dist.eq_2`",
    ),
    (
        "wrong_statement",
        "def dist (n m : Nat) := n - m + (m - n)\ntheorem bad (n m : Nat) : dist n m = n + m := dist.eq_1 n m\n",
        "",
    ),
    (
        "rewrite_then_false",
        "def answer := 42\ntheorem bad : answer = 41 := by rw [answer]\n",
        "",
    ),
    (
        "no_equation_rewrites",
        "def answer := 42\ntheorem y (n : Nat) : n = n + 0 := by rw [answer]\n",
        "Failed to rewrite using equation theorems for `answer`",
    ),
];

/// Programs the pin accepts whose equations this engine does not generate yet: each is
/// refused with the capability exit, naming the theorem.
const NOT_GENERATED: &[(&str, &str, &str)] = &[
    (
        "structural_by_matching",
        "def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
#check @fib.eq_3
",
        "the equation theorem `fib.eq_3` of `fib` is not generated here",
    ),
    (
        "rewrite_structural",
        "def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
theorem b (n : Nat) : fib (n+2) = fib n + fib (n+1) := by rw [fib]
",
        "the equation theorem `fib.eq_1` of `fib` is not generated here",
    ),
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
        "fln-equation-theorems-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

/// The installed `lean` on `HEADER` + `program`, and the pinned binary's run when present.
fn run(lib: &Path, root: &Path, name: &str, program: &str) -> (Run, Option<Run>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let collect = |output: std::process::Output| Run {
        code: output.status.code().expect("normal process exit"),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    };
    let ours = collect(
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&entry)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run the installed lean"),
    );
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            collect(
                Command::new(pinned)
                    .arg(&entry)
                    .current_dir(root)
                    .env("LEAN_PATH", lib)
                    .output()
                    .expect("run the pinned lean"),
            )
        });
    (ours, theirs)
}

#[test]
fn equation_theorems_are_the_pins_and_rewrite_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program, expected) in ACCEPTED {
        let (ours, pinned) = run(&lib, &root, name, program);
        assert_eq!(ours.code, 0, "{name}: {program}\n{}", ours.stderr);
        assert_eq!(&ours.stdout, expected, "{name}");
        if let Some(pinned) = pinned {
            assert_eq!(pinned.code, 0, "{name}: the pinned lean refuses it");
            assert_eq!(&pinned.stdout, expected, "{name}: the pin's stdout moved");
        }
    }
    for (name, program, message) in REFUSED {
        let (ours, pinned) = run(&lib, &root, name, program);
        assert_ne!(ours.code, 0, "{name}: accepted {program}");
        assert_ne!(
            ours.code, 5,
            "{name}: a capability refusal\n{}",
            ours.stderr
        );
        assert!(ours.stderr.contains(message), "{name}: {}", ours.stderr);
        if let Some(pinned) = pinned {
            assert_ne!(pinned.code, 0, "{name}: the pinned lean accepts it");
            assert!(pinned.stdout.contains(message), "{name}: {}", pinned.stdout);
        }
    }
    for (name, program, message) in NOT_GENERATED {
        let (ours, pinned) = run(&lib, &root, name, program);
        assert_eq!(ours.code, 5, "{name}: {program}\n{}", ours.stderr);
        assert!(ours.stderr.contains(message), "{name}: {}", ours.stderr);
        assert!(ours.stdout.is_empty(), "{name}: {}", ours.stdout);
        if let Some(pinned) = pinned {
            assert_eq!(pinned.code, 0, "{name}: the pinned lean refuses it");
        }
    }
}
