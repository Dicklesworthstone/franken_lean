//! Structural recursion on any strictly smaller value reachable through recursive constructor
//! fields — `fib n` under `n+2`, `len t` under `_ :: _ :: t`, `f l` under `node (node l _) r` —
//! through the installed drop-in `lean`, over `prelude` + `import Init.Data.List.Basic`
//! (bead `fln-structural-course-of-values-ofg4`). The pin's structural elaborator
//! (vendored `Lean/Elab/PreDefinition/Structural/BRecOn.lean`) reads such a call out of the
//! `T.below` dictionary of `T.brecOn`; it tries structural recursion before well-founded
//! recursion (`Lean/Elab/PreDefinition/Main.lean:327-337`), so these definitions reduce by
//! `rfl` and `decide` and depend on no axiom. It compiles the pre-definition, `f._unsafe_rec`
//! (`Lean/Elab/PreDefinition/Basic.lean:280-295`), never the `brecOn` term.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const HEADER: &str = "prelude\nimport Init.Data.List.Basic\nimport Init.Data.Repr\n";

/// The bead's own programs, with the axioms and an evaluation of the deeper Fibonacci.
const BEAD: &str = r#"def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
example : fib 10 = 55 := rfl
example : fib 12 = 144 := by decide

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | (x+2) => half x + 1
theorem half_succ_succ (a : Nat) : half (a + 2) = half a + 1 := rfl

def len : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ :: _ :: t => len t + 2
example : len [1,2,3] = 3 := rfl
#print axioms fib
#eval fib 20
"#;

/// Nested constructor patterns on a user inductive, a three-step list tail and a three-step
/// Nat history. The tree's executable body is its original one: the runtime has no lowering of
/// a user family's `brecOn`.
const DEEP: &str = r#"inductive Tree where
  | leaf : Nat → Tree
  | node : Tree → Tree → Tree

def Tree.sumLeft : Tree → Nat
  | .leaf n => n
  | .node (.leaf n) r => n + Tree.sumLeft r
  | .node (.node l _) r => Tree.sumLeft l + Tree.sumLeft r
example : Tree.sumLeft (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) = 4 := rfl
#eval Tree.sumLeft (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3))
#print axioms Tree.sumLeft

def every3 : List Nat → List Nat
  | a :: _ :: _ :: t => a :: every3 t
  | [a] => [a]
  | [a, _] => [a]
  | [] => []
example : every3 [1,2,3,4,5,6,7] = [1,4,7] := rfl
#eval every3 [1,2,3,4,5,6,7]

def tri : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n+3 => tri n + tri (n+1) + tri (n+2)
example : tri 10 = 230 := by decide
#eval tri 15
#print axioms tri
"#;

/// A fixed parameter before the decreasing one, and auto-bound universe-polymorphic element
/// types: `α : Sort ?u` keeps its universe hole until the declaration generalizes it, while the
/// dictionary entries are compared.
const FIXED: &str = r#"def addEvery (k : Nat) : List Nat → List Nat
  | [] => []
  | [a] => [a + k]
  | a :: b :: t => (a + k) :: (b + k) :: addEvery k t
example : addEvery 1 [1,2,3] = [2,3,4] := rfl
#eval addEvery 10 [1,2,3,4,5]
def mapPairs (f : α → α → β) : List α → List β
  | a :: b :: t => f a b :: mapPairs f t
  | [] => []
  | [_] => []
#eval mapPairs (· + ·) [1,2,3,4,5]
theorem mapPairs_cons2 (f : α → α → β) (a b : α) (t : List α) :
    mapPairs f (a :: b :: t) = f a b :: mapPairs f t := rfl
#print axioms mapPairs
"#;

/// `termination_by structural`, including a measure over an auto-bound polymorphic list.
const HINT: &str = r#"def fib2 (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 1
  | x+2 => fib2 x + fib2 (x+1)
termination_by structural n
theorem fib2_20 : fib2 20 = 10946 := rfl
#eval fib2 25
def len2 (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | [_] => 1
  | _ :: _ :: t => len2 t + 2
termination_by structural xs
example : len2 [1,2,3,4,5] = 5 := rfl
"#;

/// The control: no parameter admits structural recursion (`(n+1) / 2` is no subterm), so the
/// pin falls back to well-founded recursion, here with a supplied decreasing proof.
const WELL_FOUNDED: &str = r#"import Init.Data.Nat.Div.Basic
def log2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => log2 ((n+1) / 2) + 1
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)
#eval log2 1024
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
        .filter(|lib| lib.join("Init/Data/List/Basic.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

/// One workspace per test process. Its import records are warmed once, by a header-only
/// program, before any case reads them.
fn workspace(lib: &Path) -> &'static Path {
    static ROOT: OnceLock<PathBuf> = OnceLock::new();
    ROOT.get_or_init(|| {
        let path = std::env::temp_dir().join(format!(
            "fln-structural-course-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir(&path).unwrap();
        std::fs::write(path.join("Warm.lean"), HEADER).unwrap();
        let (code, _, stderr) = ours(lib, &path, "Warm.lean");
        assert_eq!(code, 0, "{stderr}");
        path
    })
}

/// The pinned `lean`'s stdout and exit code on `name` in `root`, when the binary is present.
fn pinned(lib: &Path, root: &Path, name: &str) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(name)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `name` in `root`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, name: &str) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(name)
        .current_dir(root)
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

/// `body` under [`HEADER`] is accepted with exactly `expected` on stdout, by the pin (when
/// present) and by the installed `lean`.
fn accepted(name: &str, body: &str, expected: &str) {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace(&lib);
    let file = format!("{name}.lean");
    std::fs::write(root.join(&file), format!("{HEADER}{body}")).unwrap();
    if let Some((code, stdout)) = pinned(&lib, root, &file) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
    let (code, stdout, stderr) = ours(&lib, root, &file);
    assert_eq!((code, stdout.as_str()), (0, expected), "{stderr}");
}

#[test]
fn the_beads_definitions_are_structural_reduce_and_evaluate() {
    accepted("Bead", BEAD, "'fib' does not depend on any axioms\n6765\n");
}

#[test]
fn nested_patterns_on_a_user_tree_lists_and_nat_reach_deeper_subterms() {
    accepted(
        "Deep",
        DEEP,
        "4\n'Tree.sumLeft' does not depend on any axioms\n[1, 4, 7]\n4841\n'tri' does not depend on any axioms\n",
    );
}

#[test]
fn fixed_parameters_and_auto_bound_universes_keep_course_of_values_recursion() {
    accepted(
        "Fixed",
        FIXED,
        "[11, 12, 13, 14, 15]\n[3, 7]\n'mapPairs' does not depend on any axioms\n",
    );
}

#[test]
fn termination_by_structural_accepts_deeper_calls() {
    accepted("Hint", HINT, "121393\n");
}

#[test]
fn a_call_on_no_subterm_still_falls_back_to_well_founded_recursion() {
    accepted("WellFounded", WELL_FOUNDED, "11\n");
}

/// A call on a value that is no structural subterm is refused under `termination_by
/// structural` by both: the pin with "failed to eliminate recursive application", here with
/// the typed structural refusal. Neither falls back to well-founded recursion.
#[test]
fn termination_by_structural_still_refuses_a_call_on_no_subterm() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace(&lib);
    for (name, body) in [
        (
            "NatLoop",
            "def bad : Nat → Nat\n  | 0 => 0\n  | 1 => 0\n  | n+2 => bad (n+2) + bad n\ntermination_by structural n => n\n",
        ),
        (
            "ListSwap",
            "def bad : List Nat → Nat\n  | [] => 0\n  | [_] => 0\n  | a :: b :: t => bad (b :: t) + bad (a :: t)\ntermination_by structural xs => xs\n",
        ),
        (
            "TreeGraft",
            "inductive Tree where\n  | leaf : Nat → Tree\n  | node : Tree → Tree → Tree\ndef Tree.bad : Tree → Nat\n  | .leaf n => n\n  | .node (.leaf n) r => n + Tree.bad r\n  | .node (.node l m) r => Tree.bad (.node l r) + Tree.bad m\ntermination_by structural t => t\n",
        ),
    ] {
        let file = format!("{name}.lean");
        std::fs::write(root.join(&file), format!("{HEADER}{body}")).unwrap();
        if let Some((code, stdout)) = pinned(&lib, root, &file) {
            assert_eq!(code, 1, "the pin moved: {stdout}");
            assert!(
                stdout.contains("failed to eliminate recursive application"),
                "the pin moved: {stdout}"
            );
        }
        let (code, stdout, stderr) = ours(&lib, root, &file);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            stderr.contains("recursive call is not on an immediate recursive constructor field"),
            "{name}: {stderr}"
        );
    }
}
