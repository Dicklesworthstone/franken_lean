//! Nested inductive declarations through the installed drop-in `lean`, over `prelude` +
//! `import Init.Prelude`: a field that nests the family under another inductive (`List Tree`,
//! `Array Cmd`, `Option Cmd`). The pin's kernel eliminates each occurrence into an auxiliary
//! family before it generates the recursors, and restores them as `T.rec_1, …` over the
//! original occurrences (vendored `src/kernel/inductive.cpp:828-1182`). Admission regenerates
//! the block and compares it with the proposal byte for byte; the printed recursors are compared
//! here with the pinned `lean` v4.32.0, which was run with the same header first (2026-10-22).
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = r#"prelude
import Init.Prelude
inductive Tree where
  | leaf : Tree
  | node : List Tree → Tree
#check @Tree.rec
#check @Tree.rec_1
inductive Rose (α : Type) where
  | mk : α → List (Rose α) → Rose α
#check @Rose.rec
inductive Cmd where
  | init (name : Nat) (subCmds : Array Cmd) (flags : Option Cmd)
#check @Cmd.rec_1
#check @Cmd.rec_2
#check @Cmd.rec_3
"#;

/// The pin's output for [`PROGRAM`]. `Cmd`'s `Array Cmd` also nests `List Cmd` through
/// `Array.mk`, so its block has three auxiliaries, in the pin's worklist order.
const EXPECTED: &str = "@Tree.rec : {motive_1 : Tree → Sort u_1} →
  {motive_2 : List Tree → Sort u_1} →
    motive_1 Tree.leaf →
      ((a : List Tree) → motive_2 a → motive_1 (Tree.node a)) →
        motive_2 List.nil →
          ((head : Tree) → (tail : List Tree) → motive_1 head → motive_2 tail → motive_2 (List.cons head tail)) →
            (t : Tree) → motive_1 t
@Tree.rec_1 : {motive_1 : Tree → Sort u_1} →
  {motive_2 : List Tree → Sort u_1} →
    motive_1 Tree.leaf →
      ((a : List Tree) → motive_2 a → motive_1 (Tree.node a)) →
        motive_2 List.nil →
          ((head : Tree) → (tail : List Tree) → motive_1 head → motive_2 tail → motive_2 (List.cons head tail)) →
            (t : List Tree) → motive_2 t
@Rose.rec : {α : Type} →
  {motive_1 : Rose α → Sort u_1} →
    {motive_2 : List (Rose α) → Sort u_1} →
      ((a : α) → (a_1 : List (Rose α)) → motive_2 a_1 → motive_1 (Rose.mk a a_1)) →
        motive_2 List.nil →
          ((head : Rose α) → (tail : List (Rose α)) → motive_1 head → motive_2 tail → motive_2 (List.cons head tail)) →
            (t : Rose α) → motive_1 t
@Cmd.rec_1 : {motive_1 : Cmd → Sort u_1} →
  {motive_2 : Array Cmd → Sort u_1} →
    {motive_3 : Option Cmd → Sort u_1} →
      {motive_4 : List Cmd → Sort u_1} →
        ((name : Nat) →
            (subCmds : Array Cmd) →
              (flags : Option Cmd) → motive_2 subCmds → motive_3 flags → motive_1 (Cmd.init name subCmds flags)) →
          ((toList : List Cmd) → motive_4 toList → motive_2 { toList := toList }) →
            motive_3 none →
              ((val : Cmd) → motive_1 val → motive_3 (some val)) →
                motive_4 List.nil →
                  ((head : Cmd) → (tail : List Cmd) → motive_1 head → motive_4 tail → motive_4 (List.cons head tail)) →
                    (t : Array Cmd) → motive_2 t
@Cmd.rec_2 : {motive_1 : Cmd → Sort u_1} →
  {motive_2 : Array Cmd → Sort u_1} →
    {motive_3 : Option Cmd → Sort u_1} →
      {motive_4 : List Cmd → Sort u_1} →
        ((name : Nat) →
            (subCmds : Array Cmd) →
              (flags : Option Cmd) → motive_2 subCmds → motive_3 flags → motive_1 (Cmd.init name subCmds flags)) →
          ((toList : List Cmd) → motive_4 toList → motive_2 { toList := toList }) →
            motive_3 none →
              ((val : Cmd) → motive_1 val → motive_3 (some val)) →
                motive_4 List.nil →
                  ((head : Cmd) → (tail : List Cmd) → motive_1 head → motive_4 tail → motive_4 (List.cons head tail)) →
                    (t : Option Cmd) → motive_3 t
@Cmd.rec_3 : {motive_1 : Cmd → Sort u_1} →
  {motive_2 : Array Cmd → Sort u_1} →
    {motive_3 : Option Cmd → Sort u_1} →
      {motive_4 : List Cmd → Sort u_1} →
        ((name : Nat) →
            (subCmds : Array Cmd) →
              (flags : Option Cmd) → motive_2 subCmds → motive_3 flags → motive_1 (Cmd.init name subCmds flags)) →
          ((toList : List Cmd) → motive_4 toList → motive_2 { toList := toList }) →
            motive_3 none →
              ((val : Cmd) → motive_1 val → motive_3 (some val)) →
                motive_4 List.nil →
                  ((head : Cmd) → (tail : List Cmd) → motive_1 head → motive_4 tail → motive_4 (List.cons head tail)) →
                    (t : List Cmd) → motive_4 t
";

/// A non-recursive `match` over a nested family, in a proof and a noncomputable definition, and
/// reduction through its recursor: `rfl` and `#reduce` unfold `Term.width` by iota on `Term.rec`,
/// whose motives and minors include the auxiliary `List Term`'s. Over `prelude` +
/// `import Init.Core`, as the pin was run (2026-10-22).
const MATCHES: &str = r#"prelude
import Init.Core
inductive Term where
  | var : Nat → Term
  | app : List Term → Term
theorem Term.cases (t : Term) : Or (t = t) (t = t) :=
  match t with
  | .var _ => Or.inl rfl
  | .app _ => Or.inr rfl
noncomputable def Term.width : Term → Nat
  | .var _ => 1
  | .app as => as.length
theorem Term.width_var (n : Nat) : (Term.var n).width = 1 := rfl
theorem Term.width_app (t : Term) : (Term.app (List.cons t List.nil)).width = 1 := rfl
#check @Term.cases
#reduce (Term.var 0).width
#reduce (Term.app (List.cons (Term.var 1) (List.cons (Term.var 2) List.nil))).width
"#;

/// The pin's output for [`MATCHES`].
const MATCHES_EXPECTED: &str = "Term.cases : ∀ (t : Term), t = t ∨ t = t
1
2
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
        "fln-nested-inductives-{}-{}",
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
fn nested_families_are_admitted_with_the_pins_recursors() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Nested.lean");
    std::fs::write(&entry, PROGRAM).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!((code, stdout.as_str()), (0, EXPECTED), "the pin moved");
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, EXPECTED, "{stderr}");
}

#[test]
fn matches_over_a_nested_family_elaborate_and_reduce_as_at_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let entry = root.join("Matches.lean");
    std::fs::write(&entry, MATCHES).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &entry) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, MATCHES_EXPECTED),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, &entry);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, MATCHES_EXPECTED, "{stderr}");
}
