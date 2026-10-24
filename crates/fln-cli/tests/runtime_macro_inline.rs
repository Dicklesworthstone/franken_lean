//! `@[macro_inline]` through the installed drop-in `lean`, over a `prelude` header. The pin's
//! compiler unfolds an application of a `@[macro_inline]` definition before it evaluates anything
//! (`macroInline`, vendored `src/Lean/Compiler/LCNF/ToDecl.lean:22`), so an argument the body does
//! not select is never evaluated: `||`, `&&`, `cond`, the `Decidable` instances of `∧` and `∨`, and
//! `Option.getD` from the imported `inlineAttrs`, and a definition of this file. An argument the
//! body uses twice is evaluated twice. The attribute is refused on a recursive, mutual, `partial`
//! or opaque declaration (`isValidMacroInline`, `src/Lean/Compiler/InlineAttrs.lean:31`) and
//! `local`.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and is compared with the pinned binary's output again when that is present. The
//! pin writes `dbg_trace` text into the command's message on stdout (`stderrAsMessages`), and so
//! does this `lean`: its stdout must be the pin's, byte for byte, and its stderr empty. A refusal
//! is compared by its verdict, not by the pin's wording.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Util\nimport Init.Data.ToString.Macro\n";

/// An accepted program and the pin's stdout, trace text included.
struct Accepted {
    body: &'static str,
    pin_stdout: &'static str,
}

/// The bead's divergence (`walk` recursed without end before `||` was unfolded) and the three
/// short-circuiting Prelude functions, each with its second argument selected once.
const SHORT_CIRCUIT: Accepted = Accepted {
    body: r#"partial def walk (n : Nat) : Bool := n == 0 || walk (n - 1)
#eval walk 3
def g (b : Bool) : Bool := b || (dbg_trace "or rhs"; false)
#eval g true
#eval g false
def h (b : Bool) : Bool := b && (dbg_trace "and rhs"; true)
#eval h false
#eval h true
def k (b : Bool) : Nat := cond b 1 (dbg_trace "cond else"; 2)
#eval k true
#eval k false
"#,
    pin_stdout: "true\ntrue\nor rhs\nfalse\nfalse\nand rhs\ntrue\n1\ncond else\n2\n",
};

/// `if p ∧ q` and `if p ∨ q`: the instances `instDecidableAnd` and `instDecidableOr` match on
/// the first decision before the second instance is evaluated.
const DECISIONS: Accepted = Accepted {
    body: r#"def both (a b : Bool) : Nat :=
  if a = true ∧ (dbg_trace "and right"; b) = true then 1 else 0
#eval both false true
#eval both true true
def either (a b : Bool) : Nat :=
  if a = true ∨ (dbg_trace "or right"; b) = true then 1 else 0
#eval either true false
#eval either false true
"#,
    pin_stdout: "0\nand right\n1\n1\nor right\n1\n",
};

/// `Option.getD` evaluates its default only for `none`.
const GET_D: Accepted = Accepted {
    body: r#"def dflt (o : Option Nat) : Nat := o.getD (dbg_trace "default"; 7)
#eval dflt (some 3)
#eval dflt none
"#,
    pin_stdout: "3\ndefault\n7\n",
};

/// A `@[macro_inline]` definition of this file: an unselected argument is not evaluated, a
/// duplicated one is evaluated twice, and the bare constant passed as a function is its value,
/// whose call evaluates its arguments first.
const USER: Accepted = Accepted {
    body: r#"@[macro_inline] def orElse (x y : Bool) : Bool :=
  match x with
  | true => true
  | false => y
#eval orElse true (dbg_trace "user rhs"; false)
#eval orElse false (dbg_trace "user rhs"; false)
@[macro_inline] def twice (x : Nat) : Nat := x + x
#eval twice (dbg_trace "argument"; 3)
def viaHigher (f : Bool → Bool → Bool) : Bool := f true (dbg_trace "higher"; false)
#eval viaHigher orElse
"#,
    pin_stdout: "true\nuser rhs\nfalse\nargument\nargument\n6\nhigher\ntrue\n",
};

/// Programs the pin refuses, with the pin's first error after the file name and position, and the
/// reason this `lean` gives.
const REFUSALS: &[(&str, &str, &str)] = &[
    (
        "@[macro_inline] def d : Nat → Nat\n  | 0 => 0\n  | n + 1 => d n\n",
        "error: Cannot add `[macro_inline]` attribute to `d`: This attribute does not support this \
         kind of declaration; only non-recursive definitions are supported",
        "a `macro_inline` attribute on a non-recursive definition",
    ),
    (
        "@[macro_inline] def wf (n : Nat) : Nat := if h : n = 0 then 0 else wf (n / 2)\n\
         termination_by n\n\
         decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)\n",
        "error: Cannot add `[macro_inline]` attribute to `wf`: This attribute does not support \
         this kind of declaration; only non-recursive definitions are supported",
        "a `macro_inline` attribute on a non-recursive definition",
    ),
    (
        "mutual\n@[macro_inline] def ev : Nat → Bool\n  | 0 => true\n  | n + 1 => od n\n\
         def od : Nat → Bool\n  | 0 => false\n  | n + 1 => ev n\nend\n",
        "error: Cannot add `[macro_inline]` attribute to `ev`: This attribute does not support \
         this kind of declaration; only non-recursive definitions are supported",
        "a `macro_inline` attribute on a non-recursive definition",
    ),
    (
        "@[macro_inline] partial def d (n : Nat) : Nat := if n = 0 then 0 else d (n - 1)\n",
        "error: Cannot add `[macro_inline]` attribute to `d`: This attribute does not support this \
         kind of declaration; only non-recursive definitions are supported",
        "a `macro_inline` attribute on a non-recursive definition",
    ),
    (
        "@[macro_inline] opaque d : Nat\n",
        "error: Cannot add `[macro_inline]` attribute to `d`: This attribute does not support this \
         kind of declaration; only non-recursive definitions are supported",
        "a `macro_inline` attribute on a non-recursive definition",
    ),
    (
        "@[local macro_inline] def d (n : Nat) : Nat := n\n",
        "error: Invalid attribute scope: Attribute `[macro_inline]` must be global, not `local`",
        "global compiler hint",
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
        .filter(|lib| lib.join("Init/Util.olean").is_file());
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
        "fln-macro-inline-{}-{}",
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
        .current_dir(entry.parent()?)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `HEADER` + `body`: its exit code, stdout and stderr.
fn ours(lib: &Path, root: &Path, body: &str) -> (Option<i32>, String, String) {
    let entry = root.join("MacroInline.lean");
    std::fs::write(&entry, format!("{HEADER}{body}")).unwrap();
    let records = std::env::var_os("FLN_IMPORT_REUSE_DIR")
        .map(PathBuf::from)
        .filter(|directory| directory.is_absolute())
        .unwrap_or_else(|| root.join("records"));
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", records)
        .output()
        .expect("run the installed lean");
    (
        output.status.code(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn accepted(lib: &Path, root: &Path, case: &Accepted) {
    let (code, stdout, stderr) = ours(lib, root, case.body);
    assert_eq!(code, Some(0), "stderr: {stderr}");
    assert_eq!((stdout.as_str(), stderr.as_str()), (case.pin_stdout, ""));
    if let Some((code, stdout)) = pinned(lib, &root.join("MacroInline.lean")) {
        assert_eq!(
            (code, stdout.as_str()),
            (0, case.pin_stdout),
            "the pin moved"
        );
    }
}

#[test]
fn short_circuiting_prelude_functions_evaluate_only_the_selected_argument() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    accepted(&lib, &root, &SHORT_CIRCUIT);
    accepted(&lib, &root, &DECISIONS);
    accepted(&lib, &root, &GET_D);
}

#[test]
fn a_source_macro_inline_definition_unfolds_over_its_unevaluated_arguments() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    accepted(&lib, &root, &USER);
}

#[test]
fn macro_inline_is_refused_where_the_pin_refuses_it() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (body, pin, reason) in REFUSALS {
        let (code, stdout, stderr) = ours(&lib, &root, body);
        assert_eq!(code, Some(1), "{body}\n{stderr}");
        assert_eq!(stdout, "", "{body}");
        assert!(stderr.contains(reason), "{body}\n{stderr}");
        if let Some((code, stdout)) = pinned(&lib, &root.join("MacroInline.lean")) {
            assert_eq!(code, 1, "{body}");
            assert!(stdout.contains(pin), "the pin moved: {body}\n{stdout}");
        }
    }
}
