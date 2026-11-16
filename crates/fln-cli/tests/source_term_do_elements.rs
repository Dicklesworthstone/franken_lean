//! `unless c do s`, `for x in xs do s` and `return e` in term position (`Term.termUnless`,
//! `Term.termFor`, `Term.termReturn`): the pin's `toDoElem` macros (`Lean/Elab/Do/Switch.lean`)
//! make each the one-element block `do <element>`, a fresh do block of its own. And `return` with
//! no value, in a do sequence or outside one: the pin's `elabDoReturn` returns `PUnit.unit`. Its
//! term is read only on the same line (`checkLineEq`).
//!
//! Through `fln check-source` over `prelude` with `Init.Control.Except`, `Init.Data.List.Control`
//! and `Init.System.IO`. Every program here was run through the pinned `lean` v4.32.0 with the same
//! header first (2026-10-12), with the same verdict, and is compared with the pinned binary again
//! when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str =
    "prelude\nimport Init.Control.Except\nimport Init.Data.List.Control\nimport Init.System.IO\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "unless_value",
        "def chk (b : Bool) : Except String Unit := unless b do throw \"no\"\nexample : chk false = Except.error \"no\" := rfl\nexample : chk true = Except.ok () := rfl\n",
    ),
    (
        "unless_io",
        "def check (b : Bool) : IO Unit :=\nunless b do throw (IO.userError \"no\")\n",
    ),
    (
        "unless_block",
        "def f (n : Nat) : IO Unit :=\n  unless n = 3 do\n    IO.println \"no\"\n    IO.println \"done\"\n",
    ),
    (
        "unless_argument",
        "def q (b : Bool) : IO Unit := (fun (x : IO Unit) => x) (unless b do pure ())\n",
    ),
    (
        "unless_bare_return",
        "def u (b : Bool) : IO Unit :=\n  unless b do\n    return\n",
    ),
    (
        "for_term",
        "def allSmall (xs : List Nat) : Except String Unit :=\n  for x in xs do\n    if x > 9 then throw \"big\"\n",
    ),
    (
        "for_pipe",
        "def p (xs : List Nat) : IO Unit := id <| for x in xs do IO.println \"x\"\n",
    ),
    (
        "for_mutable_body",
        "def m (xs : List Nat) : IO Unit :=\n  for x in xs do\n    let mut y := x\n    y := y + 1\n    IO.println \"y\"\n",
    ),
    (
        "return_value",
        "def r (n : Nat) : Except String Nat := return n + 1\nexample : r 2 = Except.ok 3 := rfl\n",
    ),
    (
        "return_bare",
        "def k : Except String Unit := return\nexample : k = Except.ok () := rfl\n",
    ),
    (
        "return_bare_in_branch",
        "def h (b : Bool) : Except String Unit := do\n  if b then\n    return\n  throw \"late\"\nexample : h true = Except.ok () := rfl\nexample : h false = Except.error \"late\" := rfl\n",
    ),
    ("return_bare_parenthesized", "def b : IO Unit := (return)\n"),
    (
        "do_pure_lets_at_id",
        "def v (x : Nat) : Id Nat := do\n  let y := x + x\n  pure (y * 2)\n",
    ),
    (
        "do_pure_lets_under_run",
        "def w (x : Nat) : Nat := Id.run do\n  let y := x + x\n  pure (y * 2)\n",
    ),
    // `extractMonadInfo` unfolds one definition at a time and stops at the first `m α`, so an
    // alias of `IO Nat` is read as `IO Nat`, not reduced through `EStateM` to a function type.
    (
        "do_at_abbrev_alias",
        "abbrev Act := IO Nat\ndef a : Act := do\n  let y := 1\n  pure (y + 2)\n",
    ),
    (
        "do_at_def_alias",
        "def Act := IO Nat\ndef a : Act := do\n  pure 3\n",
    ),
    (
        "do_at_def_alias_with_effects",
        "def IoActionAlias := IO Nat\ndef act : IoActionAlias := do\n  IO.println \"hi\"\n  return 42\n",
    ),
    (
        "do_at_except_alias",
        "def Res := Except String Nat\ndef r : Res := do\n  let y := 2\n  pure y\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "unless_wrong_value",
        "def chk (b : Bool) : Except String Unit := unless b do throw \"no\"\nexample : chk true = Except.error \"no\" := rfl\n",
    ),
    (
        "unless_body_type",
        "def f (b : Bool) : IO Unit := unless b do (5 : Nat)\n",
    ),
    (
        "unless_result_type",
        "def f (b : Bool) : IO Nat := unless b do pure ()\n",
    ),
    (
        "unless_then_statement",
        "def f : IO Unit :=\n  unless true do pure ()\n  pure ()\n",
    ),
    (
        "unless_then_argument",
        "def f (b : Bool) : IO Unit :=\n  unless b do pure ()\n    (pure ())\n",
    ),
    (
        "for_outer_mutable",
        "def f (xs : List Nat) : IO Unit := do\n  let mut s := 0\n  let _ ← (for x in xs do s := s + x)\n  pure ()\n",
    ),
    (
        "for_return_value",
        "def f (xs : List Nat) : Except String Nat := for x in xs do return x\n",
    ),
    (
        "return_wrong_value",
        "def r (n : Nat) : Except String Nat := return n + 1\nexample : r 2 = Except.ok 4 := rfl\n",
    ),
    (
        "return_bare_wrong_value",
        "def h (b : Bool) : Except String Unit := do\n  if b then\n    return\n  throw \"late\"\nexample : h true = Except.error \"late\" := rfl\n",
    ),
    (
        "return_value_on_next_line",
        "def bad : Except String Nat := do\n  return\n    5\n",
    ),
    (
        "return_bare_at_nat",
        "def bad : Except String Nat := return\n",
    ),
    // `extractMonadInfo` (vendored `Lean/Elab/Do/Basic.lean:741-760`): "invalid `do` notation,
    // expected type is not a monad application", even when every statement is a pure `let`
    // (upstream `elab_fail/770`).
    (
        "do_pure_lets_at_nat",
        "def u (x : Nat) : Nat := do\n  let y := x + x\n  y * (if y > 100 then 1 else (5 : Nat))\n",
    ),
    (
        "do_pure_let_at_bool",
        "def b : Bool := do\n  let y := true\n  y\n",
    ),
    // `splitMonadApp?` also needs the argument to be a type: `Fin 3` is an application of a
    // number, and an alias of `Nat` unfolds to no application at all.
    (
        "do_at_application_of_a_value",
        "def f : Fin 3 := do\n  let y : Fin 3 := 0\n  y\n",
    ),
    (
        "do_at_alias_of_nat",
        "def N := Nat\ndef n : N := do\n  let y := 1\n  y\n",
    ),
    // A block always asks for its monad's `Pure` instance (`DoElemCont.mkPure`, then
    // `mkBindUnlessPure`, vendored `Lean/Elab/Do/Basic.lean:272-302, 512-525`), even where the
    // bind is contracted away: `List` has none, so even `do xs` is refused.
    (
        "do_at_list",
        "def l : List Nat := do\n  let y := 1\n  [y]\n",
    ),
    (
        "do_bare_list",
        "def l (xs : List Nat) : List Nat := do\n  xs\n",
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
        "fln-term-do-elements-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean")
                .status
                .code()
                .expect("normal pinned exit")
        });
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn term_position_do_elements_and_bare_returns_are_the_pins_blocks() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean refuses it");
    }
    for (name, program) in REFUSED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
        match *name {
            "do_pure_lets_at_nat"
            | "do_pure_let_at_bool"
            | "do_at_application_of_a_value"
            | "do_at_alias_of_nat" => {
                assert!(
                    stderr.contains(
                        "invalid `do` notation, expected type is not a monad application"
                    ),
                    "{name}: expected non-monad diagnostic, got:\n{stderr}"
                );
            }
            "do_at_list" | "do_bare_list" => {
                assert!(
                    !stderr.contains("not a monad application"),
                    "{name}: List Nat must pass monad extraction and fail at Pure List:\n{stderr}"
                );
                assert!(
                    stderr.contains("native instance search") || stderr.contains("Pure List"),
                    "{name}: expected missing Pure List instance refusal, got:\n{stderr}"
                );
            }
            _ => {}
        }
    }
}

/// Self-contained `prelude` regression for `fln-do-expected-type-not-monad-false-accept-7aub`
/// that executes on every CI host without requiring `~/.elan`:
/// - non-monad expected types (`Nat` from upstream `elab_fail/770.lean`, `Bool`, value-indexed
///   `Fin`, and `def N := Nat`) fail at `extractMonadInfo` before reading statements;
/// - `Id Nat` and step-wise `abbrev Act := MyIO Nat` / `def Act := MyIO Nat` (backed by a
///   state-function monad `MyStateM`) stop at the first `m α` without unfolding through to `->`;
/// - `List Nat` passes `extractMonadInfo` and fails at the later `Pure List` synthesis stage.
#[test]
fn do_expected_type_monad_extraction_distinguishes_non_monad_from_missing_pure_without_reference_lib()
 {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("do_expected_type_7aub_prelude");
    std::fs::create_dir_all(&dir).expect("create 7aub prelude dir");
    let shared_monads = "\
inductive MyFin : Nat -> Type where
  | mk : (v : Nat) -> MyFin v
class Pure (f : Type -> Type) : Type 1 where
  pure : {α : Type} -> α -> f α
class Bind (f : Type -> Type) : Type 1 where
  bind : {α β : Type} -> f α -> (α -> f β) -> f β
abbrev Id (α : Type) : Type := α
instance : Pure Id where
  pure x := x
instance : Bind Id where
  bind x k := k x
def MyStateM (σ α : Type) : Type := σ -> α
instance (σ : Type) : Pure (MyStateM σ) where
  pure a := fun _ => a
instance (σ : Type) : Bind (MyStateM σ) where
  bind m k := fun s => k (m s) s
abbrev MyIO : Type -> Type := MyStateM Nat
";
    let lean_prelude_prefix = format!(
        "\
prelude
inductive Bool : Type where
  | false : Bool
  | true : Bool
inductive Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α -> List α -> List α
{shared_monads}"
    );
    let cases: &[(&str, &str, bool, &str)] = &[
        (
            "770_nat",
            "def u (x : Nat) : Nat := do\n  let y := x\n  y\n",
            false,
            "invalid `do` notation, expected type is not a monad application",
        ),
        (
            "bool_let",
            "def b : Bool := do\n  let y := Bool.true\n  y\n",
            false,
            "invalid `do` notation, expected type is not a monad application",
        ),
        (
            "fin_value_arg",
            "def f : MyFin (Nat.succ Nat.zero) := do\n  let y := MyFin.mk (Nat.succ Nat.zero)\n  y\n",
            false,
            "invalid `do` notation, expected type is not a monad application",
        ),
        (
            "alias_of_nat",
            "def N := Nat\ndef n (x : Nat) : N := do\n  let y := x\n  y\n",
            false,
            "invalid `do` notation, expected type is not a monad application",
        ),
        (
            "list_missing_pure",
            "def l (xs : List Nat) : List Nat := do\n  let y := xs\n  y\n",
            false,
            "native instance search",
        ),
        (
            "id_accepted",
            "def v (x : Nat) : Id Nat := do\n  let y := x\n  Pure.pure y\n",
            true,
            "",
        ),
        (
            "abbrev_state_monad_accepted",
            "abbrev Act := MyIO Nat\ndef a (x : Nat) : Act := do\n  let y := x\n  Pure.pure y\n",
            true,
            "",
        ),
        (
            "def_state_monad_accepted",
            "def Act := MyIO Nat\ndef a (x : Nat) : Act := do\n  let y := x\n  Pure.pure y\n",
            true,
            "",
        ),
    ];

    for (name, body, expected_ok, expected_err) in cases {
        for (door, bin, args, prefix) in [
            (
                "fln check-source",
                env!("CARGO_BIN_EXE_fln"),
                vec!["check-source"],
                shared_monads,
            ),
            (
                "lean",
                env!("CARGO_BIN_EXE_lean"),
                Vec::new(),
                lean_prelude_prefix.as_str(),
            ),
        ] {
            let entry = dir.join(format!("Case_{}_{name}.lean", door.replace(' ', "_")));
            std::fs::write(&entry, format!("{prefix}{body}")).expect("write case");
            let out = Command::new(bin)
                .args(&args)
                .arg(&entry)
                .output()
                .expect("run source door");
            let stderr = String::from_utf8_lossy(&out.stderr);
            if *expected_ok {
                assert!(
                    out.status.success(),
                    "{door} rejected valid case {name}:\n{stderr}"
                );
            } else {
                assert!(
                    !out.status.success(),
                    "{door} falsely accepted {name}:\n{body}"
                );
                assert!(
                    stderr.contains(expected_err),
                    "{door} on {name}: expected {expected_err:?}, got:\n{stderr}"
                );
                if *name == "list_missing_pure" {
                    assert!(
                        !stderr.contains("not a monad application"),
                        "{door} on {name} failed at extraction instead of Pure List:\n{stderr}"
                    );
                }
            }
        }
    }
}
