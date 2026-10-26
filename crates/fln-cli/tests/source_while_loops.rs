//! `while c do s` and `repeat s`, as the pin (`Lean/Elab/BuiltinDo/Repeat.lean`): `while` is
//! `repeat if c then s else break`, and `repeat s` is `for _ in Loop.mk do s` over `Lean.Loop`
//! (`Init/While.lean`). The loop's `mut` variables, `break`, `continue`, a named condition `h : c`
//! and a nested action are an ordinary `for` loop's. `repeat` is a do element only: as a term the
//! pin refuses it ("unexpected token 'repeat'").
//!
//! Through `fln check-source` over `prelude` with `Init.While`, `Init.Control.Except`,
//! `Init.Control.Id` and `Init.Data.List.Control`. Every program here was run through the pinned
//! `lean` v4.32.0 with the same header first (2026-10-12), with the same verdict, and is compared
//! with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.While\nimport Init.Control.Except\nimport Init.Control.Id\nimport Init.Data.List.Control\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "except_count",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := n\n  let mut s := 0\n  while i != 0 do\n    s := s + i\n    i := i - 1\n  return s\n",
    ),
    (
        "id_count",
        "def f (n : Nat) : Id Nat := do\n  let mut i := n\n  let mut s := 0\n  while i != 0 do\n    s := s + i\n    i := i - 1\n  return s\n",
    ),
    (
        "except_break",
        "def f : Except String Nat := do\n  let mut i := 0\n  while true do\n    if i > 3 then break\n    i := i + 1\n  return i\n",
    ),
    (
        "except_named",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := 0\n  while h : i < n do\n    i := i + 1\n  return i\n",
    ),
    (
        "except_nested_cond",
        "def f (c : Except String Bool) : Except String Unit := do\n  while (← c) do\n    throw \"again\"\n",
    ),
    (
        "except_inner",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := 0\n  let mut t := 0\n  while i < n do\n    let mut j := 0\n    while j < i do\n      t := t + 1\n      j := j + 1\n    i := i + 1\n  return t\n",
    ),
    (
        "id_continue",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  let mut s := 0\n  while i < n do\n    i := i + 1\n    if i % 2 == 0 then continue\n    s := s + i\n  return s\n",
    ),
    (
        "except_throw",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := n\n  while i > 0 do\n    if i == 7 then throw \"seven\"\n    i := i - 1\n  return i\n",
    ),
    (
        "repeat_except_break",
        "def f (n : Nat) : Except String Nat := do\n  let mut i := 0\n  repeat\n    if i >= n then break\n    i := i + 1\n  return i\n",
    ),
    (
        "repeat_id_break",
        "def f (n : Nat) : Id Nat := do\n  let mut i := 0\n  repeat\n    if i >= n then break\n    i := i + 1\n  return i\n",
    ),
    (
        "repeat_throw_unit",
        "def f : Except String Unit := do\n  repeat\n    throw \"stop\"\n",
    ),
    (
        "repeat_nested_action",
        "def f (c : Except String Bool) : Except String Unit := do\n  repeat\n    if (← c) then break\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "nat_condition",
        "def f : Id Unit := do\n  while (3 : Nat) do\n    pure ()\n",
    ),
    (
        "body_type",
        "def f : Id Unit := do\n  while true do\n    (5 : Nat)\n",
    ),
    (
        "not_mutable",
        "def f : Id Unit := do\n  let i := 0\n  while i < 3 do\n    i := i + 1\n",
    ),
    (
        "result_type",
        "def f : Id Nat := do\n  let mut i := 0\n  while i < 3 do\n    i := i + 1\n",
    ),
    (
        "repeat_body_type",
        "def f : Id Unit := do\n  repeat\n    (5 : Nat)\n",
    ),
    (
        "repeat_not_mutable",
        "def f : Id Unit := do\n  let i := 0\n  repeat\n    i := i + 1\n    break\n",
    ),
    ("repeat_repeat_term", "def f : Id Unit := repeat pure ()\n"),
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
        "fln-while-loops-{}-{}",
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
    check_with_header(lib, root, name, HEADER, program)
}

fn check_with_header(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
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
    let stderr = String::from_utf8_lossy(&ours.stderr).into_owned();
    let code = ours.status.code().unwrap_or_else(|| {
        panic!(
            "{name}: source checker terminated with {}\n{stderr}",
            ours.status
        )
    });
    (code, stderr, theirs)
}

#[test]
fn a_while_loop_is_its_loop_over_lean_loop() {
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
        let (code, _, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}

/// The pin inserts `unreachable!` after a break-free terminal repeat only when its result is
/// not PUnit. A terminating ForIn dictionary makes that checked continuation observable: its default
/// is the whole monadic result, and a Unit result or an explicit suffix never uses it.
#[test]
fn terminal_break_free_repeat_preserves_result_and_control_scopes() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let header = "prelude\nimport Init.While\nimport Init.Control.Except\nimport Init.Control.Id\n";
    let program = r#"
def repeatThrowNat : Except String Nat := do
  repeat
    throw "stop"
def repeatReturnNat : Except String Nat := do
  repeat
    return 42
def repeatInnerBreak : Except String Nat := do
  repeat
    repeat
      break
    return 42
def repeatForBreak : Except String Nat := do
  repeat
    for _ in Lean.Loop.mk do
      break
    throw "stop"
def repeatMutation : Except String Nat := do
  let mut n := 0
  repeat
    n := n + 1
    throw "stop"
def repeatMutableReturn : Except String Nat := do
  let mut n := 0
  repeat
    n := n + 1
    if n = 2 then return n
def repeatGeneric {A : Type} [Inhabited A] : Id A := do
  repeat
    pure ()
def stopRepeat : ForIn (Except String) Lean.Loop Unit where
  forIn _ state _ := pure state
def customRepeatUnit [ForIn (Except String) Lean.Loop Unit] : Except String Unit := do
  repeat
    throw "stop"
theorem customRepeatUnitValue : @customRepeatUnit stopRepeat = Except.ok () := by rfl
def customRepeatNat [ForIn (Except String) Lean.Loop Unit] : Except String Nat := do
  repeat
    throw "stop"
theorem customRepeatNatValue : @customRepeatNat stopRepeat = Except.error "" := by rfl
def customRepeatSuffix [ForIn (Except String) Lean.Loop Unit] : Except String Nat := do
  repeat
    throw "stop"
  return 5
theorem customRepeatSuffixValue : @customRepeatSuffix stopRepeat = Except.ok 5 := by rfl
def customRepeatMutable [ForIn (Except String) Lean.Loop Unit] : Except String Nat := do
  let mut n := 0
  repeat
    n := n + 1
    throw "stop"
theorem customRepeatMutableValue : @customRepeatMutable stopRepeat = Except.error "" := by rfl
def customRepeatReturn [ForIn (Except String) Lean.Loop Unit] : Except String Nat := do
  repeat
    return 42
theorem customRepeatReturnValue : @customRepeatReturn stopRepeat = Except.error "" := by rfl
def customRepeatMutableReturn [ForIn (Except String) Lean.Loop Unit] : Except String Nat := do
  let mut n := 0
  repeat
    n := n + 1
    return n
theorem customRepeatMutableReturnValue : @customRepeatMutableReturn stopRepeat = Except.error "" := by rfl
"#;
    let (code, stderr, pinned) = check_with_header(&lib, &root, "repeat_results", header, program);
    assert_eq!(pinned.unwrap_or(0), 0, "the pinned lean refuses {program}");
    assert_eq!(code, 0, "{program}\n{stderr}");
    for (name, program) in [
        (
            "repeat_direct_break_result",
            "def f : Except String Nat := do\n  repeat\n    break\n",
        ),
        (
            "repeat_branch_break_result",
            "def f (stop : Bool) : Except String Nat := do\n  repeat\n    if stop then break else throw \"stop\"\n",
        ),
        (
            "repeat_nested_block_break_result",
            "def f : Except String Nat := do\n  repeat\n    do\n      break\n",
        ),
        (
            "repeat_else_if_break_result",
            "def f (a b : Bool) : Except String Nat := do\n  repeat\n    if a then throw \"stop\"\n    else if b then break\n    else throw \"stop\"\n",
        ),
        (
            "repeat_requires_inhabited_result",
            "def f {A : Type} : Id A := do\n  repeat\n    pure ()\n",
        ),
        (
            "repeat_checks_body",
            "def f : Except String Nat := do\n  repeat\n    (5 : Nat)\n",
        ),
    ] {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, header, program);
        assert_eq!(
            pinned.unwrap_or(1),
            1,
            "the pinned lean did not reject {program}"
        );
        assert_eq!(
            code, 1,
            "{name}: expected a typing refusal for {program}\n{stderr}"
        );
    }
}

/// A locally registered loop dictionary indexes the reducible `Unit` alias as PUnit. Its
/// lexical registration selects the terminating implementation for both result shapes and
/// restores the imported default dictionary at `end`.
#[test]
fn local_repeat_dictionary_indexes_unit_alias_and_restores_scope() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let header = "prelude\nimport Init.While\nimport Init.Control.Except\nimport Init.Control.Id\n";
    let program = r#"
abbrev defaultRepeatInstance : ForIn (Except String) Lean.Loop Unit := inferInstance
section
local instance stopRepeat : ForIn (Except String) Lean.Loop Unit where
  forIn _ state _ := pure state
def localRepeatUnit : Except String Unit := do
  repeat
    throw "stop"
example : localRepeatUnit = Except.ok () := by rfl
def localRepeatNat : Except String Nat := do
  repeat
    throw "stop"
example : localRepeatNat = Except.error "" := by rfl
end
example : (inferInstance : ForIn (Except String) Lean.Loop Unit) = defaultRepeatInstance := by rfl
"#;
    let (code, stderr, pinned) =
        check_with_header(&lib, &root, "local_repeat_alias", header, program);
    assert_eq!(pinned.unwrap_or(0), 0, "the pinned lean refuses {program}");
    assert_eq!(code, 0, "{program}\n{stderr}");
}

/// The generated fallback contains a real `Inhabited (Except String Nat)` dictionary. Its
/// default is an error action, and its projection must have a runtime layout even when a loop
/// exits through an exception or return before that fallback can execute.
#[test]
fn result_bearing_repeats_and_except_panic_defaults_execute() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let source = root.join("RepeatExecution.lean");
    std::fs::write(
        &source,
        r#"prelude
import Init.While
import Init.Control.Except
import Init.Control.Id
def repeatThrowNat : Except String Nat := do
  repeat
    throw "stop"
def repeatReturnNat : Except String Nat := do
  repeat
    return 42
def repeatMutableReturn : Except String Nat := do
  let mut n := 0
  repeat
    n := n + 1
    if n = 2 then return n
#eval match (unreachable! : Except String Nat) with
  | Except.error _ => (0 : Nat)
  | Except.ok _ => 99
#eval match repeatThrowNat with
  | Except.error _ => (1 : Nat)
  | Except.ok _ => 0
#eval match repeatReturnNat with
  | Except.error _ => (0 : Nat)
  | Except.ok n => n
#eval match repeatMutableReturn with
  | Except.error _ => (0 : Nat)
  | Except.ok n => n
"#,
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--jobs=1"])
        .arg(&source)
        .env("LEAN_PATH", &lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .env("LEAN_BACKTRACE", "0")
        .env_remove("LEAN_ABORT_ON_PANIC")
        .output()
        .expect("run result-bearing repeat programs");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{}\n{stdout}\n{stderr}",
        output.status
    );
    assert_eq!(
        stdout.matches("\"event\":\"evaluation\"").count(),
        4,
        "{stdout}"
    );
    for (command, value) in [(3, 0), (4, 1), (5, 42), (6, 2)] {
        assert!(
            stdout.contains(&format!(
                "\"command\":{command},\"event\":\"evaluation\",\"kind\":\"nat\",\"value\":{value},"
            )),
            "{stdout}"
        );
    }
    // The JSON runner captures runtime diagnostics in the report's stdout field.
    assert!(stdout.contains("\"stdout\":\"PANIC at "), "{stdout}");
    assert_eq!(
        stdout.matches("unreachable code has been reached").count(),
        1,
        "{stdout}"
    );
    assert!(stderr.is_empty(), "{stderr}");
    if let Some(pinned) = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
    {
        let output = Command::new(pinned)
            .arg(&source)
            .env("LEAN_PATH", &lib)
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .expect("run the pinned repeat programs");
        assert!(output.status.success(), "{output:?}");
        // The pin's #eval reporter captures its panic diagnostic on stdout.
        let stdout = String::from_utf8_lossy(&output.stdout);
        let values: Vec<_> = stdout
            .lines()
            .filter(|line| !line.starts_with("PANIC at "))
            .collect();
        assert_eq!(values, ["0", "1", "42", "2"], "{stdout}");
        assert_eq!(
            stdout.matches("unreachable code has been reached").count(),
            1,
        );
        assert!(output.stderr.is_empty(), "{output:?}");
    }
}
