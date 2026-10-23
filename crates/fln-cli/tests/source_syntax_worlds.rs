//! `#guard`, `guard_target` and `fail_if_success` exist only where their declaring module is
//! imported. Each is syntax a module adds, a `ParserDescr` constant named after its kind:
//! - `Lean.Parser.Command.guardCmd` and `Lean.Parser.Tactic.guardTarget` from `Init/Guard.lean`;
//! - `Lean.Parser.Tactic.failIfSuccess` from `Init/Tactics.lean`.
//!
//! In a world whose imports do not reach that module, the pin reads `#guard` as an unknown token
//! and the tactics as unknown tactics. The rule is the one `#guard_msgs` and the tactic `sorry`
//! follow (fln-guard-msgs-lls1). Every program here was run through the pinned `lean` v4.32.0
//! with the same header first (2026-10-11), with the same verdict.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

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
        .filter(|lib| lib.join("Init/Guard.olean").is_file());
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
        "fln-syntax-worlds-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The drop-in `lean` on `header` + `program`: its exit code.
fn lean(lib: &Path, root: &Path, name: &str, header: &str, program: &str) -> i32 {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
    Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean")
        .status
        .code()
        .expect("normal process exit")
}

#[test]
fn guard_syntax_exists_where_its_module_is_imported() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, header, program, accepted) in [
        (
            "guard_core",
            "prelude\nimport Init.Core\n",
            "#guard 1 + 1 == 2\n",
            false,
        ),
        (
            "guard_guard",
            "prelude\nimport Init.Guard\n",
            "#guard 1 + 1 == 2\n",
            true,
        ),
        (
            "target_core",
            "prelude\nimport Init.Core\n",
            "theorem t : 1 = 1 := by\n  guard_target = 1 = 1\n  rfl\n",
            false,
        ),
        (
            "target_prelude",
            "prelude\nimport Init.Prelude\n",
            "theorem t : True := by\n  guard_target = True\n  exact True.intro\n",
            false,
        ),
        // `Tactic.elabTerm` synthesizes the guard's numerals, defaults included, before comparing.
        (
            "target_guard",
            "prelude\nimport Init.Guard\n",
            "theorem t : 1 = 1 := by\n  guard_target = 1 = 1\n  rfl\n",
            true,
        ),
        (
            "target_guard_syntactic",
            "prelude\nimport Init.Guard\n",
            "theorem t : 2 + 3 = 5 := by\n  guard_target =ₛ 2 + 3 = 5\n  rfl\n",
            true,
        ),
        (
            "target_guard_mismatch",
            "prelude\nimport Init.Guard\n",
            "theorem t : 2 + 3 = 5 := by\n  guard_target =ₛ 5 = 5\n  rfl\n",
            false,
        ),
        (
            "target_guard_defeq",
            "prelude\nimport Init.Guard\n",
            "theorem t : 2 + 3 = 5 := by\n  guard_target =~ 5 = 5\n  rfl\n",
            true,
        ),
        (
            "fail_if_success_prelude",
            "prelude\nimport Init.Prelude\n",
            "theorem t : True := by\n  fail_if_success exact False.elim\n  exact True.intro\n",
            false,
        ),
        (
            "fail_if_success_core",
            "prelude\nimport Init.Core\n",
            "theorem t : True := by\n  fail_if_success exact False.elim\n  exact True.intro\n",
            true,
        ),
    ] {
        let code = lean(&lib, &root, name, header, program);
        assert_eq!(code == 0, accepted, "{name}: {header}{program}");
    }
}

/// Operators and `∃` are notations of `Init.Notation` and `Init.NotationExtra`, whose tokens a
/// `prelude` file sees only through its imports: where they are not imported the pin reads `+`
/// as "unexpected token '+'" and `∃` as "expected token". Each program was run through the
/// pinned `lean` v4.32.0 with the same header first (2026-10-22), with the same verdict.
#[test]
fn a_prelude_file_reads_only_the_notation_its_imports_declare() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let plus = "theorem two_plus_two : 2 + 2 = 4 := rfl\n";
    let exists = "theorem t : ∃ n : Nat, n = n := ⟨0, rfl⟩\n";
    for (name, header, program, accepted) in [
        (
            "plus_prelude",
            "prelude\nimport Init.Prelude\n",
            plus,
            false,
        ),
        ("plus_core", "prelude\nimport Init.Core\n", plus, true),
        ("exists_core", "prelude\nimport Init.Core\n", exists, false),
        (
            "exists_extra",
            "prelude\nimport Init.NotationExtra\n",
            exists,
            true,
        ),
    ] {
        let code = lean(&lib, &root, name, header, program);
        assert_eq!(code == 0, accepted, "{name}: {header}{program}");
    }
}

/// `[a, b]` is `Init.Data.List.Notation`'s syntax and `xs[i]` is `Init.GetElem`'s. Over
/// `prelude` + `import Init.Core` neither is in scope, and the pin reads a `[` in a term only as
/// an instance binder of an arrow, `[C α] → β` (`Term.depArrow`). Each program's verdict is the
/// pinned v4.32.0's (2026-10-23).
#[test]
fn list_and_index_brackets_read_only_where_their_module_is_imported() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let core = "prelude\nimport Init.Core\n";
    let list = "def l : List Nat := [1, 2]\n";
    let index = "def g (xs : List Nat) (h : 0 < xs.length) : Nat := xs[0]\n";
    let pattern = "def p3 : List Nat → Nat\n  | x@(y :: ys) => 0\n  | [] => 1\n";
    for (name, header, program, accepted) in [
        ("list_core", core, list, false),
        (
            "list_notation",
            "prelude\nimport Init.Data.List.Notation\n",
            list,
            true,
        ),
        ("index_core", core, index, false),
        (
            "index_getelem",
            "prelude\nimport Init.GetElem\n",
            index,
            true,
        ),
        ("pattern_core", core, pattern, false),
        (
            "pattern_notation",
            "prelude\nimport Init.Data.List.Notation\n",
            pattern,
            true,
        ),
        (
            "instance_arrow_core",
            core,
            "def f (g : [Inhabited Nat] → Nat) : Nat := g\n",
            true,
        ),
    ] {
        let code = lean(&lib, &root, name, header, program);
        assert_eq!(code == 0, accepted, "{name}: {header}{program}");
    }
}

/// The `·` tactic is `Init.NotationExtra`'s syntax (`syntax (name := cdot) cdotTk
/// tacticSeqIndentGt : tactic`), while `focus` is `Init.Tactics`', which `Init.Core` already
/// imports. Over `prelude` + `import Init.SimpLemmas` the pin ends the `by` block at the first `·`
/// ("unexpected token '·'; expected command") and reports the goals left open. Each program's
/// verdict is the pinned v4.32.0's (2026-10-23).
#[test]
fn the_cdot_tactic_reads_only_where_its_module_is_imported() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let dot = "example {A : Prop} (h : A) : A ∧ A := by\n  constructor\n  · exact h\n  · exact h\n";
    let focus = "example {A : Prop} (h : A) : A ∧ A := by\n  constructor\n  focus exact h\n  focus exact h\n";
    for (name, header, program, accepted) in [
        (
            "cdot_simp_lemmas",
            "prelude\nimport Init.SimpLemmas\n",
            dot,
            false,
        ),
        (
            "cdot_notation_extra",
            "prelude\nimport Init.NotationExtra\n",
            dot,
            true,
        ),
        (
            "focus_simp_lemmas",
            "prelude\nimport Init.SimpLemmas\n",
            focus,
            true,
        ),
        ("focus_core", "prelude\nimport Init.Core\n", focus, true),
    ] {
        let code = lean(&lib, &root, name, header, program);
        assert_eq!(code == 0, accepted, "{name}: {header}{program}");
    }
}
