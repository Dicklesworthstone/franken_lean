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
