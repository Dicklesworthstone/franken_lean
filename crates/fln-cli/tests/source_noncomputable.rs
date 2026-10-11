//! `noncomputable`, as the pin's `noncomputableExt` (vendored
//! `src/Lean/Compiler/NoncomputableAttr.lean`), through the installed drop-in `lean`, which
//! compiles what it checks. A `noncomputable def` or `abbrev` is checked but never compiled, and
//! code that must run may not depend on it: a computable definition, even through a discarded
//! argument or a namespace, and an `#eval`. Theorems and propositions may. A `noncomputable
//! example` is accepted; a `noncomputable theorem` is the pin's error. Every program here was run
//! through the pinned `lean` v4.32.0 with the same header first (2026-10-11), with the same
//! verdict, and is compared with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

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

fn workspace(case: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-noncomputable-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The drop-in `lean` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn run(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let ours = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed lean");
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
fn noncomputable_declarations_are_checked_and_never_compiled() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "theorem_uses",
            "noncomputable def a : Nat := 1\ntheorem t : a = 1 := rfl\n",
        ),
        (
            "chain",
            "noncomputable def a : Nat := 1\nnoncomputable def b : Nat := a + 1\n",
        ),
        ("abbrev", "noncomputable abbrev a : Nat := 1\n"),
        ("example", "noncomputable example : Nat := 1\n"),
        (
            "prop",
            "noncomputable def a : Nat := 1\ndef b (n : Nat) : Prop := a = n\n",
        ),
        (
            "choice",
            "noncomputable def c : Nat := Classical.choice ⟨1⟩\n",
        ),
        (
            "function",
            "noncomputable def f (n : Nat) : Nat := n + 1\ntheorem t : f 2 = 3 := rfl\n",
        ),
        (
            "namespace",
            "namespace A\nnoncomputable def a : Nat := 1\nend A\nnoncomputable def b : Nat := A.a\n",
        ),
    ] {
        let (code, stderr, pinned) = run(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert!(
            pinned.is_none_or(|code| code == 0),
            "{name}: the pin refuses it"
        );
    }
}

#[test]
fn code_that_depends_on_a_noncomputable_declaration_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "depends",
            "noncomputable def a : Nat := 1\ndef b : Nat := a + 1\n",
            "failed to compile definition, consider marking it as 'noncomputable' because it depends on 'a'",
        ),
        (
            "theorem",
            "noncomputable theorem t : 1 = 1 := rfl\n",
            "'theorem' subsumes 'noncomputable', code is not generated for theorems",
        ),
        (
            "eval",
            "noncomputable def a : Nat := 1\n#eval a\n",
            "could not synthesize a `Repr` or `ToString` instance",
        ),
        (
            "discarded",
            "noncomputable def a : Nat := 1\ndef c : Nat := (fun _ => 2) a\n",
            "depends on 'a', which is 'noncomputable'",
        ),
        (
            "unmarked_choice",
            "def c : Nat := Classical.choice ⟨1⟩\n",
            "`Classical.choice` not supported by code generator",
        ),
        (
            "namespace",
            "namespace A\nnoncomputable def a : Nat := 1\nend A\ndef b : Nat := A.a\n",
            "depends on 'A.a'",
        ),
        (
            "function",
            "noncomputable def f (n : Nat) : Nat := n + 1\ndef g (n : Nat) : Nat := f n\n",
            "depends on 'f'",
        ),
    ] {
        let (code, _, pinned) = run(&lib, &root, name, program);
        assert_ne!(code, 0, "{name} was accepted; the pin: {pin}\n{program}");
        assert!(
            pinned.is_none_or(|code| code != 0),
            "{name}: the pin accepts it"
        );
    }
}

/// The tag crosses source modules: `Main` importing `Helper`'s noncomputable `a` may not compile
/// a dependent definition, and may mark it noncomputable too. (The pinned binary needs `Helper`'s
/// `.olean` to run `Main`, so it is not compared here; within one module the same programs are.)
#[test]
fn an_imported_noncomputable_declaration_stays_uncompiled() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("modules");
    std::fs::write(
        root.join("Helper.lean"),
        format!("{HEADER}noncomputable def a : Nat := 1\n"),
    )
    .unwrap();
    for (name, body, accepted) in [
        ("Main", "def b : Nat := a + 1\n", false),
        ("Marked", "noncomputable def b : Nat := a + 1\n", true),
    ] {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, format!("{HEADER}import Helper\n{body}")).unwrap();
        let ours = Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&entry)
            .current_dir(&root)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run the installed lean");
        assert_eq!(ours.status.success(), accepted, "{name}: {ours:?}");
    }
}
