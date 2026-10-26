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

/// The header of the `main` programs: `IO` and `#guard_msgs` (`Init.Notation`).
const IO_HEADER: &str = "prelude\nimport Init.System.IO\n";

/// The pin's message when the root `main` would be compiled at a type its compiler does not run.
const MAIN_TYPE: &str =
    "`main` function must have type `(List String →)? IO (UInt32 | Unit | PUnit)`";

/// The drop-in `lean` on `IO_HEADER` + `program`: exit code, stdout and stderr, and the pinned
/// binary's exit code and stdout when present.
fn run_io(
    lib: &Path,
    root: &Path,
    name: &str,
    program: &str,
) -> (i32, String, String, Option<(i32, String)>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{IO_HEADER}{program}")).unwrap();
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
            let out = Command::new(pinned)
                .arg(&entry)
                .current_dir(root)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean");
            (
                out.status.code().expect("normal pinned exit"),
                String::from_utf8_lossy(&out.stdout).into_owned(),
            )
        });
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stdout).into_owned(),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

/// `compileDecls` refuses a root `main` of any type but `(List String →)? IO (UInt32 | Unit |
/// PUnit)` (vendored `Lean/Compiler/LCNF/Main.lean:69-80, 153-156`) and keeps the declaration.
/// Under `#guard_msgs` the message is judged, as at the pin; unguarded it is a rejection. A
/// namespaced `main`, a proposition, a type former, `noncomputable`, a `noncomputable section`
/// and `[macro_inline]` generate no code and are not checked. Every program was run through the
/// pinned `lean` v4.32.0 with `IO_HEADER` first (2026-10-26), with the exit code and stdout here.
#[test]
fn a_root_main_of_another_type_is_the_pins_compile_error() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("main");
    let guarded = format!("/--\nerror: {MAIN_TYPE}\n-/\n#guard_msgs in\n");
    let cases: Vec<(&str, String, &str)> = vec![
        ("unit", format!("{guarded}def main : Unit := ()\n"), ""),
        (
            "extra",
            format!("{guarded}def main (_ : Nat) (_ : List String) : IO Unit := pure ()\n"),
            "",
        ),
        (
            "no_io",
            format!("{guarded}def main (_ : List String) : UInt32 := 0\n"),
            "",
        ),
        (
            "bytes",
            format!("{guarded}def main (args : List ByteArray) : IO Unit := pure ()\n"),
            "",
        ),
        ("nat", format!("{guarded}def main : IO Nat := pure 0\n"), ""),
        ("abbrev", format!("{guarded}abbrev main : Unit := ()\n"), ""),
        (
            "kept",
            format!("{guarded}def main : Unit := ()\n#check main\n"),
            "main : Unit\n",
        ),
        ("io_unit", "def main : IO Unit := pure ()\n".into(), ""),
        ("io_uint32", "def main : IO UInt32 := pure 0\n".into(), ""),
        (
            "args",
            "def main (_ : List String) : IO UInt32 := pure 0\n".into(),
            "",
        ),
        ("io_punit", "def main : IO PUnit := pure ()\n".into(), ""),
        (
            "namespaced",
            "namespace Foo\ndef main : Unit := ()\nend Foo\n".into(),
            "",
        ),
        ("prop", "def main : Prop := True\n".into(), ""),
        ("type", "def main : Type := Nat\n".into(), ""),
        (
            "noncomputable",
            "noncomputable def main : Unit := ()\n".into(),
            "",
        ),
        (
            "section",
            "noncomputable section\ndef main : Unit := ()\nend\n".into(),
            "",
        ),
        (
            "macro_inline",
            "@[macro_inline] def main : Unit := ()\n".into(),
            "",
        ),
    ];
    for (name, program, stdout) in &cases {
        let (code, ours, stderr, pinned) = run_io(&lib, &root, name, program);
        if let Some(pinned) = pinned {
            assert_eq!(pinned, (0, stdout.to_string()), "{name}: the pin moved");
        }
        assert_eq!(
            (code, ours.as_str()),
            (0, *stdout),
            "{name}: {program}\n{stderr}"
        );
    }
    let (code, _, stderr, pinned) = run_io(&lib, &root, "unguarded", "def main : Unit := ()\n");
    if let Some((pinned, out)) = pinned {
        assert_eq!(pinned, 1, "the pin accepts an unguarded `main : Unit`");
        assert!(out.contains(MAIN_TYPE), "the pin moved: {out}");
    }
    assert_ne!(code, 0, "an unguarded `main : Unit` was accepted");
    assert!(stderr.contains(MAIN_TYPE), "{stderr}");
}
