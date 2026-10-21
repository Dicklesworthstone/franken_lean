//! `#reduce e`, through the installed drop-in `lean`, over `prelude` + `import Init.Core`. The pin
//! elaborates `e`, then prints its normal form (`elabReduce`, vendored
//! `src/Lean/Elab/BuiltinCommand.lean:459`): `Meta.reduce` at transparency `all` without smart
//! unfolding, leaving types and proofs as they are unless `(types := true)` or `(proofs := true)`.
//! Literal arithmetic folds before delta, as the pin's `reduceNat?` does, so a large product is one
//! literal, and `Nat.succ` of a literal is the next literal.
//!
//! The program was run through the pinned `lean` v4.32.0 with the same header first (2026-10-21),
//! and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const PROGRAM: &str = "prelude
import Init.Core
#reduce 2 + 3
#reduce 10000000000000000000000 * 3
#reduce fun (x : Nat) => x + 1
#reduce (Nat.succ 4)
#reduce (fun x => x) 7
#reduce (2, 3).1
#reduce (types := true) 2 = 1 + 1
#reduce 2 = 1 + 1
";

const EXPECTED: &str = "5
30000000000000000000000
fun x => x.succ
5
7
2
2 = 2
2 = 1 + 1
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
        "fln-reduce-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `binary` on `entry`: exit code and stdout.
fn run(binary: &Path, lib: &Path, root: &Path, entry: &Path) -> (i32, String) {
    let output = Command::new(binary)
        .arg(entry)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
    )
}

fn pinned_binary(lib: &Path) -> Option<PathBuf> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    lean.is_file().then_some(lean)
}

#[test]
fn reduce_prints_the_pins_normal_forms() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let entry = root.join("Reduce.lean");
    std::fs::write(&entry, PROGRAM).unwrap();
    let ours = Path::new(env!("CARGO_BIN_EXE_lean"));
    assert_eq!(run(ours, &lib, &root, &entry), (0, EXPECTED.to_owned()));
    if let Some(pinned) = pinned_binary(&lib) {
        assert_eq!(
            run(&pinned, &lib, &root, &entry),
            (0, EXPECTED.to_owned()),
            "the pin moved"
        );
    }
}

/// An option this engine does not read is refused, not ignored.
#[test]
fn an_unread_reduce_option_is_refused() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let entry = root.join("Option.lean");
    std::fs::write(
        &entry,
        "prelude\nimport Init.Core\n#reduce (smartUnfolding := true) 2 + 3\n",
    )
    .unwrap();
    let ours = Path::new(env!("CARGO_BIN_EXE_lean"));
    let (code, stdout) = run(ours, &lib, &root, &entry);
    assert_ne!(code, 0, "{stdout}");
    assert!(stdout.is_empty(), "{stdout}");
}
