//! `private` declarations in a legacy (non-`module`) file, through the installed drop-in `lean`,
//! over `prelude` + `import Init.Core`. The pin names the main module after the file
//! (`moduleNameOfFileName`, vendored `src/Lean/Shell.lean`) and a `private` declaration under it
//! (`mkPrivateName`), while the file's other declarations stay public. Its user name still
//! resolves in the file, prints as written, and `#print` shows it `private`. A public and a
//! private declaration may not share a name, in either order. Before this, every legacy `private`
//! was refused for want of a module identity.
//!
//! Every program here was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-21), with the same verdict and output, and is compared with the pinned binary again
//! when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

const ACCEPTED: &str = "private def foo (x : Nat) : Nat := x
#check foo
#check @foo
#print foo
theorem t : foo 1 = 1 := rfl
namespace N
private def baz := 3
end N
#check N.baz
open N in #check baz
private theorem th : foo 2 = 2 := rfl
#check th
private axiom ax : Nat
#check ax
";

const EXPECTED: &str = "foo (x : Nat) : Nat
foo : Nat → Nat
private def foo : Nat → Nat :=
fun x => x
N.baz : Nat
N.baz : Nat
th : foo 2 = 2
ax : Nat
";

/// A private declaration after a public one of the same name, and the reverse (the pin: "a
/// non-private declaration `bar` has already been declared", "a private declaration `bar` has
/// already been declared").
const REFUSED: &[(&str, &str)] = &[
    (
        "private_after_public",
        "def bar := 1\nprivate def bar := 2\n",
    ),
    (
        "public_after_private",
        "private def bar := 2\ndef bar := 1\n",
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
        "fln-private-legacy-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `binary` on `entry`, run from its directory as the pin's main module is named: exit code and
/// stdout.
fn run(binary: &Path, lib: &Path, root: &Path, entry: &Path) -> (i32, String) {
    let output = Command::new(binary)
        .arg(entry.file_name().unwrap())
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
fn legacy_private_declarations_are_named_under_the_file_module() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    let ours = Path::new(env!("CARGO_BIN_EXE_lean"));
    let entry = root.join("Accepted.lean");
    std::fs::write(&entry, format!("{HEADER}{ACCEPTED}")).unwrap();
    assert_eq!(run(ours, &lib, &root, &entry), (0, EXPECTED.to_owned()));
    if let Some(pinned) = pinned_binary(&lib) {
        assert_eq!(
            run(&pinned, &lib, &root, &entry),
            (0, EXPECTED.to_owned()),
            "the pin moved"
        );
    }
    for (name, program) in REFUSED {
        let entry = root.join(format!("{name}.lean"));
        std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
        let (code, _) = run(ours, &lib, &root, &entry);
        assert_ne!(code, 0, "{name} accepted: {program}");
        if let Some(pinned) = pinned_binary(&lib) {
            assert_eq!(
                run(&pinned, &lib, &root, &entry).0,
                1,
                "{name}: the pin moved"
            );
        }
    }
}
