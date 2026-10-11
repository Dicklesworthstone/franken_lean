//! A class parameter that is neither an `outParam` nor instance-implicit may not mention an earlier
//! `outParam`: the pin's `checkOutParam` (vendored `src/Lean/Class.lean`), which `addClass` runs on
//! every new class. Through the installed drop-in `lean`, over `prelude` + `import Init.Core`.
//! Every program here was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-11), with the same verdict, and is compared with the pinned binary again when it is
//! present. The refused ones are the pin's `tests/elab_fail/classBadOutParam.lean` in both class
//! syntaxes, and a parameter typed by an earlier `outParam`.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "both_out_paren",
        "class C2 (x : outParam Nat) (y : outParam { n : Nat // n > x }) (α : Type) :=\n(val : α)\n",
    ),
    (
        "both_out_where",
        "class C2 (x : outParam Nat) (y : outParam { n : Nat // n > x }) (α : Type) where\n  val : α\n",
    ),
    (
        "instance_implicit",
        "class D (α : Type) (β : outParam Type) [Inhabited β] where\n  f : α → β\n",
    ),
    (
        "unrelated",
        "class E (x : outParam Nat) (α : Type) where\n  val : α\n",
    ),
    (
        "typed_by_out",
        "class G (β : outParam Type) (b : outParam β) where\n  val : Nat\n",
    ),
    (
        "structure",
        "structure S (x : outParam Nat) (y : { n : Nat // n > x }) where\n  val : Nat\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "dependent_paren",
        "class C1 (x : outParam Nat) (y : { n : Nat // n > x }) (α : Type) :=\n(val : α)\n",
    ),
    (
        "dependent_where",
        "class C1 (x : outParam Nat) (y : { n : Nat // n > x }) (α : Type) where\n  val : α\n",
    ),
    (
        "typed_by_regular",
        "class F (β : outParam Type) (b : β) where\n  val : Nat\n",
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
        "fln-class-out-params-{}-{}",
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
fn a_regular_class_parameter_may_not_depend_on_an_out_parameter() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = run(&lib, &root, name, program);
        assert_eq!(code, 0, "{name} is a class at the pin: {stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean refuses it");
    }
    for (name, program) in REFUSED {
        let (code, stderr, pinned) = run(&lib, &root, name, program);
        assert_ne!(code, 0, "{name} is the pin's invalid class");
        assert!(
            stderr.contains("parameter #2 depends on `outParam`, but it is not an `outParam`"),
            "{name}: {stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
}
