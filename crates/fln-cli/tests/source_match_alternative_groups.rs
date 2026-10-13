//! `| p₁ | p₂ => rhs`, one alternative with two pattern groups, is `| p₁ => rhs` and
//! `| p₂ => rhs`: the pin's `expandMatchAlt` (vendored `Lean/Elab/BindersUtil.lean`), applied by its
//! term and do `match` and by its equations. Through `fln check-source` over `prelude` +
//! `Init.Core` (+ `Init.Control.Id` for the do `match`). Every program here was run through the
//! pinned `lean` v4.32.0 with the same header first (2026-10-11), with the same verdict, and is
//! compared with the pinned binary again when it is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\nimport Init.Control.Id\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "term_match",
        "def g (n : Nat) : Nat := match n with\n  | 0 | 1 => 1\n  | _ => 2\n\
         example : g 1 = 1 := rfl\nexample : g 5 = 2 := rfl\n",
    ),
    (
        "equations",
        "def h : Nat → Bool\n| 0 | 2 => true\n| _ => false\nexample : h 2 = true := rfl\n",
    ),
    (
        "do_match",
        "def g (n : Nat) : Id Nat := do\n  match n with\n  | 0 | 1 => return 10\n  | _ => return 20\n\
         example : (g 1).run = 10 := rfl\nexample : (g 7).run = 20 := rfl\n",
    ),
    (
        "two_columns",
        "def isLeaf (o : Option Nat) (b : Bool) : Bool := match o, b with\n  \
         | none, _ | _, true => true\n  | some _, false => false\n\
         example : isLeaf none false = true := rfl\nexample : isLeaf (some 1) false = false := rfl\n",
    ),
];

const REFUSED: &[(&str, &str)] = &[
    (
        "wrong_value",
        "def g (n : Nat) : Nat := match n with\n  | 0 | 1 => 1\n  | _ => 2\nexample : g 1 = 2 := rfl\n",
    ),
    (
        "unbound_in_one_group",
        "def g (o : Option Nat) : Nat := match o with\n  | some x | none => x\n",
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
        .filter(|lib| lib.join("Init/Control/Id.olean").is_file());
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
        "fln-match-alternative-groups-{}-{}",
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
fn each_pattern_group_is_an_alternative() {
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
