//! Instance goals with universe holes, checked over the pinned `Init.Core` closure, which has the
//! `PUnit`, `Option`, `Prod`, `Sort`, `Prop`, `ULift` and `DecidableEq` instances the seed lacks.
//! The pin's `synthInstance?` searches under `withNewMCtxDepth (allowLevelAssignments := true)`:
//! - A universe hole in an input does not block a goal: `Inhabited PUnit.{?u}` is answered by
//!   `instInhabitedPUnit.{?u}`.
//! - The search may choose a universe: `(default : Sort _)` is `True`, from `instInhabitedProp`.
//! - An answer may keep a hole of the goal.
//!
//! Every program here was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-11), with the same verdict.
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
        "fln-universe-holes-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `HEADER` + `program`: (exit code, stdout, stderr).
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{HEADER}{program}")).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        output.status.code().expect("normal process exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

#[test]
fn instance_goals_with_universe_holes_resolve_as_at_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in [
        (
            "two",
            "def h {α β} [Add α] [Mul β] (a : α) (b : β) : α × β := (a + a, b * b)\ntheorem t : h 2 3 = (4, 9) := rfl\n",
        ),
        ("punit", "def x := (default : PUnit)\n"),
        (
            "option",
            "def o {α} : Option α := default\ntheorem t : (o : Option Nat) = none := rfl\n",
        ),
        (
            "decide",
            "def dd [DecidableEq α] (a b : α) : Bool := decide (a = b)\ntheorem t : dd 1 2 = false := rfl\n",
        ),
        (
            "chain",
            "instance [Inhabited α] : Inhabited (α × α) := ⟨(default, default)⟩\ndef p {α} [Inhabited α] : α × α := default\n",
        ),
        // The search chooses the universe: `instInhabitedProp` answers `Inhabited (Sort ?u)`.
        ("sort_true", "example : (default : Sort _) = True := rfl\n"),
        ("prop_true", "example : (default : Prop) = True := rfl\n"),
        (
            "type_punit",
            "example : (default : Type _) = PUnit := rfl\n",
        ),
        ("def_sort", "def s := (default : Sort _)\n"),
        (
            "def_type",
            "def s := (default : Type _)\ntheorem t : s.{0} = PUnit := rfl\n",
        ),
        (
            "punit_rfl",
            "example : (default : PUnit) = PUnit.unit := rfl\n",
        ),
        ("option_type", "def o := (default : Option (Type _))\n"),
        ("nonempty", "example : Nonempty (Sort _) := inferInstance\n"),
        (
            "ulift",
            "def u := (default : ULift Nat)\ntheorem t : u.down = 0 := rfl\n",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn universe_hole_refusals_match_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        // `Sort _` is answered by `Prop`, so its default is `True`, not `PUnit` or `False`.
        (
            "sort_punit",
            "example : (default : Sort _) = PUnit := rfl\n",
            "Type mismatch",
        ),
        (
            "sort_false",
            "example : (default : Sort _) = False := rfl\n",
            "Type mismatch",
        ),
        (
            "prop_punit",
            "example : (default : Prop) = PUnit := rfl\n",
            "Type mismatch",
        ),
        (
            "type_true",
            "example : (default : Type _) = True := rfl\n",
            "Type mismatch",
        ),
        (
            "ulift_wrong",
            "def u := (default : ULift Nat)\ntheorem t : u.down = 1 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "no_instance",
            "def f {α} : α := default\n",
            "failed to synthesize instance of type class",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: {pin}): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
}
