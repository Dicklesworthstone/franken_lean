//! `Σ xs, b` and `Σ' xs, b` (`Init/NotationExtra.lean`), expanded as the pin's
//! `expandExplicitBinders ``Sigma` and `expandExplicitBinders ``PSigma`: one `Sigma fun x : T => …`
//! per bound name, innermost last. As at the pin, they exist only where `Init.NotationExtra` is
//! imported. Over `prelude` + `import Init.Core` every program here is refused, as the pin refuses it
//! ("expected token"). Every program was run through the pinned `lean` v4.32.0 with both headers
//! first (2026-10-11), with the same verdicts.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.NotationExtra\n";
/// The closure without `Init.NotationExtra`, where the pin has no `Σ` token.
const CORE_HEADER: &str = "prelude\nimport Init.Core\n";

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
        .filter(|lib| lib.join("Init/NotationExtra.olean").is_file());
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
        "fln-sigma-binders-{case}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source --json` on `header` + `program`: (exit code, stdout, stderr).
fn check(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> (i32, String, String) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
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

const ACCEPTED: [(&str, &str); 8] = [
    ("type", "def s1 : Type := Σ n : Nat, Fin (n + 1)\n"),
    (
        "brackets",
        "def s2 : Type := Σ (a : Nat) (b : Nat), Fin (a + b + 1)\n",
    ),
    (
        "value",
        "def p : Σ n : Nat, Fin (n + 1) := ⟨0, ⟨0, Nat.zero_lt_succ 0⟩⟩\n",
    ),
    (
        "projection",
        "theorem t : (⟨1, 2⟩ : Σ _ : Nat, Nat).2 = 2 := rfl\n",
    ),
    ("psigma", "def s3 := Σ' x : Nat, x = 1\n"),
    ("two_names", "def s4 : Type 1 := Σ α n, Fin (n + 1) → α\n"),
    (
        "unfolds_to_sigma",
        "theorem t2 : (Σ n : Nat, Fin n) = Sigma (fun n : Nat => Fin n) := rfl\n",
    ),
    (
        "unfolds_to_psigma",
        "theorem t3 : (Σ' n : Nat, n = n) = PSigma (fun n : Nat => n = n) := rfl\n",
    ),
];

#[test]
fn sigma_binders_expand_as_their_macros() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("accepted");
    for (name, program) in ACCEPTED {
        let (code, stdout, stderr) = check(&lib, &root, name, HEADER, program);
        assert_eq!(code, 0, "{name}: {program}\n{stdout}\n{stderr}");
    }
}

#[test]
fn sigma_binder_refusals_match_the_pin() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace("refused");
    for (name, program, pin) in [
        (
            "empty_fin",
            "def bad : Σ n : Nat, Fin n := ⟨0, ⟨0, rfl⟩⟩\n",
            "Application type mismatch",
        ),
        (
            "predicate",
            "def bad2 := Σ x > 0, x = x\n",
            "unexpected token '>'; expected ','",
        ),
        (
            "prop",
            "def bad3 : Prop := Σ' x : Nat, x = 1\n",
            "Type mismatch",
        ),
        (
            "projection",
            "theorem bad4 : (⟨1, 2⟩ : Σ _ : Nat, Nat).2 = 3 := rfl\n",
            "Not a definitional equality",
        ),
        (
            "not_exists",
            "theorem bad5 : (Σ n : Nat, Fin n) = Exists (fun n : Nat => n = n) := rfl\n",
            "Type mismatch",
        ),
    ] {
        let (code, stdout, stderr) = check(&lib, &root, name, HEADER, program);
        assert_ne!(
            code, 0,
            "{name} accepted (the pin: {pin}): {program}\n{stdout}"
        );
        assert!(stderr.contains("\"outcome\""), "{name}: {stderr}");
    }
    // Without `Init.NotationExtra` the pin has no `Σ` token at all.
    for (name, program) in ACCEPTED {
        let (code, stdout, _) = check(&lib, &root, &format!("core_{name}"), CORE_HEADER, program);
        assert_ne!(
            code, 0,
            "{name} accepted without Init.NotationExtra (the pin: expected token)\n{stdout}"
        );
    }
}
