//! Interpolated strings expand to real class applications that execute through Golem.
//! The Reference is executed only here as the differential oracle.

use super::*;

const IMPORTS: &str = "prelude\nimport Init.Data.ToString.Basic\nimport Init.Data.ToString.Macro\nimport Init.Data.String.Defs\n";
const PROGRAM: &str = r#"
def greeting (who : String) (n : Nat) := s!"hello {who} {n + 1}"
#eval greeting "world" 41
#eval s!""
#eval s!"\{\\{(7 : Nat)}\u2665"
#eval s!"outer {s!"inner {true}"}"
structure Label where
  text : String
instance : ToString Label where
  toString value := "[" ++ value.text ++ "]"
#eval s!"value={Label.mk "custom"}"
def hygienic (toString : Nat -> Nat) (String : Nat) (n : Nat) := s!"{n + (toString String - toString String)}"
#eval hygienic (fun x => x + 100) 999 42
namespace Shadow
def ToString.toString (value : Nat) := value + 100
def String := Nat
def value := s!"{(7 : Nat)}"
end Shadow
#eval Shadow.value
section
local instance : ToString String where
  toString value := "[" ++ value ++ "]"
#eval s!"left{(7 : Nat)}right"
#eval s!""
#eval s!"{(7 : Nat)}"
end
"#;

fn reference(lib: &Path) -> PathBuf {
    std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            lib.parent()
                .and_then(Path::parent)
                .expect("the Reference lib/lean directory")
                .join("bin/lean")
        })
}

fn lean(
    workspace: &Workspace,
    executable: &Path,
    entry: &Path,
    lib: &Path,
) -> std::process::Output {
    Command::new(executable)
        .arg(entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", full_io_records(workspace))
        .output()
        .expect("run Lean source")
}

#[test]
fn interpolation_matches_the_pin_with_imported_and_local_instances_and_recovers_after_errors() {
    let Some(lib) = pinned_lib() else { return };
    let oracle = reference(&lib);
    assert!(
        oracle.is_file(),
        "Reference executable: {}",
        oracle.display()
    );
    let workspace = Workspace::new("string-interpolation");
    let source = format!("{IMPORTS}{PROGRAM}");
    let entry = workspace.write("Main.lean", &source);
    let expected = lean(&workspace, &oracle, &entry, &lib);
    assert!(expected.status.success(), "Reference: {expected:?}");
    assert!(expected.stderr.is_empty(), "Reference: {expected:?}");
    let executable = Path::new(env!("CARGO_BIN_EXE_lean"));
    let actual = lean(&workspace, executable, &entry, &lib);
    assert!(actual.status.success(), "FrankenLean: {actual:?}");
    assert!(actual.stderr.is_empty(), "FrankenLean: {actual:?}");
    assert_eq!(
        actual.stdout, expected.stdout,
        "class dispatch and escaping differ"
    );

    // A refusal must not leave a cached declaration or expansion behind for a retry.
    for invalid in [
        format!("{IMPORTS}inductive NoPrinter where | value\n#eval s!\"{{NoPrinter.value}}\"\n"),
        format!("{IMPORTS}def wrong : Nat := s!\"{{(1 : Nat)}}\"\n"),
        // ToString's class and instances do not make the macro available without its import.
        "prelude\nimport Init.Data.ToString.Basic\n#eval s!\"closed\"\n".to_string(),
    ] {
        workspace.write("Main.lean", invalid);
        let pin = lean(&workspace, &oracle, &entry, &lib);
        assert_eq!(pin.status.code(), Some(1), "Reference: {pin:?}");
        let refused = lean(&workspace, executable, &entry, &lib);
        assert_eq!(refused.status.code(), Some(1), "FrankenLean: {refused:?}");
        assert!(
            refused.stdout.is_empty(),
            "a refused program produced output: {refused:?}"
        );
    }
    workspace.write("Main.lean", &source);
    let recovered = lean(&workspace, executable, &entry, &lib);
    assert!(
        recovered.status.success(),
        "FrankenLean retry: {recovered:?}"
    );
    assert!(
        recovered.stderr.is_empty(),
        "FrankenLean retry: {recovered:?}"
    );
    assert_eq!(recovered.stdout, expected.stdout);
    assert_eq!(std::fs::read_to_string(&entry).unwrap(), source);
}
