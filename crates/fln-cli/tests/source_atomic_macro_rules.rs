//! Atomic quoted macros through the installed personality, compared with the pin.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::Command;

#[test]
fn upstream_414_and_macro_capture_warnings_match_the_reference() {
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
        .filter(|path| path.join("Init/Core.olean").is_file());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let reference = std::env::var_os("FLN_REFERENCE_BIN")
        .map(PathBuf::from)
        .unwrap_or_else(|| lib.parent().unwrap().parent().unwrap().join("bin/lean"));
    let root = std::env::temp_dir().join(format!(
        "fln-atomic-macros-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&root).unwrap();
    // The body is upstream 414, unchanged. Core supplies its quotation coercions;
    // keeping that header explicit also exercises the imported source world.
    let upstream = include_str!("../../../vendor/lean4-src/tests/elab/414.lean");
    let source = format!("prelude\nimport Init.Core\n{upstream}");
    let options = r#"prelude
import Init.Core
set_option linter.unusedVariables.patternVars false
macro_rules (kind := num) | `($quiet:num) => `("quiet")
#check 2
set_option linter.unusedVariables.patternVars true
macro_rules (kind := num) | n => `("loud")
#check 2
macro_rules (kind := num) | _ignored => `("anonymous")
#check 2
"#;
    let identifiers = r#"prelude
import Init.Core
def queryMacroTarget : Nat := 9
macro_rules
  | `(queryMacroTarget) => `(7)
  | `(undeclaredMacroTarget) => `(7)
#check queryMacroTarget
#check (queryMacroTarget)
#check undeclaredMacroTarget
"#;
    for (file, source, warning_count) in [
        ("Upstream414.lean", source.as_str(), 3),
        ("WarningOptions.lean", options, 1),
        ("IdentifierQueries.lean", identifiers, 0),
    ] {
        std::fs::write(root.join(file), source).unwrap();
        let oracle = Command::new(&reference)
            .arg(file)
            .current_dir(&root)
            .env("LEAN_PATH", &lib)
            .output()
            .expect("run the pinned Lean oracle");
        assert!(oracle.status.success(), "{oracle:?}");
        assert!(oracle.stderr.is_empty(), "{oracle:?}");
        let oracle_stdout = String::from_utf8(oracle.stdout).unwrap();
        assert_eq!(oracle_stdout.matches("warning:").count(), warning_count);
        let native = Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(file)
            .current_dir(&root)
            .env("LEAN_PATH", &lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run the native Lean personality");
        assert!(native.status.success(), "{native:?}");
        assert!(native.stderr.is_empty(), "{native:?}");
        assert_eq!(String::from_utf8(native.stdout).unwrap(), oracle_stdout);
        assert_eq!(std::fs::read_to_string(root.join(file)).unwrap(), source);
    }
}
