//! Installed commands replay only the syntax exported by actual source imports.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "fln-cli-module-grammar-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, source: &str) {
        std::fs::write(self.0.join(name), source).unwrap();
    }

    fn invoke(&self, command: &str) -> Output {
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([command, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", self.0.join("no-installed-artifacts"))
            .env("FLN_IMPORT_REUSE_DIR", self.0.join("records"))
            .output()
            .unwrap()
    }

    fn complete(&self, command: &str) -> String {
        let output = self.invoke(command);
        assert!(
            output.status.success(),
            "{command}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert_eq!(stdout.lines().count(), 1, "{stdout}");
        stdout
    }

    fn refused(&self, command: &str) -> String {
        let output = self.invoke(command);
        assert!(!output.status.success(), "{command} unexpectedly succeeded");
        assert!(
            output.stdout.is_empty(),
            "a failed source graph exposed a partial result: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(!stderr.is_empty());
        stderr
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn installed_checker_loads_syntax_only_diamonds_before_parsing_consumers() {
    let p = Project::new();
    p.write(
        "Lib.lean",
        "notation \"⟪\" x \"⟫\" => Nat.add x x\nmacro \"checked_rfl\" : tactic => `(tactic| rfl)\n",
    );
    p.write("Left.lean", "import Lib\ndef left := ⟪(10 : Nat)⟫\n");
    p.write("Right.lean", "import Lib\ndef right := ⟪(11 : Nat)⟫\n");
    let main = "import Left\nimport Right\nimport Left\ntheorem answer : left + right = 42 := by checked_rfl\n";
    p.write("Main.lean", main);
    let result = p.complete("check-source");
    assert!(result.contains("\"files\":4"), "{result}");
    assert!(result.contains("\"theorems\":1"), "{result}");
    assert!(result.contains("\"executed\":false"), "{result}");
    assert_eq!(
        std::fs::read(p.0.join("Main.lean")).unwrap(),
        main.as_bytes()
    );
}

#[test]
fn installed_checker_keeps_import_and_scope_boundaries_for_custom_tokens() {
    let p = Project::new();
    p.write("Lib.lean", "notation \"⟪\" x \"⟫\" => Nat.add x x\n");
    p.write("Other.lean", "def stolen := ⟪(2 : Nat)⟫\n");
    p.write("Main.lean", "import Lib\nimport Other\n");
    assert!(p.refused("check-source").contains("Other"));

    p.write(
        "Lib.lean",
        "section\nlocal notation \"⟪\" x \"⟫\" => Nat.add x x\ntheorem internal : ⟪(2 : Nat)⟫ = 4 := rfl\nend\n",
    );
    p.write("Main.lean", "import Lib\n");
    p.complete("check-source");
    p.write(
        "Main.lean",
        "import Lib\ntheorem leaked : ⟪(2 : Nat)⟫ = 4 := rfl\n",
    );
    p.refused("check-source");

    p.write(
        "Lib.lean",
        "namespace Ops\nscoped infixl:65 \" +++ \" => Nat.add\nend Ops\n",
    );
    p.write(
        "Main.lean",
        "import Lib\nsection\nopen scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend\n",
    );
    p.complete("check-source");
    p.write(
        "Main.lean",
        "import Lib\nsection\nopen scoped Ops\ntheorem works : (2 : Nat) +++ 3 = 5 := rfl\nend\ntheorem leaked : (2 : Nat) +++ 3 = 5 := rfl\n",
    );
    p.refused("check-source");
}

#[test]
fn installed_executor_replays_imported_quoted_rules_without_an_ambient_prelude() {
    let p = Project::new();
    p.write(
        "Core.lean",
        "prelude\ninductive Bool where\n  | false\n  | true\n",
    );
    p.write(
        "Lib.lean",
        "prelude\nimport Core\nsyntax (name := «quoted.kind») \"selected \" term:max : term\nmacro_rules | `(selected $x) => `($x)\n",
    );
    p.write(
        "Main.lean",
        "prelude\nimport Lib\n#check Bool\n#eval selected Bool.true\n",
    );
    let result = p.complete("run");
    assert!(
        result.contains("\"kind\":\"bool\",\"value\":true"),
        "{result}"
    );
    assert!(result.contains("\"module\":\"Core\""), "{result}");
    assert!(result.contains("\"module\":\"Lib\""), "{result}");
    assert!(result.contains("\"module\":\"Main\""), "{result}");

    // A fresh invocation must observe the edited syntax-only dependency, even
    // though it contains no ordinary declaration that could anchor a change.
    p.write(
        "Lib.lean",
        "prelude\nimport Core\nsyntax (name := «quoted.kind») \"selected \" term:max : term\nmacro_rules | `(selected $x) => `(Bool.false)\n",
    );
    let changed = p.complete("run");
    assert!(
        changed.contains("\"kind\":\"bool\",\"value\":false"),
        "{changed}"
    );

    p.write(
        "Main.lean",
        "prelude\nimport Lib\n#eval selected Bool.true\n#eval missing\n",
    );
    p.refused("run");
}

fn pinned_toolchain() -> Option<(PathBuf, PathBuf)> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|path| path.join("Init.olean").is_file());
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            library
                .as_ref()?
                .parent()?
                .parent()
                .map(|root| root.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    let Some((reference, library)) = reference.zip(library) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "module-local grammar requires the pinned Reference and actual Init artifacts"
        );
        eprintln!("SKIP: module-local grammar differential requires the pinned Reference");
        return None;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert!(
        String::from_utf8_lossy(&version.stdout).trim() == fln::OLEAN_PIN_COMMIT,
        "{}",
        String::from_utf8_lossy(&version.stdout)
    );
    Some((reference, library))
}

impl Project {
    fn imported(&self, library: &Path, command: &str) -> Output {
        let records = std::env::var_os("FLN_IMPORT_REUSE_DIR")
            .map(PathBuf::from)
            .filter(|path| path.is_absolute())
            .unwrap_or_else(|| self.0.join("records"));
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([command, "--json", "Main.lean"])
            .current_dir(&self.0)
            .env("LEAN_PATH", library)
            .env("FLN_IMPORT_REUSE_DIR", records)
            .output()
            .unwrap()
    }

    fn imported_complete(&self, library: &Path) {
        let output = self.imported(library, "run");
        assert!(
            output.status.success() && output.stderr.is_empty(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("\"outcome\":\"complete\""), "{stdout}");
        assert!(stdout.contains("\"value\":42"), "{stdout}");
    }

    fn imported_refused(&self, library: &Path) -> String {
        let output = self.imported(library, "run");
        assert!(!output.status.success());
        assert!(
            output.stdout.is_empty(),
            "partial source-module result: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        String::from_utf8(output.stderr).unwrap()
    }

    fn reference(&self, reference: &Path, library: &Path, args: &[&str]) -> Output {
        // Reference products never enter the native search path: FlN must
        // check Lib.lean itself and retain only its public logical exports.
        Command::new(reference)
            .arg("-j1")
            .args(args)
            .current_dir(&self.0)
            .env(
                "LEAN_PATH",
                std::env::join_paths([self.0.join("reference"), library.to_path_buf()]).unwrap(),
            )
            .output()
            .unwrap()
    }
}

const MODULE_LOCAL_GRAMMAR: &str = r#"module
namespace Source
private theorem identity (P : Prop) (h : P) : P := h
local notation "localProof" => identity
local syntax (name := localForward) "forwardLocal! " term:max : term
local macro_rules | `(forwardLocal! $value) => `($value)
local macro "twiceLocal! " value:term:max : term => `(Nat.add $value $value)
local infixl:65 " +local+ " => Nat.add
namespace Shadow
private theorem identity (P : Prop) (h : False) : P := False.elim h
public theorem checked (P : Prop) (h : P) : P := localProof P (forwardLocal! h)
@[expose] public def answer : Nat := twiceLocal! (20 +local+ 1)
end Shadow
end Source
"#;

#[test]
fn installed_module_local_grammar_uses_real_init_and_preserves_module_boundaries() {
    let Some((reference, library)) = pinned_toolchain() else {
        return;
    };
    let p = Project::new();
    std::fs::create_dir(p.0.join("reference")).unwrap();
    let main = "module\npublic import Lib\npublic theorem total : Source.Shadow.answer = 42 := rfl\n#eval Source.Shadow.answer\n";
    p.write("Lib.lean", MODULE_LOCAL_GRAMMAR);
    p.write("Main.lean", main);
    let compile_provider = || {
        let output = p.reference(
            &reference,
            &library,
            &["-o", "reference/Lib.olean", "Lib.lean"],
        );
        assert!(output.status.success(), "{output:?}");
    };
    compile_provider();
    let oracle = p.reference(&reference, &library, &["Main.lean"]);
    assert!(oracle.status.success(), "{oracle:?}");
    assert_eq!(String::from_utf8_lossy(&oracle.stdout), "42\n");
    p.imported_complete(&library);
    p.imported_complete(&library);

    // The provider's local syntax must not escape through its usage marker.
    p.write("Main.lean", "module\npublic import Lib\npublic theorem stolen (P : Prop) (h : P) : P := forwardLocal! h\n");
    assert!(
        !p.reference(&reference, &library, &["Main.lean"])
            .status
            .success()
    );
    p.imported_refused(&library);

    // An unrelated sibling cannot receive parser state from a previously
    // checked provider, even when the entry imports both modules.
    p.write(
        "Right.lean",
        "module\npublic theorem stolen (P : Prop) (h : P) : P := forwardLocal! h\n",
    );
    p.write(
        "Main.lean",
        "module\npublic import Lib\npublic import Right\n",
    );
    assert!(
        !p.reference(&reference, &library, &["Right.lean"])
            .status
            .success()
    );
    assert!(p.imported_refused(&library).contains("Right"));

    p.write("Main.lean", "module\nsection\nlocal macro \"kept! \" value:term:max : term => `($value)\npublic theorem before (P : Prop) (h : P) : P := kept! h\nend\npublic theorem after (P : Prop) (h : P) : P := kept! h\n");
    assert!(
        !p.reference(&reference, &library, &["Main.lean"])
            .status
            .success()
    );
    p.imported_refused(&library);

    // Reused import records cannot preserve a proof after its source macro
    // changes. Recovery with the original source must succeed again.
    p.write("Main.lean", main);
    p.write(
        "Lib.lean",
        &MODULE_LOCAL_GRAMMAR.replace(
            "(Nat.add $value $value)",
            "(Nat.add $value (Nat.add $value $value))",
        ),
    );
    compile_provider();
    assert!(
        !p.reference(&reference, &library, &["Main.lean"])
            .status
            .success()
    );
    p.imported_refused(&library);
    p.write("Lib.lean", MODULE_LOCAL_GRAMMAR);
    p.imported_complete(&library);

    // A global registration still generates an exported meta declaration;
    // merely targeting a local syntax kind does not make that rule local.
    p.write("Main.lean", "module\nlocal syntax \"kept! \" term:max : term\nmacro_rules | `(kept! $value) => `($value)\n");
    assert!(
        p.imported_refused(&library)
            .contains("module-system exports")
    );

    // Runtime Init is present, but `prelude` suppresses its implicit meta
    // import. Both checker and execution must retain that original header.
    p.write("Main.lean", "module\nprelude\npublic import Init\nlocal syntax \"kept! \" term:1024 : term\nlocal macro_rules | `(kept! $value) => `($value)\npublic theorem kept (P : Prop) (h : P) : P := kept! h\n");
    assert!(
        p.imported_refused(&library)
            .contains("implicit Init meta imports")
    );
    let checked = p.imported(&library, "check-source");
    assert!(!checked.status.success(), "{checked:?}");
    assert!(
        String::from_utf8_lossy(&checked.stderr).contains("implicit Init meta imports"),
        "{checked:?}"
    );

    // Source checking cannot yet serialize the generated private meta
    // declarations. The explicit artifact request must publish no products.
    let artifact = p.0.join("Local.olean");
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .args(["-j1", "-o"])
        .arg(&artifact)
        .arg("Lib.lean")
        .current_dir(&p.0)
        .env("LEAN_PATH", &library)
        .env(
            "FLN_IMPORT_REUSE_DIR",
            std::env::var_os("FLN_IMPORT_REUSE_DIR")
                .map(PathBuf::from)
                .filter(|path| path.is_absolute())
                .unwrap_or_else(|| p.0.join("records")),
        )
        .output()
        .unwrap();
    assert!(!output.status.success(), "{output:?}");
    let diagnostic = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        diagnostic.contains("sourceGrammar") || diagnostic.contains("source grammar"),
        "{diagnostic}"
    );
    for path in [
        artifact.clone(),
        artifact.with_extension("olean.server"),
        artifact.with_extension("olean.private"),
    ] {
        assert!(!path.exists(), "failed grammar export published {path:?}");
    }
}
