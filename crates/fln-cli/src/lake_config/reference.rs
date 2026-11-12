//! Actual pinned FilePath declarations, metadata, source checking and Golem execution.
use super::*;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{Budget, Engine, Environment, KVMap, OleanCheckLimits, OleanDecodeLimits};
use std::num::NonZeroUsize;

const BYTES: usize = 512 * 1024 * 1024;

fn reference_engine() -> Option<Engine> {
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
        .filter(|lib| lib.join("Init/System/FilePath.olean").is_file());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned FilePath artifacts are required"
        );
        eprintln!("SKIP: pinned Reference FilePath artifacts absent");
        return None;
    };
    let root = Name::from_components(["Init", "System", "FilePath"]);
    let mut pending = vec![root.clone()];
    let mut artifacts = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if artifacts.contains_key(&module) {
            continue;
        }
        let path = lib
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        pending
            .extend(fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES)).unwrap());
        artifacts.insert(module, parts);
    }
    let modules: Vec<_> = artifacts
        .iter()
        .map(|(name, parts)| fln::OleanModuleInput {
            name,
            artifact: &parts[0],
            server_artifact: Some(&parts[1]),
            private_artifact: Some(&parts[2]),
        })
        .collect();
    let mut limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        BYTES,
        Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
    ));
    limits.jobs = fln::OleanFrontierJobs {
        threads: NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: OLEAN_CHECK_KERNEL_STACK_BYTES,
    };
    let started = std::time::Instant::now();
    eprintln!("Lake reference: admitting {} actual modules", modules.len());
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(&modules, &[root], &KVMap::new(), limits)
        .expect("import the actual FilePath dependency closure")
        .into_complete()
        .expect("the real FilePath closure passes both checking engines");
    eprintln!(
        "Lake reference: admission completed in {:?}",
        started.elapsed()
    );
    Some(imported.engine)
}

fn configured(
    engine: &Engine,
    source: &str,
    limits: fln::EngineExecutionLimits,
) -> Result<LakeConfig, Failure> {
    evaluate(parse(source.as_bytes())?, engine.clone(), limits)
}

/// The full-admission and raw-data diagnostics exercise identical configuration
/// behavior. Only their construction of the imported engine differs.
pub(super) fn assert_configuration_cases(engine: Engine) {
    let mut limits = fln::EngineExecutionLimits::for_user_program(Budget::for_stack_bytes(
        SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    // An accidentally eager `unusedComputation` cannot fit this budget. Each
    // selected path or roots field still has ample room for real computation.
    limits.vm.max_steps = 5_000;
    let declarations = r#"
import Lake
open System Lake DSL
def countDown : Nat → Nat
  | 0 => 0
  | Nat.succ n => countDown n + 1
def unusedComputation : Nat := countDown 10000000
def folder (suffix : String) : FilePath := FilePath.mk ("src/" ++ suffix)
def libraryRoot (suffix : String) : Lean.Name :=
  Lean.Name.str (Lean.Name.str Lean.Name.anonymous "Demo") suffix
def selectedRoots (suffix : String) : Array Lean.Name :=
  Array.push #[libraryRoot suffix, Lean.Name.str Lean.Name.anonymous "Other"] (libraryRoot suffix)
def _fln_lake_path_0 : Nat := 7
def _fln_lake_path_1_result_0 : String := "wrong"
namespace Config
scoped notation "◆" s => folder s
end Config
open scoped Config
local notation "◇" => "lean"
package demo where
  srcDir := ◆ ◇
  buildDir := FilePath.mk (".lake/" ++ "native")
@[default_target] lean_lib Demo where
  srcDir := "proofs"
  roots := selectedRoots ("Ex" ++ "tra")
lean_lib Empty where
  roots := #[]
lean_lib Literals where
  roots := #[`Literal.Root, `Other]
@[default_target] lean_exe runner where
  srcDir := FilePath.mk ("ap" ++ "p")
  root := libraryRoot ("Ma" ++ "in")
"#;
    let config = configured(&engine, declarations, limits)
        .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
    assert_eq!(config.src_dir, PathBuf::from("src/lean"));
    assert_eq!(config.build_dir, PathBuf::from(".lake/native"));
    assert_eq!(config.targets[0].src_dir, Some(PathBuf::from("proofs")));
    assert_eq!(config.default_targets, ["Demo", "runner"]);
    assert_eq!(
        config.targets[0].roots,
        ["Demo.Extra", "Other", "Demo.Extra"]
    );
    assert!(config.targets[1].roots.is_empty());
    assert_eq!(config.targets[2].roots, ["Literal.Root", "Other"]);
    assert_eq!(config.targets[3].kind, TargetKind::Executable);
    assert_eq!(config.targets[3].roots, ["Demo.Main"]);
    assert_eq!(config.targets[3].src_dir, Some(PathBuf::from("app")));

    // A field-free ordinary package retains Lake's defaults without evaluating
    // even one of the user's closed definitions.
    let default = configured(
        &engine,
        "import Lake\nopen Lake DSL\npackage bare\n@[default_target] lean_lib Bare\nlean_exe Main\n",
        limits,
    )
    .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
    assert_eq!(default.src_dir, PathBuf::from("."));
    assert_eq!(default.build_dir, PathBuf::from(".lake/build"));
    assert_eq!(default.targets[0].roots, ["Bare"]);
    assert_eq!(default.targets[1].kind, TargetKind::Executable);
    assert_eq!(default.targets[1].roots, ["Main"]);

    for source in [
        "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := (42 : Nat)\nlean_lib Bad\n",
        // This comes after a well-typed field. It still prevents every execution.
        "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := \"src\"\ndef invalidUnused : Nat := \"wrong\"\nlean_lib Bad\n",
        "import Lake\nopen Lake DSL\npackage bad\nlean_lib Bad where\n  roots := (#[1] : Array Nat)\n",
        "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := \"src\"\nlean_lib Bad where\n  roots := (42 : Nat)\n",
        "import Lake\nopen Lake DSL\npackage bad\nlean_exe runner where\n  root := (#[`Main] : Array Lean.Name)\n",
        "import Lake\nopen Lake DSL\npackage bad\nlean_exe runner where\n  root := (42 : Nat)\n",
    ] {
        let error = configured(&engine, source, limits).unwrap_err();
        assert_eq!(error.class, "elaboration", "{}", error.detail);
        assert!(!error.authority);
    }
    for source in [
        "import Lake\nopen Lake DSL\nunsafe def unsafePath : System.FilePath := System.FilePath.mk \"src\"\npackage bad where\n  srcDir := unsafePath\nlean_lib Bad\n",
        "import Lake\nopen Lake DSL\n@[extern \"foreign_lake_path\"] def foreignPath : System.FilePath := System.FilePath.mk \"src\"\npackage bad where\n  srcDir := foreignPath\nlean_lib Bad\n",
        "import Lake\nopen Lake DSL\nunsafe def unsafeRoots : Array Lean.Name := #[Lean.Name.str Lean.Name.anonymous \"Bad\"]\npackage bad\nlean_lib Bad where\n  roots := unsafeRoots\n",
        "import Lake\nopen Lake DSL\n@[extern \"foreign_lake_roots\"] def foreignRoots : Array Lean.Name := #[Lean.Name.str Lean.Name.anonymous \"Bad\"]\npackage bad\nlean_lib Bad where\n  roots := foreignRoots\n",
        "import Lake\nopen Lake DSL\nunsafe def unsafeRoot : Lean.Name := `Main\npackage bad\nlean_exe runner where\n  root := unsafeRoot\n",
        "import Lake\nopen Lake DSL\n@[extern \"foreign_lake_root\"] def foreignRoot : Lean.Name := `Main\npackage bad\nlean_exe runner where\n  root := foreignRoot\n",
    ] {
        assert!(configured(&engine, source, limits).is_err());
    }
    let error = configured(
                &engine,
                "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := \"src\"\n  buildDir := \"../escape\"\nlean_lib Bad\n",
                limits,
            )
            .unwrap_err();
    assert_eq!(error.class, "unsupported");
    assert!(error.detail.contains("within the package"));

    // The observer reads Name components, not a flattened display string. In
    // particular the single component "Demo.Extra" is not the checked
    // hierarchical Demo.Extra accepted above, and numerical components cannot
    // alias string components in the module planner.
    for (expression, diagnostic) in [
        ("Lean.Name.anonymous", "anonymous module root"),
        (
            "Lean.Name.num (Lean.Name.str Lean.Name.anonymous \"Demo\") 7",
            "numeric module-name component",
        ),
        (
            "Lean.Name.str Lean.Name.anonymous \"Demo.Extra\"",
            "quoted or special module-name components",
        ),
        (
            "`«Literal.Root»",
            "quoted or special module-name components",
        ),
        (
            "Lean.Name.str (Lean.Name.str Lean.Name.anonymous \"Demo\") \"\"",
            "quoted or special module-name components",
        ),
        (
            "Lean.Name.str Lean.Name.anonymous \"../escape\"",
            "quoted or special module-name components",
        ),
        (
            "Lean.Name.str Lean.Name.anonymous \"A\\\\B\"",
            "quoted or special module-name components",
        ),
    ] {
        for (command, field, value) in [
            ("lean_lib", "roots", format!("#[{expression}]")),
            ("lean_exe", "root", expression.to_owned()),
        ] {
            let source = format!(
                "import Lake\nopen Lake DSL\npackage invalid\n{command} Invalid where\n  {field} := {value}\n"
            );
            let error = configured(&engine, &source, limits).unwrap_err();
            assert_eq!(error.class, "unsupported", "{expression}: {}", error.detail);
            assert!(error.detail.contains(diagnostic), "{}", error.detail);
            assert!(!error.authority);
        }
    }

    // Executable root identity is checked after evaluating the typed fields.
    // Distinct names and directories do not make the same module two targets.
    let conflicting = "import Lake\nopen Lake DSL\ndef entry : Lean.Name := Lean.Name.str Lean.Name.anonymous (\"Ma\" ++ \"in\")\npackage invalid\nlean_exe Main\nlean_exe runner where\n  srcDir := \"other\"\n  root := entry\n";
    let error = configured(&engine, conflicting, limits).unwrap_err();
    assert_eq!(error.class, "input", "{}", error.detail);
    assert!(error.detail.contains("share root module `Main`"), "{}", error.detail);
    assert!(!error.authority);
    let distinct = conflicting.replace("(\"Ma\" ++ \"in\")", "(\"Ot\" ++ \"her\")");
    let config = configured(&engine, &distinct, limits)
        .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
    assert_eq!(config.targets[0].roots, ["Main"]);
    assert_eq!(config.targets[1].roots, ["Other"]);

    assert_root_bounds(&engine, limits);

    let mut exhausted = limits;
    exhausted.vm.max_steps = 0;
    let error = configured(&engine, declarations, exhausted).unwrap_err();
    assert_eq!(error.class, "inconclusive", "{}", error.detail);
    assert!(!error.authority);
    let error = configured(
        &engine,
        "import Lake\nopen Lake DSL\npackage bounded\nlean_lib Bounded where\n  roots := #[Lean.Name.str Lean.Name.anonymous \"Actual\"]\n",
        exhausted,
    )
    .unwrap_err();
    assert_eq!(error.class, "inconclusive", "{}", error.detail);
    assert!(!error.authority);
    let error = configured(
        &engine,
        "import Lake\nopen Lake DSL\npackage bounded\nlean_exe runner where\n  root := `Main\n",
        exhausted,
    )
    .unwrap_err();
    assert_eq!(error.class, "inconclusive", "{}", error.detail);
    assert!(!error.authority);
}

fn assert_root_bounds(engine: &Engine, limits: fln::EngineExecutionLimits) {
    // Short source creates these real values through Golem; no mocked VM
    // return bypasses source typing or selects the native Array layout.
    for count in [256, 257] {
        let elements = std::iter::repeat_n("root", count)
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            "import Lake\nopen Lake DSL\ndef root : Lean.Name := Lean.Name.str Lean.Name.anonymous \"Root\"\npackage bounded\nlean_lib Bounded where\n  roots := #[{elements}]\n"
        );
        let result = configured(engine, &source, limits);
        if count == 256 {
            let config = result.unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
            assert_eq!(config.targets[0].roots, vec!["Root"; count]);
        } else {
            let error = result.unwrap_err();
            assert_eq!(error.class, "resource", "{}", error.detail);
            assert!(
                error.detail.contains("256 module roots"),
                "{}",
                error.detail
            );
        }
    }

    for depth in [128, 129] {
        let source = format!(
            "import Lake\nopen Lake DSL\ndef nested : Nat → Lean.Name\n  | 0 => Lean.Name.anonymous\n  | Nat.succ n => Lean.Name.str (nested n) \"A\"\npackage bounded\nlean_lib Bounded where\n  roots := #[nested {depth}]\n"
        );
        let result = configured(engine, &source, limits);
        if depth == 128 {
            let config = result.unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
            assert_eq!(config.targets[0].roots, [vec!["A"; depth].join(".")]);
        } else {
            let error = result.unwrap_err();
            assert_eq!(error.class, "resource", "{}", error.detail);
            assert!(error.detail.contains("128 components"), "{}", error.detail);
        }
    }

    // A small computed String fits alone, but its two appearances exceed the
    // aggregate output limit. The source itself stays far below the read cap.
    for (roots, accepted) in [("#[root]", true), ("#[root, root]", false)] {
        let source = format!(
            "import Lake\nopen Lake DSL\ndef doubled : Nat → String → String\n  | 0, s => s\n  | Nat.succ n, s => doubled n (s ++ s)\ndef root : Lean.Name := Lean.Name.str Lean.Name.anonymous (doubled 15 \"A\")\npackage bounded\nlean_lib Bounded where\n  roots := {roots}\n"
        );
        let result = configured(engine, &source, limits);
        if accepted {
            let config = result.unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
            assert_eq!(config.targets[0].roots, ["A".repeat(1 << 15)]);
        } else {
            let error = result.unwrap_err();
            assert_eq!(error.class, "resource", "{}", error.detail);
            assert!(error.detail.contains("64 KiB"), "{}", error.detail);
        }
    }
}

#[test]
fn native_lake_reference_configuration_execution() {
    std::thread::Builder::new()
        .name("fln-lake-reference-test".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(|| {
            let Some(engine) = reference_engine() else {
                return;
            };
            assert_configuration_cases(engine);
        })
        .unwrap()
        .join()
        .unwrap();
}
