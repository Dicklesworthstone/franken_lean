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
    // selected String projection still has ample room for real computation.
    limits.vm.max_steps = 5_000;
    let declarations = r#"
import Lake
open System Lake DSL
def countDown : Nat → Nat
  | 0 => 0
  | Nat.succ n => countDown n + 1
def unusedComputation : Nat := countDown 10000000
def folder (suffix : String) : FilePath := FilePath.mk ("src/" ++ suffix)
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
"#;
    let config = configured(&engine, declarations, limits)
        .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
    assert_eq!(config.src_dir, PathBuf::from("src/lean"));
    assert_eq!(config.build_dir, PathBuf::from(".lake/native"));
    assert_eq!(config.targets[0].src_dir, Some(PathBuf::from("proofs")));
    assert_eq!(config.default_targets, ["Demo"]);
    assert_eq!(config.targets[0].roots, ["Demo"]);

    // A field-free ordinary package retains Lake's defaults without evaluating
    // even one of the user's closed definitions.
    let default = configured(
        &engine,
        "import Lake\nopen Lake DSL\npackage bare\n@[default_target] lean_lib Bare\n",
        limits,
    )
    .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
    assert_eq!(default.src_dir, PathBuf::from("."));
    assert_eq!(default.build_dir, PathBuf::from(".lake/build"));

    for source in [
        "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := (42 : Nat)\nlean_lib Bad\n",
        // This comes after a well-typed field. It still prevents every execution.
        "import Lake\nopen Lake DSL\npackage bad where\n  srcDir := \"src\"\ndef invalidUnused : Nat := \"wrong\"\nlean_lib Bad\n",
    ] {
        let error = configured(&engine, source, limits).unwrap_err();
        assert_eq!(error.class, "elaboration", "{}", error.detail);
        assert!(!error.authority);
    }
    for source in [
        "import Lake\nopen Lake DSL\nunsafe def unsafePath : System.FilePath := System.FilePath.mk \"src\"\npackage bad where\n  srcDir := unsafePath\nlean_lib Bad\n",
        "import Lake\nopen Lake DSL\n@[extern \"foreign_lake_path\"] def foreignPath : System.FilePath := System.FilePath.mk \"src\"\npackage bad where\n  srcDir := foreignPath\nlean_lib Bad\n",
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

    let mut exhausted = limits;
    exhausted.vm.max_steps = 0;
    let error = configured(&engine, declarations, exhausted).unwrap_err();
    assert_eq!(error.class, "inconclusive", "{}", error.detail);
    assert!(!error.authority);
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
