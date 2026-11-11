//! Ordinary public stdlib imports use checked private implementation receipts
//! while preserving the actual primary artifact's logical visibility.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWriteBudget, SourceCheckLimits, SourceModuleInput,
};
use std::path::PathBuf;
use std::process::Command;

const STACK: usize = 256 << 20;
const SOURCE: &str =
    "module\nprelude\npublic import Init.Notation\npublic def answer : Nat := 42\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn reference() -> Option<(PathBuf, PathBuf)> {
    let default = std::env::var_os("HOME")
        .map(|home| PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0"));
    let lean = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
        .or_else(|| default.as_ref().map(|root| root.join("bin/lean")));
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| default.map(|root| root.join("lib/lean")));
    match (lean, lib) {
        (Some(lean), Some(lib)) if lean.is_file() && lib.is_dir() => Some((lean, lib)),
        _ => {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference binary and library are required"
            );
            eprintln!("SKIP: pinned Reference binary or library unavailable");
            None
        }
    }
}

#[test]
fn public_notation_import_builds_a_native_module_without_exposing_private_helpers() {
    let Some((lean, lib)) = reference() else {
        return;
    };
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8_lossy(&identity.stdout).trim(),
        fln_olean::format::PIN_COMMIT
    );
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let fixture =
        std::env::temp_dir().join(format!("fln-public-stdlib-{}-{unique}", std::process::id()));
    std::fs::create_dir(&fixture).unwrap();
    std::fs::write(fixture.join("Main.lean"), SOURCE).unwrap();
    let verdict = Command::new(&lean)
        .current_dir(&fixture)
        .arg("Main.lean")
        .output()
        .unwrap();
    assert!(
        verdict.status.success(),
        "{}{}",
        String::from_utf8_lossy(&verdict.stdout),
        String::from_utf8_lossy(&verdict.stderr)
    );

    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let names: Vec<_> = ["Init.Prelude", "Init.Coe", "Init.Notation"]
                .into_iter()
                .map(name)
                .collect();
            let parts: Vec<[Vec<u8>; 3]> = names
                .iter()
                .map(|module| {
                    let path = lib
                        .join(module.to_display_string().replace('.', "/"))
                        .with_extension("olean");
                    [
                        std::fs::read(&path).unwrap(),
                        std::fs::read(path.with_extension("olean.server")).unwrap(),
                        std::fs::read(path.with_extension("olean.private")).unwrap(),
                    ]
                })
                .collect();
            let inputs: Vec<_> = names
                .iter()
                .zip(&parts)
                .map(|(name, [public, server, private])| OleanModuleInput {
                    name,
                    artifact: public,
                    server_artifact: Some(server),
                    private_artifact: Some(private),
                })
                .collect();
            let options = KVMap::new();
            let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK));
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    &[name("Init.Notation")],
                    &options,
                    SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, admission.kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let root = imported.engine.logical_root(&options);
            let private_prefix = Name::num(name("_private.Init.Prelude"), 0);
            let helper = private_prefix.append_core(&name("Lean.Syntax.getHeadInfo?.match_1"));
            let implementation = name("Lean.Syntax.getHeadInfo?._unsafe_rec");
            assert!(imported.engine.environment().contains(&helper));

            let main = name("Main");
            let built = imported
                .compile_source_modules(
                    &[SourceModuleInput {
                        name: &main,
                        source: SOURCE.as_bytes(),
                    }],
                    &main,
                    &options,
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
                    OleanWriteBudget::default(),
                )
                .unwrap_or_else(|error| panic!("public Init.Notation import: {error:?}"))
                .into_complete()
                .unwrap();
            let environment = built.checked.checked.engine.environment();
            assert!(!environment.contains(&helper));
            assert_eq!(
                environment.find(&implementation),
                imported.engine.environment().find(&implementation)
            );
            assert!(matches!(
                environment.find(&implementation),
                Some(ConstantInfo::Defn(_))
            ));
            assert!(environment.contains(&name("answer")));
            assert_eq!(built.artifacts.len(), 1);
            assert_eq!(built.artifacts[0].name, main);
            assert!(built.artifacts[0].companions.is_some());
            assert_eq!(imported.engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}
