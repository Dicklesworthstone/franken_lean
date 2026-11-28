//! Constructor protection follows the same checked source and artifact path as
//! protected definitions. In particular SourceInfo.none must not shadow Option.none.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{SourceModuleBuild, SourceModuleCheckLimits};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, OleanWalkBudget, OleanWriteBudget, Outcome, SourceCheckLimits,
    SourceModuleInput,
};
use fln_elab::protected_names::ProtectedNames;
use std::path::{Path, PathBuf};
use std::process::Command;

// The seed includes Option's declarations, not Prelude's command scope. Install
// the same earlier export as Init/Prelude.lean before testing its bare fallback.
const SOURCE_INFO: &str = r#"export Option (none some)
namespace ProtectedCtorOracle
inductive SourceInfo where
  | original (position : Nat)
  /-- A token without position information. -/
  | protected none
def qualified : SourceInfo := SourceInfo.none
def inferred : SourceInfo := .none
namespace SourceInfo
def missing : Option Nat := none
def getPos? (info : SourceInfo) : Option Nat :=
  match info with
  | .original position => some position
  | .none => none
theorem missing_is_option_none : missing = (Option.none : Option Nat) := rfl
theorem no_position : getPos? SourceInfo.none = (Option.none : Option Nat) := rfl
theorem has_position : getPos? (.original 7) = Option.some 7 := rfl
end SourceInfo
open SourceInfo
def ordinary : SourceInfo := original 7
end ProtectedCtorOracle
"#;

const TOKEN: &str =
    "namespace Guard\ninductive Token where\n  | protected hidden\n  | visible\nend Guard\n";
const USE_TOKEN: &str = "open Guard.Token\ndef qualified : Guard.Token := Guard.Token.hidden\ndef inferred : Guard.Token := .hidden\ndef ordinary : Guard.Token := visible\nnamespace Facade\nexport Guard.Token (hidden)\nend Facade\ndef aliasQualified : Guard.Token := Facade.hidden\n";
const ATOMIC_USES: &[&str] = &[
    "open Guard.Token\ndef bad : Guard.Token := hidden\n",
    "namespace Guard.Token\ndef bad : Guard.Token := hidden\nend Guard.Token\n",
    "export Guard.Token (hidden)\ndef bad : Guard.Token := hidden\n",
    "namespace Facade\nexport Guard.Token (hidden)\nend Facade\nopen Facade\ndef bad : Guard.Token := hidden\n",
];

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

fn refused(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    let tags = ProtectedNames::read(base.environment()).unwrap();
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "accepted {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert_eq!(ProtectedNames::read(base.environment()).unwrap(), tags);
}

#[test]
fn source_info_protected_none_preserves_option_fallback_and_expected_type_lookup() {
    on_stack(|| {
        let base = seed();
        let env = checked(&base, SOURCE_INFO);
        let protected = ProtectedNames::read(env.environment()).unwrap();
        let constructor = name("ProtectedCtorOracle.SourceInfo.none");
        assert!(protected.contains(&constructor));
        assert!(!protected.contains(&name("ProtectedCtorOracle.SourceInfo.original")));
        assert!(!protected.contains(&name("ProtectedCtorOracle.SourceInfo")));
        assert!(matches!(
            env.environment().find(&constructor),
            Some(ConstantInfo::Ctor(_))
        ));
        assert!(!env.environment().is_assumed(&constructor));
        for theorem in ["missing_is_option_none", "no_position", "has_position"] {
            assert!(matches!(
                env.environment()
                    .find(&name(&format!("ProtectedCtorOracle.SourceInfo.{theorem}"))),
                Some(ConstantInfo::Thm(_))
            ));
        }
        assert!(!base.environment().contains(&constructor));
    });
}

#[test]
fn constructor_protection_blocks_atomic_namespace_open_and_export_aliases() {
    on_stack(|| {
        let base = checked(&seed(), TOKEN);
        checked(&base, USE_TOKEN);
        for use_ in ATOMIC_USES {
            refused(&base, use_);
        }
    });
}

#[test]
fn constructor_modifiers_preserve_private_boundaries_and_atomic_admission() {
    on_stack(|| {
        let base = seed();
        for source in [
            "private inductive Secret where\n  | protected hidden\n",
            "inductive Unsupported where\n  | private hidden\n",
            "inductive Unsupported where\n  | public hidden\n",
            "inductive Unsupported where\n  | unsafe hidden\n",
            "inductive Unsupported where\n  | noncomputable hidden\n",
            "inductive DuplicateDoc where\n  /-- First. -/\n  | /-- Second. -/ protected hidden\n",
            "inductive Invalid where\n  | protected bad : Nat\n",
        ] {
            refused(&base, source);
        }
        let root = base.logical_root(&KVMap::new());
        let tags = ProtectedNames::read(base.environment()).unwrap();
        let mut bounded = limits();
        bounded.kernel.steps = 0;
        assert!(matches!(
            base.admit_source_command(
                b"inductive Stopped where | protected hidden",
                &KVMap::new(),
                bounded,
            ),
            Ok(Outcome::Inconclusive(_))
        ));
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert_eq!(ProtectedNames::read(base.environment()).unwrap(), tags);

        // The pin rejects authored `private`, but its inherited module-private
        // default is allowed. The tag must follow the actual mangled name.
        let module = name("Main");
        let source = "module\nprelude\ninductive Hidden where\n  | protected create\n";
        let checked = Engine::builder()
            .build_empty()
            .check_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            )
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let constructor = Name::str(
            Name::str(Name::num(name("_private.Main"), 0), "Hidden"),
            "create",
        );
        assert!(
            ProtectedNames::read(checked.checked.engine.environment())
                .unwrap()
                .contains(&constructor)
        );
        assert!(matches!(
            checked.checked.engine.environment().find(&constructor),
            Some(ConstantInfo::Ctor(_))
        ));
    });
}

fn build(source: &str) -> SourceModuleBuild {
    let module = name("ProtectedConstructors");
    Engine::builder()
        .build_empty()
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

#[test]
fn public_artifacts_reimport_constructor_protection_without_hiding_qualified_names() {
    on_stack(|| {
        for header in ["prelude\n", "module\nprelude\npublic section\n"] {
            let built = build(&format!("{header}{TOKEN}"));
            let artifact = &built.artifacts[0];
            let blocks = fln_olean::region::OleanView::parse(&artifact.bytes)
                .unwrap()
                .extension_payloads(OleanWalkBudget::default(), 16 << 20)
                .unwrap();
            let metadata =
                fln_olean::source_extensions::decode(&blocks, Default::default()).unwrap();
            assert!(metadata.protected.contains(&name("Guard.Token.hidden")));
            assert!(!metadata.protected.contains(&name("Guard.Token.visible")));
            let companions = artifact.companions.as_ref();
            let loaded = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &artifact.name,
                        artifact: &artifact.bytes,
                        server_artifact: companions.map(|parts| parts.server.as_slice()),
                        private_artifact: companions.map(|parts| parts.private.as_slice()),
                    }],
                    std::slice::from_ref(&artifact.name),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(loaded.modules[0].protected, metadata.protected.len());
            assert!(
                ProtectedNames::read(loaded.engine.environment())
                    .unwrap()
                    .contains(&name("Guard.Token.hidden"))
            );
            checked(&loaded.engine, USE_TOKEN);
            for use_ in ATOMIC_USES {
                refused(&loaded.engine, use_);
            }
        }
    });
}

fn reference() -> Option<PathBuf> {
    let compiler = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    let Some(compiler) = compiler else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: protected-constructor oracle requires the pinned Reference");
        return None;
    };
    let identity = Command::new(&compiler).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    Some(compiler)
}

fn pin_check(compiler: &Path, directory: &Path, label: &str, source: &str, success: bool) {
    let file = directory.join(format!("{label}.lean"));
    std::fs::write(&file, source).unwrap();
    let output = Command::new(compiler)
        .current_dir(directory)
        .arg("-j1")
        .arg(&file)
        .output()
        .unwrap();
    assert_eq!(output.status.success(), success, "{source}\n{output:?}");
}

#[test]
fn exact_pin_agrees_on_constructor_lookup_and_reads_native_protected_tags() {
    let Some(compiler) = reference() else {
        return;
    };
    on_stack(|| {
        let directory = std::env::temp_dir().join(format!(
            "fln-protected-constructors-pin-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir(&directory).unwrap();
        pin_check(&compiler, &directory, "source_info", SOURCE_INFO, true);
        pin_check(
            &compiler,
            &directory,
            "qualified",
            &format!("{TOKEN}{USE_TOKEN}"),
            true,
        );
        for (index, source) in ATOMIC_USES.iter().enumerate() {
            pin_check(
                &compiler,
                &directory,
                &format!("atomic_{index}"),
                &format!("{TOKEN}{source}"),
                false,
            );
        }
        pin_check(
            &compiler,
            &directory,
            "private",
            "private inductive Secret where\n  | protected hidden\n",
            false,
        );
        pin_check(
            &compiler,
            &directory,
            "module_private",
            "module\nprelude\ninductive Hidden where\n  | protected create\n",
            true,
        );
        let built = build(&format!("prelude\n{TOKEN}"));
        std::fs::write(
            directory.join("ProtectedConstructors.olean"),
            &built.artifacts[0].bytes,
        )
        .unwrap();
        let library = compiler
            .parent()
            .unwrap()
            .parent()
            .unwrap()
            .join("lib/lean");
        let lean_path = std::env::join_paths([directory.as_path(), library.as_path()]).unwrap();
        for (label, source, success) in std::iter::once(("accepted".to_owned(), USE_TOKEN, true))
            .chain(
                ATOMIC_USES
                    .iter()
                    .enumerate()
                    .map(|(index, source)| (format!("rejected_{index}"), *source, false)),
            )
        {
            let file = directory.join(format!("consumer_{label}.lean"));
            std::fs::write(
                &file,
                format!("prelude\nimport ProtectedConstructors\n{source}"),
            )
            .unwrap();
            let output = Command::new(&compiler)
                .current_dir(&directory)
                .env("LEAN_PATH", &lean_path)
                .arg("-j1")
                .arg(&file)
                .output()
                .unwrap();
            assert_eq!(output.status.success(), success, "{source}\n{output:?}");
        }
    });
}
