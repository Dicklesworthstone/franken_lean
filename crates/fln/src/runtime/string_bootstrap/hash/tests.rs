//! Actual Prelude and UInt.BasicAux comparison data for the native boundary.
//! This fixture does not claim admission of those modules. Every executed source
//! candidate still crosses both ordinary checkers; the Hashable integration
//! target separately checks the genuine complete library dependency closure.

use super::*;
use crate::runtime::array_iteration::{replace, without};
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 64 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
            let Some(library) = library.filter(|library| library.is_dir()) else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "actual pinned Reference library required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let mut environment = Environment::new();
            let mut actual_externs = BTreeMap::new();
            // UInt64's public ofNat/toNat definitions are in BasicAux. Their
            // complete computational dependencies are the original Prelude;
            // retain both decoded modules without manufacturing replacements.
            for module in ["Init/Prelude", "Init/Data/UInt/BasicAux"] {
                let path = library.join(module).with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                let view = if decoded.module.is_module {
                    fln_olean::region::OleanView::parse_with_dependencies(
                        &parts[2],
                        &[&parts[0], &parts[1]],
                    )
                } else {
                    fln_olean::region::OleanView::parse(&parts[0])
                }
                .unwrap();
                let blocks = view
                    .extension_payloads(OleanWalkBudget::default(), BYTES)
                    .unwrap();
                let extensions =
                    metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
                for info in decoded.constants {
                    if let Some(previous) = environment.find(info.name()) {
                        assert_eq!(previous, &info, "conflicting actual declaration");
                    } else {
                        environment = environment.add_decl(info).unwrap();
                    }
                }
                for row in extensions.externs {
                    let entries = row
                        .entries
                        .into_iter()
                        .map(|entry| match entry {
                            metadata::ExternEntry::Adhoc { backend } => {
                                ExternEntry::Adhoc { backend }
                            }
                            metadata::ExternEntry::Inline { backend, pattern } => {
                                ExternEntry::Inline { backend, pattern }
                            }
                            metadata::ExternEntry::Standard { backend, symbol } => {
                                ExternEntry::Standard { backend, symbol }
                            }
                            metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                        })
                        .collect::<Vec<_>>();
                    if let Some(previous) =
                        actual_externs.insert(row.declaration.clone(), entries.clone())
                    {
                        assert_eq!(previous, entries, "conflicting actual extern metadata");
                    } else {
                        environment =
                            externs::register(&environment, &row.declaration, entries).unwrap();
                    }
                }
            }
            assert_eq!(
                actual_externs[&name("mixHash")],
                vec![ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "lean_uint64_mix_hash".to_owned(),
                }]
            );
            Some(Fixture {
                environment,
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .name("actual-hash-runtime-model".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            if let Some(fixture) = fixture() {
                test(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn with_extern(fixture: &Fixture, selected: Option<Vec<ExternEntry>>) -> Environment {
    let mut environment = Environment::new();
    for (label, _) in fixture.environment.constants() {
        environment = environment
            .with_entry(fixture.environment.entry(label).unwrap())
            .unwrap();
    }
    for (label, entries) in &fixture.externs {
        if label != &name("mixHash") {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    if let Some(entries) = selected {
        environment = externs::register(&environment, &name("mixHash"), entries).unwrap();
    }
    environment
}

#[test]
fn hash_mixer_requires_the_complete_model_and_selected_extern() {
    with_fixture(|fixture| {
        let head = c("mixHash");
        let limits = IngressLimits::default();
        let mut preparation = Preparation::new(&fixture.environment, limits);
        assert!(preparation.hash_mixer_call(&head, &[]).unwrap().is_some());
        let mixer = preparation
            .string_bootstrap_intrinsic_binding(&name(MIX))
            .unwrap();
        assert_eq!(mixer.row, "extern:mixHash");
        assert_eq!(mixer.arguments, [ValueType::UInt64; 2]);
        assert_eq!(mixer.argument_ownership, [ArgumentOwnership::Scalar; 2]);
        assert_eq!(mixer.result, ValueType::UInt64);
        assert_eq!(mixer.result_ownership, ResultOwnership::Scalar);
        assert_eq!(mixer.effect, EffectClass::Pure);
        assert_eq!(
            preparation
                .hash_mixer_call(&head, &[c("UInt64"), c("UInt64"), c("UInt64")])
                .unwrap(),
            None
        );

        let missing_extern = with_extern(fixture, None);
        assert_eq!(
            Preparation::new(&missing_extern, limits)
                .hash_mixer_call(&head, &[])
                .unwrap(),
            None
        );
        let foreign = with_extern(
            fixture,
            Some(vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "unavailable_hash_mixer".to_owned(),
            }]),
        );
        assert!(
            Preparation::new(&foreign, limits)
                .hash_mixer_call(&head, &[])
                .is_err()
        );

        for label in [
            "mixHash",
            "UInt64.ofBitVec",
            "Fin.mk",
            "instInhabitedUInt64",
        ] {
            let changed = without(&fixture.environment, &name(label));
            assert!(
                Preparation::new(&changed, limits)
                    .hash_mixer_call(&head, &[])
                    .is_err(),
                "missing {label}"
            );
        }
        let Some(ConstantInfo::Opaque(original)) = fixture.environment.find(&name("mixHash"))
        else {
            panic!("actual opaque mixer");
        };
        let mut changed = original.clone();
        changed.is_unsafe = true;
        let changed = replace(&fixture.environment, ConstantInfo::Opaque(changed));
        assert!(
            Preparation::new(&changed, limits)
                .hash_mixer_call(&head, &[])
                .is_err()
        );
        let bounded = IngressLimits {
            max_nodes: 1,
            ..limits
        };
        let mut exhausted = Preparation::new(&fixture.environment, bounded);
        assert!(matches!(
            exhausted.hash_mixer_call(&head, &[]),
            Err(IngressError::ResourceLimit { .. })
        ));
        assert!(!exhausted.string_bootstrap.hash.checked);
        assert!(
            exhausted
                .string_bootstrap
                .hash
                .bindings
                .iter()
                .all(Option::is_none)
        );
    });
}

fn execute(engine: &Engine, source: &str, expected: &[&str]) -> Vec<u64> {
    let options = KVMap::new();
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let complete = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits)
        .unwrap_or_else(|error| panic!("hash mixer source: {error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(complete.executions.len(), expected.len());
    complete
        .executions
        .iter()
        .zip(expected)
        .map(|(execution, expected)| {
            let VmExit::Returned(returned) = &execution.exit else {
                panic!("native mixer must return");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
                Some(*expected)
            );
            let replay = execute_flbc_artifact(
                &execution.flbc_artifact,
                &options,
                FlbcExecutionLimits::default(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
            let VmExit::Returned(replay) = replay else {
                panic!("native mixer artifact must replay");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&replay.value).as_deref(),
                Some(*expected)
            );
            assert_eq!(replay.usage, returned.usage);
            returned.usage.steps
        })
        .collect()
}

#[test]
fn hash_mixer_preserves_nested_fields_partial_calls_and_replay() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        execute(
            &engine,
            r#"
#eval UInt64.toNat (mixHash (mixHash (UInt64.ofNat 0) (UInt64.ofNat 7)) (UInt64.ofNat 11))
#eval UInt64.toNat (mixHash (mixHash (UInt64.ofNat 0) (UInt64.ofNat 11)) (UInt64.ofNat 7))
#eval let mixer := mixHash; UInt64.toNat (mixer (mixHash (UInt64.ofNat 0) (UInt64.ofNat 7)) (UInt64.ofNat 11))
#eval let mixer := mixHash (mixHash (UInt64.ofNat 0) (UInt64.ofNat 7)); UInt64.toNat (mixer (UInt64.ofNat 11))
#eval UInt64.toNat (mixHash (UInt64.ofNat 18446744073709551615) (UInt64.ofNat 9223372036854775808))
"#,
            &[
                "6296794202839683667",
                "11814235083094005023",
                "6296794202839683667",
                "6296794202839683667",
                "3117938936229954994",
            ],
        );
    });
}

#[test]
fn hash_mixer_keeps_source_operands_strict() {
    with_fixture(|fixture| {
        let engine = Engine::from_environment(fixture.environment.clone());
        let engine = engine.check_source_files(&[b"def hashSpend (n : Nat) : UInt64 := match n with | .zero => UInt64.ofNat 0 | .succ k => hashSpend k"], &KVMap::new(), SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))).unwrap().into_complete().unwrap().engine;
        let idle = execute(
            &engine,
            "#eval UInt64.toNat (mixHash (hashSpend 0) (UInt64.ofNat 0))",
            &["3866779316627607737"],
        );
        let spent = execute(
            &engine,
            "#eval UInt64.toNat (mixHash (hashSpend 12) (UInt64.ofNat 0))",
            &["3866779316627607737"],
        );
        assert!(spent[0] > idle[0]);
    });
}
