//! Modern Hashable helpers preserve the pin's no_expose boundary.
//! Actual selected Prelude/UInt declarations pass both readers and checkers;
//! no fabricated Hashable class, UInt64 carrier or hash primitive is installed.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
    SourceModuleSession,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, Expr, ExprNode, KVMap, Name, Outcome,
    SourceCheckLimits, SourceModuleInput,
};
use fln_elab::instances::InstanceRegistry;
use fln_elab::reducibility::{Reducibility, ReducibilityTable};
use std::path::PathBuf;
use std::sync::OnceLock;

#[path = "source_deriving_hashable_visibility/fixture.rs"]
mod fixture;

#[path = "fixtures/private_constructor_deriving/mod.rs"]
mod private_constructor_fixture;

const STACK: usize = 16 * 1024 * 1024;
const BYTES: usize = 128 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private(module: &str, declaration: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(declaration))
}

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission()))
}

fn foundation() -> Option<&'static Engine> {
    static ENGINE: OnceLock<Option<Engine>> = OnceLock::new();
    ENGINE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|path| path.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "actual pinned Hashable and UInt64 declarations are required"
                );
                eprintln!("SKIP: pinned Reference lib/lean unavailable");
                return None;
            };
            Some(fixture::admitted(&library))
        })
        .as_ref()
}

fn with_foundation(run: impl FnOnce(&Engine) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            if let Some(engine) = foundation() {
                run(engine);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(label, _)| name(label)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
}

fn checked(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .expect("every declaration and exported interface passes both checkers")
}

fn references(expression: &Expr, target: &Name) -> bool {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression.node() {
            ExprNode::Const { name, .. } if name == target => return true,
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::ForallE {
                binder_type, body, ..
            }
            | ExprNode::Lam {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    false
}

const CLIENT: &str = "module\nprelude\npublic import Api\npublic theorem dictionary {A : Type} [Hashable A] (x : Item A) : hash x = instHashableItem.hash x := by rfl";
const HIDDEN_CLIENT: &str = "module\nprelude\npublic import Api\npublic theorem leaked {A : Type} [Hashable A] (x : A) : instHashableItem.hash (Item.mk x) = mixHash 0 (hash x) := by rfl";

fn item_api(exposed: bool, standalone: bool) -> String {
    let start = if exposed {
        "@[expose] public section\n"
    } else {
        "public section\n"
    };
    let deriving = if standalone {
        "deriving instance Inhabited, Hashable for Item"
    } else {
        "deriving Inhabited, Hashable"
    };
    format!(
        "module\nprelude\n{start}structure Item (A : Type) where\n value : A\n{deriving}\nend\ntheorem inside {{A : Type}} [Hashable A] (x : A) : instHashableItem.hash (Item.mk x) = mixHash 0 (hash x) := by rfl"
    )
}

#[test]
fn hash_helpers_stay_hidden_while_dictionaries_remain_exposed_for_both_deriving_forms() {
    with_foundation(|base| {
        for exposed in [false, true] {
            for standalone in [false, true] {
                let api = item_api(exposed, standalone);
                let local = checked(base, &[("Api", &api)]);
                let environment = local.checked.engine.environment();
                let helper_name = name("instHashableItem.hash");
                let dictionary_name = name("instHashableItem");
                let Some(ConstantInfo::Defn(helper)) = environment.find(&helper_name) else {
                    panic!("the full environment retains the checked hash implementation");
                };
                let Some(ConstantInfo::Defn(dictionary)) = environment.find(&dictionary_name)
                else {
                    panic!("the derived dictionary remains an ordinary checked definition");
                };
                let imported = checked(base, &[("Main", CLIENT), ("Api", &api)]);
                let public = imported.checked.engine.environment();
                let Some(ConstantInfo::Axiom(interface)) = public.find(&helper_name) else {
                    panic!("a modern import receives only the checked helper signature");
                };
                assert_eq!(interface.base, helper.base);
                assert!(!interface.is_unsafe);
                assert_eq!(
                    public.find(&dictionary_name),
                    Some(&ConstantInfo::Defn(dictionary.clone()))
                );
                assert!(matches!(
                    public.find(&name("instInhabitedItem")),
                    Some(ConstantInfo::Defn(_))
                ));
                assert_eq!(
                    ReducibilityTable::effective(public)
                        .unwrap()
                        .status(&dictionary_name),
                    Reducibility::ImplicitReducible
                );
                assert_eq!(
                    InstanceRegistry::read(public)
                        .unwrap()
                        .candidates(&name("Hashable"))
                        .iter()
                        .filter(|row| row.declaration == dictionary_name)
                        .count(),
                    1
                );
                assert!(
                    check(base, &[("Main", HIDDEN_CLIENT), ("Api", &api)]).is_err(),
                    "the pin refuses to unfold the hidden helper in modern clients"
                );
                // The module's retained checked body remains available through
                // the existing legacy import route, without exporting it anew.
                let legacy = HIDDEN_CLIENT
                    .replace("module\nprelude\npublic import Api", "prelude\nimport Api")
                    .replace("public theorem", "theorem");
                checked(base, &[("Main", &legacy), ("Api", &api)]);
            }
        }
    });
}

#[test]
fn private_field_instances_are_checked_in_helpers_without_leaking_to_importers() {
    with_foundation(|base| {
        for exposed in [false, true] {
            let section = if exposed {
                "@[expose] public section"
            } else {
                "public section"
            };
            let api = format!(
                "module\nprelude\npublic inductive Field where\n | mk\nprivate instance fieldHash : Hashable Field := Hashable.mk (fun _ => 37)\n{section}\nstructure Wrap where\n field : Field\n deriving Hashable\nend"
            );
            let local = checked(base, &[("Api", &api)]);
            let secret = private("Api", "fieldHash");
            let Some(ConstantInfo::Defn(helper)) = local
                .checked
                .engine
                .environment()
                .find(&name("instHashableWrap.hash"))
            else {
                panic!("the private dictionary is used only by an admitted helper body");
            };
            assert!(references(&helper.value, &secret));
            let client = "module\nprelude\npublic import Api\npublic theorem dictionary (x : Wrap) : hash x = instHashableWrap.hash x := by rfl";
            let imported = checked(base, &[("Main", client), ("Api", &api)]);
            let environment = imported.checked.engine.environment();
            assert!(matches!(
                environment.find(&name("instHashableWrap.hash")),
                Some(ConstantInfo::Axiom(_))
            ));
            assert!(!environment.contains(&secret));
            assert!(
                InstanceRegistry::read(environment)
                    .unwrap()
                    .candidates(&name("Hashable"))
                    .iter()
                    .all(|row| row.declaration != secret)
            );
            assert!(
                imported
                    .checked
                    .engine
                    .check_source_files(
                        &[b"def unavailable : Hashable Field := inferInstance"],
                        &KVMap::new(),
                        SourceCheckLimits::new(admission()),
                    )
                    .is_err()
            );
        }
    });
}

#[test]
fn private_constructors_require_hidden_helpers_and_reject_requested_exposure() {
    with_foundation(|base| {
        // A complete genuine artifact supplies the legacy private view. This
        // test does not claim support for parsing native `| private mk` syntax.
        let imported = private_constructor_fixture::admitted(base, admission());
        let source = "deriving instance Hashable for Concealed\ndef available : Hashable Concealed := by infer_instance";
        let legacy = imported
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let environment = legacy.environment();
        assert!(environment.contains(&private("Provider", "Concealed.mk")));
        // Imported-module suffix naming is a separate existing limitation;
        // this regression follows the actual checked instance registration.
        let registry = InstanceRegistry::read(environment).unwrap();
        let derived: Vec<_> = registry
            .candidates(&name("Hashable"))
            .iter()
            .filter(|instance| !imported.environment().contains(&instance.declaration))
            .collect();
        assert_eq!(derived.len(), 1);
        let dictionary = &derived[0].declaration;
        let helper = dictionary.append_core(&name("hash"));
        assert!(matches!(
            environment.find(&helper),
            Some(ConstantInfo::Defn(_))
        ));
        assert!(matches!(
            environment.find(dictionary),
            Some(ConstantInfo::Defn(_))
        ));
        let root = imported.logical_root(&KVMap::new());
        let exposed = "@[expose] public section\nderiving instance Hashable for Concealed\nend";
        let error = imported
            .check_source_files(
                &[exposed.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .expect_err("requested expose must reject the actual imported private constructor");
        assert!(
            format!("{error:?}").contains("deriving without expose"),
            "{error:?}"
        );
        assert_eq!(imported.logical_root(&KVMap::new()), root);
        assert!(!imported.environment().contains(dictionary));
    });
}

#[test]
fn later_handler_failures_do_not_publish_hidden_helpers_or_stale_cache_entries() {
    with_foundation(|base| {
        let api = item_api(false, false);
        let names = [name("Main"), name("Api")];
        let inputs = [
            SourceModuleInput {
                name: &names[0],
                source: CLIENT.as_bytes(),
            },
            SourceModuleInput {
                name: &names[1],
                source: api.as_bytes(),
            },
        ];
        let mut session = SourceModuleSession::new(
            base.clone(),
            KVMap::new(),
            limits(),
            SourceModuleCacheLimits::default(),
        );
        let cold = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(cold.elaborated_modules, 2);
        let changed = api.replace(
            "deriving Inhabited, Hashable",
            "deriving Inhabited, Hashable, UnknownHandler",
        );
        let mut edited = inputs;
        edited[1].source = changed.as_bytes();
        assert!(matches!(session.check(&edited, &names[0]),
            Err(SourceModuleCheckError::Source { module, .. }) if module == names[1]));
        assert_eq!(session.retained_modules(), 2);
        let recovered = session
            .check(&inputs, &names[0])
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(recovered.reused_modules, 2);
        assert_eq!(
            recovered.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        assert!(matches!(
            recovered
                .checked
                .checked
                .engine
                .environment()
                .find(&name("instHashableItem.hash")),
            Some(ConstantInfo::Axiom(_))
        ));
    });
}
