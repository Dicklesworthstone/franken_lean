//! Real serialized modules cross the ordinary two-checker admission door before
//! any of their class or instance metadata influences native source elaboration.
#![forbid(unsafe_code)]
use fln::*;
use fln::source_check::modules::{SourceModuleCheckLimits, imported::*};
use fln_elab::instances::InstanceRegistry;
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::convert::{inject_expr, inject_name};
use fln_rt::obj::Obj;
use std::sync::atomic::{AtomicUsize, Ordering};

fn n(text: &str) -> Name { Name::from_components(text.split('.')) }
fn admission() -> EngineAdmissionLimits { EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20)) }
fn limits() -> SourceOleanImportLimits { SourceOleanImportLimits::new(OleanCheckLimits::new(32 << 20, admission().kernel)) }
fn seed() -> Engine { Engine::with_source_seed(admission()).unwrap().into_complete().unwrap() }
fn check(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), SourceCheckLimits::new(admission()))
        .unwrap_or_else(|error| panic!("{text}\n{error:?}")).into_complete().unwrap().engine
}
fn added(base: &Engine, text: &str) -> (Engine, Vec<ConstantInfo>) {
    let result = check(base, text);
    let constants = result.environment().constants().filter(|(name, _)| !base.environment().contains(name))
        .map(|(_, info)| info.clone()).collect();
    (result, constants)
}
fn array(indices: &[usize]) -> Obj { Obj::mk_array(indices.iter().map(|i| Obj::mk_nat(*i)).collect()) }
fn class(name: &str, outputs: &[usize]) -> Obj {
    Obj::mk_ctor(0, vec![inject_name(&n(name)), array(outputs), array(&[])], &[])
}
fn instance(name: &str, priority: usize, order: &[usize], scope: Option<&str>) -> Obj {
    instance_value(name, Expr::const_(n(name), vec![]), priority, order, scope)
}
fn instance_value(name: &str, value: Expr, priority: usize, order: &[usize], scope: Option<&str>) -> Obj {
    let entry = Obj::mk_ctor(0, vec![
        array(&[]), inject_expr(&value).unwrap(), Obj::mk_nat(priority),
        Obj::mk_ctor(1, vec![inject_name(&n(name))], &[]), array(order),
    ], &[if scope.is_some() { 2 } else { 0 }]);
    match scope {
        Some(scope) => Obj::mk_ctor(1, vec![inject_name(&n(scope)), entry], &[]),
        None => Obj::mk_ctor(0, vec![entry], &[]),
    }
}
fn default(class: &str, name: &str, priority: usize) -> Obj {
    Obj::mk_ctor(0, vec![inject_name(&n(class)), inject_name(&n(name)), Obj::mk_nat(priority)], &[])
}
fn encoded(constants: &[ConstantInfo], imports: &[&str], extensions: Vec<(&str, Vec<Obj>)>) -> Vec<u8> {
    let imports: Vec<_> = imports.iter().map(|name| OleanModuleImport {
        module: n(name), import_all: false, is_exported: true, is_meta: false,
    }).collect();
    let names: Vec<_> = extensions.iter().map(|(name, _)| n(name)).collect();
    let extensions: Vec<_> = extensions.iter().zip(&names).map(|((_, entries), name)| ModuleExtensionInput { name, entries }).collect();
    encode_module_with_extensions(
        OleanModuleWriteInput { is_module: false, imports: &imports, constants, extra_const_names: &[] },
        &extensions,
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0], flags: 1,
            lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(), githash: OLEAN_PIN_COMMIT,
            base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
        }, OleanWriteBudget::default(),
    ).unwrap().bytes
}
fn input<'a>(name: &'a Name, artifact: &'a [u8]) -> OleanModuleInput<'a> {
    OleanModuleInput { name, artifact, server_artifact: None, private_artifact: None }
}
fn import(base: &Engine, bytes: &[u8]) -> SourceOleanImport {
    let name = n("Library");
    base.import_olean_modules_for_source(&[input(&name, bytes)], std::slice::from_ref(&name), &KVMap::new(), limits())
        .unwrap().into_complete().unwrap()
}
const CLASS: &str = "Lean.classExtension";
const INSTANCE: &str = "Lean.Meta.instanceExtension";
const DEFAULT: &str = "Lean.Meta.defaultInstanceExtension";

#[test]
fn checked_artifact_metadata_drives_output_inference_and_dictionary_selection() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let (_, constants) = added(&base, r#"
class Transfer (A : Type) (B : Type) where
  convert : A -> B
def natural : Transfer Nat Nat := Transfer.mk (fun x => x + 1)
def boolean : Transfer Nat Bool := Transfer.mk (fun x => true)
def transfer {A B : Type} [d : Transfer A B] (x : A) : B := Transfer.convert x
"#);
    let bytes = encoded(&constants, &[], vec![
        (CLASS, vec![class("Transfer", &[1])]),
        (INSTANCE, vec![instance("boolean", 500, &[], None), instance("natural", 2000, &[], None)]),
        ("Unimplemented.extension", vec![Obj::mk_nat(7)]),
    ]);
    let imported = import(&base, &bytes);
    assert_ne!(imported.checked.result_logical_root, imported.result_logical_root);
    assert_eq!(imported.engine.logical_root(&KVMap::new()), imported.result_logical_root);
    assert_eq!(imported.modules[0].uninterpreted, [n("Unimplemented.extension")]);
    assert_eq!((imported.modules[0].classes, imported.modules[0].instances), (1, 2));
    assert!(imported.checked.engine.check_source_files(&[b"def before := transfer 4"], &KVMap::new(), SourceCheckLimits::new(admission())).is_err());
    check(&imported.engine, "def inferred := transfer 4\ntheorem selected : inferred = 5 := by rfl");
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("Transfer")));
}

#[test]
fn roots_control_equal_priority_order_and_shared_imports_replay_once() {
    let base = seed();
    let (core, core_constants) = added(&base, "class Pick where\n  tag : Nat");
    let (_, a_constants) = added(&core, "def dictionaryA : Pick := Pick.mk 7");
    let (_, b_constants) = added(&core, "def dictionaryB : Pick := Pick.mk 9");
    let core_bytes = encoded(&core_constants, &[], vec![(CLASS, vec![class("Pick", &[])])]);
    let a_bytes = encoded(&a_constants, &["Core"], vec![(INSTANCE, vec![instance("dictionaryA", 1000, &[], None)])]);
    let b_bytes = encoded(&b_constants, &["Core"], vec![(INSTANCE, vec![instance("dictionaryB", 1000, &[], None)])]);
    let (core_name, a, b) = (n("Core"), n("A"), n("B"));
    let modules = [input(&b, &b_bytes), input(&core_name, &core_bytes), input(&a, &a_bytes)];
    for (roots, expected, order) in [
        ([a.clone(), b.clone()], 9, vec![core_name.clone(), a.clone(), b.clone()]),
        ([b.clone(), a.clone()], 7, vec![core_name.clone(), b.clone(), a.clone()]),
    ] {
        let result = base.import_olean_modules_for_source(&modules, &roots, &KVMap::new(), limits()).unwrap().into_complete().unwrap();
        assert_eq!(result.modules.iter().map(|m| m.module.clone()).collect::<Vec<_>>(), order);
        check(&result.engine, &format!("def chosen : Nat := Pick.tag\ntheorem selected : chosen = {expected} := by rfl"));
    }
    // The three modules consume one allowance, not three fresh allowances.
    let mut aggregate = limits();
    aggregate.metadata.max_entries = 2;
    assert!(matches!(base.import_olean_modules_for_source(&modules, &[a.clone(), b.clone()], &KVMap::new(), aggregate), Err(SourceOleanImportError::Limit("metadata entries"))));
    aggregate.metadata.max_entries = 3;
    assert!(base.import_olean_modules_for_source(&modules, &[a.clone(), b.clone()], &KVMap::new(), aggregate).unwrap().into_complete().is_some());
    assert!(matches!(base.import_olean_modules_for_source(&modules, &[a], &KVMap::new(), limits()), Err(SourceOleanImportError::UnreachableModule(_))));
}

#[test]
fn scoped_instances_remain_dormant_and_defaults_are_a_separate_phase() {
    let base = seed();
    let (_, constants) = added(&base, "class Pick where\n  tag : Nat\ndef ordinary : Pick := Pick.mk 7\ndef dormantDictionary : Pick := Pick.mk 9");
    let bytes = encoded(&constants, &[], vec![
        (CLASS, vec![class("Pick", &[])]),
        (INSTANCE, vec![instance("ordinary", 1000, &[], None), instance("dormantDictionary", 10000, &[], Some("Feature"))]),
        (DEFAULT, vec![default("Pick", "dormantDictionary", 50)]),
    ]);
    let result = import(&base, &bytes);
    assert_eq!(result.modules[0].scoped_instances, 1);
    let registry = InstanceRegistry::read(result.engine.environment()).unwrap();
    assert_eq!(registry.candidates(&n("Pick")).len(), 1);
    assert_eq!(registry.candidates(&n("Pick"))[0].declaration, n("ordinary"));
    let defaults = fln_elab::instances::defaults::read(result.engine.environment()).unwrap();
    assert!(defaults.iter().any(|row| row.class == n("Pick") && row.candidate.declaration == n("dormantDictionary")));
    check(&result.engine, "def chosen : Nat := Pick.tag\ntheorem selected : chosen = 7 := by rfl");
}

#[test]
fn malformed_metadata_cannot_return_a_checked_prefix_or_poison_recovery() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let (_, constants) = added(&base, "class Pick where\n  tag : Nat\ndef dictionary : Pick := Pick.mk 7");
    for extensions in [
        vec![(CLASS, vec![class("Pick", &[0])])],
        vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance("missing", 1000, &[], None)])],
        vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance("dictionary", 1000, &[0], None)])],
        vec![(CLASS, vec![class("Pick", &[])]), (DEFAULT, vec![default("Inhabited", "dictionary", 1000)])],
        vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance_value("dictionary", Expr::const_(n("dictionary"), vec![Level::one()]), 1000, &[], None)])],
    ] {
        let bytes = encoded(&constants, &[], extensions);
        let name = n("Library");
        assert!(base.import_olean_modules_for_source(&[input(&name, &bytes)], &[name.clone()], &KVMap::new(), limits()).is_err());
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&n("Pick")));
    }
    let bytes = encoded(&constants, &[], vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance("dictionary", 1000, &[], None)])]);
    check(&import(&base, &bytes).engine, "theorem recovered : Pick.tag = 7 := by rfl");
}

#[test]
fn invalid_declaration_never_reaches_metadata_activation() {
    let base = seed();
    let (_, mut constants) = added(&base, "class Pick where\n  tag : Nat\ndef dictionary : Pick := Pick.mk 7");
    constants.push(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal { name: n("bad"), level_params: vec![], type_: Expr::const_(n("Nat"), vec![]) },
        value: Expr::const_(n("Bool.true"), vec![]), hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe, all: vec![n("bad")],
    }));
    let bytes = encoded(&constants, &[], vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance("dictionary", 1000, &[], None)])]);
    let name = n("Library");
    assert!(matches!(base.import_olean_modules_for_source(&[input(&name, &bytes)], &[name.clone()], &KVMap::new(), limits()), Err(SourceOleanImportError::Check(_))));
    assert!(!base.environment().contains(&n("Pick")));
}

#[test]
fn limits_and_final_cancellation_preserve_the_original_engine() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let (_, constants) = added(&base, "class Pick where\n  tag : Nat\ndef dictionary : Pick := Pick.mk 7");
    let bytes = encoded(&constants, &[], vec![(CLASS, vec![class("Pick", &[])]), (INSTANCE, vec![instance("dictionary", 1000, &[], None)])]);
    let name = n("Library");
    let modules = [input(&name, &bytes)];
    let mut constrained = limits();
    constrained.metadata.max_entries = 1;
    assert!(base.import_olean_modules_for_source(&modules, &[name.clone()], &KVMap::new(), constrained).is_err());
    constrained = limits(); constrained.metadata.max_objects = 0;
    assert!(base.import_olean_modules_for_source(&modules, &[name.clone()], &KVMap::new(), constrained).is_err());
    constrained = limits(); constrained.max_capture_bytes = 0;
    assert!(base.import_olean_modules_for_source(&modules, &[name.clone()], &KVMap::new(), constrained).is_err());
    struct Cancel { calls: AtomicUsize, at: usize }
    impl CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool { self.calls.fetch_add(1, Ordering::Relaxed) >= self.at }
    }
    // before council, capture, before decode, class, instance, publication.
    let cancel = Cancel { calls: AtomicUsize::new(0), at: 5 };
    let outcome = base.import_olean_modules_for_source_with_cancel(&modules, &[name.clone()], &KVMap::new(), limits(), Some(&cancel)).unwrap();
    assert!(matches!(outcome, Outcome::Inconclusive(_)));
    assert_eq!(cancel.calls.load(Ordering::Relaxed), 6);
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&n("Pick")));
    import(&base, &bytes);
}

#[test]
fn metadata_keeps_a_bound_import_engine_usable_for_source_artifact_builds() {
    let empty = Engine::from_environment(Environment::new());
    let constants = [
        ConstantInfo::Axiom(AxiomVal { base: ConstantVal { name: n("Class"), level_params: vec![], type_: Expr::sort(Level::one()) }, is_unsafe: false }),
        ConstantInfo::Axiom(AxiomVal { base: ConstantVal { name: n("dictionary"), level_params: vec![], type_: Expr::const_(n("Class"), vec![]) }, is_unsafe: false }),
    ];
    let bytes = encoded(&constants, &[], vec![(CLASS, vec![class("Class", &[])]), (INSTANCE, vec![instance("dictionary", 1000, &[], None)])]);
    let imported = import(&empty, &bytes);
    let name = n("Client");
    let source = b"prelude\nimport Library\ndef use [x : Class] : Class := x\ndef selected : Class := use";
    let result = imported.engine.compile_source_modules(
        &[SourceModuleInput { name: &name, source }], &name, &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())), OleanWriteBudget::default(),
    ).unwrap().into_complete().unwrap();
    assert_eq!(result.artifacts.len(), 1);
    assert!(result.checked.checked.engine.environment().contains(&n("selected")));
    assert!(imported.engine.imported_modules().contains(&n("Library")));
}
