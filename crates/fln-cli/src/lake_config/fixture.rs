//! Bounded execution diagnostics over actual pinned dependency data.
//!
//! Raw loading here is NOT admission of the FilePath module closure. This fixture
//! isolates native Lake field elaboration and execution while the separate
//! `reference` and installed-CLI tests exercise complete artifact admission.
//! Every configuration declaration still passes the ordinary two source checkers.
//! No seed, shim declaration, Reference process or replacement model is used.

use super::*;
use fln::{Engine, Environment, ExprNode, OleanDecodeLimits, OleanWalkBudget};
use fln_elab::instances::imported::{ClassParameters, ImportActivation, InstanceParameters};
use fln_olean::source_extensions as metadata;
use std::time::Instant;

const BYTES: usize = 256 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn instance_key(key: metadata::InstanceKey) -> fln_elab::instances::discr_tree::Key {
    use fln_elab::instances::discr_tree::Key;
    match key {
        metadata::InstanceKey::Star => Key::Star,
        metadata::InstanceKey::Other => Key::Other,
        metadata::InstanceKey::Lit(literal) => Key::Lit(literal),
        metadata::InstanceKey::FVar(name, arity) => Key::FVar(fln_core::expr::FVarId(name), arity),
        metadata::InstanceKey::Const(name, arity) => Key::Const(name, arity),
        metadata::InstanceKey::Arrow => Key::Arrow,
        metadata::InstanceKey::Proj(name, field, arity) => Key::Proj(name, field, arity),
    }
}

fn extern_entry(entry: metadata::ExternEntry) -> fln_elab::externs::ExternEntry {
    use fln_elab::externs::ExternEntry;
    match entry {
        metadata::ExternEntry::Adhoc { backend } => ExternEntry::Adhoc { backend },
        metadata::ExternEntry::Inline { backend, pattern } => {
            ExternEntry::Inline { backend, pattern }
        }
        metadata::ExternEntry::Standard { backend, symbol } => {
            ExternEntry::Standard { backend, symbol }
        }
        metadata::ExternEntry::Opaque => ExternEntry::Opaque,
    }
}

fn activate(
    environment: Environment,
    decoded: metadata::SourceExtensions,
    module: &str,
) -> Environment {
    let (classes, instances, externs): (&[&str], &[&str], &[&str]) = match module {
        "Init/Prelude" => (
            &["OfNat", "Add", "HAdd", "Append", "HAppend"],
            &[
                "instOfNatNat",
                "instHAdd",
                "instAddNat",
                "instHAppendOfAppend",
            ],
            &["Nat.add"],
        ),
        "Init/Coe" => (
            &["CoeT", "CoeHTCT", "CoeHTC", "CoeOTC", "CoeTC", "Coe"],
            &[
                "instCoeTOfCoeHTCT",
                "instCoeHTCTOfCoeHTC",
                "instCoeHTCOfCoeOTC",
                "instCoeOTCOfCoeTC",
                "instCoeTCOfCoe_1",
            ],
            &[],
        ),
        "Init/Data/String/Defs" => (&[], &["instAppendString"], &["String.append"]),
        "Init/System/FilePath" => (&[], &["System.instCoeStringFilePath"], &[]),
        _ => unreachable!("the selected actual metadata modules"),
    };
    let wanted_classes: Vec<_> = classes.iter().map(|label| name(label)).collect();
    let wanted_instances: Vec<_> = instances.iter().map(|label| name(label)).collect();
    let wanted_externs: Vec<_> = externs.iter().map(|label| name(label)).collect();
    let mut activation = ImportActivation::new(environment);
    for row in decoded.reducibility.into_iter().filter(|row| {
        wanted_instances.contains(&row.declaration)
            || (module == "Init/Prelude"
                && [name("outParam"), name("semiOutParam")].contains(&row.declaration))
    }) {
        use fln_elab::reducibility::Reducibility;
        let status = match row.status {
            metadata::ReducibilityStatus::Reducible => Reducibility::Reducible,
            metadata::ReducibilityStatus::Semireducible => Reducibility::Semireducible,
            metadata::ReducibilityStatus::Irreducible => Reducibility::Irreducible,
            metadata::ReducibilityStatus::ImplicitReducible => Reducibility::ImplicitReducible,
        };
        activation = activation
            .register_reducibility(&row.declaration, status)
            .unwrap();
    }
    let mut found_classes = 0;
    for row in decoded
        .classes
        .into_iter()
        .filter(|row| wanted_classes.contains(&row.name))
    {
        activation = activation
            .register_class(
                &row.name,
                &ClassParameters {
                    out_params: row.out_params,
                    out_level_params: row.out_level_params,
                },
            )
            .unwrap();
        found_classes += 1;
    }
    assert_eq!(
        found_classes,
        classes.len(),
        "actual class rows in {module}"
    );
    let mut found_instances = 0;
    for row in decoded
        .instances
        .into_iter()
        .filter(|row| wanted_instances.contains(&row.declaration))
    {
        assert!(matches!(row.value.node(), ExprNode::Const { name, .. }
            if name == &row.declaration));
        activation = activation
            .register_instance(
                &row.declaration,
                &InstanceParameters {
                    priority: row.priority,
                    synth_order: row.synth_order,
                    scope: row.scope,
                    keys: row.keys.into_iter().map(instance_key).collect(),
                },
            )
            .unwrap();
        found_instances += 1;
    }
    assert_eq!(
        found_instances,
        instances.len(),
        "actual instance rows in {module}"
    );
    for row in decoded
        .defaults
        .into_iter()
        .filter(|row| wanted_instances.contains(&row.declaration))
    {
        activation = activation
            .register_default(&row.declaration, row.priority)
            .unwrap();
    }
    let mut found_externs = 0;
    for row in decoded
        .externs
        .into_iter()
        .filter(|row| wanted_externs.contains(&row.declaration))
    {
        activation = activation
            .register_extern(
                &row.declaration,
                row.entries.into_iter().map(extern_entry).collect(),
            )
            .unwrap();
        found_externs += 1;
    }
    assert_eq!(
        found_externs,
        externs.len(),
        "actual extern rows in {module}"
    );
    activation.finish().unwrap()
}

fn raw_pin_engine() -> Option<Engine> {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned artifacts are required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB for the raw Lake execution diagnostic");
        return None;
    };
    let started = Instant::now();
    let mut environment = Environment::new();
    for module in [
        "Init/Prelude",
        "Init/Core",
        "Init/SimpLemmas",
        "Init/Coe",
        "Init/Data/List/Basic",
        "Init/Data/UInt/BasicAux",
        "Init/GetElem",
        "Init/Data/ByteArray/Bootstrap",
        "Init/Data/ByteArray/Basic",
        "Init/Data/ByteArray/Lemmas",
        "Init/Data/String/Defs",
        "Init/System/FilePath",
    ] {
        let path = library.join(module).with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let decoded = fln::decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(BYTES),
        )
        .unwrap();
        for constant in decoded.constants {
            if !environment.contains(constant.name()) {
                environment = environment.add_decl(constant).unwrap();
            }
        }
        if matches!(
            module,
            "Init/Prelude" | "Init/Coe" | "Init/Data/String/Defs" | "Init/System/FilePath"
        ) {
            let view = if decoded.module.is_module {
                fln_olean::region::OleanView::parse_with_dependencies(
                    &parts[2],
                    &[parts[0].as_slice(), parts[1].as_slice()],
                )
            } else {
                fln_olean::region::OleanView::parse(&parts[0])
            }
            .unwrap();
            let blocks = view
                .extension_payloads(OleanWalkBudget::default(), BYTES)
                .unwrap();
            environment = activate(
                environment,
                metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap(),
                module,
            );
        }
        eprintln!("Lake raw fixture {module}: {:?}", started.elapsed());
    }
    Some(Engine::from_environment(environment))
}

#[test]
fn raw_pin_lake_fields_compute_with_notation_coercions_and_unused_work() {
    std::thread::Builder::new()
        .name("fln-lake-raw-diagnostic".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(|| {
            let Some(engine) = raw_pin_engine() else {
                return;
            };
            let started = Instant::now();
            eprintln!("Lake raw fixture: checking all shared configuration cases");
            super::reference_tests::assert_configuration_cases(engine);
            eprintln!(
                "Lake raw fixture: all configuration cases completed in {:?}",
                started.elapsed()
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
