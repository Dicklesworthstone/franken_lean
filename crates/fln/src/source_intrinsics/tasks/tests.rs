//! These raw-artifact fixtures test recognition, not module admission.

use super::*;

fn raw_pin_environment() -> Option<Environment> {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return None;
    };
    let mut environment = Environment::new();
    for module in [
        "Init/Prelude",
        "Init/Core",
        "Init/System/ST",
        "Init/System/IOError",
        "Init/System/IO",
    ] {
        let path = library.join(module).with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        let server = std::fs::read(path.with_extension("olean.server")).unwrap();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap();
        let decoded = decode_olean_module_artifacts(
            &public,
            &server,
            &private,
            OleanDecodeLimits::new(256 * 1024 * 1024),
        )
        .unwrap();
        for info in decoded.constants {
            if !environment.contains(info.name()) {
                environment = environment.add_decl(info).unwrap();
            }
        }
    }
    Some(environment)
}

fn registered(environment: &Environment, foreign: Option<Operation>) -> Environment {
    registered_except(environment, foreign, None)
}

fn registered_except(
    environment: &Environment,
    foreign: Option<Operation>,
    omitted: Option<Operation>,
) -> Environment {
    let mut environment = environment.clone();
    for operation in [
        Operation::Pure,
        Operation::Get,
        Operation::AsTask,
        Operation::Wait,
        Operation::MapTask,
        Operation::BindTask,
    ] {
        if omitted == Some(operation) {
            continue;
        }
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.name == operation.label())
            .unwrap();
        environment = fln_elab::externs::register(
            &environment,
            &model::name(operation.label()),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: model::name("all"),
                symbol: if foreign == Some(operation) {
                    "foreign_task_implementation".to_owned()
                } else {
                    row.symbol.to_owned()
                },
            }],
        )
        .unwrap();
    }
    environment
}

fn replace(
    environment: &Environment,
    target: &Name,
    change: impl Fn(&mut ConstantInfo),
) -> Environment {
    environment
        .constants()
        .fold(Environment::new(), |output, (name, info)| {
            let mut info = info.clone();
            if name == target {
                change(&mut info);
            }
            output.add_decl(info).unwrap()
        })
}

#[test]
fn exact_task_models_require_their_family_externs_and_opaque_bodies() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    assert!(
        !family_matches(&raw, &mut None, &mut 0, IngressLimits::default()).unwrap(),
        "an ordinary same-named structure has no native Task authority"
    );
    let environment = registered(&raw, None);
    for operation in [
        Operation::Pure,
        Operation::Get,
        Operation::AsTask,
        Operation::Wait,
        Operation::MapTask,
        Operation::BindTask,
    ] {
        assert!(
            !operation_matches(&raw, operation, &mut None, &mut 0, IngressLimits::default(),)
                .unwrap(),
            "{} needs its selected extern",
            operation.label()
        );
        let mut work = 0;
        assert!(
            operation_matches(
                &environment,
                operation,
                &mut None,
                &mut work,
                IngressLimits::default()
            )
            .unwrap(),
            "{}",
            operation.label()
        );
        assert!(work > 0);
        for max_nodes in [0, work / 2, work - 1] {
            assert!(matches!(
                operation_matches(
                    &environment,
                    operation,
                    &mut None,
                    &mut 0,
                    IngressLimits {
                        max_nodes,
                        ..IngressLimits::default()
                    },
                ),
                Err(IngressError::ResourceLimit { .. })
            ));
        }
        assert!(matches!(
            operation_matches(
                &registered(&raw, Some(operation)),
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ));
        let lookalike = Name::from_components([operation.label()]);
        assert_ne!(lookalike, model::name(operation.label()));
        assert_eq!(Operation::from_name(&lookalike), None);
    }
    for (target, operation) in [
        ("Task", Operation::Pure),
        ("Task.pure", Operation::Pure),
        ("Task.rec", Operation::Get),
        ("Task.get", Operation::Get),
        ("Task.Priority", Operation::AsTask),
        ("BaseIO.asTask", Operation::AsTask),
        ("IO.wait", Operation::Wait),
        ("BaseIO.mapTask", Operation::MapTask),
        ("BaseIO.bindTask", Operation::BindTask),
        ("Task.get", Operation::Wait),
        ("Task.get", Operation::MapTask),
        ("Task.get", Operation::BindTask),
        ("Task.Priority", Operation::MapTask),
        ("Task.Priority", Operation::BindTask),
    ] {
        let changed = replace(&raw, &model::name(target), |info| match info {
            ConstantInfo::Induct(value) => value.is_unsafe = true,
            ConstantInfo::Ctor(value) => value.num_fields += 1,
            ConstantInfo::Rec(value) => value.rules[0].rhs = Expr::sort(Level::zero()),
            ConstantInfo::Defn(value) if target == "Task.Priority" => {
                value.value = Expr::const_(model::name("Bool"), vec![]);
            }
            ConstantInfo::Defn(value) => value.value = Expr::sort(Level::zero()),
            ConstantInfo::Opaque(value) => value.value = Expr::sort(Level::zero()),
            _ => unreachable!("selected Task model kind"),
        });
        assert!(
            matches!(
                operation_matches(
                    &registered(&changed, None),
                    operation,
                    &mut None,
                    &mut 0,
                    IngressLimits::default(),
                ),
                Err(IngressError::UnsupportedNode {
                    kind: "native Task differs from its complete checked logical contract"
                })
            ),
            "{target}"
        );
    }
    let foreign_priority = fln_elab::externs::register(
        &environment,
        &model::name("Task.Priority"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: model::name("all"),
            symbol: "foreign_task_priority".to_owned(),
        }],
    )
    .unwrap();
    for operation in [Operation::AsTask, Operation::MapTask, Operation::BindTask] {
        assert!(matches!(
            operation_matches(
                &foreign_priority,
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ));
    }
    let world = replace(&raw, &model::name("BaseIO"), |info| {
        let ConstantInfo::Defn(value) = info else {
            unreachable!()
        };
        value.value = Expr::const_(model::name("IO"), vec![]);
    });
    for operation in [
        Operation::AsTask,
        Operation::Wait,
        Operation::MapTask,
        Operation::BindTask,
    ] {
        assert!(matches!(
            operation_matches(
                &registered(&world, None),
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode { .. })
        ));
    }
    for operation in [Operation::Wait, Operation::MapTask, Operation::BindTask] {
        assert!(
            operation_matches(
                &registered_except(&raw, None, Some(Operation::Get)),
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap()
        );
        assert!(matches!(
            operation_matches(
                &registered(&raw, Some(Operation::Get)),
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ));
    }
    for operation in [Operation::MapTask, Operation::BindTask] {
        for mutation in 0..3 {
            let changed = replace(&raw, &model::name(operation.label()), |info| {
                let ConstantInfo::Opaque(value) = info else {
                    unreachable!("composition is an actual opaque declaration")
                };
                match mutation {
                    0 => value.base.level_params.clear(),
                    1 => value.is_unsafe = true,
                    2 => value.all.clear(),
                    _ => unreachable!(),
                }
            });
            assert!(matches!(
                operation_matches(
                    &registered(&changed, None),
                    operation,
                    &mut None,
                    &mut 0,
                    IngressLimits::default(),
                ),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
    }
}
