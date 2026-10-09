//! Contract recognition controls over actual decoded pin metadata. These raw
//! environments carry no module admission or verified import-reuse claim.

use super::*;

fn operations() -> [Operation; 2] {
    [Operation::CheckCanceled, Operation::Initializing]
}

fn raw_pin_environment() -> Option<Environment> {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LIB to the pinned lib/lean");
        return None;
    };
    let mut environment = Environment::new();
    for module in [
        "Init/Prelude",
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

mod execution;

fn register(environment: &Environment, operation: Operation, foreign: bool) -> Environment {
    let label = operation.source_name().to_display_string();
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == label)
        .unwrap();
    let symbol = if foreign {
        "foreign_base_io_observation".to_owned()
    } else {
        row.symbol.to_owned()
    };
    fln_elab::externs::register(
        environment,
        &operation.source_name(),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: Name::from_components(["all"]),
            symbol,
        }],
    )
    .unwrap()
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
fn exact_base_io_observation_contracts_require_externs_and_complete_pin_models() {
    let Some(raw) = raw_pin_environment() else {
        return;
    };
    for operation in operations() {
        let name = operation.source_name();
        assert!(
            !primitive_matches(&raw, operation, &mut None, &mut 0, IngressLimits::default(),)
                .unwrap(),
            "a logical opaque default has no native implementation authority"
        );
        let environment = register(&raw, operation, false);
        let mut work = 0;
        assert!(
            primitive_matches(
                &environment,
                operation,
                &mut None,
                &mut work,
                IngressLimits::default(),
            )
            .unwrap()
        );
        assert!(work > 0);
        for max_nodes in [0, work / 2, work - 1] {
            assert!(matches!(
                primitive_matches(
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
        let foreign = register(&raw, operation, true);
        assert!(matches!(
            primitive_matches(
                &foreign,
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ));
        for mutation in 0..6 {
            let changed = replace(&raw, &name, |info| {
                let ConstantInfo::Opaque(value) = info else {
                    panic!("the actual observation is opaque");
                };
                match mutation {
                    0 => value.value = c("Bool.false"),
                    1 => value.base.type_ = Expr::app(c("BaseIO"), c("Nat")),
                    2 => value.is_unsafe = true,
                    3 => value.all.push(Name::from_components(["foreignMember"])),
                    4 => value.base.level_params.push(Name::from_components(["u"])),
                    5 => {
                        *info = ConstantInfo::Defn(DefinitionVal {
                            base: value.base.clone(),
                            value: value.value.clone(),
                            hints: ReducibilityHints::Regular(1),
                            safety: DefinitionSafety::Safe,
                            all: value.all.clone(),
                        })
                    }
                    _ => unreachable!(),
                }
            });
            let changed = register(&changed, operation, false);
            assert!(
                matches!(
                    primitive_matches(
                        &changed,
                        operation,
                        &mut None,
                        &mut 0,
                        IngressLimits::default(),
                    ),
                    Err(IngressError::UnsupportedNode {
                        kind: "native BaseIO extern does not match its complete checked contract"
                    })
                ),
                "{name:?}: mutation {mutation}"
            );
        }
        let changed_world = replace(&raw, &Name::from_components(["BaseIO"]), |info| {
            let ConstantInfo::Defn(value) = info else {
                panic!("the actual BaseIO alias is a definition");
            };
            value.value = c("IO");
        });
        assert!(matches!(
            primitive_matches(
                &register(&changed_world, operation, false),
                operation,
                &mut None,
                &mut 0,
                IngressLimits::default(),
            ),
            Err(IngressError::UnsupportedNode {
                kind: "native BaseIO extern requires the complete checked IO world"
            })
        ));
    }
}
