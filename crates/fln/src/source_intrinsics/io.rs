//! Exact checked type contracts for explicit IO evaluation.
//!
//! These are recognition data, never declarations to admit. In particular, the
//! opaque `IO.RealWorld` carrier does not grant a logical world inhabitant.
//! Its already-proved ST representation is used only after admission.

use super::*;

mod model;

/// Recognize the pinned IO aliases and opaque state carrier. No IO primitive
/// implementation is selected here; effectful externs retain their own gates.
pub(crate) fn io_world_contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    charge_catalog_node(visited, limits)?;
    if !st::st_world_contract_matches(environment, visited, limits)? {
        return Ok(false);
    }
    let models = model::declarations();
    let mut comparison = Comparison { visited, limits };
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Ok(false);
        }
    }
    // Check authority only after selecting the complete model. An explicit
    // foreign implementation must never disappear behind entry preparation.
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_io_result_types_have_a_complete_runtime_interface() {
        let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
        else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference is required"
            );
            eprintln!("SKIP: FLN_REFERENCE_LIB absent");
            return;
        };
        // This small raw-artifact probe isolates runtime type discovery. It
        // supplies no module admission; the source bodies below still pass
        // the normal declaration checks before any executable preparation.
        let mut environment = Environment::new();
        for module in [
            "Init/Prelude",
            "Init/System/ST",
            "Init/System/IOError",
            "Init/System/IO",
        ] {
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
                OleanDecodeLimits::new(256 * 1024 * 1024),
            )
            .unwrap();
            for constant in decoded.constants {
                if !environment.contains(constant.name()) {
                    environment = environment.add_decl(constant).unwrap();
                }
            }
        }
        for family in ["IO", "BaseIO"] {
            let action = Expr::app(
                Expr::const_(Name::from_components([family]), vec![]),
                Expr::const_(Name::from_components(["Nat"]), vec![]),
            );
            let mut preparation = runtime::Preparation::new(&environment, IngressLimits::default());
            // Only entry/type construction is inspected; this placeholder is
            // never compiled, admitted or executed.
            assert!(
                preparation
                    .evaluation_entry(&Expr::sort(Level::zero()), &action)
                    .unwrap()
                    .is_some(),
                "{family}"
            );
        }
        // Raw decoding omits executable extension registration. Supply only
        // the generated, exact ST extern selection for this runtime probe;
        // complete selected-declaration admission has its separate gate.
        for label in [
            "ST.Prim.mkRef",
            "ST.Prim.Ref.get",
            "ST.Prim.Ref.set",
            "ST.Prim.Ref.swap",
        ] {
            let row = fln_vm::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|row| row.name == label)
                .unwrap();
            environment = fln_elab::externs::register(
                &environment,
                &Name::from_components(label.split('.')),
                vec![fln_elab::externs::ExternEntry::Standard {
                    backend: Name::from_components(["all"]),
                    symbol: row.symbol.to_owned(),
                }],
            )
            .unwrap();
        }
        let engine = Engine::from_environment(environment);
        for source in [
            "#eval (show IO Nat from fun world => @EST.Out.ok IO.Error IO.RealWorld Nat 42 world)",
            "#eval (show BaseIO Nat from fun world => @ST.Out.mk IO.RealWorld Nat 42 world)",
            // IO.mkRef's actual body selects the ST-to-BaseIO dictionary.
            // Its phantom IO.RealWorld parameter must remain inert metadata
            // while the returned reference action stays deferred until run.
            concat!(
                "#eval (show IO Nat from fun world => ",
                "match IO.mkRef (0 : Nat) world with | .mk reference afterNew => ",
                "match @ST.Prim.Ref.set IO.RealWorld Nat reference 37 afterNew with | .mk _ afterSet => ",
                "match @ST.Prim.Ref.swap IO.RealWorld Nat reference 42 afterSet with | .mk previous afterSwap => ",
                "match @ST.Prim.Ref.get IO.RealWorld Nat reference afterSwap with | .mk current last => ",
                "@EST.Out.ok IO.Error IO.RealWorld Nat (Nat.add previous (Nat.sub current 37)) last)",
            ),
        ] {
            let batch = engine
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(256 * 1024 * 1024)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let index = batch.batch.source_evaluation_indices[0];
            let execution = &batch.batch.executions[index];
            let Some(IoEvaluationOutcome::Returned { exit, .. }) =
                execution.io_evaluation_outcome().unwrap()
            else {
                panic!("explicit checked action evaluation");
            };
            let VmExit::Returned(returned) = exit else {
                unreachable!();
            };
            assert_eq!(nat_decimal(&returned.value).as_deref(), Some("42"));
        }
        for source in [
            "#eval (show ST Nat Nat from fun world => @ST.Out.mk Nat Nat 42 world)",
            "#eval (show EST String Nat Nat from fun world => @EST.Out.ok String Nat Nat 42 world)",
        ] {
            let batch = engine
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(Budget::for_stack_bytes(256 * 1024 * 1024)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let index = batch.batch.source_evaluation_indices[0];
            let execution = &batch.batch.executions[index];
            assert!(execution.io_evaluation_outcome().unwrap().is_none());
            let VmExit::Returned(returned) = &execution.exit else {
                panic!("the other-state action remains a deferred value");
            };
            assert_eq!(vm_value_kind(&returned.value), VmValueKind::Closure);
        }
    }

    #[test]
    fn exact_io_models_match_actual_pinned_artifacts() {
        let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
        else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "pinned Reference is required"
            );
            eprintln!("SKIP: FLN_REFERENCE_LIB absent");
            return;
        };
        let path = library.join("Init/System/IO.olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let decoded = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(256 * 1024 * 1024),
        )
        .unwrap();
        // Raw actual constants validate the recognizer's fixed models only.
        // The integration gate independently admits the selected declarations.
        for expected in model::declarations() {
            let actual = decoded
                .constants
                .iter()
                .find(|actual| actual.name() == expected.name())
                .unwrap();
            let environment = Environment::new().add_decl(actual.clone()).unwrap();
            assert!(
                Comparison {
                    visited: &mut 0,
                    limits: IngressLimits::default(),
                }
                .constant(&environment, expected.clone())
                .unwrap(),
                "{}",
                expected.name().to_display_string()
            );
        }
    }

    #[test]
    fn io_models_bind_every_body_telescope_and_safety_field() {
        for expected in model::declarations() {
            let base = Environment::new().add_decl(expected.clone()).unwrap();
            let mut visited = 0;
            assert!(
                Comparison {
                    visited: &mut visited,
                    limits: IngressLimits::default(),
                }
                .constant(&base, expected.clone())
                .unwrap()
            );
            assert!(visited > 1);
            for mutation in 0..5 {
                let mut changed = expected.clone();
                match &mut changed {
                    ConstantInfo::Defn(value) => match mutation {
                        0 => value.value = Expr::sort(Level::zero()),
                        1 => value.base.type_ = Expr::sort(Level::zero()),
                        2 => value.safety = DefinitionSafety::Unsafe,
                        3 => value.base.level_params.push(Name::anonymous()),
                        _ => value.all.clear(),
                    },
                    ConstantInfo::Opaque(value) => match mutation {
                        0 => value.value = Expr::sort(Level::zero()),
                        1 => value.base.type_ = Expr::sort(Level::zero()),
                        2 => value.is_unsafe = true,
                        3 => value.base.level_params.push(Name::anonymous()),
                        _ => value.all.clear(),
                    },
                    _ => unreachable!("fixed IO aliases and carrier"),
                }
                let changed = Environment::new().add_decl(changed).unwrap();
                assert!(
                    !Comparison {
                        visited: &mut 0,
                        limits: IngressLimits::default(),
                    }
                    .constant(&changed, expected.clone())
                    .unwrap(),
                    "{} mutation {mutation}",
                    expected.name().to_display_string(),
                );
            }
        }
    }
}
