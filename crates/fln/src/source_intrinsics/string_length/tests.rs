use super::*;
use fln_elab::externs::{self, ExternEntry};

/// Structural inputs for recognizer tests only. Native tests distinguish the
/// decoded raw-fixture smoke from execution after both engines admit imports.
fn model() -> Vec<ConstantInfo> {
    let mut values: Vec<_> = definitions()
        .into_iter()
        .chain(string_internal::scalar_records())
        .chain(character_records())
        .collect();
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        list_family(),
    ] {
        let Declaration::Inductive(block) = declaration else {
            unreachable!("fixed scalar and List families")
        };
        values.extend(block.types.into_iter().map(ConstantInfo::Induct));
        values.extend(block.ctors.into_iter().map(ConstantInfo::Ctor));
        values.extend(block.recursors.into_iter().map(ConstantInfo::Rec));
    }
    values
}

fn canonical(label: &str) -> ExternEntry {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == label)
        .unwrap();
    ExternEntry::Standard {
        backend: name("all"),
        symbol: row.symbol.to_owned(),
    }
}

fn bare_environment(change: impl Fn(&mut ConstantInfo)) -> Environment {
    model()
        .into_iter()
        .fold(Environment::new(), |environment, mut info| {
            change(&mut info);
            environment.add_decl(info).unwrap()
        })
}

fn environment(change: impl Fn(&mut ConstantInfo)) -> Environment {
    ["String.length", "String.toList"].into_iter().fold(
        bare_environment(change),
        |environment, label| {
            externs::register(&environment, &name(label), vec![canonical(label)]).unwrap()
        },
    )
}

fn matches(environment: &Environment) -> Result<bool, IngressError> {
    imported_string_length_matches(
        environment,
        &name("String.length"),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

#[test]
fn complete_public_string_contract_selects_the_existing_borrowed_native_row() {
    let environment = environment(|_| {});
    assert!(matches(&environment).unwrap());
    let binding = executable_intrinsic_binding(
        &environment,
        &name("String.length"),
        &mut 0,
        IngressLimits::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(binding.row, "extern:String.length");
    assert_eq!(binding.arguments, [ValueType::String]);
    assert_eq!(binding.result, ValueType::Nat);
    assert_eq!(binding.effect, fln_comp::fir::EffectClass::Pure);
    assert_eq!(
        binding.argument_ownership,
        [fln_comp::flbc::ArgumentOwnership::Borrowed]
    );
    assert_eq!(
        binding.result_ownership,
        fln_comp::flbc::ResultOwnership::Owned
    );

    let mut visited = 0;
    assert!(
        imported_string_length_matches(
            &environment,
            &name("String.length"),
            &mut None,
            &mut visited,
            IngressLimits::default(),
        )
        .unwrap()
    );
    assert!(
        visited > 100,
        "complete declarations and families were compared"
    );
    assert!(matches!(
        imported_string_length_matches(
            &environment,
            &name("String.length"),
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            },
        ),
        Err(IngressError::ResourceLimit { .. })
    ));
    assert!(
        matches(&environment).unwrap(),
        "a resource refusal changes no authority"
    );
}

#[test]
fn changed_definition_bodies_types_and_metadata_cannot_acquire_the_string_extern() {
    for target in ["String.length", "String.toList"] {
        for mutation in 0..7 {
            let changed = environment(|info| {
                if info.name() != &name(target) {
                    return;
                }
                let ConstantInfo::Defn(value) = info else {
                    unreachable!("the imported public operation is an ordinary definition")
                };
                match mutation {
                    0 => {
                        let result = if target == "String.length" {
                            Expr::lit(Literal::Nat(NatLit::from_u64(37)))
                        } else {
                            Expr::app(
                                Expr::const_(name("List.nil"), vec![Level::zero()]),
                                constant("Char"),
                            )
                        };
                        value.value = lambda(constant("String"), result);
                    }
                    1 => value.base.type_ = arrow(constant("Nat"), constant("Nat")),
                    2 => value.safety = DefinitionSafety::Unsafe,
                    3 => value.all.push(name("differentMutualMember")),
                    4 => value.base.level_params.push(name("u")),
                    5 => value.hints = ReducibilityHints::Abbrev,
                    6 => {
                        *info = ConstantInfo::Opaque(OpaqueVal {
                            base: value.base.clone(),
                            value: value.value.clone(),
                            is_unsafe: false,
                            all: value.all.clone(),
                        });
                    }
                    _ => unreachable!(),
                }
            });
            assert!(
                matches!(matches(&changed), Err(IngressError::UnsupportedNode { .. })),
                "{target}, mutation {mutation}"
            );
            assert!(
                matches!(
                    executable_intrinsic_binding(
                        &changed,
                        &name("String.length"),
                        &mut 0,
                        IngressLimits::default()
                    ),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "the compiler must not fall back through an incompatible explicit extern"
            );
        }
    }
}

#[test]
fn changed_scalar_and_list_families_do_not_inherit_a_familiar_function_name() {
    for target in [
        "String",
        "String.ofByteArray",
        "ByteArray.mk",
        "Char",
        "Char.mk",
        "UInt32.ofBitVec",
        "Nat",
        "Nat.succ",
        "List",
        "List.cons",
        "List.rec",
    ] {
        let changed = environment(|info| {
            if info.name() != &name(target) {
                return;
            }
            match info {
                ConstantInfo::Induct(family) => family.is_unsafe = true,
                ConstantInfo::Ctor(constructor) => constructor.num_fields += 1,
                ConstantInfo::Rec(recursor) => recursor.rules[0].nfields += 1,
                _ => unreachable!("a fixed ABI family member"),
            }
        });
        assert!(
            matches!(matches(&changed), Err(IngressError::UnsupportedNode { .. })),
            "changed {target}"
        );
    }
}

#[test]
fn public_string_length_requires_canonical_explicit_extern_entries() {
    let bare = bare_environment(|_| {});
    assert!(!matches(&bare).unwrap());
    let only_length = externs::register(
        &bare,
        &name("String.length"),
        vec![canonical("String.length")],
    )
    .unwrap();
    assert!(matches!(
        matches(&only_length),
        Err(IngressError::UnsupportedNode { .. })
    ));
    for target in ["String.length", "String.toList"] {
        for entries in [
            vec![],
            vec![ExternEntry::Opaque],
            vec![ExternEntry::Standard {
                backend: name("c"),
                symbol: match canonical(target) {
                    ExternEntry::Standard { symbol, .. } => symbol,
                    _ => unreachable!(),
                },
            }],
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "a_different_implementation".to_owned(),
            }],
            vec![canonical(target), ExternEntry::Opaque],
        ] {
            let changed = externs::register(&environment(|_| {}), &name(target), entries).unwrap();
            assert!(matches!(
                matches(&changed),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }
    }
}

#[test]
fn binder_labels_are_not_part_of_the_native_string_contract() {
    let renamed = environment(|info| {
        if let ConstantInfo::Defn(value) = info {
            let ExprNode::Lam {
                binder_type,
                body,
                binder_info,
                ..
            } = value.value.node()
            else {
                unreachable!("the two supported string lambdas")
            };
            value.value = Expr::lam(
                name("aHygienicImportedBinder"),
                binder_type.clone(),
                body.clone(),
                *binder_info,
            );
        }
    });
    assert!(matches(&renamed).unwrap());
}

mod native_tests;
