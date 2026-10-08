//! Model recognition controls. Bare environments here test the recognizer, not
//! admission; the integration gate admits the actual import closure through
//! both checkers before executing reference actions.

use super::*;
use model::name;

fn models() -> Vec<ConstantInfo> {
    let mut values = model::world();
    values.extend(model::references());
    values.extend(model::PRIMITIVES.map(|label| ConstantInfo::Opaque(model::primitive(label))));
    values.extend(["runST", "runEST"].map(|label| model::runner(&name(label)).unwrap()));
    let Declaration::Inductive(nat) = fln_elab::seed::nat_inductive_seed_declaration() else {
        unreachable!("fixed Nat family")
    };
    values.extend(nat.types.into_iter().map(ConstantInfo::Induct));
    values.extend(nat.ctors.into_iter().map(ConstantInfo::Ctor));
    values.extend(nat.recursors.into_iter().map(ConstantInfo::Rec));
    values
}

fn bare(change: impl Fn(&mut ConstantInfo)) -> Environment {
    models()
        .into_iter()
        .fold(Environment::new(), |env, mut value| {
            change(&mut value);
            env.add_decl(value).unwrap()
        })
}

fn entry(label: &str) -> fln_elab::externs::ExternEntry {
    let row = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|r| r.name == label)
        .unwrap();
    fln_elab::externs::ExternEntry::Standard {
        backend: name("all"),
        symbol: row.symbol.to_owned(),
    }
}

fn with_externs(env: Environment) -> Environment {
    model::PRIMITIVES.into_iter().fold(env, |env, label| {
        fln_elab::externs::register(&env, &name(label), vec![entry(label)]).unwrap()
    })
}

#[test]
fn exact_st_contracts_require_explicit_externs_and_meter_comparisons() {
    let bare = bare(|_| {});
    let env = with_externs(bare.clone());
    for label in model::PRIMITIVES {
        assert!(
            !st_primitive_matches(
                &bare,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
        let mut work = 0;
        assert!(
            st_primitive_matches(
                &env,
                &name(label),
                &mut None,
                &mut work,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(work > 100, "the complete representation is traversed");
        for max_nodes in [0, 1, work / 2, work - 1] {
            assert!(
                matches!(
                    st_primitive_matches(
                        &env,
                        &name(label),
                        &mut None,
                        &mut 0,
                        IngressLimits {
                            max_nodes,
                            ..IngressLimits::default()
                        }
                    ),
                    Err(IngressError::ResourceLimit { .. })
                ),
                "{label}: {max_nodes}"
            );
        }
        assert!(
            st_primitive_matches(
                &env,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits::default()
            )
            .unwrap(),
            "a resource refusal publishes no failed decision"
        );
    }
}

#[test]
fn changed_opaque_body_kind_telescope_or_safety_cannot_gain_st_authority() {
    for target in model::PRIMITIVES {
        for mutation in 0..6 {
            let env = with_externs(bare(|info| {
                if info.name() != &name(target) {
                    return;
                }
                let ConstantInfo::Opaque(value) = info else {
                    unreachable!()
                };
                match mutation {
                    0 => {
                        value.value = Expr::app(
                            Expr::lam(
                                Name::anonymous(),
                                value.base.type_.clone(),
                                Expr::bvar(0).unwrap(),
                                BinderInfo::Default,
                            ),
                            value.value.clone(),
                        )
                    }
                    1 => value.base.type_ = Expr::const_(name("Nat"), vec![]),
                    2 => value.is_unsafe = true,
                    3 => value.all.push(name("foreignMember")),
                    4 => value.base.level_params.push(name("u")),
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
            }));
            assert!(
                matches!(
                    st_primitive_matches(
                        &env,
                        &name(target),
                        &mut None,
                        &mut 0,
                        IngressLimits::default()
                    ),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{target}, mutation {mutation}"
            );
        }
    }
}

#[test]
fn changed_world_result_or_reference_family_does_not_select_native_cells() {
    for expected in model::world().into_iter().chain(model::references()) {
        let target = expected.name().clone();
        let env = with_externs(bare(|info| {
            if info.name() != &target {
                return;
            }
            match info {
                ConstantInfo::Defn(v) => v.safety = DefinitionSafety::Unsafe,
                ConstantInfo::Opaque(v) => v.is_unsafe = true,
                ConstantInfo::Induct(v) => v.num_indices += 1,
                ConstantInfo::Ctor(v) => v.num_fields += 1,
                ConstantInfo::Rec(v) => v.rules[0].rhs = Expr::sort(Level::zero()),
                _ => unreachable!("model inventory"),
            }
        }));
        assert!(
            matches!(
                st_primitive_matches(
                    &env,
                    &name("ST.Prim.mkRef"),
                    &mut None,
                    &mut 0,
                    IngressLimits::default()
                ),
                Err(IngressError::UnsupportedNode { .. })
            ),
            "{}",
            target.to_display_string()
        );
    }
}

#[test]
fn conflicting_externs_are_refused_and_runner_bodies_remain_ordinary() {
    use fln_elab::externs::{self, ExternEntry};
    for label in model::PRIMITIVES {
        let env = externs::register(
            &bare(|_| {}),
            &name(label),
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "different_runtime".to_owned(),
            }],
        )
        .unwrap();
        assert!(matches!(
            st_primitive_matches(
                &env,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits::default()
            ),
            Err(IngressError::UnsupportedNode { .. })
        ));
    }
    for label in ["runST", "runEST"] {
        assert!(
            st_runner_matches(
                &bare(|_| {}),
                &name(label),
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
        let env = bare(|info| {
            if info.name() == &name(label) {
                let ConstantInfo::Defn(v) = info else {
                    unreachable!()
                };
                v.value = Expr::app(
                    Expr::lam(
                        Name::anonymous(),
                        v.base.type_.clone(),
                        Expr::bvar(0).unwrap(),
                        BinderInfo::Default,
                    ),
                    v.value.clone(),
                );
            }
        });
        assert!(!st_runner_matches(&env, &name(label), &mut 0, IngressLimits::default()).unwrap());
    }
    assert!(
        !st_runner_matches(
            &bare(|_| {}),
            &name("ordinaryRunner"),
            &mut 0,
            IngressLimits::default()
        )
        .unwrap()
    );
}

#[test]
fn exact_runners_do_not_inline_over_explicit_extern_metadata() {
    use fln_elab::externs::{self, ExternEntry};
    let constant = |label| Expr::const_(name(label), vec![]);
    let apply = |head: Expr, arguments: Vec<Expr>| arguments.into_iter().fold(head, Expr::app);
    for label in ["runST", "runEST"] {
        let env = externs::register(
            &bare(|_| {}),
            &name(label),
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_runner_implementation".to_owned(),
            }],
        )
        .unwrap();
        // The declaration body still has the exact pinned model. The runtime
        // must consult its explicit extern before exposing that lambda.
        assert!(st_runner_matches(&env, &name(label), &mut 0, IngressLimits::default()).unwrap());
        let mut fields = vec![];
        if label == "runEST" {
            fields.push(constant("Nat"));
        }
        fields.extend([
            Expr::bvar(1).unwrap(),
            constant("Nat"),
            Expr::lit(Literal::Nat(NatLit::from_u64(7))),
            Expr::bvar(0).unwrap(),
        ]);
        let callback = Expr::lam(
            name("sigma"),
            Expr::sort(Level::one()),
            Expr::lam(
                name("world"),
                Expr::app(constant("Void"), Expr::bvar(0).unwrap()),
                apply(
                    constant(if label == "runST" {
                        "ST.Out.mk"
                    } else {
                        "EST.Out.ok"
                    }),
                    fields,
                ),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let mut arguments = vec![constant("Nat")];
        if label == "runEST" {
            arguments.push(constant("Nat"));
        }
        arguments.push(callback);
        let result = runtime::Preparation::new(&env, IngressLimits::default())
            .expression(&apply(constant(label), arguments));
        assert!(
            matches!(
                result,
                Err(IngressError::UnsupportedNode {
                    kind: "native extern attribute does not match the supported ABI"
                })
            ),
            "{label}: {result:?}"
        );
    }
}

#[test]
fn exact_st_models_match_actual_pinned_artifacts() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: FLN_REFERENCE_LIB absent");
        return;
    };
    let expected = models();
    let names: std::collections::BTreeSet<_> = expected.iter().map(|v| v.name().clone()).collect();
    let mut env = Environment::new();
    for module in ["Init/Prelude", "Init/System/ST"] {
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
        for value in decoded
            .constants
            .into_iter()
            .filter(|v| names.contains(v.name()))
        {
            env = env.add_decl(value).unwrap();
        }
    }
    for value in expected {
        assert!(
            Comparison {
                visited: &mut 0,
                limits: IngressLimits::default()
            }
            .constant(&env, value.clone())
            .unwrap(),
            "{}",
            value.name().to_display_string()
        );
    }
    let env = with_externs(env);
    for label in model::PRIMITIVES {
        assert!(
            st_primitive_matches(
                &env,
                &name(label),
                &mut None,
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
    }
}
