//! Scientific lowering must not route through unrelated same-name helpers.
#![forbid(unsafe_code)]

use fln::{
    Budget, ClosedFloatValue, Declaration, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, Environment, Expr, KVMap, Name,
};
use fln_core::expr::{BinderInfo, ExprNode, Literal, NatLit};
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn name(spelling: &str) -> Name {
    Name::from_components(spelling.split('.'))
}

fn constant(spelling: &str) -> Expr {
    Expr::const_(name(spelling), vec![])
}

fn number(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn call(spelling: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(constant(spelling), Expr::app)
}

fn definition(label: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![],
    })
}

fn base() -> Engine {
    Engine::from_environment(Environment::new())
        .admit_declarations(
            &[
                fln_elab::seed::nat_seed_declaration(),
                fln_elab::seed::bool_seed_declaration(),
            ],
            &KVMap::new(),
            EngineAdmissionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn scalar_environment(base: &Engine, replaced: &str) -> Engine {
    // The replacement computes zero through the opposite precision's canonical
    // rows, so it is valid and executable without calling itself indirectly.
    let (other, other_word, conversion) = match replaced {
        "Float.ofBits" => ("Float32", "UInt32", "Float32.toFloat"),
        "UInt64.ofNat" => ("Float32", "UInt32", "Float32.toUInt64"),
        "Float32.ofBits" => ("Float", "UInt64", "Float.toFloat32"),
        "UInt32.ofNat" => ("Float", "UInt64", "Float.toUInt32"),
        "" => ("Float", "UInt64", "Float.toFloat32"),
        _ => panic!("unexpected replacement"),
    };
    let required = [
        "Float",
        "Float32",
        "UInt32",
        "UInt64",
        "Float.ofScientific",
        "Float32.ofScientific",
        "Float.ofBits",
        "Float32.ofBits",
        "UInt64.ofNat",
        "UInt32.ofNat",
        "Float.toFloat32",
        "Float32.toFloat",
        "Float.toUInt32",
        "Float32.toUInt64",
    ];
    let mut declarations = Vec::new();
    let mut replacement = None;
    for candidate in fln_elab::seed::float_seed_declarations() {
        let Declaration::Axiom(axiom) = &candidate else {
            continue;
        };
        let spelling = axiom.base.name.to_display_string();
        if !required.contains(&spelling.as_str()) {
            continue;
        }
        if spelling == replaced {
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                ..
            } = axiom.base.type_.node()
            else {
                panic!("conversion must take one argument");
            };
            let zero = call(
                &format!("{other}.ofBits"),
                [call(&format!("{other_word}.ofNat"), [number(0)])],
            );
            replacement = Some(definition(
                replaced,
                axiom.base.type_.clone(),
                Expr::lam(
                    binder_name.clone(),
                    binder_type.clone(),
                    call(conversion, [zero]),
                    BinderInfo::Default,
                ),
            ));
        } else {
            declarations.push(candidate);
        }
    }
    if !replaced.is_empty() {
        declarations.push(replacement.expect("the replaced helper exists in the seed"));
    }
    base.admit_declarations(
        &declarations,
        &KVMap::new(),
        EngineAdmissionLimits::new(limits().kernel),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}

#[test]
fn scientific_literals_require_both_canonical_bit_helpers_in_each_precision() {
    let base = base();
    let options = KVMap::new();
    for (scalar, word, expected) in [
        (
            "Float",
            "UInt64",
            ClosedFloatValue::Float(1.25f64.to_bits()),
        ),
        (
            "Float32",
            "UInt32",
            ClosedFloatValue::Float32(1.25f32.to_bits()),
        ),
    ] {
        let entry = definition(
            "literal",
            constant(scalar),
            call(
                &format!("{scalar}.ofScientific"),
                [number(125), constant("Bool.true"), number(2)],
            ),
        );
        let canonical = scalar_environment(&base, "")
            .execute_definition(entry.clone(), &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            fln::closed_float_value(&canonical.runtime_type, &canonical.exit),
            Ok(Some(expected))
        );

        for helper in [format!("{scalar}.ofBits"), format!("{word}.ofNat")] {
            let engine = scalar_environment(&base, &helper);
            let root = engine.logical_root(&options);
            // Familiar helper names still execute their ordinary admitted
            // bodies when called directly; the literal compiler must not use
            // those altered bodies as a representation conversion.
            let ordinary = engine
                .execute_definition(
                    definition(
                        "ordinary",
                        constant(scalar),
                        call(
                            &format!("{scalar}.ofBits"),
                            [call(&format!("{word}.ofNat"), [number(42)])],
                        ),
                    ),
                    &options,
                    limits(),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let zero = if scalar == "Float" {
                ClosedFloatValue::Float(0)
            } else {
                ClosedFloatValue::Float32(0)
            };
            assert_eq!(
                fln::closed_float_value(&ordinary.runtime_type, &ordinary.exit),
                Ok(Some(zero)),
                "{helper}"
            );
            let result = engine.execute_definition(entry.clone(), &options, limits());
            assert!(
                matches!(
                    result,
                    Err(EngineExecutionError::Ingress(
                        fln_comp::ingress::IngressError::UnsupportedNode {
                            kind: "noncanonical scientific bit conversion"
                        }
                    ))
                ),
                "{helper}: {result:?}"
            );
            assert_eq!(engine.logical_root(&options), root);
            assert!(!engine.environment().contains(&name("literal")));
        }
    }
}
