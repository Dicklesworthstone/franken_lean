//! Scientific lowering must not route through unrelated same-name helpers.
#![forbid(unsafe_code)]

use fln::{
    Budget, ClosedFloatValue, Declaration, Engine, EngineAdmissionLimits, EngineExecutionError,
    EngineExecutionLimits, Environment, Expr, KVMap, Name,
};
use fln_core::expr::{BinderInfo, ExprNode, Literal, NatLit};
use fln_core::level::Level;
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

#[test]
fn checked_same_named_word_records_use_their_actual_fields() {
    for word in ["UInt32", "UInt64"] {
        let source = format!(
            "structure {word} where\n  value : Nat\n\
             def read (x : {word}) : Nat := x.value\n\
             #eval read {{ value := 42 }}"
        );
        let result = base()
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_or_else(|error| panic!("{word}: {error:?}"))
            .into_complete()
            .unwrap();
        let fln::VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("word record must return its field");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
    }
}

#[test]
fn enclosing_records_discover_checked_word_layouts_before_compiling_their_consumers() {
    for word in ["UInt32", "UInt64"] {
        let source = format!(
            "structure {word} where\n  value : Nat\n\
             structure Cell where\n  word : {word}\n\
             structure Envelope where\n  cell : Cell\n\
             def read (x : Envelope) : Nat := x.cell.word.value\n\
             #eval read {{ cell := {{ word := {{ value := 42 }} }} }}"
        );
        let engine = base();
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let execute = || {
            engine
                .execute_source_definitions(&[source.as_bytes()], &options, limits())
                .unwrap_or_else(|error| panic!("nested {word}: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = execute();
        let result = first.executions.last().unwrap();
        let fln::VmExit::Returned(value) = &result.exit else {
            panic!("nested word record must return its field")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42")
        );
        assert_eq!(
            result.flbc_artifact,
            execute().executions.last().unwrap().flbc_artifact
        );
        assert_eq!(engine.logical_root(&options), root);
    }
}

#[test]
fn native_word_rows_require_the_matching_opaque_family_contract() {
    for word in ["UInt32", "UInt64"] {
        // This alias and these axioms are all admitted by both checkers. Their
        // familiar names cannot grant a native word ABI to an arbitrary Nat.
        let mut declarations = vec![definition(word, Expr::sort(Level::one()), constant("Nat"))];
        for operation in ["ofNat", "toNat"] {
            declarations.push(
                fln_elab::seed::float_intrinsic_seed_declaration(&name(&format!(
                    "{word}.{operation}"
                )))
                .unwrap(),
            );
        }
        let options = KVMap::new();
        let engine = base()
            .admit_declarations(
                &declarations,
                &options,
                EngineAdmissionLimits::new(limits().kernel),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let root = engine.logical_root(&options);
        let entry = definition(
            "roundtrip",
            constant("Nat"),
            call(
                &format!("{word}.toNat"),
                [call(&format!("{word}.ofNat"), [number(42)])],
            ),
        );
        assert!(matches!(
            engine.execute_definition(entry, &options, limits()),
            Err(EngineExecutionError::Ingress(
                fln_comp::ingress::IngressError::UnknownConstant { .. }
            ))
        ));
        assert_eq!(engine.logical_root(&options), root);
        assert!(!engine.environment().contains(&name("roundtrip")));
    }
}
