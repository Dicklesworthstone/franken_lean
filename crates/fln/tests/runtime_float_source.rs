//! Floating-point source programs use checked types, native VM boxes and rows.
#![forbid(unsafe_code)]
use fln::{Budget, ClosedFloatValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn floats(source: &str) -> Vec<ClosedFloatValue> {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    report
        .executions
        .iter()
        .filter_map(|execution| {
            fln::closed_float_value(&execution.runtime_type, &execution.exit).unwrap()
        })
        .collect()
}

fn f64_value(value: f64) -> ClosedFloatValue {
    ClosedFloatValue::Float(value.to_bits())
}
fn f32_value(value: f32) -> ClosedFloatValue {
    ClosedFloatValue::Float32(value.to_bits())
}

#[test]
fn decimal_and_scientific_literals_execute_in_both_precisions() {
    assert_eq!(
        floats(
            "#eval (1.5 : Float)\n#eval (1.5 : Float32)\n#eval (125e-2 : Float)\n#eval (125e-2 : Float32)\n#eval (1. : Float)\n#eval (2.5e2 : Float)\n#eval (0 : Float32)\n#eval (-0.0 : Float)\n#eval (-0.0 : Float32)"
        ),
        vec![
            f64_value(1.5),
            f32_value(1.5),
            f64_value(1.25),
            f32_value(1.25),
            f64_value(1.0),
            f64_value(250.0),
            f32_value(0.0),
            f64_value(-0.0),
            f32_value(-0.0)
        ]
    );
}

#[test]
fn arithmetic_functions_branches_and_closures_preserve_float_types() {
    assert_eq!(
        floats(
            r#"
def affine (x : Float) (slope : Float) : Float := x * slope + 0.5
def choose (flag : Bool) (x y : Float32) : Float32 := if flag then x else y
#eval affine 2.5 4.0
#eval choose true (1.5 + 2.25) (9.0 / 2.0)
#eval let offset : Float := 0.5; let f := fun (x : Float) => x + offset; f 2.0 + f 3.0
#eval let apply := fun (f : Float32 -> Float32) => f 2.5; apply (fun x => -x / 2.0)
"#
        ),
        vec![
            f64_value(10.5),
            f32_value(3.75),
            f64_value(6.0),
            f32_value(-1.25)
        ]
    );
}

#[test]
fn native_integer_and_precision_conversions_compose_with_float_results() {
    assert_eq!(
        floats(
            r#"
#eval Float.ofBits (UInt64.ofNat 9223372036854775808)
#eval Float32.ofBits (UInt32.ofNat 2147483648)
#eval Float.toFloat32 (1.25 : Float)
#eval Float32.toFloat (1.25 : Float32)
#eval UInt64.toFloat32 (UInt64.ofNat 9223372586610589697)
#eval Float.ofNat 18446744073709551616
"#
        ),
        vec![
            f64_value(-0.0),
            f32_value(-0.0),
            f32_value(1.25),
            f64_value(1.25),
            ClosedFloatValue::Float32(0x5f00_0001),
            f64_value(18446744073709551616.0)
        ]
    );
}

#[test]
fn classifications_to_bits_and_strings_return_ordinary_source_values() {
    let source = r#"
#eval UInt64.toNat (Float.toBits (-0.0 : Float))
#eval UInt32.toNat (Float32.toBits (-0.0 : Float32))
#eval UInt64.toNat (Float.toUInt64 (1.0 / 0.0))
#eval Float.isNaN (0.0 / 0.0)
#eval Float32.isInf (1.0 / 0.0)
#eval Float.toString (2.1 : Float) ++ "!"
#eval Float32.toString (3.2 : Float32)
"#;
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    let values: Vec<_> = report
        .executions
        .iter()
        .map(|execution| fln::closed_vm_value(&execution.exit).unwrap().unwrap())
        .collect();
    assert_eq!(
        values,
        vec![
            fln::ClosedVmValue::NonnegativeMpz("9223372036854775808".to_owned()),
            fln::ClosedVmValue::Scalar(2147483648),
            fln::ClosedVmValue::NonnegativeMpz("18446744073709551615".to_owned()),
            fln::ClosedVmValue::Scalar(1),
            fln::ClosedVmValue::Scalar(1),
            fln::ClosedVmValue::String("2.100000!".to_owned()),
            fln::ClosedVmValue::String("3.200000".to_owned()),
        ]
    );
}

#[test]
fn float_mismatches_and_literal_resource_stops_keep_the_original_environment() {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    for source in [
        "#eval Float.add (1.0 : Float32) 2.0",
        "#eval Float32.toBits (1.0 : Float)",
    ] {
        assert!(!matches!(
            engine.execute_source_definitions(&[source.as_bytes()], &options, limits()),
            Ok(fln::Outcome::Complete(_))
        ));
    }
    let mut bounded = limits();
    bounded.ingress.max_literal_bytes = 8;
    assert!(!matches!(
        engine.execute_source_definitions(&[b"#eval (1e1000 : Float)"], &options, bounded),
        Ok(fln::Outcome::Complete(_))
    ));
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn single_field_dictionary_projection_keeps_computed_values_and_arguments_strict() {
    let run = |cost: u32, supplied_argument: bool| {
        let expression = if supplied_argument {
            format!("make (count {cost})")
        } else {
            format!("{{ payload := count {cost} }}")
        };
        let source = format!(
            r#"
class Cell (A : Type) where
  payload : A
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def make (ignored : Nat) : Cell Nat := {{ payload := 42 }}
#eval @Cell.payload Nat ({expression})
"#
        );
        let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
            .unwrap()
            .into_complete()
            .unwrap();
        let report = engine
            .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let fln::VmExit::Returned(returned) = &report.executions.last().unwrap().exit else {
            panic!("dictionary projection did not return");
        };
        assert_eq!(
            returned.value.unbox(),
            if supplied_argument { 42 } else { cost as usize }
        );
        returned.usage.steps
    };
    for supplied_argument in [false, true] {
        let idle = run(0, supplied_argument);
        let busy = run(30, supplied_argument);
        assert!(
            busy > idle + 30,
            "dictionary computation vanished: {idle} vs {busy}"
        );
    }
}

#[test]
fn typed_float_projection_refuses_an_immediate_from_an_unrelated_source_type() {
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let report = engine
        .execute_source_definitions(&[b"#eval 42"], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let exit = &report.executions.last().unwrap().exit;
    for source_type in ["Float", "Float32"] {
        let type_ = fln::Expr::const_(fln::Name::from_components([source_type]), vec![]);
        assert_eq!(
            fln::closed_float_value(&type_, exit),
            Err(fln::ClosedVmValueError::InvalidFloatRepresentation { source_type })
        );
    }
}

#[test]
fn dynamic_explicit_record_projections_keep_the_receivers_ground_layout() {
    let source = "structure Box (A : Type) where\n  value : A\ndef read (x : Box Nat) : Nat := Box.value x\n#eval read { value := 42 }";
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let report = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&report.executions.last().unwrap().exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(42))
    );
}

#[test]
fn unary_math_pow_and_atan2_reach_the_owned_numerics_plane_from_source() {
    // IEEE-exact rows carry definitional goldens; sqrt(-1) leaves the real
    // line and must surface as a NaN value, never a refusal.
    assert_eq!(
        floats(
            "#eval Float.sqrt 4.0\n#eval Float32.sqrt 2.25\n#eval Float.floor 2.9\n#eval Float.ceil (-2.9)\n#eval Float.round 2.5\n#eval Float.pow 2.0 10.0\n#eval Float32.pow 2.0 10.0"
        ),
        vec![
            f64_value(2.0),
            f32_value(1.5),
            f64_value(2.0),
            f64_value(-2.0),
            f64_value(3.0),
            f64_value(1024.0),
            f32_value(1024.0),
        ]
    );
    // Transcendental results are the owned plane's exact bits at each width
    // (§6.8, D21) — including the canonical NaN for a domain-edge input and
    // atan2's pin argument order, `atan2 (y x)`.
    assert_eq!(
        floats(
            "#eval Float.sin 1.0\n#eval Float32.sin 1.0\n#eval Float.exp 1.0\n#eval Float.log2 5.0\n#eval Float.atan2 1.0 0.0\n#eval Float.log (-1.0)\n#eval Float32.cbrt 2.0"
        ),
        vec![
            f64_value(fln_libm::sin(1.0)),
            f32_value(fln_libm::f32::sin(1.0)),
            f64_value(fln_libm::exp(1.0)),
            f64_value(fln_libm::log2(5.0)),
            f64_value(fln_libm::atan2(1.0, 0.0)),
            f64_value(fln_libm::log(-1.0)),
            f32_value(fln_libm::f32::cbrt(2.0)),
        ]
    );
}
