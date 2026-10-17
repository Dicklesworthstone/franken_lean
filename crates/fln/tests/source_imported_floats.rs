//! Admit the complete actual scientific-float import closure, then check,
//! execute, and replay the unchanged regression example and dynamic conversions.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedFloatValue, ClosedVmValue, Engine, EngineExecutionLimits, Environment,
    FlbcExecutionLimits, KVMap, Name, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput,
    VmExit,
};
use fln_comp::flbc::{CodecLimits, Instruction, decode_canonical};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;

fn pinned_lib() -> Option<PathBuf> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|library| library.is_dir());
    assert!(
        library.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the actual pinned Reference library is required"
    );
    library
}

fn read_parts(library: &Path, module: &Name) -> [Vec<u8>; 3] {
    let path = library
        .join(module.to_display_string().replace('.', "/"))
        .with_extension("olean");
    [
        std::fs::read(&path).expect("actual exported olean"),
        std::fs::read(path.with_extension("olean.server")).expect("actual server olean"),
        std::fs::read(path.with_extension("olean.private")).expect("actual private olean"),
    ]
}

fn actual_scientific_import(library: &Path) -> Engine {
    let root = Name::from_components(["Init", "Data", "OfScientific"]);
    let mut pending = vec![(root.clone(), false)];
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    while let Some((module, finished)) = pending.pop() {
        if finished {
            ordered.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        assert!(
            seen.len() <= 100,
            "the fixed pinned closure remains bounded"
        );
        let parts = read_parts(library, &module);
        let imports = fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES))
            .expect("actual pinned import graph");
        artifacts.insert(module.clone(), parts);
        pending.push((module, true));
        pending.extend(imports.into_iter().rev().map(|module| (module, false)));
    }
    assert_eq!(
        ordered.len(),
        55,
        "the exact pinned scientific-float closure"
    );
    let inputs: Vec<_> = ordered
        .iter()
        .map(|module| {
            let [exported, server, private] = &artifacts[module];
            OleanModuleInput {
                name: module,
                artifact: exported,
                server_artifact: Some(server),
                private_artifact: Some(private),
            }
        })
        .collect();
    eprintln!(
        "admitting {} actual modules, {} artifact bytes",
        inputs.len(),
        artifacts
            .values()
            .flat_map(|parts| parts.iter())
            .map(Vec::len)
            .sum::<usize>()
    );
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &[root],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .expect("actual scientific-float closure passes the ordinary admission council")
        .into_complete()
        .expect("actual import completes within its explicit limits");
    assert_eq!(imported.modules.len(), 55);
    eprintln!(
        "admitted {} actual declarations and activated their source metadata",
        imported.engine.environment().constants().count()
    );
    imported.engine
}

fn assert_example_value(index: usize, type_: &fln::Expr, exit: &VmExit) {
    match index {
        0 => assert_eq!(
            fln::closed_float_value(type_, exit).unwrap(),
            Some(ClosedFloatValue::Float(10.5f64.to_bits()))
        ),
        1 => assert_eq!(
            fln::closed_float_value(type_, exit).unwrap(),
            Some(ClosedFloatValue::Float32(125.0f32.to_bits()))
        ),
        2 => assert_eq!(
            fln::closed_vm_value(exit).unwrap(),
            Some(ClosedVmValue::String("2.100000".to_owned()))
        ),
        3 => {
            let VmExit::Returned(value) = exit else {
                panic!("negative-zero bits must return a Nat: {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some("9223372036854775808")
            );
        }
        _ => panic!("unexpected regression result {index}"),
    }
}

fn assert_dynamic_conversions(engine: &Engine, options: &KVMap) {
    // These functions keep the mantissa, sign and exponent as runtime
    // parameters. The full import grants executable-body authority to the
    // actual opaque definitions through their complete private journals.
    let source = r#"
def dynamicScientific64 (m : Nat) (s : Bool) (e : Nat) : Float :=
  Float.ofScientific m s e
def dynamicScientific32 (m : Nat) (s : Bool) (e : Nat) : Float32 :=
  Float32.ofScientific m s e
def useScientific64 (f : Nat → Bool → Nat → Float) (m : Nat) (s : Bool) (e : Nat) : Float :=
  f m s e
def useScientific32 (f : Nat → Bool → Nat → Float32) (m : Nat) (s : Bool) (e : Nat) : Float32 :=
  f m s e
def decimal64 (m : Nat) : Nat → Float := Float.ofScientific m true
def dynamicNat64 (n : Nat) : Float := Float.ofNat n
def dynamicNat32 (n : Nat) : Float32 := Float32.ofNat n
def useNat64 (f : Nat → Float) (n : Nat) : Float := f n
def useNat32 (f : Nat → Float32) (n : Nat) : Float32 := f n
def dynamicInt64 (n : Int) : Float := Float.ofInt n
def dynamicInt32 (n : Int) : Float32 := Float32.ofInt n
#eval dynamicScientific64 21 true 1
#eval dynamicScientific32 21 true 1
#eval dynamicScientific64 1 false 20
#eval useScientific64 Float.ofScientific 1245 true 3
#eval useScientific32 Float32.ofScientific 1245 true 3
#eval decimal64 21 1
#eval dynamicScientific64 24703282292062328 true 340
#eval dynamicScientific64 24703282292062330 true 340
#eval dynamicScientific32 1 true 45
#eval dynamicScientific64 1 false 309
#eval dynamicScientific32 1 false 39
#eval dynamicNat64 18446744073709553665
#eval dynamicNat32 9223372586610589697
#eval useNat64 Nat.toFloat 42
#eval useNat32 Nat.toFloat32 42
#eval dynamicInt64 (Int.negSucc 41)
#eval dynamicInt32 (Int.ofNat 125)
"#;
    // Pin semantics first retain 64 mantissa bits, then round to the requested
    // width, then scale. The two subnormal cases distinguish that order from a
    // correctly rounded decimal parser; the large Float32 input distinguishes
    // direct UInt64-to-Float32 conversion from an intermediate Float cast.
    let expected = [
        ClosedFloatValue::Float(0x4000_cccc_cccc_cccd),
        ClosedFloatValue::Float32(0x4006_6666),
        ClosedFloatValue::Float(0x4415_af1d_78b5_8c40),
        ClosedFloatValue::Float(4_608_285_800_708_723_180),
        ClosedFloatValue::Float32(1_067_408_425),
        ClosedFloatValue::Float(0x4000_cccc_cccc_cccd),
        ClosedFloatValue::Float(0),
        ClosedFloatValue::Float(1),
        ClosedFloatValue::Float32(1),
        ClosedFloatValue::Float(0x7ff0_0000_0000_0000),
        ClosedFloatValue::Float32(0x7f80_0000),
        ClosedFloatValue::Float(0x43f0_0000_0000_0000),
        ClosedFloatValue::Float32(0x5f00_0001),
        ClosedFloatValue::Float(42.0f64.to_bits()),
        ClosedFloatValue::Float32(42.0f32.to_bits()),
        ClosedFloatValue::Float((-42.0f64).to_bits()),
        ClosedFloatValue::Float32(125.0f32.to_bits()),
    ];
    let executed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("dynamic conversions execute the actual admitted scientific bodies")
        .into_complete()
        .expect("dynamic conversion execution completes within its explicit limits");
    let evaluations = &executed.batch.source_evaluation_indices;
    assert_eq!(evaluations.len(), expected.len());
    for (index, (&evaluation, expected)) in evaluations.iter().zip(expected).enumerate() {
        let execution = &executed.batch.executions[evaluation];
        let program = decode_canonical(&execution.flbc_artifact, CodecLimits::default())
            .expect("dynamic conversions produce validated independent FLBC");
        let has_intrinsic = |wanted: &str| {
            program.functions().iter().any(|function| {
                function.code.iter().any(|instruction| {
                    matches!(instruction, Instruction::Intrinsic { row, .. } if row == wanted)
                })
            })
        };
        let scaling = match expected {
            ClosedFloatValue::Float(_) => "extern:Float.scaleB",
            ClosedFloatValue::Float32(_) => "extern:Float32.scaleB",
        };
        assert!(
            has_intrinsic(scaling) && has_intrinsic("extern:Nat.pow"),
            "evaluation {index} must execute scientific arithmetic at runtime"
        );
        assert_eq!(
            fln::closed_float_value(&execution.runtime_type, &execution.exit).unwrap(),
            Some(expected),
            "dynamic evaluation {index}"
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            options,
            FlbcExecutionLimits::default(),
        )
        .expect("dynamic conversion output is an independent FLBC artifact")
        .into_complete()
        .expect("dynamic conversion FLBC replay completes");
        assert_eq!(
            fln::closed_float_value(&execution.runtime_type, &replay).unwrap(),
            Some(expected),
            "dynamic replay {index}"
        );
    }
}

#[test]
fn actual_imported_scientific_floats_execute_and_replay_the_regression() {
    let Some(library) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    std::thread::Builder::new()
        .name("actual-imported-floats".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            let engine = actual_scientific_import(&library);
            let options = KVMap::new();
            let root = engine.logical_root(&options);
            let executed = engine
                .execute_source_commands_with_checks(
                    // File-relative: compile-time bytes need no compile-time tree root.
                    include_bytes!("../../../examples/native_float_runtime.lean"),
                    &options,
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .expect("the unchanged regression executes over its actual admitted imports")
                .into_complete()
                .expect("the regression execution completes");
            let evaluations = &executed.batch.source_evaluation_indices;
            assert_eq!(evaluations.len(), 4);
            for (index, &execution) in evaluations.iter().enumerate() {
                let execution = &executed.batch.executions[execution];
                assert_example_value(index, &execution.runtime_type, &execution.exit);
                let replay = fln::execute_flbc_artifact(
                    &execution.flbc_artifact,
                    &options,
                    FlbcExecutionLimits::default(),
                )
                .expect("the compiler output is an independent FLBC artifact")
                .into_complete()
                .expect("the FLBC artifact completes");
                assert_example_value(index, &execution.runtime_type, &replay);
            }
            assert_dynamic_conversions(&engine, &options);
            assert_eq!(engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}
