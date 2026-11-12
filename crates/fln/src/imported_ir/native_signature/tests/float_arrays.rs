//! FloatArray's packed representation and proof-erased native IR boundaries.
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

const NAMES: [&str; 12] = [
    "FloatArray.mk",
    "FloatArray.data",
    "FloatArray.emptyWithCapacity",
    "FloatArray.push",
    "FloatArray.size",
    "FloatArray.usize",
    "FloatArray.get",
    "FloatArray.get!",
    "FloatArray.uget",
    "FloatArray.set",
    "FloatArray.set!",
    "FloatArray.uset",
];

#[test]
fn float_array_prototypes_authenticate_scalar_types_borrowing_and_erased_proofs() {
    for (target, parameters, result) in [
        (
            "FloatArray.mk",
            vec![(IrType::Object, false)],
            IrType::Object,
        ),
        (
            "FloatArray.data",
            vec![(IrType::Object, false)],
            IrType::Object,
        ),
        (
            "FloatArray.emptyWithCapacity",
            vec![(IrType::TObject, true)],
            IrType::Object,
        ),
        (
            "FloatArray.push",
            vec![(IrType::Object, false), (IrType::Float, false)],
            IrType::Object,
        ),
        (
            "FloatArray.size",
            vec![(IrType::Object, true)],
            IrType::Tagged,
        ),
        (
            "FloatArray.usize",
            vec![(IrType::Object, true)],
            IrType::USize,
        ),
        (
            "FloatArray.get!",
            vec![(IrType::Object, true), (IrType::TObject, true)],
            IrType::Float,
        ),
        (
            "FloatArray.get",
            vec![
                (IrType::Object, true),
                (IrType::TObject, true),
                (IrType::Erased, false),
            ],
            IrType::Float,
        ),
        (
            "FloatArray.uget",
            vec![
                (IrType::Object, true),
                (IrType::USize, false),
                (IrType::Erased, false),
            ],
            IrType::Float,
        ),
        (
            "FloatArray.set!",
            vec![
                (IrType::Object, false),
                (IrType::TObject, true),
                (IrType::Float, false),
            ],
            IrType::Object,
        ),
        (
            "FloatArray.set",
            vec![
                (IrType::Object, false),
                (IrType::TObject, true),
                (IrType::Float, false),
                (IrType::Erased, false),
            ],
            IrType::Object,
        ),
        (
            "FloatArray.uset",
            vec![
                (IrType::Object, false),
                (IrType::USize, false),
                (IrType::Float, false),
                (IrType::Erased, false),
            ],
            IrType::Object,
        ),
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        let params: Vec<_> = parameters
            .into_iter()
            .enumerate()
            .map(|(x, (ty, borrow))| IrParam {
                x: x as u64,
                ty,
                borrow,
            })
            .collect();
        assert_eq!(bridge.arity(), params.len());
        validate_extern_signature(row, &params, &result).unwrap();
        for index in 0..params.len() {
            for change_type in [false, true] {
                let mut wrong = params.clone();
                if change_type {
                    wrong[index].ty = if wrong[index].ty == IrType::Erased {
                        IrType::TObject
                    } else {
                        IrType::Erased
                    };
                } else {
                    wrong[index].borrow = !wrong[index].borrow;
                }
                assert!(
                    matches!(
                        validate_extern_signature(row, &wrong, &result),
                        Err(IrExecutionError::NativeContract { .. })
                    ),
                    "{target} parameter {index}"
                );
            }
        }
        assert!(matches!(
            validate_extern_signature(row, &params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        for changed in [
            GeneratedExternRow {
                symbol: "foreign_float_array",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*row
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}

fn typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn typed_call(x: u64, ty: IrType, target: &str, args: Vec<IrArg>) -> IrStmt {
    typed(
        x,
        ty,
        IrExpr::Fap {
            function: name(target),
            args,
        },
    )
}

fn setup() -> Vec<IrStmt> {
    vec![
        num(1, 1.25f64.to_bits()),
        typed_call(2, IrType::UInt64, "UInt64.ofNat", vec![var(1)]),
        typed_call(3, IrType::Float, "Float.ofBits", vec![var(2)]),
        num(4, 0),
        typed_call(
            5,
            IrType::Object,
            "FloatArray.emptyWithCapacity",
            vec![var(4)],
        ),
        typed_call(6, IrType::Object, "FloatArray.push", vec![var(5), var(3)]),
    ]
}

#[test]
fn float_array_boxed_setter_keeps_pending_proofs_and_reusable_captures() {
    let mut stmts = setup();
    stmts.extend([
        typed(
            7,
            IrType::Object,
            IrExpr::Box {
                ty: IrType::Float,
                x: 3,
            },
        ),
        typed(
            8,
            IrType::Object,
            IrExpr::Pap {
                function: name("FloatArray.set._boxed"),
                args: vec![var(6), var(4)],
            },
        ),
        // Supplying only the Float leaves the erased proof as a distinct
        // callable stage. The second call reuses the original array capture.
        typed(
            9,
            IrType::Object,
            IrExpr::Ap {
                x: 8,
                args: vec![var(7)],
            },
        ),
        typed(
            10,
            IrType::Object,
            IrExpr::Ap {
                x: 9,
                args: vec![IrArg::Erased],
            },
        ),
        num(11, 2.5f64.to_bits()),
        typed_call(12, IrType::UInt64, "UInt64.ofNat", vec![var(11)]),
        typed_call(13, IrType::Float, "Float.ofBits", vec![var(12)]),
        typed(
            14,
            IrType::Object,
            IrExpr::Box {
                ty: IrType::Float,
                x: 13,
            },
        ),
        typed(
            15,
            IrType::Object,
            IrExpr::Ap {
                x: 8,
                args: vec![var(14), IrArg::Erased],
            },
        ),
        typed_call(
            16,
            IrType::Float,
            "FloatArray.get",
            vec![var(10), var(4), IrArg::Erased],
        ),
        typed_call(
            17,
            IrType::Float,
            "FloatArray.get",
            vec![var(15), var(4), IrArg::Erased],
        ),
        typed_call(
            18,
            IrType::Float,
            "FloatArray.get",
            vec![var(6), var(4), IrArg::Erased],
        ),
        typed_call(19, IrType::UInt64, "Float.toBits", vec![var(16)]),
        typed_call(20, IrType::UInt64, "Float.toBits", vec![var(17)]),
        typed_call(21, IrType::UInt64, "Float.toBits", vec![var(18)]),
        call(22, "UInt64.toNat", &[19]),
        call(23, "UInt64.toNat", &[20]),
        call(24, "UInt64.toNat", &[21]),
        call(25, "Nat.add", &[22, 23]),
        call(26, "Nat.add", &[25, 24]),
    ]);
    let compiled = compile_declarations(vec![entry(stmts, 26)]).unwrap();
    let expected = 1.25f64.to_bits() * 2 + 2.5f64.to_bits();
    assert_nat(&compiled, &expected.to_string());
    assert!(
        compiled
            .native_externs()
            .iter()
            .any(|row| row == "extern:FloatArray.set")
    );
    assert!(
        compiled
            .reference_functions()
            .iter()
            .all(|f| f.name == name("Arity.main"))
    );
}

#[test]
fn float_array_direct_calls_refuse_observable_proof_slots() {
    let mut stmts = setup();
    stmts.push(typed_call(
        7,
        IrType::Float,
        "FloatArray.get",
        vec![var(6), var(4), var(4)],
    ));
    let mut declaration = entry(stmts, 7);
    let IrDecl::Function { result, .. } = &mut declaration else {
        unreachable!();
    };
    *result = IrType::Float;
    assert!(matches!(
        compile_declarations(vec![declaration]),
        Err(IrExecutionError::Unsupported {
            form: "unreviewed native erased operand",
            ..
        })
    ));
}

fn reference() -> Option<PathBuf> {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    if reference.is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for FloatArray IR"
        );
        eprintln!("SKIP: FloatArray IR requires FLN_REFERENCE_LEAN");
    }
    reference
}

#[test]
fn live_float_array_ir_matches_pin_with_full_native_and_boxed_prototypes() {
    let Some(reference) = reference() else {
        return;
    };
    let lock = include_str!("../../../../../../SUITE.lock");
    let pin = lock
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .unwrap();
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            reference
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("lib/lean")
        });
    let bytes = std::fs::read(library.join("Init/Data/FloatArray/Basic.ir")).unwrap();
    fln_olean::pin::check_pinned_header(&bytes).unwrap();
    let raw = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    let mut declarations = Vec::new();
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    for declaration in raw.decls {
        let (row, is_boxed) = match crate::imported_ir::native_row(declaration.name()) {
            Some(row) => (row, false),
            None => {
                let Some(row) = boxed_row(declaration.name()) else {
                    continue;
                };
                (row, true)
            }
        };
        if !NAMES.contains(&row.name) {
            continue;
        }
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        if is_boxed {
            bridge.validate_declaration(&declaration).unwrap();
            assert!(wrappers.insert(row.name));
        } else {
            let IrDecl::Extern { params, result, .. } = &declaration else {
                panic!("FloatArray native prototype is not extern: {}", row.name);
            };
            validate_extern_signature(row, params, result).unwrap();
            assert_eq!(params.len(), bridge.arity());
            assert!(externs.insert(row.name));
        }
        declarations.push(declaration);
    }
    let expected: BTreeSet<_> = NAMES.into_iter().collect();
    assert_eq!(externs, expected);
    assert_eq!(wrappers, expected);
    let native = IrModule {
        decls: declarations,
        ..IrModule::default()
    };

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = root.join(format!(
        "float-array-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let source = r#"module
prelude
public import Init
public import Init.Data.FloatArray.Basic
public section
@[noinline] def floatArrayAnswer (first second : Float) : UInt64 :=
  let initial := (FloatArray.emptyWithCapacity 8).push first
  let both := initial.push second
  let updated := both.set! 0 second
  let restored := FloatArray.mk updated.data
  (restored.get! 0 + initial.get! 0).toBits
@[noinline] def floatArrayProofAnswer (first second : Float) : UInt64 :=
  let both := ((FloatArray.emptyWithCapacity 0).push first).push second
  if h : 1 < both.size then
    let changed := both.set 1 first h
    if hu : (0 : USize).toNat < changed.size then
      let value := changed.uget 0 hu
      if hv : (1 : USize).toNat < changed.size then
        let final := changed.uset 1 value hv
        if hf : 0 < final.size then (final.get 0 hf).toBits else 0
      else 0
    else 0
  else 0
#eval floatArrayAnswer 1.25 2.5 == (3.75 : Float).toBits
#eval floatArrayProofAnswer 1.25 2.5 == (1.25 : Float).toBits
"#;
    std::fs::write(root.join("NativeFloatArray.lean"), source).unwrap();
    let output = Command::new(&reference)
        .current_dir(&root)
        .args([
            "-j1",
            "-o",
            "NativeFloatArray.olean",
            "NativeFloatArray.lean",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "true\ntrue\n");
    assert!(output.stderr.is_empty());
    let user = crate::decode_ir_artifact(
        &std::fs::read(root.join("NativeFloatArray.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    // The pin hoists closed values into helpers owned by this user module.
    // Those helpers must be executable without admitting toolchain bodies.
    let users: BTreeSet<_> = user
        .decls
        .iter()
        .map(|declaration| declaration.name().clone())
        .collect();
    let partition = VerifiedPartition::user_fixture();
    for (entry, expected) in [
        ("floatArrayAnswer", 3.75f64.to_bits()),
        ("floatArrayProofAnswer", 1.25f64.to_bits()),
    ] {
        let compiled = compile(
            &[user.clone(), native.clone()],
            &name(entry),
            &[
                EntryArgument::FloatBits(1.25f64.to_bits()),
                EntryArgument::FloatBits(2.5f64.to_bits()),
            ],
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry}: {error:?}"));
        let bytes =
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        for program in [compiled.program.program(), &replay] {
            let outcome = execute(program, ExecutionLimits::default(), None);
            let Outcome::Complete(VmExit::Returned(value)) = outcome else {
                panic!("{outcome:?}");
            };
            assert_eq!(value.value.try_ctor_scalar_u64(0), Some(expected));
        }
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|f| f.producer() == "reference" && users.contains(&f.name))
        );
    }
}
