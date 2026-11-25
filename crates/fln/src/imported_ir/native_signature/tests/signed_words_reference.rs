//! Signed-word native wrappers, including real pin-produced higher-order IR.
use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use fln_vm::interpreter::VmRefusal;
use std::path::{Path, PathBuf};
use std::process::Command;

const FAMILIES: [(&str, u32); 5] = [
    ("Int8", 8),
    ("Int16", 16),
    ("Int32", 32),
    ("Int64", 64),
    ("ISize", usize::BITS),
];
const OPERATIONS: [&str; 21] = [
    "add",
    "sub",
    "mul",
    "div",
    "mod",
    "land",
    "lor",
    "xor",
    "shiftLeft",
    "shiftRight",
    "complement",
    "neg",
    "abs",
    "decEq",
    "decLe",
    "decLt",
    "ofNat",
    "ofInt",
    "toInt",
    "toFloat",
    "toFloat32",
];

fn names() -> Vec<String> {
    FAMILIES
        .into_iter()
        .flat_map(|(family, _)| {
            OPERATIONS
                .into_iter()
                .map(move |operation| format!("{family}.{operation}"))
                .chain(
                    FAMILIES
                        .into_iter()
                        .filter(move |(other, _)| *other != family)
                        .map(move |(other, _)| format!("{family}.to{other}")),
                )
        })
        .collect()
}

#[test]
fn signed_word_wrappers_bind_all_generated_native_contracts() {
    let wanted: BTreeSet<_> = names().into_iter().collect();
    let published: BTreeSet<_> = crate::imported_ir::EXTERN_ROWS
        .iter()
        .filter(|row| {
            row.name
                .split_once('.')
                .is_some_and(|(family, _)| FAMILIES.iter().any(|(name, _)| *name == family))
        })
        .map(|row| row.name.to_owned())
        .collect();
    assert_eq!(wanted, published);
    assert_eq!(wanted.len(), 125);
    for target in wanted {
        let row = crate::imported_ir::native_row(&name(&target)).unwrap();
        assert!(BoxedNative::from_row(row).unwrap().is_some(), "{target}");
        for changed in [
            GeneratedExternRow {
                name: "Foreign.value",
                ..*row
            },
            GeneratedExternRow {
                symbol: "foreign_value",
                ..*row
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*row
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow { levels: 1, ..*row },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                effect: "io",
                ..*row
            },
            GeneratedExternRow {
                safety: "unsafe",
                ..*row
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*row
            },
            GeneratedExternRow {
                entry_class: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                entry_scope: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                mode: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                profile: "standard",
                ..*row
            },
        ] {
            assert!(
                matches!(
                    BoxedNative::from_row(&changed),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "{target}: {changed:?}"
            );
        }
    }
}

fn types(family: &str) -> (IrType, IrType, IrType) {
    match family {
        "Int8" => (IrType::UInt8, IrType::Tagged, IrType::Tagged),
        "Int16" => (IrType::UInt16, IrType::Tagged, IrType::Tagged),
        "Int32" => (IrType::UInt32, IrType::TObject, IrType::TObject),
        "Int64" => (IrType::UInt64, IrType::Object, IrType::TObject),
        "ISize" => (IrType::USize, IrType::TObject, IrType::TObject),
        _ => unreachable!("test families are explicit"),
    }
}

fn typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn typed_call(x: u64, ty: IrType, target: &str, args: &[u64]) -> IrStmt {
    typed(
        x,
        ty,
        IrExpr::Fap {
            function: name(target),
            args: args.iter().copied().map(var).collect(),
        },
    )
}

fn capture_entry(family: &str) -> IrDecl {
    let (raw, boxed, integer) = types(family);
    entry(
        vec![
            // Truncation yields -1 at every width, including a heap-backed
            // all-ones UInt64 representation on the wide path.
            num(1, u64::MAX),
            typed_call(2, raw.clone(), &format!("{family}.ofNat"), &[1]),
            typed(
                3,
                boxed.clone(),
                IrExpr::Box {
                    ty: raw.clone(),
                    x: 2,
                },
            ),
            bind(
                4,
                IrExpr::Pap {
                    function: name(&format!("{family}.add._boxed")),
                    args: vec![var(3)],
                },
            ),
            num(5, 2),
            typed_call(6, raw.clone(), &format!("{family}.ofNat"), &[5]),
            typed(
                7,
                boxed.clone(),
                IrExpr::Box {
                    ty: raw.clone(),
                    x: 6,
                },
            ),
            typed(
                8,
                boxed.clone(),
                IrExpr::Ap {
                    x: 4,
                    args: vec![var(7)],
                },
            ),
            typed(
                9,
                boxed,
                IrExpr::Ap {
                    x: 4,
                    args: vec![var(3)],
                },
            ),
            typed(10, raw.clone(), IrExpr::Unbox { x: 8 }),
            typed(11, raw, IrExpr::Unbox { x: 9 }),
            typed_call(12, integer.clone(), &format!("{family}.toInt"), &[10]),
            typed_call(13, integer.clone(), &format!("{family}.toInt"), &[11]),
            typed_call(14, integer, &format!("{family}.toInt"), &[2]),
            call(15, "Int.natAbs", &[12]),
            call(16, "Int.natAbs", &[13]),
            call(17, "Int.natAbs", &[14]),
            num(18, 1000),
            call(19, "Nat.mul", &[16, 18]),
            num(20, 1_000_000),
            call(21, "Nat.mul", &[17, 20]),
            call(22, "Nat.add", &[15, 19]),
            call(23, "Nat.add", &[22, 21]),
        ],
        23,
    )
}

#[test]
fn signed_word_closures_preserve_negative_captures_and_canonical_replay() {
    for (family, _) in FAMILIES {
        let compiled = compile_declarations(vec![capture_entry(family)]).unwrap();
        assert_nat(&compiled, "1002001");
        assert!(
            compiled
                .native_externs()
                .contains(&format!("extern:{family}.add"))
        );
        assert!(matches!(
            compiled
                .execute(
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None
                )
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&|| true))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert_nat(&compiled, "1002001");
    }
}

#[test]
fn signed_word_native_wrappers_refuse_forged_telescope_and_values() {
    for (family, _) in FAMILIES {
        let (raw, boxed, _) = types(family);
        let target = format!("{family}.add");
        let row = crate::imported_ir::native_row(&name(&target)).unwrap();
        let raw_parameters: Vec<_> = (1..=2)
            .map(|x| IrParam {
                x,
                borrow: false,
                ty: raw.clone(),
            })
            .collect();
        validate_extern_signature(row, &raw_parameters, &raw).unwrap();
        for index in 0..raw_parameters.len() {
            let mut wrong = raw_parameters.clone();
            wrong[index].ty = IrType::Erased;
            assert!(validate_extern_signature(row, &wrong, &raw).is_err());
            wrong = raw_parameters.clone();
            wrong[index].borrow = true;
            assert!(validate_extern_signature(row, &wrong, &raw).is_err());
        }
        assert!(validate_extern_signature(row, &raw_parameters, &IrType::Void).is_err());

        let forged = IrDecl::Function {
            name: Name::str(name(&target), "_boxed"),
            params: (1..=2)
                .map(|x| IrParam {
                    x,
                    borrow: false,
                    ty: boxed.clone(),
                })
                .collect(),
            result: boxed,
            body: IrBody {
                stmts: vec![num(3, 99)],
                terminal: Box::new(IrTerminal::Ret(var(3))),
            },
            sorry_dep: None,
        };
        // A matching reserved native name never grants its supplied body
        // interpretation authority; the result still comes from native add.
        assert_nat(
            &compile_declarations(vec![capture_entry(family), forged.clone()]).unwrap(),
            "1002001",
        );
        for change in 0..5 {
            let mut wrong = forged.clone();
            let IrDecl::Function {
                params,
                result,
                sorry_dep,
                ..
            } = &mut wrong
            else {
                unreachable!()
            };
            match change {
                0 => params[0].borrow = true,
                1 => params[1].ty = IrType::Erased,
                2 => *result = IrType::Void,
                3 => *sorry_dep = Some(name("sorryAx")),
                _ => {
                    params.pop();
                }
            }
            assert!(matches!(
                compile_declarations(vec![capture_entry(family), wrong]),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        let mut bad_value = capture_entry(family);
        let IrDecl::Function { body, .. } = &mut bad_value else {
            unreachable!()
        };
        body.stmts[2] = bind(3, IrExpr::Lit(IrLit::Str("not a signed word".to_owned())));
        match compile_declarations(vec![bad_value]) {
            Err(IrExecutionError::IrValidation(_)) => {}
            Ok(compiled) => assert!(matches!(
                compiled.execute(ExecutionLimits::default(), None).outcome,
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::TypeMismatch { .. },
                    ..
                })
            )),
            other => panic!("malformed word must fail type validation: {other:?}"),
        }
        assert_nat(
            &compile_declarations(vec![capture_entry(family)]).unwrap(),
            "1002001",
        );
    }
}

struct Fixture {
    source: String,
    roots: BTreeSet<String>,
    cases: Vec<(String, Vec<u128>)>,
}

fn fixture() -> Fixture {
    let mut fixture = Fixture {
        source: "module\nprelude\npublic import Init\npublic section\n\n@[inline] def swEncode (n : Int) : Nat :=\n  if n < 0 then Int.natAbs n * 2 + 1 else Int.natAbs n * 2\n".to_owned(),
        roots: BTreeSet::from(["swEncode".to_owned()]),
        cases: Vec::new(),
    };
    for (family, bits) in FAMILIES {
        let helper = format!("sw{family}Transform");
        fixture.roots.insert(helper.clone());
        fixture.source.push_str(&format!(
            "\n@[noinline, nospecialize] def {helper} (f : {family} → {family}) (n : {family}) : Nat :=\n  swEncode ({family}.toInt (f n)) + 1024 * swEncode ({family}.toInt (f ({family}.add n ({family}.ofNat 1))))\n"
        ));
        let decision = format!("sw{family}Decision");
        fixture.roots.insert(decision.clone());
        fixture.source.push_str(&format!(
            "\n@[noinline, nospecialize] def {decision} {{p : {family} → Prop}}\n    (f : (n : {family}) → Decidable (p n)) (n : {family}) : Nat :=\n  let first := match f n with | .isTrue _ => 1 | .isFalse _ => 0\n  let second := match f ({family}.add n ({family}.ofNat 1)) with | .isTrue _ => 2 | .isFalse _ => 0\n  first + second\n"
        ));
        let half = 1u128 << (bits - 1);
        let max = half * 2 - 1;
        for operation in
            OPERATIONS
                .into_iter()
                .chain(
                    FAMILIES
                        .iter()
                        .filter(|(other, _)| *other != family)
                        .map(|(other, _)| match *other {
                            "Int8" => "toInt8",
                            "Int16" => "toInt16",
                            "Int32" => "toInt32",
                            "Int64" => "toInt64",
                            "ISize" => "toISize",
                            _ => unreachable!(),
                        }),
                )
        {
            let entry = format!("sw{family}_{operation}");
            fixture.roots.insert(entry.clone());
            let binary = matches!(
                operation,
                "add"
                    | "sub"
                    | "mul"
                    | "div"
                    | "mod"
                    | "land"
                    | "lor"
                    | "xor"
                    | "shiftLeft"
                    | "shiftRight"
                    | "decEq"
                    | "decLe"
                    | "decLt"
            );
            let body = if matches!(operation, "decEq" | "decLe" | "decLt") {
                format!("{decision} ({family}.{operation} ({family}.ofNat a)) ({family}.ofNat b)")
            } else if binary {
                format!("{helper} ({family}.{operation} ({family}.ofNat a)) ({family}.ofNat b)")
            } else if matches!(operation, "neg" | "abs" | "complement") {
                format!("{helper} {family}.{operation} ({family}.ofNat a)")
            } else {
                let conversion = format!("sw{family}Use_{operation}");
                fixture.roots.insert(conversion.clone());
                let (input, output, encode, argument) = match operation {
                    "ofNat" => (
                        "Nat",
                        family,
                        format!("fun n => swEncode ({family}.toInt n)"),
                        "a".to_owned(),
                    ),
                    "ofInt" => (
                        "Int",
                        family,
                        format!("fun n => swEncode ({family}.toInt n)"),
                        "Int.neg (Int.ofNat a)".to_owned(),
                    ),
                    "toInt" => (
                        family,
                        "Int",
                        "swEncode".to_owned(),
                        format!("{family}.ofNat a"),
                    ),
                    "toFloat" => (
                        family,
                        "Float",
                        "fun n => UInt64.toNat (Float.toBits n)".to_owned(),
                        format!("{family}.ofNat a"),
                    ),
                    "toFloat32" => (
                        family,
                        "Float32",
                        "fun n => UInt32.toNat (Float32.toBits n)".to_owned(),
                        format!("{family}.ofNat a"),
                    ),
                    _ => {
                        let output = operation.strip_prefix("to").unwrap();
                        (
                            family,
                            output,
                            format!("fun n => swEncode ({output}.toInt n)"),
                            format!("{family}.ofNat a"),
                        )
                    }
                };
                fixture.source.push_str(&format!(
                    "\n@[noinline, nospecialize] def {conversion} (f : {input} → {output}) (n : {input}) : Nat :=\n  ({encode}) (f n) + 1024 * ({encode}) (f (n + 1))\n"
                ));
                format!("{conversion} {family}.{operation} ({argument})")
            };
            fixture.source.push_str(&format!(
                "\n@[noinline] def {entry} ({} : Nat) : Nat := {body}\n",
                if binary { "a b" } else { "a" }
            ));
            if binary {
                for arguments in [
                    [0, 0],
                    [7, 3],
                    [max, 3],
                    [half, max],
                    [half, 0],
                    [max, max],
                    [half - 1, 1],
                    [1, half],
                    [1, max],
                    [max + 2, 1],
                ] {
                    fixture.cases.push((entry.clone(), arguments.to_vec()));
                }
            } else {
                for value in [0, 1, 7, half - 1, half, max, max + 2] {
                    fixture.cases.push((entry.clone(), vec![value]));
                }
            }
        }
    }
    fixture
}

#[test]
fn live_pinned_signed_words_preserve_all_native_prototypes_and_higher_order_values() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for signed-word IR"
        );
        eprintln!("SKIP: live signed-word IR requires FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let prototypes = native_prototypes(&reference);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "signed-words-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = fixture();
    std::fs::write(dir.join("SignedWords.lean"), &fixture.source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "-o", "SignedWords.olean", "SignedWords.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("SignedWords.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|decl| match decl {
            IrDecl::Function { body, .. } => body.bodies(),
            IrDecl::Extern { .. } => Vec::new(),
        })
        .flat_map(|body| &body.stmts)
        .filter_map(|stmt| match stmt {
            IrStmt::VDecl {
                expr: IrExpr::Pap { function, .. },
                ..
            } => Some(function.clone()),
            _ => None,
        })
        .collect();
    for target in names() {
        assert!(
            partials.contains(&Name::str(name(&target), "_boxed")),
            "{target} partial application optimized away; {dir:?}"
        );
    }
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|decl| {
            let text = decl.name().to_display_string();
            assert!(
                fixture.roots.contains(text.split('.').next().unwrap()),
                "unexpected fixture declaration: {text}"
            );
            assert!(crate::imported_ir::native_row(decl.name()).is_none());
            assert!(boxed_row(decl.name()).is_none());
            decl.name().clone()
        })
        .collect();
    let mut source = fixture.source;
    for (entry, arguments) in &fixture.cases {
        source.push_str(&format!("\n#eval {entry}"));
        for argument in arguments {
            source.push_str(&format!(" {argument}"));
        }
        source.push('\n');
    }
    std::fs::write(dir.join("Oracle.lean"), source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "Oracle.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(
        expected.len(),
        fixture.cases.len(),
        "unexpected oracle output: {output}"
    );
    let modules = [module, prototypes];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, values), expected) in fixture.cases.into_iter().zip(expected) {
        let arguments: Vec<_> = values
            .iter()
            .map(|&value| {
                EntryArgument::Nat(if value <= u128::from(u64::MAX) {
                    IrNat::Small(value as u64)
                } else {
                    IrNat::Big(vec![value as u64, (value >> 64) as u64])
                })
            })
            .collect();
        let compiled = compile(
            &modules,
            &name(&entry),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {values:?}: {error:?}; {dir:?}"));
        eprintln!("live signed-word Reference and Golem: {entry} {values:?} = {expected}");
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .any(|function| function.name == name(&entry))
        );
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                ),
            "native signed-word bodies must not acquire interpretation authority"
        );
        observed.extend(compiled.native_externs().iter().cloned());
    }
    for target in names() {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked"
        );
    }
}

fn native_prototypes(reference: &Path) -> IrModule {
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
    let wanted: BTreeSet<_> = names().into_iter().collect();
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    let mut declarations = Vec::new();
    for relative in [
        "Init/Data/SInt/Basic.ir",
        "Init/Data/SInt/Float.ir",
        "Init/Data/SInt/Float32.ir",
    ] {
        let path = library.join(relative);
        let module = crate::decode_ir_artifact(&std::fs::read(&path).unwrap(), 32 * 1024 * 1024)
            .unwrap_or_else(|error| panic!("{path:?}: {error:?}"));
        for declaration in module.decls {
            let (row, is_boxed) = match crate::imported_ir::native_row(declaration.name()) {
                Some(row) => (row, false),
                None => {
                    let Some(row) = boxed_row(declaration.name()) else {
                        continue;
                    };
                    (row, true)
                }
            };
            if !wanted.contains(row.name) {
                continue;
            }
            let bridge = BoxedNative::from_row(row).unwrap().unwrap();
            if is_boxed {
                bridge
                    .validate_declaration(&declaration)
                    .unwrap_or_else(|error| {
                        panic!("{} in {path:?}: {error:?}; {declaration:?}", row.name)
                    });
                assert!(wrappers.insert(row.name.to_owned()));
            } else {
                let IrDecl::Extern { params, result, .. } = &declaration else {
                    panic!("{} is not an extern in {path:?}", row.name)
                };
                validate_extern_signature(row, params, result).unwrap_or_else(|error| {
                    panic!("{} in {path:?}: {error:?}; {declaration:?}", row.name)
                });
                assert_eq!(
                    validated_ir_arity(row, params.len()).unwrap(),
                    bridge.arity()
                );
                assert!(externs.insert(row.name.to_owned()));
                // These are mutations of independently decoded prototypes,
                // not expectations reconstructed from the new bridge table.
                for index in 0..params.len() {
                    let mut wrong = params.clone();
                    wrong[index].borrow = !wrong[index].borrow;
                    assert!(validate_extern_signature(row, &wrong, result).is_err());
                    wrong = params.clone();
                    wrong[index].ty = IrType::Erased;
                    assert!(validate_extern_signature(row, &wrong, result).is_err());
                }
                assert!(validate_extern_signature(row, params, &IrType::Void).is_err());
            }
            declarations.push(declaration);
        }
    }
    assert_eq!(externs, wanted, "all 125 signed-word raw native prototypes");
    assert_eq!(
        wrappers, wanted,
        "all 125 signed-word boxed native prototypes"
    );
    assert_eq!(declarations.len(), wanted.len() * 2);
    IrModule {
        decls: declarations,
        ..IrModule::default()
    }
}
