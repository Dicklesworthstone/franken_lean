//! Actual higher-order primitive IR with every reviewed native prototype.
use super::arrays_reference::assert_nat_replay;
use super::boxed_primitives::{STRING_PREDICATES, WORD_FAMILIES, names};
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::{Path, PathBuf};
use std::process::Command;

#[test]
fn live_pinned_boxed_primitives_preserve_values_captures_and_canonical_replay() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for live native primitive closures"
        );
        eprintln!("SKIP: live native primitive closures require FLN_REFERENCE_LEAN");
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
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "primitive-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeScalarModule.lean");
    std::fs::write(dir.join("NativeScalarModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeScalarModule.olean", "NativeScalarModule.lean"])
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
        &std::fs::read(dir.join("NativeScalarModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let boxed_partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|declaration| {
            let bodies = match declaration {
                IrDecl::Function { body, .. } => body.bodies(),
                IrDecl::Extern { .. } => Vec::new(),
            };
            bodies
                .into_iter()
                .flat_map(|body| body.stmts.iter())
                .filter_map(|statement| match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, .. },
                        ..
                    } => Some(function.clone()),
                    _ => None,
                })
        })
        .collect();
    for target in names() {
        assert!(
            boxed_partials.contains(&Name::str(name(&target), "_boxed")),
            "{target} partial application optimized away; {dir:?}"
        );
    }
    let cases = cases();
    let mut users: BTreeSet<_> = cases.iter().map(|(entry, _)| name(entry)).collect();
    // Exact helper and constant names emitted by this pinned fixture.
    users.extend(
        [
            "useNatTransform",
            "useNatPredicate",
            "useNatDecision._redArg",
            "useStringTransform",
            "useCharTransform",
            "useCharTransform._boxed_const_1",
            "useStringMeasure",
            "useStringHash",
            "useStringDecision._redArg",
            "useStringTransform._closed_0",
            "useStringMeasure._closed_0",
            "natBoxedPred._closed_0",
            "stringBoxedLength._closed_0",
            "stringBoxedBytes._closed_0",
            "stringBoxedHash._closed_0",
        ]
        .map(name),
    );
    // These are the new fixture's own public families and their compiler
    // helpers. Native primitive names are separately reserved by selection;
    // no blanket namespace grant is used for the imported toolchain modules.
    let word_prefixes: Vec<_> = WORD_FAMILIES
        .into_iter()
        .flat_map(|family| {
            std::iter::once(name(&format!("{}Boxed", family.to_ascii_lowercase()))).chain(
                ["Transform", "Decision", "FromNat", "ToNat"]
                    .into_iter()
                    .map(move |suffix| name(&format!("use{family}{suffix}"))),
            )
        })
        .collect();
    users.extend(module.decls.iter().filter_map(|declaration| {
        let declaration = declaration.name();
        word_prefixes
            .iter()
            .any(|prefix| {
                declaration == prefix
                    || declaration
                        .to_display_string()
                        .starts_with(&format!("{}.", prefix.to_display_string()))
            })
            .then(|| declaration.clone())
    }));
    let mut oracle_source = source.to_owned();
    for (entry, arguments) in &cases {
        oracle_source.push_str(&format!("\n#eval {entry}"));
        for argument in arguments {
            let text = match argument {
                EntryArgument::Nat(IrNat::Small(value)) => value.to_string(),
                EntryArgument::String(value) => {
                    format!("\"{}\"", value.replace('\\', "\\\\").replace('"', "\\\""))
                }
                _ => unreachable!("fixture supplies only natural and UTF-8 string arguments"),
            };
            oracle_source.push(' ');
            oracle_source.push_str(&text);
        }
        oracle_source.push('\n');
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
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
        cases.len(),
        "unexpected oracle output: {output}"
    );
    assert!(
        expected
            .iter()
            .all(|line| !line.is_empty() && line.bytes().all(|byte| byte.is_ascii_digit()))
    );
    assert!(
        cases.iter().zip(&expected).any(|((entry, _), value)| {
            *entry == "stringBoxedHash" && value.parse::<u64>().unwrap() > u64::MAX / 2
        }),
        "the fixture must exercise a full-width boxed hash"
    );
    assert!(
        cases.iter().zip(&expected).any(|((entry, _), value)| {
            *entry == "natBoxedMul" && value.parse::<u64>().is_err()
        }),
        "the fixture must retain heap-sized natural results"
    );
    let modules = [module, native_prototypes(&reference)];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, arguments), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            &modules,
            &name(entry),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {arguments:?}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .any(|function| function.name == name(entry))
        );
        assert!(
            compiled.reference_functions().iter().all(|function| {
                function.producer() == "reference" && users.contains(&function.name)
            }),
            "native wrapper bodies must never become interpreted Reference functions"
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
        assert_nat_replay(&compiled, expected);
        observed.extend(compiled.native_externs().iter().cloned());
        eprintln!("live Reference and Golem: {entry} {arguments:?} = {expected}");
    }
    for target in names() {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked"
        );
    }
}

fn cases() -> Vec<(&'static str, Vec<EntryArgument>)> {
    let nat = |value| EntryArgument::Nat(IrNat::Small(value));
    let string = |value: &str| EntryArgument::String(value.to_owned());
    let mut cases = Vec::new();
    for entry in [
        "natBoxedAdd",
        "natBoxedSub",
        "natBoxedMul",
        "natBoxedDiv",
        "natBoxedMod",
        "natBoxedPow",
    ] {
        for (a, b) in [(0, 0), (42, 0), (42, 7), (u64::MAX, 2)] {
            cases.push((entry, vec![nat(a), nat(b)]));
        }
    }
    for value in [0, 1, 42, u64::MAX] {
        cases.push(("natBoxedPred", vec![nat(value)]));
    }
    for entry in [
        "natBoxedBeq",
        "natBoxedBle",
        "natBoxedDecEq",
        "natBoxedDecLe",
        "natBoxedDecLt",
    ] {
        for (a, b) in [(0, 0), (42, 41), (42, 42), (42, 43), (u64::MAX, u64::MAX)] {
            cases.push((entry, vec![nat(a), nat(b)]));
        }
    }
    for (a, b) in [("", ""), ("prefix", "tail"), ("λ", "🦀"), ("λ🦀", "λ🦀")] {
        cases.push(("stringBoxedAppend", vec![string(a), string(b)]));
    }
    for entry in [
        "stringBoxedPush",
        "stringBoxedLength",
        "stringBoxedBytes",
        "stringBoxedHash",
    ] {
        for value in ["", "ascii", "λ🦀", "é", "e\u{301}"] {
            cases.push((entry, vec![string(value)]));
        }
    }
    for (a, b) in [
        ("", ""),
        ("a!", "a"),
        ("λ🦀", "λ🦀"),
        ("é", "e\u{301}"),
        ("a", "b"),
    ] {
        cases.push(("stringBoxedEq", vec![string(a), string(b)]));
    }
    for entry in [
        "uint8Boxed",
        "uint16Boxed",
        "uint32Boxed",
        "uint64Boxed",
        "usizeBoxed",
    ] {
        for operation in 0..18 {
            for (a, b) in [(0, 0), (42, 7), (255, 8), (65_535, 32), (u64::MAX, 64)] {
                cases.push((entry, vec![nat(operation), nat(a), nat(b)]));
            }
        }
    }
    cases
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
    native_prototypes_from_library(&library)
}

#[test]
fn pinned_native_primitive_prototypes_match_boxed_and_unboxed_contracts() {
    let Some(library) = std::env::var_os("FLN_REFERENCE_LIB") else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for native primitive prototypes"
        );
        eprintln!("SKIP: native primitive prototypes require FLN_REFERENCE_LIB");
        return;
    };
    native_prototypes_from_library(Path::new(&library));
}

fn native_prototypes_from_library(library: &Path) -> IrModule {
    let wanted: BTreeSet<_> = names()
        .into_iter()
        .chain(STRING_PREDICATES.into_iter().map(str::to_owned))
        .chain(
            super::array_operations::BYTE_ARRAY_NAMES
                .into_iter()
                .map(str::to_owned),
        )
        .collect();
    let mut externs = BTreeSet::new();
    let mut wrappers = BTreeSet::new();
    let mut declarations = Vec::new();
    for relative in [
        "Init/Prelude.ir",
        "Init/Data/String/Defs.ir",
        "Init/Data/String/Bootstrap.ir",
        "Init/Data/String/Length.ir",
        "Init/Data/String/Basic.ir",
        "Init/Data/ByteArray/Basic.ir",
        "Init/Data/UInt/BasicAux.ir",
        "Init/Data/UInt/Basic.ir",
        "Init/Data/UInt/Log2.ir",
    ] {
        let path = library.join(relative);
        let bytes = std::fs::read(&path).unwrap();
        fln_olean::pin::check_pinned_header(&bytes)
            .unwrap_or_else(|error| panic!("{path:?}: {error:?}"));
        let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024)
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
                        panic!(
                            "{} boxed prototype in {path:?}: {error}; {declaration:?}",
                            row.name
                        )
                    });
                assert!(wrappers.insert(row.name.to_owned()));
            } else {
                let IrDecl::Extern { params, result, .. } = &declaration else {
                    panic!("{} is not an extern in {path:?}", row.name)
                };
                validate_extern_signature(row, params, result).unwrap_or_else(|error| {
                    panic!(
                        "{} native prototype in {path:?}: {error}; {declaration:?}",
                        row.name
                    )
                });
                assert_eq!(
                    validated_ir_arity(row, params.len()).unwrap(),
                    bridge.arity()
                );
                assert!(externs.insert(row.name.to_owned()));
            }
            declarations.push(declaration);
        }
    }
    assert_eq!(externs, wanted, "all reviewed native raw prototypes");
    assert_eq!(wrappers, wanted, "all reviewed compiler boxed prototypes");
    assert_eq!(declarations.len(), wanted.len() * 2);
    IrModule {
        decls: declarations,
        ..IrModule::default()
    }
}

#[test]
fn live_pinned_string_predicates_preserve_owned_ir_and_borrowed_native_contracts() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for live String predicate closures"
        );
        eprintln!("SKIP: live String predicate closures require FLN_REFERENCE_LEAN");
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
    let identity = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "string-predicate-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = r#"module
prelude
public import Init
public section

@[noinline, nospecialize] def useStringPredicate (f : String → Bool) (s : String) : Nat :=
  (if f s then 1 else 0) + (if f (s ++ "!") then 2 else 0) + s.utf8ByteSize

@[noinline] def stringDirectEmpty (s : String) : Nat :=
  (if String.Internal.isEmpty s then 1 else 0) + s.utf8ByteSize

@[noinline] def stringDirectPrefix (p s : String) : Nat :=
  (if String.Internal.isPrefixOf p s then 1 else 0) + p.utf8ByteSize + s.utf8ByteSize

@[noinline] def stringBoxedEmpty (s : String) : Nat :=
  useStringPredicate String.Internal.isEmpty s

@[noinline] def stringBoxedPrefix (p s : String) : Nat :=
  useStringPredicate (String.Internal.isPrefixOf p) s + p.utf8ByteSize

@[noinline] def stringAliasedPrefix (s : String) : Nat :=
  (if String.Internal.isPrefixOf s s then 1 else 0) +
  useStringPredicate (String.Internal.isPrefixOf s) s + s.utf8ByteSize
"#;
    std::fs::write(dir.join("StringPredicateModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "StringPredicateModule.olean",
            "StringPredicateModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr),
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("StringPredicateModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let mut partials = BTreeSet::new();
    let mut direct = BTreeSet::new();
    let mut aliased_prefix = false;
    for declaration in &module.decls {
        let IrDecl::Function { body, .. } = declaration else {
            continue;
        };
        for body in body.bodies() {
            for statement in &body.stmts {
                match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, .. },
                        ..
                    } => {
                        partials.insert(function.clone());
                    }
                    IrStmt::VDecl {
                        expr: IrExpr::Fap { function, args },
                        ..
                    } => {
                        direct.insert(function.clone());
                        aliased_prefix |= function == &name("String.Internal.isPrefixOf")
                            && args.len() == 2
                            && args[0] == args[1];
                    }
                    _ => {}
                }
            }
        }
    }
    for target in STRING_PREDICATES {
        assert!(
            partials.contains(&Name::str(name(target), "_boxed")),
            "{target} partial optimized away; {dir:?}"
        );
        assert!(
            direct.contains(&name(target)),
            "{target} direct call optimized away; {dir:?}"
        );
    }
    assert!(
        aliased_prefix,
        "the same object must supply both owned prefix operands"
    );
    let mut cases = Vec::new();
    for entry in [
        "stringDirectEmpty",
        "stringBoxedEmpty",
        "stringAliasedPrefix",
    ] {
        for value in ["", "x", "é😀", "e\u{301}"] {
            cases.push((entry, vec![value]));
        }
    }
    for entry in ["stringDirectPrefix", "stringBoxedPrefix"] {
        for (prefix, candidate) in [
            ("", ""),
            ("", "é😀"),
            ("é", "é😀"),
            ("😀", "é😀"),
            ("é😀", "é"),
            ("é", "e\u{301}"),
            ("e", "e\u{301}"),
            ("x", "x"),
        ] {
            cases.push((entry, vec![prefix, candidate]));
        }
    }
    let mut oracle_source = source.to_owned();
    for (entry, arguments) in &cases {
        oracle_source.push_str(&format!("\n#eval {entry}"));
        for argument in arguments {
            // The fixture strings contain no escapes or control characters.
            oracle_source.push_str(&format!(" \"{argument}\""));
        }
        oracle_source.push('\n');
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
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
        cases.len(),
        "unexpected oracle output: {output}"
    );
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter(|decl| matches!(decl, IrDecl::Function { .. }))
        .map(|decl| decl.name().clone())
        .collect();
    let modules = [module, native_prototypes(&reference)];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, strings), expected) in cases.into_iter().zip(expected) {
        let arguments: Vec<_> = strings
            .iter()
            .map(|value| EntryArgument::String((*value).to_owned()))
            .collect();
        let compiled = compile(
            &modules,
            &name(entry),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {strings:?}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                )
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
        observed.extend(compiled.native_externs().iter().cloned());
    }
    for target in STRING_PREDICATES {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} was not linked"
        );
    }
}

#[test]
fn live_pinned_byte_array_closures_preserve_scalars_aliasing_and_canonical_replay() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for live ByteArray closures"
        );
        eprintln!("SKIP: live ByteArray closures require FLN_REFERENCE_LEAN");
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
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "byte-array-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = r#"module
prelude
public import Init
public import Init.Data.ByteArray.Basic
public import Init.Data.String.Basic
public section

@[noinline] def byteSeed (n : Nat) : ByteArray :=
  (ByteArray.emptyWithCapacity 0).push (UInt8.ofNat n)

@[noinline, nospecialize] def byteUsePack
    (f : Array UInt8 → ByteArray) (a : Array UInt8) : Nat :=
  (f a).size + ((f a).get! 0).toNat

@[noinline, nospecialize] def byteUseData
    (f : ByteArray → Array UInt8) (a : ByteArray) : Nat :=
  (f a).size + ((f a)[0]!).toNat

@[noinline, nospecialize] def byteUseEmpty (f : Nat → ByteArray) (n : Nat) : Nat :=
  (f n).size + (f 0).size

@[noinline, nospecialize] def byteUsePush
    (f : UInt8 → ByteArray) (n : UInt8) : Nat :=
  let first := f n
  let second := f 255
  first.size + (first.get! 1).toNat + (second.get! 1).toNat

@[noinline, nospecialize] def byteUseMeasure
    (f : ByteArray → Nat) (a : ByteArray) : Nat :=
  f a + f (a.push 65)

@[noinline, nospecialize] def byteUseWord
    (f : ByteArray → USize) (a : ByteArray) : Nat :=
  (f a).toNat + (f (a.push 65)).toNat

@[noinline, nospecialize] def byteUseGet (f : Nat → UInt8) (n : Nat) : Nat :=
  (f 0).toNat + (f (n % 2)).toNat

@[noinline, nospecialize] def byteUseSet
    (f : UInt8 → ByteArray) (n : UInt8) : Nat :=
  ((f n).get! 0).toNat + ((f 255).get! 0).toNat

@[noinline, nospecialize] def byteUsePredicate
    (f : ByteArray → Bool) (a : ByteArray) : Nat :=
  (if f a then 1 else 0) + (if f (a.push 65) then 2 else 0)

@[noinline, nospecialize] def byteUseDecision {p : ByteArray → Prop}
    (f : (a : ByteArray) → Decidable (p a)) (a : ByteArray) : Nat :=
  (match f a with | .isTrue _ => 1 | .isFalse _ => 0) +
  (match f (a.push 65) with | .isTrue _ => 2 | .isFalse _ => 0)

@[noinline, nospecialize] def byteUseHash
    (f : ByteArray → UInt64) (a : ByteArray) : Nat :=
  (f a).toNat

@[noinline, nospecialize] def byteUseCopy (f : Bool → ByteArray) : Nat :=
  let exact := f true
  let growing := f false
  exact.size + (exact.get! 1).toNat + (growing.get! 2).toNat

@[noinline] def byteBoxedMk (n : Nat) : Nat :=
  byteUsePack ByteArray.mk #[UInt8.ofNat n, 65]
@[noinline] def byteBoxedData (n : Nat) : Nat :=
  byteUseData ByteArray.data (byteSeed n)
@[noinline] def byteBoxedEmpty (n : Nat) : Nat :=
  byteUseEmpty ByteArray.emptyWithCapacity n
@[noinline] def byteBoxedPush (n : Nat) : Nat :=
  let original := byteSeed 65
  byteUsePush (ByteArray.push original) (UInt8.ofNat n) + original.size
@[noinline] def byteBoxedSize (n : Nat) : Nat :=
  byteUseMeasure ByteArray.size (byteSeed n)
@[noinline] def byteBoxedUsize (n : Nat) : Nat :=
  byteUseWord ByteArray.usize (byteSeed n)
@[noinline] def byteBoxedGet (n : Nat) : Nat :=
  byteUseGet (ByteArray.get! ((byteSeed n).push 65)) n
@[noinline] def byteBoxedSet (n : Nat) : Nat :=
  let original := byteSeed 65
  byteUseSet (ByteArray.set! original 0) (UInt8.ofNat n) +
    (original.get! 0).toNat
@[noinline] def byteBoxedBeq (n : Nat) : Nat :=
  let original := byteSeed n
  byteUsePredicate (ByteArray.beq original) original
@[noinline] def byteBoxedDecEq (n : Nat) : Nat :=
  let original := byteSeed n
  byteUseDecision (ByteArray.decEq original) original
@[noinline] def byteBoxedHash (n : Nat) : Nat :=
  byteUseHash ByteArray.hash (byteSeed n)
@[noinline] def byteBoxedCopy (n : Nat) : Nat :=
  let original := (byteSeed n).push 65
  byteUseCopy (ByteArray.copySlice original 0 original 1 2) +
    (original.get! 1).toNat
@[noinline] def byteBoxedUtf8 (n : Nat) : Nat :=
  byteUsePredicate ByteArray.validateUTF8 (byteSeed n)
"#;
    std::fs::write(dir.join("NativeByteArray.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "-o", "NativeByteArray.olean", "NativeByteArray.lean"])
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
    assert!(generated.stdout.is_empty());
    assert!(generated.stderr.is_empty());
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeByteArray.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|declaration| {
            let bodies = match declaration {
                IrDecl::Function { body, .. } => body.bodies(),
                IrDecl::Extern { .. } => Vec::new(),
            };
            bodies
                .into_iter()
                .flat_map(|body| body.stmts.iter())
                .filter_map(|statement| match statement {
                    IrStmt::VDecl {
                        expr: IrExpr::Pap { function, .. },
                        ..
                    } => Some(function.clone()),
                    _ => None,
                })
        })
        .collect();
    for target in super::array_operations::BYTE_ARRAY_NAMES {
        assert!(
            partials.contains(&Name::str(name(target), "_boxed")),
            "{target} partial application optimized away; {dir:?}"
        );
    }
    let entries = [
        "byteBoxedMk",
        "byteBoxedData",
        "byteBoxedEmpty",
        "byteBoxedPush",
        "byteBoxedSize",
        "byteBoxedUsize",
        "byteBoxedGet",
        "byteBoxedSet",
        "byteBoxedBeq",
        "byteBoxedDecEq",
        "byteBoxedHash",
        "byteBoxedCopy",
        "byteBoxedUtf8",
    ];
    let cases: Vec<_> = entries
        .into_iter()
        .flat_map(|entry| [0u64, 65, 255].into_iter().map(move |n| (entry, n)))
        .collect();
    let mut oracle_source = source.to_owned();
    for (entry, n) in &cases {
        oracle_source.push_str(&format!("\n#eval {entry} {n}\n"));
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
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
    assert!(oracle.stderr.is_empty());
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(
        expected.len(),
        cases.len(),
        "unexpected oracle output: {output}"
    );
    assert!(
        expected
            .iter()
            .all(|line| !line.is_empty() && line.bytes().all(|byte| byte.is_ascii_digit()))
    );
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter(|declaration| matches!(declaration, IrDecl::Function { .. }))
        .map(|declaration| declaration.name().clone())
        .collect();
    let modules = [module, native_prototypes(&reference)];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, n), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            &modules,
            &name(entry),
            &[EntryArgument::Nat(IrNat::Small(n))],
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {n}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled.reference_functions().iter().all(|function| {
                function.producer() == "reference" && users.contains(&function.name)
            })
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
        assert_nat_replay(&compiled, expected);
        observed.extend(compiled.native_externs().iter().cloned());
    }
    for target in super::array_operations::BYTE_ARRAY_NAMES {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked"
        );
    }
}
