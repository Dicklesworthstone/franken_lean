//! Actual pin-produced name construction through the native computed-field
//! constructor, including the library helpers used by syntax quotations.

use super::*;
use fln_rt::convert::Conversion;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_name_constructors_match_components_hashes_and_canonical_replay() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native name constructors"
        );
        eprintln!("SKIP: native name constructor oracle requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
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
    let partition_file = std::env::var_os("FLN_REFERENCE_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../contracts/builtin_partition.tsv")
        });
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition_file).unwrap())
            .unwrap();
    let constructor = name("Lean.Name.str._override");
    assert_eq!(
        partition.classify(&constructor),
        Some(GraphClass::ToolchainApi)
    );
    let helpers = [name("Lean.Name.mkStr2"), name("Lean.Name.mkStr4")];
    for helper in &helpers {
        assert_eq!(partition.classify(helper), Some(GraphClass::LibraryCode));
    }
    let mut prelude = crate::decode_ir_artifact(
        &std::fs::read(library.join("Init/Prelude.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    prelude.decls.retain(|declaration| {
        declaration.name() == &constructor || helpers.contains(declaration.name())
    });
    assert_eq!(prelude.decls.len(), 3);
    let actual_constructor = prelude
        .decls
        .iter()
        .find(|declaration| declaration.name() == &constructor)
        .unwrap();
    let IrDecl::Function { params, result, .. } = actual_constructor else {
        panic!("computed-field constructor is not a function")
    };
    assert_eq!(params.len(), 2);
    assert!(params.iter().all(|parameter| !parameter.borrow));
    assert_eq!(params[0].ty, IrType::TObject);
    assert_eq!(params[1].ty, IrType::Object);
    assert_eq!(*result, IrType::TObject);
    let native_row = fln_vm::macro_native::row_for_name(&constructor).unwrap();
    assert_eq!(native_row.borrowed, [false, false]);
    assert_eq!(native_row.parameters, ["tobj", "obj"]);
    assert_eq!(native_row.result_type, "tobj");

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("name-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../fln-olean/fixtures/ir/NativeNameModule.lean");
    std::fs::write(dir.join("NativeNameModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "NativeNameModule.olean",
            "NativeNameModule.lean",
        ])
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
        &std::fs::read(dir.join("NativeNameModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let mut oracle_source = source.to_owned();
    let mut cases = Vec::new();
    for entry in ["nativeNameDirect", "nativeNameTwo", "nativeNameFour"] {
        for argument in [0, 1, 2, u64::MAX] {
            oracle_source.push_str(&format!("\n#eval ({entry} {argument}).hash\n"));
            cases.push((entry, argument));
        }
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
    let hashes: Vec<u64> = output.lines().map(|line| line.parse().unwrap()).collect();
    assert_eq!(hashes.len(), cases.len());
    let modules = [module, prelude];
    for ((entry, argument), hash) in cases.into_iter().zip(hashes) {
        let compiled = compile(
            &modules,
            &name(entry),
            &[nat(argument)],
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {argument}: {error:?}; {dir:?}"));
        let component = match argument {
            0 => "A.B\0🙂",
            1 => "",
            _ => "λ",
        };
        let parent = match entry {
            "nativeNameDirect" => name("Root"),
            "nativeNameTwo" => name("Parent"),
            _ => name("Lean.Parser.Tactic"),
        };
        let expected = Name::str(parent, component);
        assert_eq!(expected.hash(), hash, "{entry} {argument}: actual pin hash");
        let bytes =
            flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                .unwrap();
        let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        assert_eq!(
            flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
            bytes
        );
        for program in [compiled.program.program(), &replay] {
            let Outcome::Complete(VmExit::Returned(value)) =
                fln_vm::interpreter::execute(program, ExecutionLimits::default(), None)
            else {
                panic!("{entry} {argument} did not return; {dir:?}")
            };
            assert_eq!(
                Conversion::new().project_name(&value.value).unwrap(),
                expected
            );
        }
        assert!(
            compiled
                .native_externs()
                .iter()
                .any(|row| row == native_row.id)
        );
        assert!(compiled.reference_functions().iter().all(|function| {
            function.name != constructor
                && (users.contains(&function.name) || helpers.contains(&function.name))
        }));
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
        let cancelled = || true;
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&cancelled))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            Outcome::Complete(VmExit::Returned(_))
        ));
        eprintln!("live Reference and native Name: {entry} {argument}, hash={hash}");
    }
}
