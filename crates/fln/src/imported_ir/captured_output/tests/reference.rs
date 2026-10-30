//! Live pin-compiled IO bodies exercise the actual native stream/result ABI.
use super::*;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_output_matches_reference_and_consumes_native_io_results() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required for live imported output IR"
        );
        eprintln!("SKIP: live imported output IR requires the pinned Reference");
        return;
    };
    let pin = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"))
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|s| s.strip_prefix("commit="))
        })
        .unwrap();
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
    let dir = root.join(format!("output-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeOutputModule.lean"
    ));
    std::fs::write(dir.join("NativeOutputModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeOutputModule.olean", "NativeOutputModule.lean"])
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
        &std::fs::read(dir.join("NativeOutputModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            IrDecl::Function { name, .. } if native_row(name).is_none() => Some(name.clone()),
            _ => None,
        })
        .collect();
    let prepare = |entry: &str, arguments: &[EntryArgument], max_bytes| {
        compile_with_captured_output(
            std::slice::from_ref(&module),
            &name(entry),
            arguments,
            &partition(),
            &users,
            IrExecutionLimits::default(),
            max_bytes,
        )
        .unwrap_or_else(|error| panic!("{entry}: {error:?}; artifacts {dir:?}"))
    };

    std::fs::write(
        dir.join("Oracle.lean"),
        format!("{source}\n#eval localOutputAction \"α\\x00\"\n"),
    )
    .unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let expected = "α\0tail\0🙂\n".as_bytes();
    assert_eq!(oracle.stdout, [expected, b"42\n"].concat());

    let arguments = [
        EntryArgument::String("α\0".to_owned()),
        EntryArgument::Erased,
    ];
    let compiled = prepare("localOutputAction", &arguments, expected.len());
    assert!(
        compiled
            .native_externs()
            .iter()
            .any(|row| row == "extern:IO.getStdout")
    );
    let canonical =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&canonical, flbc::CodecLimits::default()).unwrap();
    for program in [compiled.program.program(), &replay] {
        let (outcome, output) = execute(program, ExecutionLimits::default(), None, expected.len());
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{outcome:?}; {dir:?}")
        };
        assert_eq!(
            (result.value.header().tag, result.value.header().other),
            (0, 1)
        );
        assert_eq!(
            nat_decimal(&result.value.try_ctor_child(0).unwrap()).as_deref(),
            Some("42")
        );
        assert_eq!(output.bytes, expected);
    }
    let report = prepare("localOutputAction", &arguments, expected.len() - 1)
        .execute(ExecutionLimits::default(), None);
    assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
    assert_eq!(report.captured_output.unwrap().bytes, "α\0".as_bytes());

    let report =
        prepare("localOutputDirect", &arguments, 3).execute(ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(
        (result.value.header().tag, result.value.header().other),
        (0, 1)
    );
    assert_eq!(
        nat_decimal(&result.value.try_ctor_child(0).unwrap()).as_deref(),
        Some("0")
    );
    assert_eq!(report.captured_output.unwrap().bytes, "α\0".as_bytes());

    let report = prepare("localOutputRead", &[EntryArgument::Erased], 100)
        .execute(ExecutionLimits::default(), None);
    assert!(matches!(
        report.outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::NativeStdoutContract {
                reason: "captured Reference output does not authorize stream reads"
            },
            ..
        })
    ));
    assert!(report.captured_output.unwrap().bytes.is_empty());
}
