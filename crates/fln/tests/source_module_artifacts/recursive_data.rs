//! Recursive source data crosses the native logical and executable module boundary.
use super::*;
use fln::source_check::modules::SourceModuleIrLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln_olean::ir::{IrDecl, IrType};
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn ordinary_auxiliary_lookalikes_keep_executable_entries() {
    let initial = Engine::builder().build_empty();
    let source = concat!(
        "module\nprelude\n",
        "public inductive PUnit where | unit\n",
        "public inductive Plain where | left | right\n",
        // PUnit enables the genuine casesOn, while the equality and numeric
        // prerequisites for the other logical constructions are still absent.
        "public abbrev Plain.noConfusion : Plain := Plain.left\n",
        "public abbrev Plain.noConfusionType : Plain := Plain.right\n",
        "public abbrev Plain.ctorElimType : Plain := Plain.left\n",
        "public abbrev Plain.brecOn.go : Plain := Plain.right\n",
    );
    let mut built = build(&initial, &[("Main", source)], OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let artifact = &mut built.artifacts[0];
    let encoded = artifact
        .compile_ir(SourceModuleIrLimits::new(fln::EngineExecutionLimits::new(
            limits().source.admission.kernel,
        )))
        .unwrap()
        .into_complete()
        .unwrap();
    let view = fln_olean::region::OleanView::parse(&encoded.bytes).unwrap();
    let blocks = view
        .extension_payloads(fln::OleanWalkBudget::default(), 16 << 20)
        .unwrap();
    let ir = fln_olean::ir::decode_ir(&blocks, Default::default()).unwrap();
    for ordinary in [
        "Plain.noConfusion",
        "Plain.noConfusionType",
        "Plain.ctorElimType",
        "Plain.brecOn.go",
    ] {
        assert!(
            ir.decls
                .iter()
                .any(|declaration| declaration.name() == &name(ordinary)),
            "ordinary checked definition must remain executable: {ordinary}",
        );
    }
    assert!(initial.environment().is_empty());
}

#[test]
fn recursive_data_exports_survive_native_artifacts_and_fresh_consumers() {
    // The exact Prelude supplies the same auxiliary-construction prerequisites
    // as an ordinary downstream library. A prelude-free inductive deliberately
    // has no casesOn until PUnit exists, in both the native and pinned frontends.
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .filter(|path| path.is_dir())
    else {
        assert_ne!(std::env::var("FLN_REQUIRE_REFERENCE").as_deref(), Ok("1"));
        eprintln!("SKIP: recursive module consumers require the actual pinned Prelude");
        return;
    };
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || check_recursive_module_consumers(lib))
        .unwrap()
        .join()
        .unwrap();
}

fn check_recursive_module_consumers(lib: PathBuf) {
    let initial = Engine::builder().build_empty();
    let prelude = name("Init.Prelude");
    let path = lib.join("Init/Prelude.olean");
    let exported = std::fs::read(&path).unwrap();
    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
    let prelude_input = OleanModuleInput {
        name: &prelude,
        artifact: &exported,
        server_artifact: Some(&server),
        private_artifact: Some(&private),
    };
    let import_limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        64 * 1024 * 1024,
        Budget::for_stack_bytes(64 * 1024 * 1024),
    ));
    let producer = initial
        .import_olean_modules_for_source(
            &[prelude_input],
            std::slice::from_ref(&prelude),
            &KVMap::new(),
            import_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let source_files = [
        (
            "Base",
            concat!(
                "module\nprelude\npublic import Init.Prelude\n",
                "public inductive Lib.Color where | red | green\n",
                "public def Lib.firstColor : Lib.Color := Lib.Color.red\n",
                "public inductive Lib.Chain where\n | stop\n | next (tail : Lib.Chain)\n",
                "public def Lib.prepend (tail : Lib.Chain) : Lib.Chain := Lib.Chain.next tail\n",
            ),
        ),
        (
            "Main",
            concat!(
                "module\nprelude\npublic import Base\n",
                "public def Lib.keepChain (p : Lib.Chain) : Lib.Chain := p\n",
                "public def Lib.tailChain (p : Lib.Chain) : Lib.Chain := match p with | .stop => .stop | .next tail => tail\n",
                "public def Lib.applyChain (f : Lib.Chain -> Lib.Chain) (p : Lib.Chain) : Lib.Chain := f p\n",
                "public def Lib.two : Lib.Chain := Lib.prepend (Lib.prepend Lib.Chain.stop)\n",
                "public def Lib.observed : Lib.Chain := Lib.tailChain (Lib.tailChain Lib.two)\n",
            ),
        ),
    ];
    let module_names: Vec<_> = source_files
        .iter()
        .map(|(module, _)| name(module))
        .collect();
    let modules: Vec<_> = source_files
        .iter()
        .zip(&module_names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let mut built = producer
        .compile_source_modules(
            &modules,
            &name("Main"),
            &KVMap::new(),
            limits(),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let execution = fln::EngineExecutionLimits::new(limits().source.admission.kernel);
    let mut executable_bytes = Vec::new();
    let mut executable_modules = Vec::new();
    let mut users = BTreeSet::new();
    for artifact in &mut built.artifacts {
        let encoded = artifact
            .compile_ir(SourceModuleIrLimits::new(execution))
            .unwrap()
            .into_complete()
            .unwrap();
        let view = fln_olean::region::OleanView::parse(&encoded.bytes).unwrap();
        let blocks = view
            .extension_payloads(fln::OleanWalkBudget::default(), 16 << 20)
            .unwrap();
        let ir = fln_olean::ir::decode_ir(&blocks, Default::default()).unwrap();
        for declaration in &ir.decls {
            users.insert(declaration.name().clone());
            if matches!(
                declaration.name().to_display_string().as_str(),
                "Lib.prepend" | "Lib.keepChain" | "Lib.tailChain"
            ) {
                let IrDecl::Function { params, result, .. } = declaration else {
                    panic!("recursive data source entry");
                };
                assert_eq!(params.len(), 1);
                assert_eq!(params[0].ty, IrType::TObject);
                assert_eq!(*result, IrType::TObject);
            }
        }
        executable_modules.push(ir);
        executable_bytes.push(encoded.bytes);
    }
    assert!(users.contains(&name("Lib.Color.ctorIdx")));
    assert!(users.contains(&name("Lib.firstColor")));
    assert!(users.contains(&name("Lib.Chain.ctorIdx")));
    for logical in [
        "Lib.Color.noConfusionType",
        "Lib.Color.noConfusion",
        "Lib.Color.ctorElimType",
        "Lib.Chain.recOn",
        "Lib.Chain.casesOn",
        "Lib.Chain.ctorElimType",
        "Lib.Chain.noConfusionType",
        "Lib.Chain.noConfusion",
        "Lib.Chain.below",
        "Lib.Chain.brecOn",
        "Lib.Chain.brecOn.go",
    ] {
        assert!(
            !users.contains(&name(logical)),
            "the pin does not schedule generated logical helper {logical}",
        );
    }
    assert!(initial.environment().is_empty());
    let mut inputs = vec![OleanModuleInput {
        name: &prelude,
        artifact: &exported,
        server_artifact: Some(&server),
        private_artifact: Some(&private),
    }];
    inputs.extend(built.artifacts.iter().map(|artifact| {
        OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.server.as_slice()),
            private_artifact: artifact
                .companions
                .as_ref()
                .map(|parts| parts.private.as_slice()),
        }
    }));
    let fresh = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(&inputs, &[name("Main")], &KVMap::new(), import_limits)
        .unwrap()
        .into_complete()
        .unwrap();
    fresh
        .engine
        .check_source_files(
            &[b"def downstream : Lib.Chain := Lib.applyChain Lib.prepend (Lib.tailChain Lib.two)"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let partition_path = std::env::var_os("FLN_BUILTIN_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    if partition_path.is_file() {
        let partition = fln::imported_ir::VerifiedPartition::from_pinned_tsv(
            &std::fs::read_to_string(partition_path).unwrap(),
        )
        .unwrap();
        let compiled = fln::imported_ir::compile(
            &executable_modules,
            &name("Lib.observed"),
            &[],
            &partition,
            &users,
            Default::default(),
        )
        .unwrap();
        let exit = compiled
            .execute(execution.vm, None)
            .outcome
            .into_complete()
            .unwrap();
        assert_eq!(
            fln::closed_vm_value(&exit).unwrap(),
            Some(fln::ClosedVmValue::Scalar(0))
        );
    } else {
        eprintln!("SKIP: recursive imported-IR execution requires the pinned builtin partition");
    }
    let Some(lean) = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
    else {
        assert_ne!(std::env::var("FLN_REQUIRE_REFERENCE").as_deref(), Ok("1"));
        return;
    };
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "fln-recursive-artifacts-{}-{nonce}",
        std::process::id(),
    ));
    std::fs::create_dir_all(&directory).unwrap();
    for (artifact, ir) in built.artifacts.iter().zip(executable_bytes) {
        let path = directory
            .join(artifact.name.to_display_string())
            .with_extension("olean");
        std::fs::write(&path, &artifact.bytes).unwrap();
        let companions = artifact.companions.as_ref().unwrap();
        std::fs::write(path.with_extension("olean.server"), &companions.server).unwrap();
        std::fs::write(path.with_extension("olean.private"), &companions.private).unwrap();
        std::fs::write(path.with_extension("ir"), ir).unwrap();
    }
    // A fresh pin compiler consumes the native caches, then evalConst loads
    // emitted IR bodies. The callback wraps a retained recursive input, so the
    // returned children and their shared caller-owned aliases must stay valid.
    std::fs::write(directory.join("Consumer.lean"), concat!(
        "import Lean\nimport Main\n",
        "def depth : Lib.Chain -> Nat\n",
        "  | .stop => 0\n",
        "  | .next tail => depth tail + 1\n",
        "private unsafe def fetch (A : Type) (env : Lean.Environment) (n : Lean.Name) : IO A :=\n",
        "  match env.evalConst A {} n (checkMeta := false) with\n",
        "  | .error message => throw (IO.userError message)\n",
        "  | .ok value => pure value\n",
        "unsafe def main : IO Unit := do\n",
        "  Lean.enableInitializersExecution\n",
        "  let env ← Lean.importModules #[{ module := `Main, isMeta := true }] {} (loadExts := true)\n",
        "  let prepend ← fetch (Lib.Chain -> Lib.Chain) env `Lib.prepend\n",
        "  let keep ← fetch (Lib.Chain -> Lib.Chain) env `Lib.keepChain\n",
        "  let tail ← fetch (Lib.Chain -> Lib.Chain) env `Lib.tailChain\n",
        "  let invoke ← fetch ((Lib.Chain -> Lib.Chain) -> Lib.Chain -> Lib.Chain) env `Lib.applyChain\n",
        "  let two ← fetch Lib.Chain env `Lib.two\n",
        "  let color ← fetch Lib.Color env `Lib.firstColor\n",
        "  let p := prepend (prepend .stop)\n",
        "  let q := invoke (fun t => .next t) p\n",
        "  IO.println (reprStr (depth two, depth (keep p), depth (tail p), depth q, depth p))\n",
        "  IO.println (match color with | .red => \"red\" | .green => \"green\")\n",
    )).unwrap();
    let output = Command::new(lean)
        .current_dir(&directory)
        .env("LEAN_PATH", &directory)
        .args(["-j", "1", "--run", "Consumer.lean"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "(2, 2, 1, 3, 2)\nred\n"
    );
}
