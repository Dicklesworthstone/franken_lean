//! Transparent source aliases retain the already supported exported ABI.
use super::*;
use fln::imported_ir::{EntryArgument, VerifiedPartition};

const ALIASES: &str = concat!(
    "abbrev AliasCount := Nat\n",
    "abbrev AliasCountAgain := AliasCount\n",
    "abbrev AliasText := String\n",
    "abbrev AliasBool := Bool\n",
    "abbrev AliasCallback := AliasCount -> AliasCount\n",
    "abbrev AliasHigherOrder := AliasCallback -> AliasCount -> AliasCount\n",
    "abbrev AliasStatic := (_A : Type) -> AliasCount -> AliasCount\n",
    "abbrev AliasProofFunction := (n : AliasCount) -> n = n -> AliasCount\n",
    "abbrev AliasPacked := IRScalarBox\n",
    "abbrev AliasBoolWrapper := IRBoolBox\n",
    "abbrev AliasStringWrapper := IRStringWrapper\n",
    "abbrev AliasChain := IRRecursive\n",
    "abbrev AliasPoly.{u} (A : Type u) := A\n",
    "opaque AliasOpaque : Type := Nat\n",
    "abbrev AliasOpaqueAgain := AliasOpaque\n",
    "abbrev AliasUnsupported := IRBoxedParam Nat\n",
);

fn alias_base() -> Engine {
    boxed_base()
        .check_source_files(
            &[ALIASES.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn alias_cases() -> Vec<BoxedExportCase> {
    vec![
        BoxedExportCase {
            ty: "AliasCountAgain -> AliasCount",
            body: "fun n => Nat.succ n",
            application: "(compiled 41, compiled large)",
            expected: "(42, 184467440737095516161)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasText -> AliasText",
            body: "fun s => s",
            application: "(compiled heap, heap)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasBool -> AliasCount -> AliasCount -> AliasCount",
            body: "fun b x y => if b then x else y",
            application: "(compiled true 11 22, compiled false 11 22)",
            expected: "(11, 22)",
            parameters: vec![IrType::UInt8, IrType::TObject, IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasCallback",
            body: "fun n => n",
            application: "compiled 42",
            expected: "42",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasHigherOrder",
            body: "fun f n => f n",
            application: "compiled Nat.succ 41",
            expected: "42",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasStatic",
            body: "fun _ n => n",
            application: "compiled String 42",
            expected: "42",
            parameters: vec![IrType::Erased, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("AliasCount -> AliasCount", "compiled 42")),
        },
        BoxedExportCase {
            ty: "AliasProofFunction",
            body: "fun n _ => n",
            application: "compiled 42 rfl",
            expected: "42",
            parameters: vec![IrType::TObject, IrType::Erased],
            result: IrType::TObject,
            reduced: Some(("AliasCount -> AliasCount", "compiled 42")),
        },
        BoxedExportCase {
            ty: "AliasPacked -> AliasBool",
            body: "fun p => p.flag",
            application: "let p := IRScalarBox.mk large true; (compiled p, compiled (.mk 7 false), p.number)",
            expected: "(true, false, 184467440737095516160)",
            parameters: vec![IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasBoolWrapper -> AliasBoolWrapper",
            body: "fun b => b",
            application: "((compiled (.mk false)).value, (compiled (.mk true)).value)",
            expected: "(false, true)",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasStringWrapper -> AliasStringWrapper",
            body: "fun p => p",
            application: "let p := IRStringWrapper.mk heap; let q := compiled p; (q.value, p.value, heap)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasChain -> AliasChain",
            body: "fun p => match p with | .empty => .empty | .next _ tail => tail",
            application: "let p := IRRecursive.next large (.next 2 .empty); ((match compiled p with | .empty => 0 | .next n _ => n), (match p with | .empty => 0 | .next n _ => n))",
            expected: "(2, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "AliasCount -> (AliasPacked -> AliasPacked) -> AliasPacked -> AliasBool",
            body: "fun _ f p => match f p with | .mk _ b => b",
            application: "compiled 9 (fun _ => .mk large true) (.mk 0 false)",
            expected: "true",
            parameters: vec![IrType::TObject, IrType::Object, IrType::Object],
            result: IrType::UInt8,
            reduced: Some((
                "(AliasPacked -> AliasPacked) -> AliasPacked -> AliasBool",
                "compiled (fun _ => .mk large true) (.mk 0 false)",
            )),
        },
        BoxedExportCase {
            ty: "AliasPoly Nat -> AliasPoly Nat",
            body: "fun n => n",
            application: "compiled 42",
            expected: "42",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
    ]
}

fn partition() -> VerifiedPartition {
    let path = std::env::var_os("FLN_BUILTIN_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn native_value(
    module: &fln_olean::ir::IrModule,
    entry: &str,
    args: &[EntryArgument],
) -> fln::ClosedVmValue {
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let compiled = fln::imported_ir::compile(
        std::slice::from_ref(module),
        &name(entry),
        args,
        &partition(),
        &users,
        Default::default(),
    )
    .unwrap();
    let exit = compiled
        .execute(limits().vm, None)
        .outcome
        .into_complete()
        .unwrap();
    fln::closed_vm_value(&exit).unwrap().unwrap()
}

#[test]
fn transparent_alias_exports_keep_checked_declarations_erasures_and_runtime_values() {
    let base = alias_base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for case in alias_cases() {
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, checked) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_definition_admission(&base, &checked, &compiled, &options);
        let IrDecl::Function { params, result, .. } = compiled
            .module
            .decls
            .iter()
            .find(|d| d.name() == &name("compiled"))
            .unwrap()
        else {
            panic!("source entry");
        };
        assert_eq!(
            params.iter().map(|p| p.ty.clone()).collect::<Vec<_>>(),
            case.parameters,
            "{source}"
        );
        assert_eq!(*result, case.result, "{source}");
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|d| d.name() == &name("compiled._redArg")),
            case.reduced.is_some(),
            "{source}"
        );
        let nat = |n| EntryArgument::Nat(IrNat::Small(n));
        let example = match case.ty {
            "AliasCountAgain -> AliasCount" => {
                Some((vec![nat(41)], fln::ClosedVmValue::Scalar(42)))
            }
            "AliasText -> AliasText" | "AliasStringWrapper -> AliasStringWrapper" => Some((
                vec![EntryArgument::String("allocated alias payload".into())],
                fln::ClosedVmValue::String("allocated alias payload".into()),
            )),
            "AliasBool -> AliasCount -> AliasCount -> AliasCount" => Some((
                vec![nat(0), nat(11), nat(22)],
                fln::ClosedVmValue::Scalar(22),
            )),
            "AliasCallback" | "AliasPoly Nat -> AliasPoly Nat" => {
                Some((vec![nat(42)], fln::ClosedVmValue::Scalar(42)))
            }
            "AliasStatic" => Some((
                vec![EntryArgument::Erased, nat(42)],
                fln::ClosedVmValue::Scalar(42),
            )),
            "AliasProofFunction" => Some((
                vec![nat(42), EntryArgument::Erased],
                fln::ClosedVmValue::Scalar(42),
            )),
            "AliasBoolWrapper -> AliasBoolWrapper" => {
                Some((vec![nat(1)], fln::ClosedVmValue::Scalar(1)))
            }
            _ => None,
        };
        if let Some((args, expected)) = example {
            assert_eq!(
                native_value(&compiled.module, "compiled", &args),
                expected,
                "{source}"
            );
        }
        if matches!(case.ty, "AliasStatic" | "AliasProofFunction") {
            assert_eq!(
                native_value(&compiled.module, "compiled._redArg", &[nat(42)]),
                fln::ClosedVmValue::Scalar(42)
            );
        }
    }
    assert_eq!(base.logical_root(&options), original);
}

#[test]
fn alias_normalization_preserves_opaque_carriers_refusals_and_work_limits() {
    let base = alias_base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (source, reason) in [
        (
            "def compiled (x : AliasOpaque) : AliasOpaque := x",
            "source export carrier",
        ),
        (
            "def compiled (x : AliasOpaqueAgain) : AliasOpaqueAgain := x",
            "source export carrier",
        ),
        (
            "def compiled (x : AliasUnsupported) : AliasUnsupported := x",
            "source export carrier",
        ),
        (
            "def compiled (_f : AliasCallback) (n : AliasCount) : AliasCount := n",
            "unused higher-order source parameter",
        ),
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(ir::compile_source_definition(&base, declaration, &options, limits(), CompileLimits::default()), Err(ir::DefinitionCompileError::Ir(ir::CompileError::Unsupported { what })) if what == reason),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    let (declaration, _) = checked_definition(
        &base,
        "def compiled (n : AliasCountAgain) : AliasCount := n",
    );
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    assert!(matches!(
        ir::compile_source_definition(
            &base,
            declaration,
            &options,
            bounded,
            CompileLimits::default()
        ),
        Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
    ));
    assert_eq!(base.logical_root(&options), original);
}

#[test]
fn the_pin_executes_alias_exports_with_heap_callbacks_and_reduced_entries() {
    let Some(lean) = reference() else {
        assert_ne!(std::env::var("FLN_REQUIRE_REFERENCE").as_deref(), Ok("1"));
        eprintln!("SKIP: alias export consumption requires the exact pin");
        return;
    };
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let base = alias_base();
    for (index, case) in alias_cases().into_iter().enumerate() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "fln-alias-ir-{}-{nonce}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("heap-input.txt"), "boxed heap payload").unwrap();
        std::fs::write(dir.join("heap-nat.txt"), "184467440737095516160").unwrap();
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, _) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &KVMap::new(),
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        std::fs::write(dir.join("NativeIrCase.lean"), format!("module\npublic section\n{INTERNAL_DATA_HELPERS}\n{ENUM_DATA_HELPERS}\n{BOXED_DATA_HELPERS}\n{ALIASES}\nopaque compiled : {} := {}\n", case.ty, case.body)).unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        assert_probe(generated, &dir, "compile", "");
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        let expected = format!("{}\n{}", case.expected, case.expected);
        for (label, bytes) in [
            ("reference", original.clone()),
            ("native", encode(&compiled.module, &original)),
        ] {
            std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
            assert_probe(
                consume_alias_ir(&lean, &dir, label, &case),
                &dir,
                label,
                &expected,
            );
        }
        if let Some((ty, application)) = case.reduced {
            assert_probe(
                consume_boxed_ir(&lean, &dir, "reduced", ty, application, "compiled._redArg"),
                &dir,
                "reduced",
                &expected,
            );
        }
        if index == 0 {
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, params, .. } = mutant
                .decls
                .iter_mut()
                .find(|d| d.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("source function");
            };
            let x = params.len() as u64 + 1;
            *body = IrBody {
                stmts: vec![
                    IrStmt::Dec {
                        x: params[0].x,
                        n: 1,
                        checked: true,
                        persistent: false,
                    },
                    IrStmt::VDecl {
                        x,
                        ty: IrType::TObject,
                        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(99))),
                    },
                ],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(x))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_boxed_ir(
                    &lean,
                    &dir,
                    "changed-ir",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-ir",
                "(99, 99)\n(99, 99)",
            );
        }
    }
}

fn consume_alias_ir(
    lean: &Path,
    dir: &Path,
    label: &str,
    case: &BoxedExportCase,
) -> std::process::Output {
    if case.ty != "AliasStatic" {
        return consume_boxed_ir(lean, dir, label, case.ty, case.application, "compiled");
    }
    // AliasStatic lives in Type 1. Reuse the existing Reference-only lookup
    // bridge, lifting only evalConst's erased universe. Retain the exact alias
    // and its full type-argument telescope; both pin-original and native IR
    // pass through this same consumer. No target value is cast to a new ABI.
    let source = format!(
        "import Lean\nimport NativeIrCase\n{POLYMORPHIC_EVAL_CONST}unsafe def main : IO Unit := do\n  Lean.enableInitializersExecution\n  let env ← Lean.importModules #[{{ module := `NativeIrCase, isMeta := true }}] {{}} (loadExts := true)\n  match evalConstAt ({}) env {{}} `compiled false with\n  | .error message => throw (IO.userError message)\n  | .ok compiled => do\n    IO.println (reprStr ({}))\n    IO.println (reprStr ({}))\n",
        case.ty, case.application, case.application,
    );
    let filename = format!("AliasRuntime-{label}.lean");
    std::fs::write(dir.join(&filename), source).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["-j", "1", "--run", &filename])
        .output()
        .unwrap()
}

#[test]
fn alias_modules_export_native_logical_and_executable_artifacts_for_fresh_consumers() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .filter(|path| path.is_dir())
    else {
        assert_ne!(std::env::var("FLN_REQUIRE_REFERENCE").as_deref(), Ok("1"));
        eprintln!("SKIP: native alias module requires the exact Prelude");
        return;
    };
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || check_alias_module(lib))
        .unwrap()
        .join()
        .unwrap();
}

fn check_alias_module(lib: PathBuf) {
    use fln::source_check::modules::imported::SourceOleanImportLimits;
    use fln::source_check::modules::{SourceModuleCheckLimits, SourceModuleIrLimits};
    use fln::{OleanCheckLimits, OleanModuleInput};

    let prelude_name = name("Init.Prelude");
    let prelude = lib.join("Init/Prelude.olean");
    let public = std::fs::read(&prelude).unwrap();
    let server = std::fs::read(prelude.with_extension("olean.server")).unwrap();
    let private = std::fs::read(prelude.with_extension("olean.private")).unwrap();
    let import_limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        64 << 20,
        Budget::for_stack_bytes(64 << 20),
    ));
    // Module compilation consumes the retained import receipt, not an engine
    // extracted from it: that receipt owns the public/private import context.
    let producer = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &prelude_name,
                artifact: &public,
                server_artifact: Some(&server),
                private_artifact: Some(&private),
            }],
            std::slice::from_ref(&prelude_name),
            &KVMap::new(),
            import_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let source = concat!(
        "module\nprelude\npublic import Init.Prelude\n",
        "public abbrev NativeAliases.Count := Nat\n",
        "public abbrev NativeAliases.Callback := NativeAliases.Count -> NativeAliases.Count\n",
        "public def NativeAliases.bump (n : NativeAliases.Count) : NativeAliases.Count := Nat.succ n\n",
        "public def NativeAliases.apply (f : NativeAliases.Callback) (n : NativeAliases.Count) : NativeAliases.Count := f n\n",
        "public def NativeAliases.value : NativeAliases.Count := 41\n",
        "public partial def NativeAliases.countdown (n : NativeAliases.Count) (value : NativeAliases.Count) : NativeAliases.Count :=\n",
        "  match Nat.beq n 0 with\n",
        "  | Bool.true => value\n",
        "  | Bool.false => NativeAliases.countdown (Nat.sub n 1) value\n",
    );
    let module_name = name("AliasExport");
    let source_limits = fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel));
    let original = producer.engine.logical_root(&KVMap::new());
    let mut built = producer
        .compile_source_modules(
            &[fln::SourceModuleInput {
                name: &module_name,
                source: source.as_bytes(),
            }],
            &module_name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(source_limits),
            fln::OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let artifact = &mut built.artifacts[0];
    let encoded = artifact
        .compile_ir(SourceModuleIrLimits::new(limits()))
        .unwrap()
        .into_complete()
        .unwrap();
    let view = OleanView::parse(&encoded.bytes).unwrap();
    let module = fln_olean::ir::decode_ir(
        &view
            .extension_payloads(WalkBudget::default(), 16 << 20)
            .unwrap(),
        Default::default(),
    )
    .unwrap();
    for alias in ["NativeAliases.Count", "NativeAliases.Callback"] {
        assert!(!module.decls.iter().any(|decl| decl.name() == &name(alias)));
    }
    assert_eq!(
        native_value(
            &module,
            "NativeAliases.bump",
            &[EntryArgument::Nat(IrNat::Small(41))]
        ),
        fln::ClosedVmValue::Scalar(42)
    );
    assert_eq!(
        native_value(&module, "NativeAliases.value", &[]),
        fln::ClosedVmValue::Scalar(41)
    );
    assert_eq!(
        native_value(
            &module,
            "NativeAliases.countdown",
            &[
                EntryArgument::Nat(IrNat::Small(7)),
                EntryArgument::Nat(IrNat::Small(42))
            ]
        ),
        fln::ClosedVmValue::Scalar(42)
    );
    assert_eq!(producer.engine.logical_root(&KVMap::new()), original);
    let companions = artifact.companions.as_ref().unwrap();
    let fresh = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &[
                OleanModuleInput {
                    name: &prelude_name,
                    artifact: &public,
                    server_artifact: Some(&server),
                    private_artifact: Some(&private),
                },
                OleanModuleInput {
                    name: &module_name,
                    artifact: &artifact.bytes,
                    server_artifact: Some(&companions.server),
                    private_artifact: Some(&companions.private),
                },
            ],
            std::slice::from_ref(&module_name),
            &KVMap::new(),
            import_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    fresh.engine.check_source_files(
        &[b"def importedAlias (n : NativeAliases.Count) : NativeAliases.Count := NativeAliases.bump n"],
        &KVMap::new(), source_limits,
    ).unwrap().into_complete().unwrap();

    let Some(lean) = reference() else {
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
    let dir = std::env::temp_dir().join(format!("fln-alias-module-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("AliasExport.olean"), &artifact.bytes).unwrap();
    std::fs::write(dir.join("AliasExport.olean.server"), &companions.server).unwrap();
    std::fs::write(dir.join("AliasExport.olean.private"), &companions.private).unwrap();
    std::fs::write(dir.join("AliasExport.ir"), &encoded.bytes).unwrap();
    std::fs::write(dir.join("Consumer.lean"), concat!(
        "import Lean\nimport AliasExport\n",
        "example : NativeAliases.Count = Nat := rfl\n",
        "private unsafe def fetch (A : Type) (env : Lean.Environment) (n : Lean.Name) : IO A :=\n",
        "  match env.evalConst A {} n (checkMeta := false) with\n",
        "  | .error message => throw (IO.userError message)\n",
        "  | .ok value => pure value\n",
        "unsafe def main : IO Unit := do\n",
        "  Lean.enableInitializersExecution\n",
        "  let env ← Lean.importModules #[{ module := `AliasExport, isMeta := true }] {} (loadExts := true)\n",
        "  let bump ← fetch NativeAliases.Callback env `NativeAliases.bump\n",
        "  let apply ← fetch (NativeAliases.Callback -> NativeAliases.Count -> NativeAliases.Count) env `NativeAliases.apply\n",
        "  let value ← fetch NativeAliases.Count env `NativeAliases.value\n",
        "  let countdown ← fetch (NativeAliases.Count -> NativeAliases.Count -> NativeAliases.Count) env `NativeAliases.countdown\n",
        "  IO.println (reprStr (bump value, apply Nat.succ value, value, countdown 7 42))\n",
    )).unwrap();
    let output = Command::new(lean)
        .current_dir(&dir)
        .env("LEAN_PATH", &dir)
        .args(["-j", "1", "--run", "Consumer.lean"])
        .output()
        .unwrap();
    assert_probe(output, &dir, "native-module-consumer", "(42, 42, 41, 42)");
}
