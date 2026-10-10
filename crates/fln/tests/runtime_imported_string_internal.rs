//! Real Bootstrap opaque string primitives retain the generated native ABI.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, ConstantInfo, Declaration, DefinitionVal, Engine, EngineAdmissionLimits,
    EngineExecutionLimits, Environment, Expr, ExprNode, KVMap, Name, OleanCheckLimits,
    OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput, SourceModuleInput,
};
use fln_core::expr::{BinderInfo, Literal};
use fln_env::constants::{DefinitionSafety, ReducibilityHints};
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn artifacts(root: &Name, lib: &Path) -> BTreeMap<Name, Parts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let path = lib
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
        let optional = |path| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("read companion: {error}"),
        };
        modules.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    modules
}

fn copy_extensions(
    original: &Environment,
    mut base: Environment,
    keep_externs: bool,
) -> Environment {
    for (name, state) in original.extensions() {
        if !keep_externs && name == &fln_elab::externs::journal_name() {
            continue;
        }
        base = base.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            base = base
                .push_extension_entry(name, entry.payload.clone())
                .unwrap();
        }
    }
    base
}

fn without_externs(engine: &Engine) -> Engine {
    let original = engine.environment();
    let mut base = Environment::new();
    for (name, _) in original.constants() {
        base = base.with_entry(original.entry(name).unwrap()).unwrap();
    }
    Engine::from_environment(copy_extensions(original, base, false))
}

fn replace_checked(
    engine: &Engine,
    target: &str,
    change: impl FnOnce(ConstantInfo) -> Declaration,
) -> Engine {
    let target = name(target);
    let original = engine.environment();
    let mut base = Environment::new();
    for (name, _) in original.constants() {
        if name != &target {
            base = base.with_entry(original.entry(name).unwrap()).unwrap();
        }
    }
    Engine::from_environment(copy_extensions(original, base, true))
        .admit_declaration(
            change(original.find(&target).unwrap().clone()),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("counterfeit body is still well typed")
        .into_complete()
        .unwrap()
        .engine
}

fn query(label: &str) -> Declaration {
    let value = Expr::app(
        Expr::const_(name("String.Internal.length"), vec![]),
        Expr::lit(Literal::Str("λé".to_owned())),
    );
    Declaration::Defn(DefinitionVal {
        base: fln::ConstantVal {
            name: name(label),
            level_params: vec![],
            type_: Expr::const_(name("Nat"), vec![]),
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

#[test]
fn admitted_bootstrap_strings_execute_unicode_and_refuse_changed_opaque_contracts() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let module = name("Init.Data.String.Bootstrap");
        let artifacts = artifacts(&module, &lib);
        let inputs: Vec<_> = artifacts.iter().map(|(name, (public, server, private))| OleanModuleInput { name, artifact: public, server_artifact: server.as_deref(), private_artifact: private.as_deref() }).collect();
        let options = KVMap::new();
        let mut admission = SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
        admission.jobs = OleanFrontierJobs { threads: NonZeroUsize::new(1).unwrap(), worker_stack_bytes: STACK };
        let imported = Engine::from_environment(Environment::new()).import_olean_modules_for_source(&inputs, &[module], &options, admission).unwrap().into_complete().unwrap();
        assert!(imported.modules.iter().any(|report| report.module == name("Init.Data.String.Bootstrap") && report.externs > 0));
        let externs = fln_elab::externs::ExternTable::read(imported.engine.environment()).unwrap();
        for (declaration, symbol) in [
            ("String.Internal.append", "lean_string_append"),
            ("String.Internal.length", "lean_string_length"),
            ("String.utf8ByteSize", "lean_string_utf8_byte_size"),
            ("String.Internal.posOf", "lean_string_posof"),
            ("String.Internal.offsetOfPos", "lean_string_offsetofpos"),
            ("String.Internal.extract", "lean_string_utf8_extract"),
            ("String.Internal.next", "lean_string_utf8_next"),
            ("String.Internal.pushn", "lean_string_pushn"),
        ] {
            assert_eq!(externs.get(&name(declaration)), Some([fln_elab::externs::ExternEntry::Standard { backend: name("all"), symbol: symbol.to_owned() }].as_slice()), "the real artifact supplies execution metadata");
        }
        let original_root = imported.engine.logical_root(&options);
        let source = r#"prelude
import Init.Data.String.Bootstrap
#eval String.Internal.append "λ" "é😀"
#eval String.Internal.append "" ""
#eval String.Internal.append "x" ""
#eval String.Internal.append "" "é"
#eval String.Internal.length "é😀a"
#eval String.Internal.length ""
#eval Nat.add 20 22
#eval Nat.div 43 5
#eval String.utf8ByteSize "é😀a"
#eval String.Pos.Raw.byteIdx (String.Internal.posOf "aλ😀z" '😀')
#eval String.Internal.offsetOfPos "aλ😀z" (String.Internal.posOf "aλ😀z" '😀')
#eval String.Internal.extract "aλ😀z" (String.Pos.Raw.mk 1) (String.Pos.Raw.mk 7)
#eval String.Pos.Raw.byteIdx (String.Internal.next "aλ😀z" (String.Pos.Raw.mk 1))
#eval String.Internal.pushn "x" 'λ' 3
#eval let clip := String.Internal.extract "aλ😀z" (String.Pos.Raw.mk 1); clip (String.Pos.Raw.mk 3)
#eval let pad := String.Internal.pushn "x" '🦀'; pad 2
#eval let seek := String.Internal.posOf; String.Pos.Raw.byteIdx (seek "aλ😀z" 'q')
#eval String.Internal.pushn "unchanged" 'λ' 0
"#;
        let entry = name("Main");
        let modules = [SourceModuleInput { name: &entry, source: source.as_bytes() }];
        let limits = SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)));
        let run = || imported.execute_source_modules(&modules, &entry, &options, limits, None).unwrap().into_complete().unwrap();
        let first = run();
        let executions = &first.modules[0].commands.batch.executions;
        assert_eq!(executions.iter().map(|execution| fln::closed_vm_value(&execution.exit).unwrap()).collect::<Vec<_>>(), [Some(ClosedVmValue::String("λé😀".to_owned())), Some(ClosedVmValue::String(String::new())), Some(ClosedVmValue::String("x".to_owned())), Some(ClosedVmValue::String("é".to_owned())), Some(ClosedVmValue::Scalar(3)), Some(ClosedVmValue::Scalar(0)), Some(ClosedVmValue::Scalar(42)), Some(ClosedVmValue::Scalar(8)),
            Some(ClosedVmValue::Scalar(7)), Some(ClosedVmValue::Scalar(3)),
            Some(ClosedVmValue::Scalar(2)), Some(ClosedVmValue::String("λ😀".to_owned())),
            Some(ClosedVmValue::Scalar(3)), Some(ClosedVmValue::String("xλλλ".to_owned())),
            Some(ClosedVmValue::String("λ".to_owned())), Some(ClosedVmValue::String("x🦀🦀".to_owned())),
            Some(ClosedVmValue::Scalar(8)), Some(ClosedVmValue::String("unchanged".to_owned())),
        ]);
        assert_eq!("é😀a".len(), 7, "the native length result counts codepoints, not bytes");
        // Replay the actual bytes emitted after both imported-module and
        // source-declaration admission, without rebuilding any compiler state.
        let mut string_rows = std::collections::BTreeSet::new();
        for execution in executions {
            assert_eq!(execution.checker.ground, fln::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType);
            let decoded = fln_comp::flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
            assert_eq!(fln_comp::flbc::encode_canonical(&decoded, Default::default()).unwrap(), execution.flbc_artifact);
            for instruction in decoded.functions().iter().flat_map(|function| &function.code) {
                if let fln_comp::flbc::Instruction::Intrinsic { row, .. } = instruction
                    && row.starts_with("extern:String.")
                {
                    string_rows.insert(row.clone());
                }
            }
            let replay = fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default()).unwrap().into_complete().unwrap();
            assert_eq!(fln::closed_vm_value(&replay).unwrap(), fln::closed_vm_value(&execution.exit).unwrap());
        }
        for operation in ["utf8ByteSize", "Internal.posOf", "Internal.offsetOfPos", "Internal.extract", "Internal.next", "Internal.pushn"] {
            assert!(string_rows.contains(&format!("extern:String.{operation}")), "the admitted source must select {operation}'s actual native row");
        }
        let mut tight = limits;
        tight.execution.ingress.max_nodes = 1;
        assert!(imported.execute_source_modules(&modules, &entry, &options, tight, None).is_err());
        // Existing intrinsic adapters require saturated calls. Preserve that
        // explicit refusal instead of silently changing a strict call to a closure.
        let partial = b"prelude\nimport Init.Data.String.Bootstrap\n#eval let append := String.Internal.append \"left\"; append \"right\"\n";
        let failure = imported.execute_source_modules(&[SourceModuleInput { name: &entry, source: partial }], &entry, &options, limits, None).expect_err("unsaturated intrinsic calls retain their bounded refusal");
        let fln::source_check::modules::SourceModuleCheckError::Source { error: fln::source_check::SourceCheckError::Command { error, .. }, .. } = failure else { panic!("unexpected refusal {failure:?}") };
        assert!(matches!(*error, fln::EngineExecutionError::Ingress(fln::IngressError::IntrinsicTermArity { expected: 2, actual: 1, .. })));
        let retry = run();
        assert_eq!(executions.iter().map(|execution| &execution.flbc_artifact).collect::<Vec<_>>(), retry.modules[0].commands.batch.executions.iter().map(|execution| &execution.flbc_artifact).collect::<Vec<_>>());
        assert_eq!(imported.engine.logical_root(&options), original_root);

        let changed_body = replace_checked(&imported.engine, "String.Internal.length", |info| {
            let ConstantInfo::Opaque(mut value) = info else { unreachable!() };
            value.value = Expr::lam(Name::anonymous(), Expr::const_(name("String"), vec![]), Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7))), BinderInfo::Default);
            Declaration::Opaque(value)
        });
        let changed_dependency = replace_checked(&imported.engine, "String.instInhabited", |info| {
            let ConstantInfo::Defn(mut value) = info else { unreachable!() };
            let ExprNode::App { f, .. } = value.value.node() else { panic!("actual String inhabitant constructor") };
            value.value = Expr::app(f.clone(), Expr::lit(Literal::Str("different".to_owned())));
            Declaration::Defn(value)
        });
        for engine in [changed_body, changed_dependency] {
            let root = engine.logical_root(&options);
            let failure = engine.execute_definition(query("counterfeitResult"), &options, limits.execution).expect_err("an altered opaque or dictionary must not acquire native authority");
            assert!(matches!(failure, fln::EngineExecutionError::Ingress(_)), "{failure:?}");
            assert_eq!(engine.logical_root(&options), root);
        }
        let ordinary = replace_checked(&imported.engine, "String.Internal.length", |info| {
            let ConstantInfo::Opaque(value) = info else { unreachable!() };
            Declaration::Defn(DefinitionVal {
                base: value.base,
                value: Expr::lam(Name::anonymous(), Expr::const_(name("String"), vec![]), Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(7))), BinderInfo::Default),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: value.all,
            })
        });
        let failure = ordinary.execute_definition(query("attributedDefinition"), &options, limits.execution).expect_err("retaining the explicit extern must not silently execute a changed logical definition");
        assert!(matches!(failure, fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })), "{failure:?}");
        let ordinary = without_externs(&ordinary);
        let root = ordinary.logical_root(&options);
        let result = ordinary.execute_definition(query("ordinaryResult"), &options, limits.execution).unwrap().into_complete().unwrap();
        assert_eq!(fln::closed_vm_value(&result.exit).unwrap(), Some(ClosedVmValue::Scalar(7)), "same-named ordinary definitions execute their own body");
        assert_eq!(ordinary.logical_root(&options), root);
        let no_attribute = without_externs(&imported.engine);
        let root = no_attribute.logical_root(&options);
        let failure = no_attribute.execute_definition(query("noAttributeResult"), &options, limits.execution).expect_err("identical opaque constants without extern metadata grant no native binding");
        assert!(matches!(failure, fln::EngineExecutionError::Ingress(_)), "{failure:?}");
        assert_eq!(no_attribute.logical_root(&options), root);
        use fln_elab::externs::ExternEntry;
        let canonical = ExternEntry::Standard { backend: name("all"), symbol: "lean_string_length".to_owned() };
        for entries in [
            vec![],
            vec![ExternEntry::Standard { backend: name("c"), symbol: "lean_string_length".to_owned() }],
            vec![ExternEntry::Standard { backend: name("all"), symbol: "other_symbol".to_owned() }],
            vec![canonical.clone(), ExternEntry::Opaque],
            vec![ExternEntry::Opaque, canonical],
        ] {
            let changed = Engine::from_environment(fln_elab::externs::register(imported.engine.environment(), &name("String.Internal.length"), entries).unwrap());
            let root = changed.logical_root(&options);
            let failure = changed.execute_definition(query("changedAttributeResult"), &options, limits.execution).expect_err("the exact supported extern entry is required");
            assert!(matches!(failure, fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })), "{failure:?}");
            assert_eq!(changed.logical_root(&options), root);
        }
        let result = imported.engine.execute_definition(query("cleanResult"), &options, limits.execution).unwrap().into_complete().unwrap();
        assert_eq!(fln::closed_vm_value(&result.exit).unwrap(), Some(ClosedVmValue::Scalar(2)));
        assert_eq!(imported.engine.logical_root(&options), original_root);
    }).unwrap().join().unwrap();
}
