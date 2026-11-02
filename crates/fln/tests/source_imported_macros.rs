//! Public artifact admission and imported macro execution, without a source seed
//! or caller-constructed checked-module/import-identity witnesses.
#![forbid(unsafe_code)]

use fln::imported_ir::VerifiedPartition;
use fln::imported_macros::registrations::{
    MacroRegistrationError, MacroRegistryLimits, MacroTreeLimits,
};
use fln::imported_macros::source::{SourceMacroError, SourceMacroInvocation};
use fln::imported_macros::{MacroContext, MacroState};
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, CheckerAdmissionGround, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    Environment, KVMap, Name, OleanCheckLimits, OleanModuleInput, Outcome,
};
use fln_core::expr::ExprNode;
use fln_olean::ir::IrDecl;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

const STACK: usize = 256 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn parts(root: &Path, module: &str) -> [Vec<u8>; 3] {
    let path = root.join(module).with_extension("olean");
    [
        std::fs::read(&path).unwrap(),
        std::fs::read(path.with_extension("olean.server")).unwrap(),
        std::fs::read(path.with_extension("olean.private")).unwrap(),
    ]
}

#[test]
fn actual_admitted_artifacts_drive_macro_source_declarations_and_proofs() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(library), Some(partition)) = (reference, library, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "actual macro admission requires the pinned executable, library and partition"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN, FLN_REFERENCE_LIB and FLN_REFERENCE_PARTITION");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || actual_artifacts(reference, library, partition))
        .unwrap()
        .join()
        .unwrap();
}

fn actual_artifacts(reference: PathBuf, library: PathBuf, partition: PathBuf) {
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "admitted-source-macro-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean");
    std::fs::write(dir.join("AdmittedSourceMacro.lean"), source).unwrap();
    let compiled = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "AdmittedSourceMacro.olean",
            "AdmittedSourceMacro.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &compiled.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &compiled.stderr).unwrap();
    assert!(compiled.status.success(), "{compiled:?}; {dir:?}");
    assert_eq!(compiled.stdout, b"Nat : Type\nadmittedMacroValue : Nat\n");
    assert!(compiled.stderr.is_empty());

    let prelude_name = name("Init.Prelude");
    let module_name = name("AdmittedSourceMacro");
    let prelude = parts(&library, "Init/Prelude");
    let module = parts(&dir, "AdmittedSourceMacro");
    let inputs = [
        OleanModuleInput {
            name: &prelude_name,
            artifact: &prelude[0],
            server_artifact: Some(&prelude[1]),
            private_artifact: Some(&prelude[2]),
        },
        OleanModuleInput {
            name: &module_name,
            artifact: &module[0],
            server_artifact: Some(&module[1]),
            private_artifact: Some(&module[2]),
        },
    ];
    let options = KVMap::new();
    let original = Engine::from_environment(Environment::new());
    let original_root = original.logical_root(&options);
    let budget = Budget::for_stack_bytes(STACK);
    let imported = original
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&module_name),
            &options,
            SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, budget)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.checked.modules.len(), 2);
    assert!(imported.engine.environment().len() > 2000);
    assert_eq!(imported.engine.imported_modules().len(), 2);
    assert!(original.environment().is_empty());
    assert_eq!(original.logical_root(&options), original_root);
    let checked = imported
        .checked
        .modules
        .iter()
        .find(|checked| checked.name == module_name)
        .unwrap();
    assert!(
        checked
            .declarations
            .iter()
            .any(|record| record.name == name("admittedChooseTerm")),
        "the actual macro owner must have a council admission record"
    );
    let code = [fln::decode_ir_artifact(
        &std::fs::read(dir.join("AdmittedSourceMacro.ir")).unwrap(),
        STACK,
    )
    .unwrap()];
    let users: BTreeSet<_> = code
        .iter()
        .flat_map(|module| &module.decls)
        .filter_map(|decl| match decl {
            IrDecl::Function { name, .. } => Some(name.clone()),
            IrDecl::Extern { .. } => None,
        })
        .collect();
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition).unwrap()).unwrap();
    assert!(matches!(
        imported.prepare_imported_macros(
            &code,
            &partition,
            &users,
            MacroRegistryLimits {
                max_macros: 0,
                ..MacroRegistryLimits::default()
            },
        ),
        Err(MacroRegistrationError::Limit("compiled macros"))
    ));
    assert!(matches!(
        imported.prepare_imported_macros(&[], &partition, &users, MacroRegistryLimits::default()),
        Err(MacroRegistrationError::Compile { declaration, .. })
            if declaration == name("admittedChooseTerm")
    ));
    let registry = imported
        .prepare_imported_macros(&code, &partition, &users, MacroRegistryLimits::default())
        .unwrap();
    let engine = &imported.engine;
    let base_root = engine.logical_root(&options);
    let admission = EngineAdmissionLimits::new(budget);
    assert!(
        engine
            .check_source_command(b"#check (Nat : Bool)", &options, admission)
            .is_err()
    );
    let context = MacroContext {
        quotation_context: name("MacroClient"),
        current_macro_scope: 0,
        current_recursion_depth: 0,
        max_recursion_depth: 1000,
    };
    let invocation = || SourceMacroInvocation {
        registry: &registry,
        context: &context,
        state: MacroState::default(),
        lookup: None,
        limits: MacroTreeLimits::default(),
        cancellation: None,
    };
    let refused = engine.admit_source_declaration_with_imported_macros(
        b"def badMacroValue : Bool := (11 : Bool)",
        &options,
        admission,
        invocation(),
    );
    assert!(matches!(
        refused.outcome,
        Outcome::Complete(Err(SourceMacroError::Frontend(_)))
    ));
    assert_eq!(refused.attempts.len(), 1);
    assert!(refused.state.is_none());
    assert!(!engine.environment().contains(&name("badMacroValue")));
    assert_eq!(engine.logical_root(&options), base_root);
    let checked = engine.check_source_command_with_imported_macros(
        b"#check (Nat : Bool)",
        &options,
        admission,
        invocation(),
    );
    let Outcome::Complete(Ok(result)) = &checked.outcome else {
        panic!("{checked:?}")
    };
    assert!(
        matches!(result.checked_type.node(), ExprNode::Sort { level } if level.to_nat() == Some(1))
    );
    let fln::Declaration::Defn(query) = &result.declaration else {
        panic!("{result:?}")
    };
    assert!(
        matches!(query.value.node(), ExprNode::Const { name: value, .. } if *value == name("Nat"))
    );
    assert_eq!(checked.attempts.len(), 1);
    assert_eq!(checked.attempts[0].module, module_name);
    assert_eq!(checked.attempts[0].declaration, name("admittedChooseTerm"));
    assert!(checked.attempts[0].vm_usage.as_ref().unwrap().steps > 0);
    assert!(
        checked.attempts[0]
            .native_functions
            .iter()
            .any(|row| row == "mirror:Lean.Macro.resolveNamespace")
    );
    assert!(
        checked.attempts[0]
            .reference_functions
            .iter()
            .any(|function| {
                function.name == name("admittedChooseTerm") && function.producer() == "reference"
            })
    );

    let empty_environment = Environment::new();
    let anonymous = Name::anonymous();
    let empty_lookup = fln::imported_macros::lookup::EnvironmentMacroLookup::new(
        &empty_environment,
        &anonymous,
        &anonymous,
        &[],
    );
    let missing_namespace = engine.check_source_command_with_imported_macros(
        b"#check (Nat : Bool)",
        &options,
        admission,
        SourceMacroInvocation {
            lookup: Some(&empty_lookup),
            ..invocation()
        },
    );
    assert!(
        matches!(missing_namespace.outcome, Outcome::Complete(Err(_))),
        "{missing_namespace:?}"
    );
    assert!(missing_namespace.attempts.iter().any(|attempt| {
        attempt
            .native_functions
            .iter()
            .any(|row| row == "mirror:Lean.Macro.resolveNamespace")
    }));
    assert_eq!(engine.logical_root(&options), base_root);

    let report = engine.admit_source_declaration_with_imported_macros(
        b"def nativeAdmittedMacroValue : Nat := (11 : Bool)",
        &options,
        admission,
        invocation(),
    );
    let Outcome::Complete(Ok(admitted)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(report.state.is_some());
    assert_eq!(report.attempts.len(), 1);
    assert_eq!(
        admitted.admission.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    let successor = &admitted.admission.engine;
    let proved = successor.admit_source_declaration(
        b"theorem nativeAdmittedMacroValue_eq : Eq nativeAdmittedMacroValue 11 := Eq.refl nativeAdmittedMacroValue",
        &options, admission,
    ).unwrap().into_complete().unwrap();
    assert_eq!(
        proved.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    assert!(successor.admit_source_declaration(
        b"theorem falseNativeValue : Eq nativeAdmittedMacroValue 18 := Eq.refl nativeAdmittedMacroValue",
        &options, admission,
    ).is_err());
    let evaluated = successor
        .execute_source_commands_with_checks(
            b"#eval nativeAdmittedMacroValue",
            &options,
            EngineExecutionLimits::new(budget),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&evaluated.batch.executions[0].exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(11))
    );
    assert!(
        !engine
            .environment()
            .contains(&name("nativeAdmittedMacroValue"))
    );
    assert_eq!(engine.logical_root(&options), base_root);

    let ambient = Engine::from_environment(engine.environment().clone());
    let refused = ambient.check_source_command_with_imported_macros(
        b"#check (Nat : Bool)",
        &options,
        admission,
        invocation(),
    );
    assert!(matches!(
        refused.outcome,
        Outcome::Complete(Err(SourceMacroError::Binding(_)))
    ));
    assert!(refused.attempts.is_empty());
    assert!(refused.state.is_none());
}
