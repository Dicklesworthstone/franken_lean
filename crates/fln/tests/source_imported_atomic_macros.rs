//! Real imported identifier macros at the native term-elaboration boundary.
//! The provider is compiled by the exact pin; only its artifacts are visible
//! to the client. Every imported declaration passes the ordinary council.
#![forbid(unsafe_code)]

use fln::imported_ir::VerifiedPartition;
use fln::imported_macros::registrations::{
    MacroCompilationInputs, MacroRegistryLimits, MacroTreeLimits,
};
use fln::imported_macros::{MacroContext, MacroState};
use fln::imported_parsers::ParserRegistryLimits;
use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceMacroModuleCheck, SourceModuleCheck, SourceModuleCheckLimits,
    SourceModuleDeferredMacroInputs,
};
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment,
    EvaluationPresentation, KVMap, Name, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput,
    Outcome, SourceCheckLimits, SourceModuleInput, olean_module_imports,
};
use fln_core::expr::ExprNode;
use fln_olean::ir::IrDecl;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const STACK: usize = 256 * 1024 * 1024;
const HEADER: &str = "prelude\nimport AdmittedAtomicMacro\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

struct Fixture {
    root: PathBuf,
    reference: PathBuf,
    library: PathBuf,
    imported: SourceOleanImport,
    compilation: MacroCompilationInputs,
}

impl Fixture {
    fn prepare(reference: PathBuf, library: PathBuf, partition: PathBuf) -> Self {
        let version = Command::new(&reference).arg("--githash").output().unwrap();
        assert!(version.status.success(), "{version:?}");
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            fln::OLEAN_PIN_COMMIT
        );
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
            .map(PathBuf::from)
            .unwrap_or_else(std::env::temp_dir)
            .join(format!("fln-atomic-macro-{}-{stamp}", std::process::id()));
        for directory in ["provider", "objects", "client"] {
            std::fs::create_dir_all(root.join(directory)).unwrap();
        }
        std::fs::write(
            root.join("provider/AdmittedAtomicMacro.lean"),
            include_str!("../../fln-olean/fixtures/ir/AdmittedAtomicMacro.lean"),
        )
        .unwrap();
        let compiled = Command::new(&reference)
            .current_dir(root.join("provider"))
            .env("LEAN_PATH", &library)
            .args([
                "-j1",
                "-o",
                "../objects/AdmittedAtomicMacro.olean",
                "AdmittedAtomicMacro.lean",
            ])
            .output()
            .unwrap();
        std::fs::write(root.join("compile.stdout"), &compiled.stdout).unwrap();
        std::fs::write(root.join("compile.stderr"), &compiled.stderr).unwrap();
        assert!(compiled.status.success(), "{compiled:?}; {root:?}");
        assert!(compiled.stdout.is_empty(), "{compiled:?}");
        assert!(compiled.stderr.is_empty(), "{compiled:?}");
        assert!(!root.join("objects/AdmittedAtomicMacro.lean").exists());
        assert!(!root.join("client/AdmittedAtomicMacro.lean").exists());

        let module = name("AdmittedAtomicMacro");
        let mut pending = vec![module.clone()];
        let mut seen = BTreeSet::new();
        let mut names = Vec::new();
        let mut parts = Vec::new();
        let mut code = Vec::new();
        let mut users = BTreeSet::new();
        while let Some(current) = pending.pop() {
            if !seen.insert(current.clone()) {
                continue;
            }
            let base = if current == module {
                root.join("objects")
            } else {
                library.clone()
            };
            let path = module_path(&base, &current);
            let exported = std::fs::read(&path).unwrap();
            pending.extend(
                olean_module_imports(&exported, OleanDecodeLimits::new(exported.len())).unwrap(),
            );
            let ir =
                fln::decode_ir_artifact(&std::fs::read(path.with_extension("ir")).unwrap(), STACK)
                    .unwrap();
            if current == module {
                users.extend(ir.decls.iter().filter_map(|decl| match decl {
                    IrDecl::Function { name, .. } => Some(name.clone()),
                    IrDecl::Extern { .. } => None,
                }));
            }
            code.push(ir);
            parts.push([
                exported,
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ]);
            names.push(current);
        }
        let artifact_bytes = parts.iter().flatten().map(Vec::len).sum();
        let inputs: Vec<_> = names
            .iter()
            .zip(&parts)
            .map(|(name, [artifact, server, private])| OleanModuleInput {
                name,
                artifact,
                server_artifact: Some(server),
                private_artifact: Some(private),
            })
            .collect();
        let mut imported = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(
                &inputs,
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    artifact_bytes,
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(imported.checked.modules.len(), names.len());
        assert!(
            imported.checked.modules.iter().any(|checked| {
                checked.name == module
                    && checked
                        .declarations
                        .iter()
                        .any(|record| record.name == name("atomicIdentifier"))
            }),
            "the macro owner must have a real council admission record"
        );
        imported
            .enable_imported_syntax(&[module], ParserRegistryLimits::default())
            .unwrap();
        let partition =
            VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition).unwrap())
                .unwrap();
        Self {
            root,
            reference,
            library,
            imported,
            compilation: MacroCompilationInputs::new(code, partition, users),
        }
    }

    fn input(&self, limits: MacroTreeLimits) -> SourceModuleDeferredMacroInputs {
        SourceModuleDeferredMacroInputs {
            compilation: self.compilation.clone(),
            registry_limits: MacroRegistryLimits::default(),
            context: MacroContext {
                quotation_context: name("Main"),
                current_macro_scope: 0,
                current_recursion_depth: 0,
                max_recursion_depth: 1000,
            },
            state: MacroState::default(),
            limits,
        }
    }

    fn oracle(&self, label: &str, body: &str) -> Output {
        let source = format!("{HEADER}{body}");
        let file = format!("{label}.lean");
        std::fs::write(self.root.join("client").join(&file), &source).unwrap();
        let output = Command::new(&self.reference)
            .current_dir(self.root.join("client"))
            .arg("-j1")
            .arg(&file)
            .env(
                "LEAN_PATH",
                std::env::join_paths([self.root.join("objects"), self.library.clone()]).unwrap(),
            )
            .output()
            .unwrap();
        std::fs::write(self.root.join(format!("{label}.stdout")), &output.stdout).unwrap();
        std::fs::write(self.root.join(format!("{label}.stderr")), &output.stderr).unwrap();
        output
    }

    fn check(&self, body: &str, limits: MacroTreeLimits) -> SourceMacroModuleCheck {
        let source = format!("{HEADER}{body}");
        let main = name("Main");
        self.imported
            .check_source_modules_with_deferred_imported_macros(
                &[SourceModuleInput {
                    name: &main,
                    source: source.as_bytes(),
                }],
                &main,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                ))),
                self.input(limits),
                None,
            )
    }
}

fn module_path(base: &Path, module: &Name) -> PathBuf {
    module
        .to_display_string()
        .split('.')
        .fold(base.to_path_buf(), |path, part| path.join(part))
        .with_extension("olean")
}

fn succeeded(report: &SourceMacroModuleCheck) -> &SourceModuleCheck {
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{report:?}")
    };
    assert!(report.states.is_some());
    checked
}

const DECLARATIONS: &str = r#"
set_option linter.unusedVariables false
def atomicLoop : Nat := Nat.zero
def binderName (atomicLoop : Nat) : Nat := Nat.zero
def inferred : atomicType := atomicNat
theorem inferred_eq : Eq inferred 2 := Eq.refl inferred
def builtinFallback (n : Nat) : Nat := n
def directApplication : Nat := atomicFunction Nat.zero
def explicitApplication : Nat := @atomicFunction Nat.zero
def expandedApplication : Nat := (atomicFunction) Nat.zero
def unknownExpandedApplication : Nat := (atomicUnknownFunction) Nat.zero
theorem directApplication_eq : Eq directApplication 0 := Eq.refl directApplication
theorem explicitApplication_eq : Eq explicitApplication 0 := Eq.refl explicitApplication
theorem expandedApplication_eq : Eq expandedApplication 1 := Eq.refl expandedApplication
theorem unknownExpandedApplication_eq : Eq unknownExpandedApplication 1 := Eq.refl unknownExpandedApplication
def antiquoted (A : Type) (value : A) : A := atomicIdentity! value
theorem antiquoted_eq (n : Nat) : Eq (antiquoted Nat n) n := Eq.refl n
def localMacro (atomicNat : Nat) : Nat := atomicNat
theorem localMacro_eq : Eq (localMacro 9) 2 := Eq.refl (localMacro 9)
def chained : Nat := atomicChain
theorem chained_eq : Eq chained 1 := Eq.refl chained
def hygienicLet (hidden : Nat) : Nat := atomicLet
theorem hygienicLet_eq : Eq (hygienicLet 9) 1 := Eq.refl (hygienicLet 9)
theorem rootResolution (atomicRootValue : Bool) : Eq (11 : Nat) 11 := atomicRootProof
theorem generatedProof : True := atomicProof
def beforeScope : Nat := atomicNat
section
open scoped AtomicScope
def inScope : Nat := atomicNat
end
def afterScope : Nat := atomicNat
theorem beforeScope_eq : Eq beforeScope 2 := Eq.refl beforeScope
theorem inScope_eq : Eq inScope 1 := Eq.refl inScope
theorem afterScope_eq : Eq afterScope 2 := Eq.refl afterScope
"#;

const QUERIES: &str = r#"
#check atomicNat
#check (atomicNat)
#check atomicType
#check (atomicType)
#check (atomicProof : True)
#eval atomicNat
#eval atomicChain
#eval atomicLet
#eval atomicIdentity! atomicNat
"#;

#[test]
fn admitted_atomic_macros_expand_only_terms_and_keep_checked_runtime_boundaries() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(library), Some(partition)) = (reference, library, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "atomic macro admission requires the pinned executable, library and partition"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN, FLN_REFERENCE_LIB and FLN_REFERENCE_PARTITION");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || actual_artifacts(Fixture::prepare(reference, library, partition)))
        .unwrap()
        .join()
        .unwrap();
}

fn actual_artifacts(fixture: Fixture) {
    let options = KVMap::new();
    let base = fixture.imported.engine.logical_root(&options);
    let oracle = fixture.oracle("Declarations", DECLARATIONS);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", fixture.root);
    let report = fixture.check(DECLARATIONS, MacroTreeLimits::default());
    let checked = succeeded(&report);
    assert_eq!(checked.checked.theorems, 14);
    for declaration in [
        "atomicLoop",
        "binderName",
        "rootResolution",
        "generatedProof",
    ] {
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name(declaration))
        );
    }
    assert!(report.completed_vm_usage.steps > 0);
    for declaration in [
        "atomicIdentifier",
        "atomicTryNext",
        "AtomicScope.atomicScopedIdentifier",
    ] {
        assert!(
            report.attempts.iter().any(|attempt| {
                attempt.declaration == name(declaration)
                    && attempt.module == name("AdmittedAtomicMacro")
                    && attempt
                        .vm_usage
                        .as_ref()
                        .is_some_and(|usage| usage.steps > 0)
                    && attempt.reference_functions.iter().any(|function| {
                        function.name == name(declaration) && function.producer() == "reference"
                    })
            }),
            "missing real execution of {declaration}: {report:?}"
        );
    }
    assert!(report.attempts.windows(2).any(|pair| {
        pair[0].declaration == name("atomicTryNext")
            && pair[1].declaration == name("atomicIdentifier")
    }));

    let oracle = fixture.oracle("Queries", QUERIES);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", fixture.root);
    assert!(String::from_utf8_lossy(&oracle.stdout).ends_with("2\n1\n1\n2\n"));
    let source = format!("{HEADER}{QUERIES}");
    let main = name("Main");
    let execution = fixture
        .imported
        .execute_source_modules_with_deferred_imported_macros(
            &[SourceModuleInput {
                name: &main,
                source: source.as_bytes(),
            }],
            &main,
            &options,
            SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))),
            fixture.input(MacroTreeLimits::default()),
            None,
            EvaluationPresentation::Raw,
        );
    let Outcome::Complete(Ok(program)) = &execution.outcome else {
        panic!("{execution:?}")
    };
    assert!(execution.states.is_some());
    let commands = &program.modules.last().unwrap().commands;
    assert_eq!(commands.checks.len(), 5);
    for (query, expected) in commands.checks[..3].iter().zip(["Bool", "Nat", "Bool"]) {
        assert!(
            matches!(query.checked_type.node(), ExprNode::Const { name: n, .. }
            if *n == name(expected)),
            "{query:?}"
        );
    }
    assert!(matches!(
        commands.checks[3].checked_type.node(),
        ExprNode::Sort { .. }
    ));
    assert!(
        matches!(commands.checks[4].checked_type.node(), ExprNode::Const { name: n, .. }
        if *n == name("True"))
    );
    let values: Vec<_> = commands
        .batch
        .source_evaluation_indices
        .iter()
        .map(|index| fln::closed_vm_value(&commands.batch.executions[*index].exit).unwrap())
        .collect();
    assert_eq!(
        values,
        [2, 1, 1, 2].map(|value| Some(ClosedVmValue::Scalar(value)))
    );

    for (label, body) in [
        ("WrongType", "def wrongType : Bool := atomicNat"),
        (
            "FalseProof",
            "theorem falseProof : Eq atomicNat 3 := Eq.refl atomicNat",
        ),
        ("Diagnostic", "def errorValue : Nat := atomicError"),
        (
            "UnknownFunction",
            "def unknown : Nat := atomicUnknownFunction Nat.zero",
        ),
        (
            "FailedSuffix",
            "def successfulPrefix : Nat := atomicNat\ndef suffix : Bool := atomicNat",
        ),
    ] {
        assert!(
            !fixture.oracle(label, body).status.success(),
            "pin accepted {label}"
        );
        let refused = fixture.check(body, MacroTreeLimits::default());
        assert!(
            matches!(refused.outcome, Outcome::Complete(Err(_))),
            "{label}: {refused:?}"
        );
        assert!(refused.states.is_none());
        assert_eq!(fixture.imported.engine.logical_root(&options), base);
        assert!(
            !fixture
                .imported
                .engine
                .environment()
                .contains(&name("successfulPrefix"))
        );
    }

    let looping = "set_option maxRecDepth 32\ndef never : Nat := atomicLoop";
    let oracle = fixture.oracle("Nonterminating", looping);
    assert!(!oracle.status.success(), "{oracle:?}");
    assert!(
        String::from_utf8_lossy(&oracle.stdout).contains("maximum recursion depth"),
        "{oracle:?}"
    );
    let stopped = fixture.check(looping, MacroTreeLimits::default());
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.states.is_none());
    assert!(!stopped.attempts.is_empty());
    assert_eq!(fixture.imported.engine.logical_root(&options), base);

    let recovery = fixture.check(DECLARATIONS, MacroTreeLimits::default());
    assert_eq!(
        succeeded(&recovery).checked.result_logical_root,
        checked.checked.result_logical_root
    );
    assert_eq!(fixture.imported.engine.logical_root(&options), base);
}
