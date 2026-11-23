//! Bootstrap unsafe axioms retain their safety through source checking and artifacts.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::{SourceProgramExecution, SourceProgramLimits};
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{SourceModuleCheckError, SourceModuleCheckLimits};
use fln::{
    BinderInfo, Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits,
    EvaluationPresentation, Expr, KVMap, Level, Name, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, Outcome, SourceCheckLimits, SourceModuleInput,
};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

const AXIOMS: &str = "prelude\nunsafe axiom lcErased : Type\nunsafe axiom lcAny : Type\nunsafe axiom lcVoid : Type\nunsafe axiom U : Type\nunsafe axiom u : U\nunsafe axiom evidence (P : Prop) : P\n";

// The real Prelude begins with these module, exposure and documentation scopes.
const PUBLIC_AXIOMS: &str = "module\nprelude\npublic section\nset_option linter.missingDocs true\n@[expose] section\nuniverse v\n/-- Compiler erasure marker. -/\nunsafe axiom lcErased : Type\n/-- Compiler box marker. -/\nunsafe axiom lcAny : Type\n/-- Compiler void marker. -/\nunsafe axiom lcVoid : Type\n/-- Unsafe carrier. -/\nunsafe axiom U : Type\n/-- Unsafe element. -/\nunsafe axiom u : U\nend\n";

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn run(
    receipt: &SourceOleanImport,
    source: &str,
) -> Result<Outcome<SourceProgramExecution>, SourceModuleCheckError> {
    let entry = name("Main");
    receipt.execute_lean_source_modules_with_presentation(
        &[SourceModuleInput {
            name: &entry,
            source: source.as_bytes(),
        }],
        &entry,
        &KVMap::new(),
        SourceProgramLimits::new(EngineExecutionLimits::new(budget())),
        None,
        EvaluationPresentation::Lean,
    )
}

fn complete(source: &str) -> Engine {
    let mut result = run(&SourceOleanImport::empty(&KVMap::new()), source)
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(result.modules.len(), 1);
    result.modules.pop().unwrap().commands.batch.engine
}

fn reference() -> Option<&'static Path> {
    static REFERENCE: OnceLock<Option<PathBuf>> = OnceLock::new();
    REFERENCE
        .get_or_init(|| {
            let binary = std::env::var_os("FLN_REFERENCE_LEAN")
                .map(PathBuf::from)
                .or_else(|| {
                    let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
                    Some(library.parent()?.parent()?.join("bin/lean"))
                })
                .filter(|path| path.is_file());
            assert!(
                binary.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference is required for unsafe axiom controls",
            );
            if let Some(binary) = &binary {
                let output = Command::new(binary).arg("--githash").output().unwrap();
                assert!(output.status.success(), "{output:?}");
                assert_eq!(
                    String::from_utf8(output.stdout).unwrap().trim(),
                    fln::OLEAN_PIN_COMMIT,
                );
            }
            binary
        })
        .as_deref()
}

fn check_reference(label: &str, source: &str, rejection: Option<&str>) {
    let Some(binary) = reference() else {
        return;
    };
    let directory =
        std::env::temp_dir().join(format!("fln-unsafe-axioms-{}-{label}", std::process::id(),));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("Main.lean");
    std::fs::write(&path, source).unwrap();
    let output = Command::new(binary)
        .arg("-j1")
        .arg(&path)
        .env_remove("LEAN_PATH")
        .output()
        .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    assert_eq!(
        output.status.code(),
        Some(if rejection.is_none() { 0 } else { 1 }),
        "{source}\n{output:?}",
    );
    if let Some(expected) = rejection {
        let diagnostic = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(diagnostic.contains(expected), "{diagnostic}");
    }
}

#[test]
fn unsafe_axioms_and_their_unsafe_consumers_match_the_pin() {
    let source = format!(
        "{AXIOMS}unsafe def identity (x : U) : U := x\nunsafe def typeAlias : Type := U\nunsafe def proof (P : Prop) : P := evidence P\n",
    );
    check_reference("accepted", &source, None);
    let engine = complete(&source);
    for constant in ["lcErased", "lcAny", "lcVoid", "U", "u", "evidence"] {
        let constant = name(constant);
        assert!(matches!(
            engine.environment().find(&constant),
            Some(ConstantInfo::Axiom(value)) if value.is_unsafe
        ));
        assert!(
            !engine
                .environment()
                .contains(&Name::str(constant, "_unsafe_rec"))
        );
    }
    // The dependent unsafe axiom is checked in unsafe mode, not merely tagged
    // after a safe header check or turned into a recursive definition.
    let Some(ConstantInfo::Axiom(element)) = engine.environment().find(&name("u")) else {
        panic!("the unsafe element remains an axiom")
    };
    assert_eq!(element.base.type_, Expr::const_(name("U"), vec![]));
}

#[test]
fn safe_axioms_definitions_and_proofs_cannot_consume_unsafe_axioms() {
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let root = receipt.engine.logical_root(&KVMap::new());
    for (label, declaration) in [
        ("safe_axiom", "axiom leak : U"),
        ("safe_type", "def leak : Type := U"),
        ("noncomputable", "noncomputable def leak : U := u"),
        ("safe_proof", "theorem leak (P : Prop) : P := evidence P"),
    ] {
        let source = format!("{AXIOMS}{declaration}\n");
        check_reference(label, &source, Some("unsafe declaration"));
        let error = run(&receipt, &source).expect_err(declaration);
        assert_eq!(error.disposition().2, 1, "{error:?}");
        assert!(
            format!("{error:?}").contains("SafetyViolation"),
            "{error:?}"
        );
        assert!(receipt.engine.environment().is_empty());
        assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unsafe_axiom_headers_close_only_used_section_binders() {
    let source = "prelude\nuniverse v\nsection\nvariable (A : Sort v) (unused : Type)\nunsafe axiom chosen : A\nend\n";
    check_reference("section", source, None);
    let engine = complete(source);
    let Some(ConstantInfo::Axiom(chosen)) = engine.environment().find(&name("chosen")) else {
        panic!("an unsafe axiom")
    };
    assert!(chosen.is_unsafe);
    assert_eq!(chosen.base.level_params, [name("v")]);
    assert_eq!(
        chosen.base.type_,
        Expr::forall_e(
            name("A"),
            Expr::sort(Level::param(name("v"))),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
    );
}

#[test]
fn public_unsafe_axioms_keep_their_safety_after_physical_artifact_import() {
    check_reference("public_module", PUBLIC_AXIOMS, None);
    let checked = complete(PUBLIC_AXIOMS);
    let base = Engine::builder().build_empty();
    let module = name("Unsafe");
    let built = base
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: PUBLIC_AXIOMS.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                budget(),
            ))),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let inputs: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
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
        })
        .collect();
    let imported = base
        .import_olean_modules_for_source(
            &inputs,
            &[module],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(4 * 1024 * 1024, budget())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    for constant in ["lcErased", "lcAny", "lcVoid", "U", "u"] {
        assert_eq!(
            imported.engine.environment().find(&name(constant)),
            checked.environment().find(&name(constant)),
            "{constant}",
        );
        assert!(matches!(
            imported.engine.environment().find(&name(constant)),
            Some(ConstantInfo::Axiom(value)) if value.is_unsafe
        ));
    }
    let limits = SourceCheckLimits::new(EngineAdmissionLimits::new(budget()));
    imported
        .engine
        .check_source_files(&[b"unsafe axiom next : U\n"], &KVMap::new(), limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let error = imported
        .engine
        .check_source_files(&[b"axiom leak : U\n"], &KVMap::new(), limits)
        .expect_err("serialization must not grant unsafe declarations safe authority");
    assert!(
        format!("{error:?}").contains("SafetyViolation"),
        "{error:?}"
    );
    assert!(base.environment().is_empty());
}

#[test]
fn unsafe_header_classification_preserves_proof_erasure_and_data_compilation() {
    let proof = "prelude\nunsafe axiom U : Type\nunsafe axiom evidence (x : U) (P : Prop) : P\nunsafe def proof (x : U) (P : Prop) : P := evidence x P\n";
    check_reference("unsafe_domain_proof", proof, None);
    let engine = complete(proof);
    assert!(matches!(
        engine.environment().find(&name("proof")),
        Some(ConstantInfo::Defn(value)) if value.safety == fln::DefinitionSafety::Unsafe
    ));
    for marker in ["lcAny", "lcErased"] {
        assert!(!engine.environment().contains(&name(marker)));
    }

    // An unsafe data result still needs compilation: a safety-aware Prop query
    // must not turn arbitrary unsafe headers into erased proof definitions.
    let data = "prelude\nunsafe axiom U : Type\nunsafe def identity (x : U) : U := x\n";
    check_reference("unsafe_domain_data", data, Some("Unknown constant `lcAny`"));
    let receipt = SourceOleanImport::empty(&KVMap::new());
    let error = run(&receipt, data).expect_err("unsafe data still needs the compiler marker");
    assert_eq!(error.disposition(), ("compilation", false, 1), "{error:?}");
    assert!(
        error.to_string().contains("Unknown constant `lcAny`"),
        "{error:?}",
    );

    // The proof's type is entirely safe here, so rejection must come from the
    // unsafe proof constant itself, not an unsafe type in the theorem header.
    let leak = "prelude\nunsafe axiom evidence (P : Prop) : P\nunsafe def proof (P : Prop) : P := evidence P\ntheorem leak (P : Prop) : P := proof P\n";
    check_reference(
        "unsafe_proof_leak",
        leak,
        Some("unsafe declaration 'proof'"),
    );
    let error = run(&receipt, leak).expect_err("an erased unsafe proof is never safe evidence");
    let diagnostic = format!("{error:?}");
    assert_eq!(error.disposition().2, 1, "{diagnostic}");
    assert!(
        diagnostic.contains("SafetyViolation") && diagnostic.contains("proof"),
        "{diagnostic}",
    );
    assert!(receipt.engine.environment().is_empty());
}
