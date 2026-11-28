//! Logical declarations must not prevent the executable facet of their module.
use super::*;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{SourceModuleArtifact, SourceModuleIrLimits};
use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrStmt, IrTerminal};
use std::collections::BTreeSet;
use std::path::Path;
use std::process::Command;

const LOGICAL: &str = concat!(
    "module\nprelude\n",
    "public inductive Lib.Proof : Prop where | intro\n",
    "public inductive Lib.Value where | left | right\n",
    "public def Lib.proof : Lib.Proof := Lib.Proof.intro\n",
    "public def Lib.proofFunction (P : Prop) (h : P) : P := h\n",
    "public def Lib.Predicate (_A : Type) : Prop := Lib.Proof\n",
    "public def Lib.proofAlias : Lib.Predicate Lib.Value := Lib.Proof.intro\n",
    "public abbrev Lib.Alias : Type := Lib.Value\n",
    "public def Lib.identityType (A : Type) : Type := A\n",
    "public opaque Lib.opaqueProof : Lib.Proof := Lib.Proof.intro\n",
    "public opaque Lib.opaqueType : Type := Lib.Value\n",
);
const LIVE: &str = concat!(
    "public def Lib.live : Lib.Value := Lib.Value.right\n",
    "public opaque Lib.liveOpaque : Lib.Value := Lib.Value.left\n",
    "public def Lib.typeNamedButRelevant (x : Lib.Value) : Lib.Value := x\n",
);
const IRRELEVANT: &[&str] = &[
    "Lib.proof",
    "Lib.proofFunction",
    "Lib.Predicate",
    "Lib.proofAlias",
    "Lib.Alias",
    "Lib.identityType",
    "Lib.opaqueProof",
    "Lib.opaqueType",
];
const RELEVANT: &[&str] = &["Lib.live", "Lib.liveOpaque", "Lib.typeNamedButRelevant"];

fn execution_limits() -> fln::EngineExecutionLimits {
    fln::EngineExecutionLimits::new(limits().source.admission.kernel)
}

fn produce(tail: &str) -> SourceModuleBuild {
    let initial = Engine::builder().build_empty();
    let built = build(
        &initial,
        &[("Main", &format!("{LOGICAL}{tail}"))],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert!(initial.environment().is_empty());
    built
}

fn decode_ir(bytes: &[u8]) -> IrModule {
    let view = fln_olean::region::OleanView::parse(bytes).unwrap();
    let blocks = view
        .extension_payloads(fln::OleanWalkBudget::default(), 16 << 20)
        .unwrap();
    fln_olean::ir::decode_ir(&blocks, Default::default()).unwrap()
}

fn artifacts(artifact: &SourceModuleArtifact) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let companions = artifact.companions.as_ref().unwrap();
    (
        artifact.bytes.clone(),
        companions.server.clone(),
        companions.private.clone(),
    )
}

fn assert_schedule(module: &IrModule) {
    let names: BTreeSet<_> = module.decls.iter().map(IrDecl::name).collect();
    for omitted in IRRELEVANT {
        assert!(
            !names.contains(&name(omitted)),
            "irrelevant entry {omitted}"
        );
    }
    for executable in RELEVANT {
        assert!(
            names.contains(&name(executable)),
            "missing entry {executable}"
        );
    }
}

#[test]
fn irrelevant_definitions_preserve_logical_artifacts_and_live_executable_entries() {
    let mut built = produce(LIVE);
    let artifact = &mut built.artifacts[0];
    let before = fln::decode_olean_artifact(
        &artifact.bytes,
        fln::OleanDecodeLimits::new(artifact.bytes.len()),
    )
    .unwrap()
    .constants;
    let encoded = artifact
        .compile_ir(SourceModuleIrLimits::new(execution_limits()))
        .unwrap()
        .into_complete()
        .unwrap();
    let module = decode_ir(&encoded.bytes);
    assert_schedule(&module);
    let after = fln::decode_olean_artifact(
        &artifact.bytes,
        fln::OleanDecodeLimits::new(artifact.bytes.len()),
    )
    .unwrap()
    .constants;
    assert_eq!(
        before, after,
        "code generation preserves every logical declaration"
    );
    for retained in IRRELEVANT {
        assert!(
            after
                .iter()
                .any(|constant| constant.name() == &name(retained))
        );
    }
    let companions = artifact.companions.as_ref().unwrap();
    let fresh = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &[OleanModuleInput {
                name: &artifact.name,
                artifact: &artifact.bytes,
                server_artifact: Some(&companions.server),
                private_artifact: Some(&companions.private),
            }],
            std::slice::from_ref(&artifact.name),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                16 << 20,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    fresh
        .engine
        .check_source_files(
            &[concat!(
                "def retainedProof : Lib.Predicate Lib.Value := Lib.proofAlias\n",
                "def retainedProofFunction (P : Prop) (h : P) : P := Lib.proofFunction P h\n",
                "def retainedAlias : Lib.Alias := Lib.live\n",
                "def retainedFamily : Lib.identityType Lib.Value := Lib.Value.left\n",
                "def retainedOpaqueProof : Lib.Proof := Lib.opaqueProof\n",
                "def retainedOpaqueType : Type := Lib.opaqueType\n",
            )
            .as_bytes()],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();

    let partition = fln::imported_ir::VerifiedPartition::from_pinned_tsv(
        &std::fs::read_to_string(
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv"),
        )
        .unwrap(),
    )
    .unwrap();
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let executable = fln::imported_ir::compile(
        &[module],
        &name("Lib.live"),
        &[],
        &partition,
        &users,
        Default::default(),
    )
    .unwrap();
    let exit = executable
        .execute(execution_limits().vm, None)
        .outcome
        .into_complete()
        .unwrap();
    assert_eq!(
        fln::closed_vm_value(&exit).unwrap(),
        Some(fln::ClosedVmValue::Scalar(1))
    );

    // Classification is work, even when a declaration produces no code. A
    // resource stop cannot replace any of the already published companions.
    let published = artifacts(artifact);
    let mut exhausted = SourceModuleIrLimits::new(execution_limits());
    exhausted.compiler.max_work = 0;
    let error = artifact.compile_ir(exhausted).unwrap_err();
    assert_eq!(error.disposition().0, "resource");
    assert_eq!(artifacts(artifact), published);
}

#[test]
fn irrelevant_headers_do_not_hide_unsupported_runtime_definitions() {
    for (source, reason) in [
        (
            "public def Lib.unsupported (_f : Lib.Value -> Lib.Value) (x : Lib.Value) : Lib.Value := x\n",
            "unused higher-order source parameter",
        ),
        // Omitting a type alias's own executable entry does not extend the
        // separately checked representation of ordinary runtime signatures.
        (
            "public def Lib.unsupported (x : Lib.Alias) : Lib.Alias := x\n",
            "source export carrier",
        ),
    ] {
        let mut built = produce(source);
        let artifact = &mut built.artifacts[0];
        let before = artifacts(artifact);
        let error = artifact
            .compile_ir(SourceModuleIrLimits::new(execution_limits()))
            .unwrap_err();
        assert_eq!(error.disposition().0, "unsupported");
        assert!(error.to_string().contains(reason), "{error}");
        assert_eq!(artifacts(artifact), before);
    }
}

fn write_native(directory: &Path, artifact: &SourceModuleArtifact, ir: &[u8]) {
    std::fs::create_dir_all(directory).unwrap();
    std::fs::write(directory.join("Main.olean"), &artifact.bytes).unwrap();
    let companions = artifact.companions.as_ref().unwrap();
    std::fs::write(directory.join("Main.olean.server"), &companions.server).unwrap();
    std::fs::write(directory.join("Main.olean.private"), &companions.private).unwrap();
    std::fs::write(directory.join("Main.ir"), ir).unwrap();
}

#[test]
fn the_pin_consumes_logical_declarations_and_executes_the_remaining_native_entries() {
    let Some(lean) =
        std::env::var_os("FLN_REFERENCE_LEAN").or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
    else {
        assert_ne!(std::env::var("FLN_REQUIRE_REFERENCE").as_deref(), Ok("1"));
        eprintln!("SKIP: irrelevant-header artifact consumer requires the exact pin");
        return;
    };
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success(), "{identity:?}");
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        fln::OLEAN_PIN_COMMIT
    );
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = std::env::temp_dir().join(format!(
        "fln-irrelevant-artifacts-{}-{nonce}",
        std::process::id()
    ));
    let reference = directory.join("reference");
    std::fs::create_dir_all(&reference).unwrap();
    std::fs::write(reference.join("Main.lean"), format!("{LOGICAL}{LIVE}")).unwrap();
    let output = Command::new(&lean)
        .current_dir(&reference)
        .args(["-o", "Main.olean", "Main.lean"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_schedule(&decode_ir(
        &std::fs::read(reference.join("Main.ir")).unwrap(),
    ));

    let mut built = produce(LIVE);
    let artifact = &mut built.artifacts[0];
    let encoded = artifact
        .compile_ir(SourceModuleIrLimits::new(execution_limits()))
        .unwrap()
        .into_complete()
        .unwrap();
    let native = directory.join("native");
    write_native(&native, artifact, &encoded.bytes);
    let consumer = concat!(
        "import Lean\nimport Main\n",
        "example : Lib.Proof := Lib.proof\n",
        "example (P : Prop) (h : P) : P := Lib.proofFunction P h\n",
        "example : Lib.Predicate Lib.Value := Lib.proofAlias\n",
        "def retainedAlias : Lib.Alias := Lib.Value.right\n",
        "def retainedFamily : Lib.identityType Lib.Value := Lib.Value.left\n",
        "example : Lib.Proof := Lib.opaqueProof\n",
        "def retainedOpaqueType : Type := Lib.opaqueType\n",
        // The prelude-free producer has no PUnit, so neither frontend creates
        // casesOn. Observe its scalar enum representation in this unsafe
        // reference-only runtime probe; logical uses are checked above.
        "private unsafe def observe (value : Lib.Value) : Nat := unsafeCast value\n",
        "private unsafe def fetch (A : Type) (env : Lean.Environment) (n : Lean.Name) : IO A :=\n",
        "  match env.evalConst A {} n (checkMeta := false) with\n",
        "  | .error message => throw (IO.userError message)\n",
        "  | .ok value => pure value\n",
        "unsafe def main : IO Unit := do\n",
        "  Lean.enableInitializersExecution\n",
        "  let env ← Lean.importModules #[{ module := `Main, isMeta := true }] {} (loadExts := true)\n",
        "  let value ← fetch Lib.Value env `Lib.live\n",
        "  let opaqueValue ← fetch Lib.Value env `Lib.liveOpaque\n",
        "  let keep ← fetch (Lib.Value -> Lib.Value) env `Lib.typeNamedButRelevant\n",
        "  IO.println (reprStr (observe value, observe opaqueValue, observe (keep value)))\n",
    );
    let run = |directory: &Path, expected: &str| {
        std::fs::write(directory.join("Consumer.lean"), consumer).unwrap();
        let output = Command::new(&lean)
            .current_dir(directory)
            .env("LEAN_PATH", directory)
            .args(["-j", "1", "--run", "Consumer.lean"])
            .output()
            .unwrap();
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    };
    run(&reference, "(1, 0, 1)\n");
    run(&native, "(1, 0, 1)\n");

    // Change executable bytes alone. The consumer must observe the changed
    // live function while the proof/type declarations and logical body stay fixed.
    let mut mutant = decode_ir(&encoded.bytes);
    let IrDecl::Function { body, result, .. } = mutant
        .decls
        .iter_mut()
        .find(|decl| decl.name() == &name("Lib.live"))
        .unwrap()
    else {
        panic!("live function");
    };
    *body = IrBody {
        stmts: vec![IrStmt::VDecl {
            x: 1,
            ty: result.clone(),
            expr: IrExpr::Lit(IrLit::Num(IrNat::Small(0))),
        }],
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
    };
    let header = fln_olean::region::OleanView::parse(&encoded.bytes).unwrap();
    let names: Vec<_> = mutant
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let changed = fln_olean::ir::write::encode_ir(
        fln_olean::ir::write::IrWriteInput {
            module: fln::OleanModuleWriteInput {
                is_module: true,
                imports: &[],
                constants: &[],
                extra_const_names: &names,
            },
            declarations: &mutant.decls,
            initializers: &[],
            additional_extensions: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG
                .strip_prefix('v')
                .unwrap_or(fln::OLEAN_PIN_TAG),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: header.header.base_addr,
        },
        Default::default(),
    )
    .unwrap();
    std::fs::write(native.join("Main.ir"), changed.bytes).unwrap();
    run(&native, "(0, 0, 0)\n");
}
