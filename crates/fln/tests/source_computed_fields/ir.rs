//! Inherited computed models do not block independent executable declarations.
//! Actual cached carriers still require their own source ABI lowering.
use super::*;
use fln::imported_ir::{EntryArgument, VerifiedPartition};
use fln::ir::{CompileError, DefinitionCompileError};
use fln::source_check::modules::SourceModuleBuild;
use fln_olean::ir::{IrDecl, IrNat, IrType};
use std::collections::BTreeSet;

const INHERITED_BOUNDARY: &str =
    "computed-field source representation requires cached constructor and replacement ABI lowering";

pub(super) fn logical_artifacts(artifact: &SourceModuleArtifact) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let parts = artifact.companions.as_ref().unwrap();
    (
        artifact.bytes.clone(),
        parts.server.clone(),
        parts.private.clone(),
    )
}

fn assert_compile_boundary(artifact: &mut SourceModuleArtifact, declaration: &str, reason: &str) {
    let before = logical_artifacts(artifact);
    let error = artifact
        .compile_ir(SourceModuleIrLimits::new(limits()))
        .expect_err("unsupported representations cannot publish executable companions");
    let SourceModuleIrError::Compile {
        module,
        declaration: failed,
        error: inner,
    } = &error
    else {
        panic!("unexpected source IR refusal: {error:?}");
    };
    assert_eq!(module, &artifact.name, "{error:?}");
    assert_eq!(failed, &name(declaration), "{error:?}");
    assert!(
        matches!(inner.as_ref(), DefinitionCompileError::Ir(CompileError::Unsupported { what }) if *what == reason),
        "unexpected source IR boundary: {error:?}"
    );
    assert_eq!(logical_artifacts(artifact), before);
}

pub(super) fn assert_inherited_ir_boundary(artifact: &mut SourceModuleArtifact, declaration: &str) {
    assert_compile_boundary(artifact, declaration, INHERITED_BOUNDARY);
}

fn build(imported: &SourceOleanImport, module: &str, source: &str) -> SourceModuleBuild {
    let module = name(module);
    imported
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(check_limits()),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn fresh(fixture: &Fixture, artifact: &SourceModuleArtifact) -> SourceOleanImport {
    let prelude = name("Init.Prelude");
    let parts = artifact.companions.as_ref().unwrap();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &[
                OleanModuleInput {
                    name: &prelude,
                    artifact: &fixture.prelude[0],
                    server_artifact: Some(&fixture.prelude[1]),
                    private_artifact: Some(&fixture.prelude[2]),
                },
                OleanModuleInput {
                    name: &artifact.name,
                    artifact: &artifact.bytes,
                    server_artifact: Some(&parts.server),
                    private_artifact: Some(&parts.private),
                },
            ],
            std::slice::from_ref(&artifact.name),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                IMPORT_STACK,
                Budget::for_stack_bytes(IMPORT_STACK),
            )),
        )
        .expect("physical artifacts retain checked computed provenance")
        .into_complete()
        .unwrap()
}

#[test]
fn independent_source_ir_survives_computed_prelude_import_and_physical_reimport() {
    with_fixture(|fixture| {
        let source = r#"module
prelude
public import Init.Prelude
public def Independent.next (n : Nat) : Nat := Nat.succ n
public def Independent.keepText (value : String) : String := value
public def Independent.invert (value : Bool) : Bool :=
  match value with | false => true | true => false
public abbrev Independent.NameAlias := Lean.Name
public def Independent.proofOnly
    (_h : Eq Lean.Name.anonymous Lean.Name.anonymous) (n : Nat) : Nat := n
"#;
        let root = fixture.imported.engine.logical_root(&KVMap::new());
        // The imported upstream Prelude uses its pinned Name implementation;
        // it does not claim native generator provenance. Produce and reimport
        // a genuine native family to exercise the inherited-layout boundary.
        let provider_source =
            format!("module\nprelude\npublic import Init.Prelude\npublic section\n{SINGLE}");
        let mut provider = build(&fixture.imported, "CacheProvider", &provider_source);
        assert_computed_ir_boundary(&mut provider.artifacts[0], "Cache");
        let native_base = fresh(fixture, &provider.artifacts[0]);
        let families = fln_elab::computed_fields::families(
            native_base.engine.environment(),
            Default::default(),
        )
        .unwrap();
        assert!(families.contains(&name("Cache")));
        let native_source = source
            .replace("public import Init.Prelude", "public import CacheProvider")
            .replace("Lean.Name.anonymous", "Cache.empty")
            .replace("Lean.Name", "Cache");
        let mut native = build(&native_base, "NativeComputedIndependent", &native_source);
        let native_encoded = native.artifacts[0]
            .compile_ir(SourceModuleIrLimits::new(limits()))
            .expect("inherited native caches in erased proofs and types require no runtime layout")
            .into_complete()
            .unwrap();
        let native_module = fln::decode_ir_artifact(&native_encoded.bytes, IMPORT_STACK).unwrap();

        // Separately check the pinned executable ABI using its real Prelude
        // dependency. The native cache-owning provider above deliberately has
        // no IR; no fabricated or upstream IR fills that unsupported facet.
        let mut built = build(&fixture.imported, "ComputedIndependent", source);
        let artifact = &mut built.artifacts[0];
        let original_constants =
            fln::decode_olean_artifact(&artifact.bytes, fln::OleanDecodeLimits::new(IMPORT_STACK))
                .unwrap()
                .constants;
        let encoded = artifact
            .compile_ir(SourceModuleIrLimits::new(limits()))
            .expect("ordinary primitive code does not require inherited cache layouts")
            .into_complete()
            .unwrap();
        assert_eq!(
            original_constants,
            fln::decode_olean_artifact(&artifact.bytes, fln::OleanDecodeLimits::new(IMPORT_STACK),)
                .unwrap()
                .constants,
        );
        let module = fln::decode_ir_artifact(&encoded.bytes, IMPORT_STACK).unwrap();
        for module in [&native_module, &module] {
            for (declaration, parameters, result) in [
                ("Independent.next", vec![IrType::TObject], IrType::TObject),
                ("Independent.keepText", vec![IrType::Object], IrType::Object),
                ("Independent.invert", vec![IrType::UInt8], IrType::UInt8),
                (
                    "Independent.proofOnly",
                    vec![IrType::Erased, IrType::TObject],
                    IrType::TObject,
                ),
            ] {
                let Some(IrDecl::Function {
                    params,
                    result: actual,
                    ..
                }) = module
                    .decls
                    .iter()
                    .find(|row| row.name() == &name(declaration))
                else {
                    panic!("missing native source entry {declaration}");
                };
                assert_eq!(
                    params
                        .iter()
                        .map(|param| param.ty.clone())
                        .collect::<Vec<_>>(),
                    parameters
                );
                assert_eq!(*actual, result);
            }
            assert!(module.decls.iter().all(|row| {
                row.name() != &name("Independent.NameAlias")
                    && row.name().to_display_string().starts_with("Independent.")
            }));
            let partition_path = std::env::var_os("FLN_BUILTIN_PARTITION")
                .map(PathBuf::from)
                .unwrap_or_else(|| {
                    fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
                });
            let partition = VerifiedPartition::from_pinned_tsv(
                &std::fs::read_to_string(partition_path).unwrap(),
            )
            .unwrap();
            let users: BTreeSet<_> = module.decls.iter().map(|row| row.name().clone()).collect();
            for (entry, arguments, expected) in [
                (
                    "Independent.next",
                    vec![EntryArgument::Nat(IrNat::Small(41))],
                    fln::ClosedVmValue::Scalar(42),
                ),
                (
                    "Independent.keepText",
                    vec![EntryArgument::String("computed imports".into())],
                    fln::ClosedVmValue::String("computed imports".into()),
                ),
                (
                    "Independent.invert",
                    vec![EntryArgument::Nat(IrNat::Small(1))],
                    fln::ClosedVmValue::Scalar(0),
                ),
                (
                    "Independent.proofOnly",
                    vec![EntryArgument::Erased, EntryArgument::Nat(IrNat::Small(42))],
                    fln::ClosedVmValue::Scalar(42),
                ),
            ] {
                let executable = fln::imported_ir::compile(
                    std::slice::from_ref(module),
                    &name(entry),
                    &arguments,
                    &partition,
                    &users,
                    Default::default(),
                )
                .unwrap_or_else(|error| panic!("{entry}: {error:?}"));
                let exit = executable
                    .execute(limits().vm, None)
                    .outcome
                    .into_complete()
                    .unwrap();
                assert_eq!(
                    fln::closed_vm_value(&exit).unwrap(),
                    Some(expected),
                    "{entry}"
                );
            }
        }
        let imported = fresh(fixture, artifact);
        checked(
            &imported.engine,
            "def importedAlias : Independent.NameAlias := Lean.Name.anonymous\n",
        );
        execute(
            &imported.engine,
            "#eval Independent.next 41\n#eval Independent.proofOnly (Eq.refl Lean.Name.anonymous) 42\n#eval match Independent.invert true with | false => 42 | true => 0\n",
            &["42", "42", "42"],
        );
        let directory = std::env::temp_dir().join(format!(
            "fln-independent-computed-ir-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let (public, server, private) = logical_artifacts(artifact);
        for (suffix, bytes) in [
            ("olean", public),
            ("olean.server", server),
            ("olean.private", private),
            ("ir", encoded.bytes),
        ] {
            std::fs::write(
                directory.join(format!("ComputedIndependent.{suffix}")),
                bytes,
            )
            .unwrap();
        }
        let consumer = r#"import Lean
import ComputedIndependent
private unsafe def fetch (A : Type) (env : Lean.Environment) (n : Lean.Name) : IO A :=
  match env.evalConst A {} n (checkMeta := false) with
  | .error message => throw (IO.userError message)
  | .ok value => pure value
unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `ComputedIndependent, isMeta := true }] {} (loadExts := true)
  let next ← fetch (Nat → Nat) env `Independent.next
  let keepText ← fetch (String → String) env `Independent.keepText
  let invert ← fetch (Bool → Bool) env `Independent.invert
  let proofOnly ← fetch (Eq Lean.Name.anonymous Lean.Name.anonymous → Nat → Nat) env `Independent.proofOnly
  IO.println (next 41)
  IO.println (keepText "computed imports")
  IO.println (invert true)
  IO.println (proofOnly (Eq.refl Lean.Name.anonymous) 42)
"#;
        std::fs::write(directory.join("Consumer.lean"), consumer).unwrap();
        let pin = Command::new(&fixture.compiler)
            .current_dir(&directory)
            .env(
                "LEAN_PATH",
                std::env::join_paths([&directory, &fixture.library]).unwrap(),
            )
            .args(["-j1", "--run", "Consumer.lean"])
            .output()
            .unwrap();
        assert!(pin.status.success(), "native IR pin consumer: {pin:?}");
        assert!(pin.stderr.is_empty(), "{pin:?}");
        assert_eq!(
            String::from_utf8(pin.stdout).unwrap(),
            "42\ncomputed imports\nfalse\n42\n"
        );
        assert_eq!(fixture.imported.engine.logical_root(&KVMap::new()), root);
    });
}

#[test]
fn inherited_cache_carriers_and_internal_construction_still_refuse_ir_atomically() {
    with_fixture(|fixture| {
        // Unlike the recursive Cache._impl, this physical family fits the
        // ordinary Bool-field carrier classifier. Its cached representation
        // must still be found when an exported parameter is never used.
        let simple = r#"inductive CacheFlag where
  | off
  | on (value : Bool)
with
  @[computed_field] cached : CacheFlag → Bool
    | .off => false
    | .on value => value
"#;
        let source = format!(
            "module\nprelude\npublic import Init.Prelude\npublic section\n{SINGLE}{simple}"
        );
        let mut provider = build(&fixture.imported, "CacheProvider", &source);
        assert_computed_ir_boundary(&mut provider.artifacts[0], "Cache");
        let imported = fresh(fixture, &provider.artifacts[0]);
        let root = imported.engine.logical_root(&KVMap::new());
        let cases = [
            (
                "public def use (value : Cache) : Cache := value\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (_value : Cache) : Nat := 7\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (f : Cache → Nat) (value : Cache) : Nat := f value\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (_f : Nat → Cache) : Nat := 7\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (n : Nat) : Nat := Cache.total (Cache.add n Cache.empty)\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (value : CacheFlag._impl) : CacheFlag._impl := value\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (_value : CacheFlag._impl) : Nat := 7\n",
                "use",
                INHERITED_BOUNDARY,
            ),
            (
                "public def use (_value : Cache._impl) : Nat := 7\n",
                "use",
                "source export carrier",
            ),
            (
                "public structure Holder where\n  value : Cache\npublic def use (value : Holder) : Holder := value\n",
                "Holder.value",
                "source export carrier",
            ),
        ];
        for (index, (body, declaration, reason)) in cases.iter().enumerate() {
            let source = format!("module\nprelude\npublic import CacheProvider\n{body}");
            let mut consumer = build(&imported, &format!("CacheConsumer{index}"), &source);
            assert_compile_boundary(&mut consumer.artifacts[0], declaration, reason);
            assert_eq!(imported.engine.logical_root(&KVMap::new()), root);
        }
    });
}
