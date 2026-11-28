//! The actual Reference produces the same representation and consumes our
//! metadata and visibility projection. No Reference IR supplies native code.
use super::*;
use std::path::{Path, PathBuf};
use std::process::Command;

const PIN_STACK: usize = 128 << 20;
const BYTES: usize = 128 << 20;
const MODULE: &str = "NativeComputedFields";
const SOURCE: &str = r#"module
prelude
public import Init.Prelude
public section
inductive NativeCache where
  | off
  | on (value : Bool)
with
  @[computed_field, inline] value : NativeCache → Bool
    | .off => Bool.false
    | .on value => value
  @[computed_field, inline] score : NativeCache → Nat
    | .off => 0
    | .on _ => 42
"#;

fn reference() -> Option<(PathBuf, PathBuf)> {
    let compiler = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        })
        .filter(|path| path.is_file());
    let Some(compiler) = compiler else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required"
        );
        eprintln!("SKIP: computed-field artifact oracle requires the pinned Reference");
        return None;
    };
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            compiler
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("lib/lean")
        });
    let identity = Command::new(&compiler).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8(identity.stdout).unwrap().trim(),
        OLEAN_PIN_COMMIT
    );
    Some((compiler, library))
}

fn metadata(bytes: &[u8]) -> fln_olean::source_extensions::SourceExtensions {
    let blocks = fln_olean::region::OleanView::parse(bytes)
        .unwrap()
        .extension_payloads(OleanWalkBudget::default(), BYTES)
        .unwrap();
    fln_olean::source_extensions::decode(&blocks, Default::default()).unwrap()
}

fn run_reference(compiler: &Path, library: &Path, directory: &Path, file: &str, args: &[&str]) {
    let output = Command::new(compiler)
        .current_dir(directory)
        .env(
            "LEAN_PATH",
            std::env::join_paths([directory, library]).unwrap(),
        )
        .arg("-j1")
        .args(args)
        .arg(file)
        .output()
        .unwrap();
    assert!(output.status.success(), "{file}\n{output:?}");
    assert!(
        output.stdout.is_empty() && output.stderr.is_empty(),
        "{file}\n{output:?}"
    );
}

#[test]
fn actual_pin_reads_native_computed_field_tags_and_matches_cache_declarations() {
    let Some((compiler, library)) = reference() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(PIN_STACK)
        .spawn(move || {
            let workspace = std::env::temp_dir().join(format!(
                "fln-computed-fields-pin-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos(),
            ));
            let pinned = workspace.join("pin");
            let native = workspace.join("native");
            std::fs::create_dir_all(&pinned).unwrap();
            std::fs::create_dir_all(&native).unwrap();
            std::fs::write(pinned.join(format!("{MODULE}.lean")), SOURCE).unwrap();
            run_reference(
                &compiler,
                &library,
                &pinned,
                &format!("{MODULE}.lean"),
                &["-o", &format!("{MODULE}.olean")],
            );

            // The native producer checks the actual Prelude and every new logical
            // declaration; neither the seed nor an assumed family substitutes for it.
            let prelude = name("Init.Prelude");
            let public = std::fs::read(library.join("Init/Prelude.olean")).unwrap();
            let server = std::fs::read(library.join("Init/Prelude.olean.server")).unwrap();
            let private = std::fs::read(library.join("Init/Prelude.olean.private")).unwrap();
            let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(PIN_STACK));
            let base = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &prelude,
                        artifact: &public,
                        server_artifact: Some(&server),
                        private_artifact: Some(&private),
                    }],
                    std::slice::from_ref(&prelude),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, admission.kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let initial = base.engine.logical_root(&KVMap::new());
            assert_recursive_computed_field_bundle(&base.engine);
            assert_mutual_computed_field_order(&base.engine);
            assert_eq!(base.engine.logical_root(&KVMap::new()), initial);
            let module = name(MODULE);
            let built = base
                .compile_source_modules(
                    &[SourceModuleInput {
                        name: &module,
                        source: SOURCE.as_bytes(),
                    }],
                    &module,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
                    OleanWriteBudget::default(),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(base.engine.logical_root(&KVMap::new()), initial);
            let artifact = &built.artifacts[0];
            let pin_bytes = std::fs::read(pinned.join(format!("{MODULE}.olean"))).unwrap();
            let ours = metadata(&artifact.bytes);
            let theirs = metadata(&pin_bytes);
            assert_eq!(ours.computed_fields, theirs.computed_fields);
            let edges = |rows: &[fln_olean::source_extensions::ImplementedByEntry]| {
                rows.iter()
                    .map(|row| (row.declaration.clone(), row.implementation.clone()))
                    .collect::<BTreeSet<_>>()
            };
            assert_eq!(edges(&ours.implemented_by), edges(&theirs.implemented_by));
            let inline = |rows: &[fln_olean::source_extensions::InlineEntry]| {
                rows.iter()
                    .map(|row| (row.declaration.clone(), row.kind))
                    .collect::<std::collections::BTreeMap<_, _>>()
            };
            assert_eq!(inline(&ours.inline), inline(&theirs.inline));
            assert!(
                ours.aux_recursors
                    .contains(&name("NativeCache._impl.casesOn"))
            );
            let eliminator = name("NativeCache._impl.casesOn");
            assert_eq!(
                ours.reducibility
                    .iter()
                    .find(|row| row.declaration == eliminator)
                    .unwrap(),
                theirs
                    .reducibility
                    .iter()
                    .find(|row| row.declaration == eliminator)
                    .unwrap(),
            );
            let ours =
                decode_olean_artifact(&artifact.bytes, OleanDecodeLimits::new(BYTES)).unwrap();
            let theirs = decode_olean_artifact(&pin_bytes, OleanDecodeLimits::new(BYTES)).unwrap();
            for constant in [
                "NativeCache._impl",
                "NativeCache.off._impl",
                "NativeCache.on._impl",
                "NativeCache._impl.rec",
                "NativeCache._impl.casesOn",
            ] {
                let key = name(constant);
                let native_info = ours
                    .constants
                    .iter()
                    .find(|value| value.name() == &key)
                    .unwrap();
                let pinned_info = theirs
                    .constants
                    .iter()
                    .find(|value| value.name() == &key)
                    .unwrap();
                assert_eq!(native_info, pinned_info, "cache declaration {constant}");
            }
            let companions = artifact.companions.as_ref().unwrap();
            std::fs::write(native.join(format!("{MODULE}.olean")), &artifact.bytes).unwrap();
            std::fs::write(
                native.join(format!("{MODULE}.olean.server")),
                &companions.server,
            )
            .unwrap();
            std::fs::write(
                native.join(format!("{MODULE}.olean.private")),
                &companions.private,
            )
            .unwrap();
            assert!(!native.join(format!("{MODULE}.ir")).exists());
            std::fs::write(
                native.join("Consumer.lean"),
                r#"module
import Lean
public meta import Lean.Elab.ComputedFields
public import NativeComputedFields
open Lean in
run_meta do
  let env ← getEnv
  unless Lean.TagAttribute.hasTag Lean.Elab.ComputedFields.computedFieldAttr env `NativeCache.value do
    throwError "missing computed-field tag"
  unless Lean.TagAttribute.hasTag Lean.Elab.ComputedFields.computedFieldAttr env `NativeCache.score do
    throwError "missing second computed-field tag"
  unless Lean.isAuxRecursor env `NativeCache._impl.casesOn do
    throwError "missing cached eliminator tag"
  for (source, target) in #[
      (`NativeCache.off, `NativeCache.off._override),
      (`NativeCache.on, `NativeCache.on._override),
      (`NativeCache.casesOn, `NativeCache.casesOn._override),
      (`NativeCache.value, `NativeCache.value._override),
      (`NativeCache.score, `NativeCache.score._override)] do
    unless Lean.Compiler.getImplementedBy? env source == some target do
      throwError "missing computed-field implementation: {source}"
  let some logical := env.find? `NativeCache.value | throwError "missing logical field"
  if logical.hasValue then
    throwError "the logical field body was exposed"
  for helper in [`NativeCache._impl.casesOn, `NativeCache.off._override,
      `NativeCache.on._override, `NativeCache.casesOn._override,
      `NativeCache.value._override, `NativeCache.score._override] do
    unless ((env.setExporting true).find? helper).any ConstantInfo.hasValue do
      throwError "generated helper body was hidden: {helper}"
"#,
            )
            .unwrap();
            run_reference(&compiler, &library, &native, "Consumer.lean", &[]);
        })
        .unwrap()
        .join()
        .unwrap();
}
