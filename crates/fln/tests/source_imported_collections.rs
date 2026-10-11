//! Imported structural definitions keep their recursive calls available to simp.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    SourceCheckLimits,
};

// These are the two induction laws from native_collections.lean whose complete
// dependencies live in Prelude. APIs such as List.head? belong to later Init
// modules and must not prevent this genuine imported-definition regression.
const COLLECTION_LAWS: &[u8] = br#"
theorem append_nil.{u} {A : Type u} (xs : List A) : List.append xs List.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [List.append]; rw [ih]

theorem map_identity.{u} {A : Type u} (xs : List A) : List.map (fun x => x) xs = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [List.map]; rw [ih]
"#;

#[test]
fn imported_collection_laws_use_checked_smart_unfolding() {
    const STACK: usize = 128 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let module = Name::from_components(["Init", "Prelude"]);
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                ),
                server_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                )),
                private_artifact: Some(include_bytes!(
                    "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                )),
            }];
            let options = KVMap::new();
            let imported = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &options,
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        16 << 20,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let engine = imported.engine;
            let auxiliary =
                fln_elab::aux_recursors::AuxRecursors::read(engine.environment()).unwrap();
            for label in [
                "List.append.match_1",
                "instDecidableEqList.match_1",
                "List.casesOn",
                "List.brecOn",
            ] {
                eprintln!(
                    "auxiliary {label}: {}",
                    auxiliary.contains(&Name::from_components(label.split('.')))
                );
            }
            let root = engine.logical_root(&options);
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            engine
                .check_source_files(&[COLLECTION_LAWS], &options, limits)
                .unwrap_or_else(|error| panic!("imported collection proof: {error:?}"))
                .into_complete()
                .unwrap();
            assert_eq!(engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}
