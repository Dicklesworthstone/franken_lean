//! Executable metadata crosses source/artifact boundaries without changing logic.
#![cfg(test)]
#![forbid(unsafe_code)]
use super::*;
use fln_elab::externs::{ExternEntry, ExternTable};
use fln_elab::implemented_by::ImplementedByTable;

const BASE: &str = r##"prelude
def right.{v} (A : Sort v) (x y : A) : A := y
@[implemented_by right] def logical.{u} (A : Sort u) (x y : A) : A := x
@[extern c inline "#1" cpp "foreign_λ"] axiom foreign.{u} : (A : Sort u) -> A -> A
"##;

const MAIN: &str = r#"prelude
import Left
import Right
def left.{u} (A : Sort u) (x y : A) : A := x
@[implemented_by right, implemented_by left] def final.{v} (A : Sort v) (x y : A) : A := y
@[extern "old", extern "last"] axiom last.{u} : (A : Sort u) -> A -> A
@[extern] axiom adhoc.{u} : (A : Sort u) -> A -> A
"#;

#[test]
fn executable_attributes_export_owned_final_maps_across_a_diamond() {
    let built = compiled(&[
        ("Main", MAIN),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", BASE),
    ]);
    let before = built.checked.checked.engine.environment();
    let receipt = imported(&built);
    let after = receipt.engine.environment();
    let implementations = ImplementedByTable::read(after).unwrap();
    assert_eq!(ImplementedByTable::read(before).unwrap(), implementations);
    assert_eq!(implementations.get(&name("logical")), Some(&name("right")));
    assert_eq!(implementations.get(&name("final")), Some(&name("left")));
    let externs = ExternTable::read(after).unwrap();
    assert_eq!(ExternTable::read(before).unwrap(), externs);
    assert_eq!(
        externs.get(&name("last")),
        Some(
            [ExternEntry::Standard {
                backend: name("all"),
                symbol: "last".into(),
            }]
            .as_slice()
        )
    );
    assert_eq!(
        externs.get(&name("adhoc")),
        Some(
            [ExternEntry::Adhoc {
                backend: name("all"),
            }]
            .as_slice()
        )
    );
    assert_eq!(
        externs.get(&name("foreign")),
        Some(
            [
                ExternEntry::Inline {
                    backend: name("c"),
                    pattern: "#1".into()
                },
                ExternEntry::Standard {
                    backend: name("cpp"),
                    symbol: "foreign_λ".into()
                },
            ]
            .as_slice()
        )
    );
    let counts: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| {
            let metadata = metadata(&artifact.bytes);
            (
                artifact.name.clone(),
                metadata.implemented_by.len(),
                metadata.externs.len(),
            )
        })
        .collect();
    assert_eq!(
        counts,
        [
            (name("Base"), 1, 1),
            (name("Left"), 0, 0),
            (name("Right"), 0, 0),
            (name("Main"), 1, 2),
        ]
    );
    aliases::reference_import_stdout(
        &built,
        r##"prelude
import Lean
import Main
example (A : Type) (x y : A) : logical A x y = x := rfl
example (A : Type) (x y : A) : final A x y = y := rfl
run_cmd do
  let env ← Lean.getEnv
  unless Lean.Compiler.getImplementedBy? env `logical == some `right do
    throwError "logical executable replacement changed"
  unless Lean.Compiler.getImplementedBy? env `final == some `left do
    throwError "last implemented_by attribute did not win"
  unless (Lean.externAttr.getParam? env `foreign).map (·.entries) ==
      some [.inline `c "#1", .standard `cpp "foreign_λ"] do
    throwError "extern entry kinds, backends, text, or order changed"
  unless (Lean.externAttr.getParam? env `last).map (·.entries) ==
      some [.standard `all "last"] do
    throwError "last extern attribute did not win"
  unless (Lean.externAttr.getParam? env `adhoc).map (·.entries) ==
      some [.adhoc `all] do
    throwError "empty extern syntax lost its adhoc entry"
"##,
        true,
        Some(""),
    );
}

#[test]
fn invalid_executable_attributes_and_post_compilation_updates_are_refused_atomically() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "prelude\n@[implemented_by missing] def f (A : Type) (x : A) : A := x",
        "prelude\n@[implemented_by f] def f (A : Type) (x : A) : A := x",
        "prelude\ndef target (A : Type) (x : A) : A := x\n@[implemented_by target] def f (A : Type) : Type := A",
        "prelude\ndef target (A : Type) (x : A) : A := x\n@[local implemented_by target] def f (A : Type) (x : A) : A := x",
        "prelude\n@[scoped extern \"symbol\"] axiom f : Type",
        // The pin's earlier generated IR is not reconstructible from a final
        // journal, so these post-compilation updates are explicitly unsupported.
        "prelude\ndef target (A : Type) (x : A) : A := x\ndef f (A : Type) (x : A) : A := x\nattribute [implemented_by target] f",
        "prelude\naxiom f : Type\nattribute [extern \"symbol\"] f",
        "prelude\ndef target (A : Type) (x : A) : A := x\naxiom f : (A : Type) -> A -> A\nattribute [implemented_by target] f\nattribute [implemented_by target] f",
    ] {
        let error = build(&engine, &[("Main", source)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn native_producer_replacements_execute_in_fresh_native_and_pinned_consumers() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned Prelude and runtime oracle are required",
        );
        eprintln!("SKIP: pinned v4.32.0 lib/lean is unavailable");
        return;
    };
    const STACK: usize = 64 * 1024 * 1024;
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let path = lib.join("Init/Prelude.olean");
        let exported = std::fs::read(&path).unwrap();
        let server = std::fs::read(path.with_extension("olean.server")).unwrap();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap();
        let prelude = name("Init.Prelude");
        let prelude_input = OleanModuleInput {
            name: &prelude,
            artifact: &exported,
            server_artifact: Some(&server),
            private_artifact: Some(&private),
        };
        let import_limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
            STACK, Budget::for_stack_bytes(STACK),
        ));
        let producer = Engine::builder().build_empty()
            .import_olean_modules_for_source(
                &[prelude_input],
                std::slice::from_ref(&prelude),
                &KVMap::new(),
                import_limits,
            ).unwrap().into_complete().unwrap().engine;
        let source = r#"prelude
import Init.Prelude
@[implemented_by Nat.succ] def replaced (n : Nat) : Nat := 0
@[implemented_by replaced] def chained (n : Nat) : Nat := 0
axiom late : Nat -> Nat
attribute [implemented_by Nat.succ] late
@[extern "franken_lean_missing_callable"] def blocked (n : Nat) : Nat := 99
@[extern "franken_lean_missing_poly"] def blockedPoly.{u} (A : Type u) (x : A) : A := x
@[extern "franken_lean_missing_pair"] def blockedPair : Nat × Nat := (99, 100)
@[extern "franken_lean_missing_lift"] def blockedLift (n : Nat) : ULift.{0,0} Nat := ULift.up n
@[reducible, extern "franken_lean_missing_dictionary"] def blockedDefault : Inhabited Nat := ⟨99⟩
"#;
        let built = build(&producer, &[("Main", source)], OleanWriteBudget::default())
            .unwrap().into_complete().unwrap();
        let mut inputs = vec![OleanModuleInput {
            name: &prelude,
            artifact: &exported,
            server_artifact: Some(&server),
            private_artifact: Some(&private),
        }];
        inputs.extend(built.artifacts.iter().map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        }));
        let engine = Engine::builder().build_empty()
            .import_olean_modules_for_source(
                &inputs,
                &[name("Main")],
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    STACK, Budget::for_stack_bytes(STACK),
                )),
            ).unwrap().into_complete().unwrap().engine;
        let logical = "example (n : Nat) : replaced n = 0 := rfl\nexample (n : Nat) : chained n = 0 := rfl\n";
        engine.check_source_files(
            &[logical.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        ).unwrap().into_complete().unwrap();
        let queries = concat!(
            "#eval replaced 5\n#eval chained 11\n#eval late 19\n",
            "#eval (fun (f : Nat -> Nat -> Nat) => f 10 13) Nat.add\n",
            "#eval @default Nat ⟨41⟩\n",
        );
        let bounded = fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let run = engine.execute_source_commands_with_checks(
            queries.as_bytes(), &KVMap::new(), bounded,
        ).unwrap().into_complete().unwrap();
        let values: Vec<_> = run.batch.executions.iter()
            .map(|execution| fln::closed_vm_value(&execution.exit).unwrap()).collect();
        assert_eq!(values, [
            Some(fln::ClosedVmValue::Scalar(6)),
            Some(fln::ClosedVmValue::Scalar(12)),
            Some(fln::ClosedVmValue::Scalar(20)),
            Some(fln::ClosedVmValue::Scalar(23)),
            Some(fln::ClosedVmValue::Scalar(41)),
        ]);
        assert_eq!(
            ExternTable::read(engine.environment()).unwrap().get(&name("blocked")),
            Some([ExternEntry::Standard {
                backend: name("all"),
                symbol: "franken_lean_missing_callable".into(),
            }].as_slice()),
        );
        for query in [
            "#eval blocked 4",
            "#eval blockedPoly Nat 7",
            "#eval blockedPair.fst",
            "#eval (blockedLift 4).down",
            "#eval @default Nat blockedDefault",
        ] {
            let error = match engine.execute_source_commands_with_checks(
                query.as_bytes(), &KVMap::new(), bounded,
            ) {
                Err(error) => error,
                Ok(_) => panic!("{query}: an unknown extern executed its logical default"),
            };
            assert!(format!("{error:?}").contains("native extern attribute does not match the supported ABI"), "{query}: {error:?}");
        }
        // Nat.succ already has the pin's compiled code. Owned implementation
        // bodies requiring an IR/LCNF facet are not claimed by this test.
        aliases::reference_import_stdout(
            &built,
            &format!("import Main\n{logical}{queries}"),
            true,
            Some("6\n12\n20\n23\n41\n"),
        );
        aliases::reference_import(&built, "import Main\n#eval blocked 4", false);
    }).unwrap().join().unwrap();
}
