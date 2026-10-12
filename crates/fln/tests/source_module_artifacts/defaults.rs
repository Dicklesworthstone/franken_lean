//! Defaults survive physical library imports without duplicating inherited rows.
use super::*;

const BASE: &str = "prelude\ninductive First where | mk\ninductive Second where | mk\nclass Choice (A : Type) where\n  value : A\n@[default_instance 2000] def firstChoice : Choice First := Choice.mk First.mk\ndef secondChoice : Choice Second := Choice.mk Second.mk";

fn assert_choice(engine: &Engine, selected: &str) {
    let root = engine.logical_root(&KVMap::new());
    // A bare polymorphic constant retains its implicit telescope. Supplying
    // an unknown let type creates the pending application that defaults may
    // resolve before the later proof fixes its carrier.
    let source = format!(
        "def bare := Choice.value\ndef inferred := let value : _ := Choice.value; value\ndef selected (P : {selected} -> Prop) (h : P {selected}.mk) : P inferred := h"
    );
    let checked = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    let env = checked.engine.environment();
    assert!(matches!(
        env.find(&name("bare")).unwrap().constant_val().type_.node(),
        fln::ExprNode::ForallE {
            binder_info: fln::BinderInfo::Implicit,
            ..
        }
    ));
    assert_eq!(
        env.find(&name("inferred")).unwrap().constant_val().type_,
        fln::Expr::const_(name(selected), vec![])
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn default_priority_history_survives_a_real_compiled_library_import() {
    let source = format!(
        "{BASE}\nattribute [default_instance 100] firstChoice\nattribute [default_instance 1000] secondChoice"
    );
    let built = compiled(&[("Main", &source)]);
    let defaults = metadata(&built.artifacts[0].bytes).defaults;
    assert_eq!(
        defaults
            .iter()
            .map(|row| (row.declaration.clone(), row.priority))
            .collect::<Vec<_>>(),
        [
            (name("firstChoice"), 2000),
            (name("firstChoice"), 100),
            (name("secondChoice"), 1000)
        ]
    );
    assert!(metadata(&built.artifacts[0].bytes).instances.is_empty());
    // Lowering a later registration does not erase the earlier higher-priority
    // row. A map keyed only by declaration would choose Second incorrectly.
    assert_choice(&built.checked.checked.engine, "First");
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].defaults, 3);
    assert_choice(&receipt.engine, "First");
}

#[test]
fn a_diamond_exports_owned_default_rows_even_for_imported_candidates() {
    let built = compiled(&[
        ("Main", "prelude\nimport Left\nimport Right"),
        (
            "Left",
            "prelude\nimport Base\nattribute [default_instance 100] firstChoice\nattribute [default_instance 2000] secondChoice\nattribute [default_instance 2000] secondChoice",
        ),
        ("Right", "prelude\nimport Base"),
        ("Base", BASE),
    ]);
    assert_eq!(
        built
            .artifacts
            .iter()
            .map(|artifact| (
                artifact.name.clone(),
                metadata(&artifact.bytes).defaults.len()
            ))
            .collect::<Vec<_>>(),
        [
            (name("Base"), 1),
            (name("Left"), 3),
            (name("Right"), 0),
            (name("Main"), 0)
        ]
    );
    let left = built
        .artifacts
        .iter()
        .find(|artifact| artifact.name == name("Left"))
        .unwrap();
    assert_eq!(left.report.constants, 0);
    let receipt = imported(&built);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|row| row.defaults)
            .sum::<usize>(),
        4
    );
    let defaults = fln_elab::instances::defaults::read(receipt.engine.environment()).unwrap();
    assert_eq!(defaults.len(), 4);
    assert_eq!(defaults[0].candidate.declaration, name("secondChoice"));
    assert_eq!(defaults[1].candidate.declaration, name("secondChoice"));
    assert_eq!(defaults[0].candidate.order, 3);
    assert_eq!(defaults[1].candidate.order, 2);
    assert_choice(&built.checked.checked.engine, "Second");
    assert_choice(&receipt.engine, "Second");
}
