//! Native instance registrations remain usable across compiled module boundaries.
#![forbid(unsafe_code)]
use super::*;

const PICK: &str =
    "prelude\ninductive Token where\n  | left\n  | right\nclass Pick where\n  value : Token";
const CHOICES: &str = "instance (priority := 500) fallback : Pick := Pick.mk Token.left\ninstance (priority := 2000) preferred : Pick := Pick.mk Token.right";

fn assert_choice(engine: &Engine, selected: &str) {
    let root = engine.logical_root(&KVMap::new());
    let source = format!(
        "def chosen : Token := Pick.value\ndef choiceIsPreserved (P : Token -> Prop) (h : P Token.{selected}) : P chosen := h"
    );
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn compiled_global_instances_drive_real_downstream_dictionary_selection() {
    let source = format!("{PICK}\n{CHOICES}");
    let built = compiled(&[("Main", &source)]);
    assert_choice(&built.checked.checked.engine, "right");
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(
        rows.iter()
            .map(|row| (row.declaration.clone(), row.priority))
            .collect::<Vec<_>>(),
        [(name("fallback"), 500), (name("preferred"), 2000)]
    );
    for row in &rows {
        assert_eq!(
            row.keys,
            [source_extensions::DiscrTreeKey::Const(name("Pick"), 0)]
        );
        assert!(row.synth_order.is_empty());
        assert!(row.scope.is_none());
    }
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].instances, 2);
    assert_choice(&receipt.engine, "right");
    let root = receipt.engine.logical_root(&KVMap::new());
    assert!(
        receipt.engine.check_source_files(
            &[b"def chosenWrong : Token := Pick.value\ndef wrongChoice (P : Token -> Prop) (h : P Token.left) : P chosenWrong := h"],
            &KVMap::new(),
            limits().source,
        ).is_err(),
        "the lower-priority dictionary must not be selected"
    );
    assert_eq!(receipt.engine.logical_root(&KVMap::new()), root);
}

#[test]
fn compiled_scoped_instances_activate_only_in_the_consumers_lexical_scope() {
    let source = format!(
        "{PICK}\ninstance fallback : Pick := Pick.mk Token.left\nnamespace Regional\nscoped instance preferred : Pick := Pick.mk Token.right\nend Regional"
    );
    let built = compiled(&[("Main", "prelude\nimport Lib"), ("Lib", &source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].scope, None);
    assert_eq!(rows[1].declaration, name("Regional.preferred"));
    assert_eq!(rows[1].scope, Some(name("Regional")));
    assert!(metadata(&built.artifacts[1].bytes).instances.is_empty());
    let receipt = imported(&built);
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        assert_choice(engine, "left");
        engine
            .check_source_files(
                &[br#"
section
open scoped Regional
def regionalChoice : Token := Pick.value
def regionalProof (P : Token -> Prop) (h : P Token.right) : P regionalChoice := h
end
def restoredChoice : Token := Pick.value
def restoredProof (P : Token -> Prop) (h : P Token.left) : P restoredChoice := h
namespace Regional
def namespaceChoice : Token := Pick.value
def namespaceProof (P : Token -> Prop) (h : P Token.right) : P namespaceChoice := h
end Regional
"#],
                &KVMap::new(),
                limits().source,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(engine.check_source_files(
            &[b"open scoped Regional\ndef choice : Token := Pick.value\ndef wrong (P : Token -> Prop) (h : P Token.left) : P choice := h"],
            &KVMap::new(), limits().source,
        ).is_err(), "opening the scope must select the scoped dictionary");
    }
}

#[test]
fn compiled_scoped_ties_follow_activation_order_and_reopening_is_idempotent() {
    let source = format!(
        "{PICK}\nnamespace Alpha\nscoped instance first : Pick := Pick.mk Token.left\nend Alpha\nnamespace Omega\nscoped instance second : Pick := Pick.mk Token.right\nend Omega"
    );
    let built = compiled(&[("Main", &source)]);
    let receipt = imported(&built);
    assert!(
        receipt
            .engine
            .check_source_files(
                &[b"def noScope : Token := Pick.value"],
                &KVMap::new(),
                limits().source,
            )
            .is_err(),
        "an inactive scoped instance must not become a global fallback"
    );
    for (first, last, expected) in [("Alpha", "Omega", "right"), ("Omega", "Alpha", "left")] {
        let source = format!(
            "open scoped {first}\nopen scoped {last}\nopen scoped {first}\ndef chosen : Token := Pick.value\ndef chosenProof (P : Token -> Prop) (h : P Token.{expected}) : P chosen := h"
        );
        receipt
            .engine
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
    }
}

#[test]
fn priority_updates_preserve_first_registration_order_for_equal_priority_instances() {
    let source = format!(
        "{PICK}\ninstance zFirst : Pick := Pick.mk Token.left\ninstance aSecond : Pick := Pick.mk Token.right\nattribute [instance 2000] zFirst\nattribute [instance 1000] zFirst"
    );
    let built = compiled(&[("Main", &source)]);
    assert_choice(&built.checked.checked.engine, "right");
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(
        rows.iter()
            .map(|row| (row.declaration.clone(), row.priority))
            .collect::<Vec<_>>(),
        [
            (name("zFirst"), 1000),
            (name("aSecond"), 1000),
            (name("zFirst"), 2000),
            (name("zFirst"), 1000)
        ]
    );
    assert_choice(&imported(&built).engine, "right");
}

#[test]
fn a_diamond_exports_only_each_modules_own_instance_registrations() {
    let base = format!("{PICK}\ninstance (priority := 500) fallback : Pick := Pick.mk Token.left");
    let built = compiled(&[
        ("Main", "prelude\nimport Left\nimport Right"),
        (
            "Left",
            "prelude\nimport Base\ninstance (priority := 2000) preferred : Pick := Pick.mk Token.right",
        ),
        ("Right", "prelude\nimport Base"),
        ("Base", &base),
    ]);
    assert_eq!(
        built
            .artifacts
            .iter()
            .map(|artifact| (
                artifact.name.clone(),
                metadata(&artifact.bytes).instances.len()
            ))
            .collect::<Vec<_>>(),
        [
            (name("Base"), 1),
            (name("Left"), 1),
            (name("Right"), 0),
            (name("Main"), 0)
        ]
    );
    let receipt = imported(&built);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|row| row.instances)
            .sum::<usize>(),
        2
    );
    assert_choice(&receipt.engine, "right");
}

#[test]
fn imported_instance_priorities_survive_metadata_only_modules_and_physical_imports() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let base = format!("{PICK}\n{CHOICES}");
    let built = build(
        &initial,
        &[
            ("Main", "prelude\nimport Raised"),
            (
                "Raised",
                "prelude\nimport Base\nattribute [instance 3000] fallback",
            ),
            ("Base", &base),
        ],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let raised = &built.artifacts[1];
    assert_eq!(raised.name, name("Raised"));
    assert_eq!(raised.report.constants, 0);
    let rows = metadata(&raised.bytes).instances;
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].declaration, name("fallback"));
    assert_eq!(rows[0].priority, 3000);
    assert!(metadata(&built.artifacts[2].bytes).instances.is_empty());
    assert_choice(&built.checked.checked.engine, "left");
    assert_choice(&imported(&built).engine, "left");
    aliases::reference_import(
        &built,
        "prelude\nimport Main\nnoncomputable section\ndef chosen : Token := Pick.value\ntheorem choice (P : Token -> Prop) (h : P Token.left) : P chosen := h",
        true,
    );
    aliases::reference_import(
        &built,
        "prelude\nimport Main\nnoncomputable section\ndef chosen : Token := Pick.value\ntheorem wrong (P : Token -> Prop) (h : P Token.right) : P chosen := h",
        false,
    );
    assert_eq!(initial.logical_root(&KVMap::new()), root);
}

#[test]
fn imported_priority_ties_keep_the_original_slot_through_a_diamond() {
    let base = format!("{PICK}\n{CHOICES}");
    let built = compiled(&[
        ("Main", "prelude\nimport Tied\nimport Other"),
        (
            "Tied",
            "prelude\nimport Raised\nattribute [instance 2000] fallback",
        ),
        (
            "Raised",
            "prelude\nimport Base\nattribute [instance 3000] fallback",
        ),
        ("Other", "prelude\nimport Base"),
        ("Base", &base),
    ]);
    assert_choice(&built.checked.checked.engine, "right");
    let receipt = imported(&built);
    assert_choice(&receipt.engine, "right");
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|module| module.instances)
            .sum::<usize>(),
        4
    );
    aliases::reference_import(
        &built,
        "prelude\nimport Main\nnoncomputable section\ndef chosen : Token := Pick.value\ntheorem originalSlot (P : Token -> Prop) (h : P Token.right) : P chosen := h",
        true,
    );
}

#[test]
fn imported_definitions_can_acquire_global_and_scoped_instance_registrations() {
    let base =
        format!("{PICK}\n{CHOICES}\n@[reducible] def unregistered : Pick := Pick.mk Token.left");
    for (registration, scope) in [
        ("attribute [instance 3000] unregistered", None),
        (
            "namespace Regional\nattribute [scoped instance 3000] unregistered\nend Regional",
            Some("Regional"),
        ),
    ] {
        let adapter = format!("prelude\nimport Base\n{registration}");
        let built = compiled(&[
            ("Main", "prelude\nimport Adapter"),
            ("Adapter", &adapter),
            ("Base", &base),
        ]);
        let adapter = &built.artifacts[1];
        assert_eq!(adapter.report.constants, 0);
        let rows = metadata(&adapter.bytes).instances;
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].declaration, name("unregistered"));
        assert_eq!(rows[0].scope, scope.map(name));
        let receipt = imported(&built);
        for engine in [&built.checked.checked.engine, &receipt.engine] {
            assert_choice(engine, if scope.is_some() { "right" } else { "left" });
            if scope.is_some() {
                engine.check_source_files(
                    &[b"open scoped Regional\ndef chosen : Token := Pick.value\ntheorem activated (P : Token -> Prop) (h : P Token.left) : P chosen := h"],
                    &KVMap::new(), limits().source,
                ).unwrap().into_complete().unwrap();
                assert_choice(engine, "right");
            }
        }
        let activation = if scope.is_some() {
            "open scoped Regional\n"
        } else {
            ""
        };
        aliases::reference_import(
            &built,
            &format!(
                "prelude\nimport Main\nnoncomputable section\n{activation}def chosen : Token := Pick.value\ntheorem choice (P : Token -> Prop) (h : P Token.left) : P chosen := h"
            ),
            true,
        );
    }
}

#[test]
fn instance_artifacts_are_byte_stable_and_writer_exhaustion_preserves_reusable_modules() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let module = name("Main");
    let source = format!("{PICK}\n{CHOICES}");
    let inputs = [SourceModuleInput {
        name: &module,
        source: source.as_bytes(),
    }];
    let cold = session
        .compile(&inputs, &module, OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let bytes = cold.artifacts[0].bytes.clone();
    let report = &cold.artifacts[0].report;
    let exact = OleanWriteBudget {
        max_bytes: report.file_bytes,
        max_objects: report.runtime_objects,
    };
    let warm = session
        .compile(&inputs, &module, exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (1, 0));
    assert_eq!(warm.artifacts[0].bytes, bytes);
    for budget in [
        OleanWriteBudget {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
        OleanWriteBudget {
            max_objects: exact.max_objects - 1,
            ..exact
        },
    ] {
        let error = session.compile(&inputs, &module, budget).unwrap_err();
        assert_eq!(error.disposition(), ("resource", false, 3));
    }
    let recovered = session
        .compile(&inputs, &module, exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 1);
    assert_eq!(recovered.artifacts[0].bytes, bytes);
    assert_choice(&imported(&recovered).engine, "right");
}

#[test]
fn generic_instance_prerequisites_keep_absolute_telescope_positions() {
    let source = format!(
        "{CLASS}\ninstance mapperId (A : Type) : Mapper A := Mapper.mk (fun x => x)\nclass Adapter (A : Type) where\n  apply : A -> A\ninstance adapter (A : Type) [d : Mapper A] : Adapter A := Adapter.mk (fun x => Mapper.apply x)"
    );
    let built = compiled(&[("Main", &source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    let adapter = rows
        .iter()
        .find(|row| row.declaration == name("adapter"))
        .unwrap();
    assert_eq!(adapter.synth_order, [1]);
    assert_eq!(
        adapter.keys,
        [
            source_extensions::DiscrTreeKey::Const(name("Adapter"), 1),
            source_extensions::DiscrTreeKey::Star
        ]
    );
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].instances, 2);
    receipt.engine.check_source_files(
        &[b"def adapterIdentity (A : Type) (P : A -> Prop) (x : A) (h : P x) : P (Adapter.apply x) := h"],
        &KVMap::new(), limits().source,
    ).unwrap().into_complete().unwrap();
}

#[test]
fn output_parameters_preserve_the_dependency_order_of_instance_prerequisites() {
    let source = format!(
        "{PICK}\ndef outParam.{{u}} (A : Sort u) : Sort u := A\nclass Need (A : Type) where\n  value : Token\nclass Choose (A : outParam Type) where\n  value : A\ninstance needToken : Need Token := Need.mk Token.right\ninstance chooseToken : Choose Token := Choose.mk Token.right\ninstance combined {{A : Type}} [need : Need A] [choice : Choose A] : Pick := Pick.mk (@Need.value A need)"
    );
    let built = compiled(&[("Main", &source)]);
    assert_choice(&built.checked.checked.engine, "right");
    let rows = metadata(&built.artifacts[0].bytes).instances;
    let combined = rows
        .iter()
        .find(|row| row.declaration == name("combined"))
        .unwrap();
    assert_eq!(
        combined.synth_order,
        [2, 1],
        "Choose supplies the type needed by the earlier Need prerequisite"
    );
    let choose = rows
        .iter()
        .find(|row| row.declaration == name("chooseToken"))
        .unwrap();
    assert_eq!(
        choose.keys,
        [
            source_extensions::DiscrTreeKey::Const(name("Choose"), 1),
            source_extensions::DiscrTreeKey::Const(name("Token"), 0)
        ],
        "the pin retains an explicit concrete output type in its index"
    );
    let receipt = imported(&built);
    assert_choice(&receipt.engine, "right");
}

#[test]
fn generic_and_specific_paths_preserve_selection_across_the_compiled_boundary() {
    let source = format!(
        "{PICK}\nclass Mark (A : Type) where\n  apply : A -> Token\ninstance specific : Mark Token := Mark.mk (fun x => Token.right)\ninstance generic (A : Type) : Mark A := Mark.mk (fun x => Token.left)"
    );
    let built = compiled(&[("Main", &source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 2);
    assert_eq!(
        rows[0].keys,
        [
            source_extensions::DiscrTreeKey::Const(name("Mark"), 1),
            source_extensions::DiscrTreeKey::Const(name("Token"), 0)
        ]
    );
    assert_eq!(
        rows[1].keys,
        [
            source_extensions::DiscrTreeKey::Const(name("Mark"), 1),
            source_extensions::DiscrTreeKey::Star
        ]
    );
    let receipt = imported(&built);
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        engine.check_source_files(
            &[b"def marked : Token := Mark.apply Token.left\ndef specificWins (P : Token -> Prop) (h : P Token.right) : P marked := h"],
            &KVMap::new(), limits().source,
        ).unwrap().into_complete().unwrap();
    }
}
