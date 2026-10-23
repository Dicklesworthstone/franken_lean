//! Complete structure interfaces survive physical module boundaries.
#![forbid(unsafe_code)]
use super::*;

const BASE: &str = "prelude\ninductive Token where | left | right\n\
    inductive Single where | mk (value : Token)\n\
    structure Parent where\n  value : Token\n\
    structure Other where\n  extra : Token\n";
const CHILD: &str = "prelude\nimport Base\n\
    structure Child extends first : Parent, Other where\n  tag : Token\n";

fn built_records() -> SourceModuleBuild {
    compiled(&[
        ("Main", "prelude\nimport Child"),
        ("Child", CHILD),
        ("Base", BASE),
    ])
}

#[test]
fn compiled_structure_interfaces_preserve_named_parents_literals_and_updates() {
    let built = built_records();
    let base = metadata(&built.artifacts[0].bytes).structures;
    assert_eq!(base.len(), 2);
    assert!(
        base.iter()
            .all(|row| [name("Parent"), name("Other")].contains(&row.name)),
        "ordinary single-constructor inductives must not become structures"
    );
    let children = metadata(&built.artifacts[1].bytes).structures;
    assert_eq!(children.len(), 1);
    let child = &children[0];
    assert_eq!(child.name, name("Child"));
    assert_eq!(
        child
            .fields
            .iter()
            .map(|field| field.name.clone())
            .collect::<Vec<_>>(),
        [name("first"), name("toOther"), name("tag")]
    );
    assert_eq!(
        child
            .parents
            .iter()
            .map(|parent| (parent.name.clone(), parent.projection.clone()))
            .collect::<Vec<_>>(),
        [
            (name("Parent"), name("Child.first")),
            (name("Other"), name("Child.toOther"))
        ]
    );
    assert!(child.parents.iter().all(|parent| parent.subobject));
    assert!(metadata(&built.artifacts[2].bytes).structures.is_empty());

    let imported = imported(&built);
    let probe = "def before : Child := { value := Token.left, extra := Token.right, tag := Token.left }\n\
        def after : Child := { before with value := Token.right }\n\
        theorem inherited (P : Token -> Prop) (h : P Token.left) : P before.value := h\n\
        theorem replaced (P : Token -> Prop) (h : P Token.right) : P after.value := h\n\
        theorem otherParent (P : Token -> Prop) (h : P Token.right) : P after.extra := h\n\
        theorem ownField (P : Token -> Prop) (h : P Token.left) : P after.tag := h\n";
    for engine in [&built.checked.checked.engine, &imported.engine] {
        engine
            .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
    }
    assert_eq!(
        built_records()
            .artifacts
            .iter()
            .map(|a| &a.bytes)
            .collect::<Vec<_>>(),
        built.artifacts.iter().map(|a| &a.bytes).collect::<Vec<_>>()
    );
}

#[test]
fn the_pin_constructs_and_updates_records_from_native_structure_metadata() {
    let built = built_records();
    aliases::reference_import(
        &built,
        "prelude\nimport Main\n\
        theorem inherited (P : Token -> Prop) (h : P Token.left) :\n\
          P (({ value := Token.left, extra := Token.right, tag := Token.left } : Child).value) := h\n\
        theorem replaced (P : Token -> Prop) (h : P Token.right) :\n\
          let before : Child := { value := Token.left, extra := Token.right, tag := Token.left }\n\
          P ({ before with value := Token.right }.value) := h\n",
        true,
    );
    aliases::reference_import(
        &built,
        "prelude\nimport Main\n\
        theorem wrong (P : Token -> Prop) (h : P Token.right) :\n\
          P (({ value := Token.left, extra := Token.right, tag := Token.left } : Child).value) := h\n",
        false,
    );
}

#[test]
fn compiled_class_parents_remain_real_instances_after_physical_import() {
    let base = "prelude\ninductive Token where | left | right\nclass Pick where\n  value : Token\n\
        class Need where\n  marker : Token\ninstance givenNeed : Need := { marker := Token.left }\n";
    let child = "prelude\nimport Base\nclass Leaf [need : Need] extends Pick where\n  marker : Token\n\
        instance selected : Leaf := { value := Token.right, marker := Token.left }\n";
    let built = compiled(&[
        ("Main", "prelude\nimport Child"),
        ("Child", child),
        ("Base", base),
    ]);
    let metadata = metadata(&built.artifacts[1].bytes);
    assert_eq!(
        metadata.structures[0].parents[0].projection,
        name("Leaf.toPick")
    );
    let parent_instance = metadata
        .instances
        .iter()
        .find(|row| row.declaration == name("Leaf.toPick"))
        .unwrap();
    // The implicit Need parameter is learned from the self dictionary. The
    // pin's projection exception schedules self at absolute telescope index 1.
    assert_eq!(parent_instance.synth_order, [1]);
    let probe =
        "theorem selectedParent (P : Token -> Prop) (h : P Token.right) : P Pick.value := h";
    imported(&built)
        .engine
        .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    aliases::reference_import(&built, &format!("prelude\nimport Main\n{probe}"), true);
}

#[test]
fn field_default_effects_remain_an_explicit_refusal_until_their_writer_exists() {
    let error = build(
        &Engine::builder().build_empty(),
        &[(
            "Main",
            "prelude\n\
        inductive Token where | mk\nstructure WithDefault where\n  value : Token := Token.mk\n",
        )],
        OleanWriteBudget::default(),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            SourceModuleBuildError::Check(SourceModuleCheckError::Extension { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn checked_named_defaults_follow_the_pin_after_a_physical_import() {
    let built = compiled(&[(
        "Main",
        "prelude\ninductive Token where | left | right\n\
         structure Plain where\n  value : Token\n\
         def Plain.value._default : Token := Token.right\n",
    )]);
    let probe = "theorem selected (P : Token -> Prop) (h : P Token.right) :\n\
        P (({} : Plain).value) := h";
    for engine in [&built.checked.checked.engine, &imported(&built).engine] {
        engine
            .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
    }
    aliases::reference_import(&built, &format!("prelude\nimport Main\n{probe}"), true);
}

#[test]
fn polymorphic_and_proof_structures_preserve_checked_interfaces() {
    let built = compiled(&[(
        "Main",
        "prelude\nstructure Box.{u} (A : Type u) where\n  value : A\n\
         structure Evidence (P : Prop) : Prop where\n  proof : P\n\
         structure Package where\n  carrier : Type\n  value : carrier\n\
         structure Detailed extends Package where\n  extra : carrier\n",
    )]);
    let rows = metadata(&built.artifacts[0].bytes).structures;
    assert_eq!(rows.len(), 4);
    assert!(matches!(
        built
            .checked
            .checked
            .engine
            .environment()
            .find(&name("Evidence.mk._flat_ctor")),
        Some(fln::ConstantInfo::Defn(_))
    ));
    assert!(matches!(
        built
            .checked
            .checked
            .engine
            .environment()
            .find(&name("Evidence.proof")),
        Some(fln::ConstantInfo::Thm(_))
    ));
    let probe = "theorem boxField.{u} {A : Type u} (x : A) (P : A -> Prop) (h : P x) :\n\
          P (({ value := x } : Box A).value) := h\n\
        theorem proofField (P : Prop) (h : P) : P := ({ proof := h } : Evidence P).proof\n\
        theorem dependentParent (A : Type) (x : A) (P : A -> Prop) (h : P x) :\n\
          P (({ carrier := A, value := x, extra := x } : Detailed).extra) := h\n";
    for engine in [&built.checked.checked.engine, &imported(&built).engine] {
        engine
            .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
    }
    aliases::reference_import(&built, &format!("prelude\nimport Main\n{probe}"), true);
}
