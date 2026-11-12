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
fn ordinary_defaults_survive_compiled_modules_with_actual_field_dependencies() {
    use fln_elab::reducibility::{Reducibility, known_status};

    let base = r#"prelude
universe u
inductive Marker where | left | right
structure Bundle (A : Type u) (fallback : A) where
  carrier : Type u := A
  value : carrier
  copy : carrier := value
  run (value : carrier) : carrier := value
  marker : A := fallback
structure Parent (A : Type u) where
  first : A
structure Derived (A : Type u) extends Parent A where
  copy : A := first
class Seed (A : Type) where
  value : A
structure FromInstance (A : Type) [Seed A] where
  value : A := Seed.value
structure Evidence (P : Prop) (witness : P) : Prop where
  holds : P := witness
section
variable {A : Type} (fallback : A)
structure Scoped where
  value : A := fallback
  run (value : A) : A := value
end
"#;
    let child = r#"prelude
import Base
universe u
structure Child (A : Type u) (fallback : A) extends Bundle A fallback where
  marker := later
  later : A
structure Grandchild (A : Type u) (fallback : A) extends Child A fallback
"#;
    let built = compiled(&[
        ("Main", "prelude\nimport Child"),
        ("Child", child),
        ("Base", base),
    ]);
    let receipt = imported(&built);
    let probe = r#"def selected : Grandchild Marker Marker.left :=
  { value := Marker.right, later := Marker.right }
def explicitCopy : Grandchild Marker Marker.left :=
  { value := Marker.right, copy := Marker.left, later := Marker.left }
def updated : Grandchild Marker Marker.left := { selected with value := Marker.left }
theorem defaultCopied (P : Marker -> Prop) (h : P Marker.right) : P selected.copy := h
theorem childOverrides (P : Marker -> Prop) (h : P Marker.right) : P selected.marker := h
theorem methodParameter (P : Marker -> Prop) (h : P Marker.left) :
  P (selected.run Marker.left) := h
theorem explicitWins (P : Marker -> Prop) (h : P Marker.left) : P explicitCopy.copy := h
theorem updateKeepsCopy (P : Marker -> Prop) (h : P Marker.right) : P updated.copy := h
def parent : Parent Marker := { first := Marker.right }
def wholeParent : Derived Marker := { toParent := parent }
theorem wholeParentValue (P : Marker -> Prop) (h : P Marker.right) : P wholeParent.copy := h
def changedCarrier : Bundle Marker Marker.left :=
  { carrier := Marker -> Marker, value := fun _ => Marker.right }
theorem changedValue (P : Marker -> Prop) (h : P Marker.right) :
  P (changedCarrier.copy Marker.left) := h
theorem universeChoice (P : Type -> Prop) (h : P Marker) :
  P (({ value := Marker } : Bundle Type Marker).copy) := h
instance chosenSeed : Seed Marker := Seed.mk Marker.right
def fromInstance : FromInstance Marker := {}
theorem actualDictionary (P : Marker -> Prop) (h : P Marker.right) : P fromInstance.value := h
def fromSection : Scoped Marker.left := {}
theorem sectionParameter (P : Marker -> Prop) (h : P Marker.left) : P fromSection.value := h
theorem scopedMethodParameter (P : Marker -> Prop) (h : P Marker.right) :
  P (fromSection.run Marker.right) := h
theorem proofDefault (P : Prop) (witness : P) : P := ({} : Evidence P witness).holds
"#;
    let bad = r#"theorem wrong (P : Marker -> Prop) (h : P Marker.left) :
  P (({ value := Marker.right } : Bundle Marker Marker.left).copy) := h
"#;
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        for helper in [
            "Bundle.carrier._default",
            "Bundle.copy._default",
            "Bundle.run._default",
            "Derived.copy._default",
            "FromInstance.value._default",
            "Scoped.value._default",
            "Evidence.holds._default",
            "Grandchild.copy._inherited_default",
        ] {
            assert!(matches!(
                engine.environment().find(&name(helper)),
                Some(fln::ConstantInfo::Defn(_))
            ));
            assert_eq!(
                known_status(engine.environment(), &name(helper)).unwrap(),
                Some(Reducibility::Semireducible),
            );
        }
        assert!(
            fln_elab::records::defaults::RecordDefaults::read(engine.environment())
                .unwrap()
                .helper(&name("Bundle"), 2)
                .is_none(),
            "ordinary defaults must use checked declarations across the module boundary"
        );
        engine
            .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
        let root = engine.logical_root(&KVMap::new());
        assert!(
            engine
                .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits().source)
                .is_err()
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    // Source artifacts contain checked declarations, not the pin's compiled IR.
    // These probes check the imported defaults through elaboration and proofs.
    aliases::reference_import(
        &built,
        &format!("prelude\nimport Main\nnoncomputable section\n{probe}"),
        true,
    );
    aliases::reference_import(&built, &format!("prelude\nimport Main\n{bad}"), false);
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
fn inherited_overrides_and_proof_helpers_survive_a_physical_module_roundtrip() {
    use fln_elab::reducibility::{Reducibility, known_status};

    // Inherited overrides retain their declared and frozen helper distinction
    // through ordinary definition serialization, including proof defaults.
    let base = r#"prelude
inductive Token where | left | right
structure Parent (A : Type) (P : Prop) where
  value : A
  run : A -> A
  holds : P
"#;
    let child = r#"prelude
import Base
structure Child (A : Type) (fallback : A) (P : Prop) (witness : P) extends Parent A P where
  value := later
  run x := fallback
  holds := witness
  later : A
structure Grandchild (A : Type) (fallback : A) (P : Prop) (witness : P)
    extends Child A fallback P witness
"#;
    let built = compiled(&[
        ("Main", "prelude\nimport Child"),
        ("Child", child),
        ("Base", base),
    ]);
    let receipt = imported(&built);
    let probe = r#"def selected (P : Prop) (w : P) : Grandchild Token Token.right P w :=
  { later := Token.left }
theorem laterWins (P : Prop) (w : P) (Q : Token -> Prop) (h : Q Token.left) :
  Q (selected P w).value := h
theorem parameterWins (P : Prop) (w : P) (Q : Token -> Prop) (h : Q Token.right) :
  Q ((selected P w).run Token.left) := h
theorem proofDefault (P : Prop) (w : P) : P := (selected P w).holds
"#;
    let bad = r#"theorem wrong (P : Prop) (w : P) (Q : Token -> Prop) (h : Q Token.right) :
  Q (({ later := Token.left } : Grandchild Token Token.right P w).value) := h
"#;
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        for (record, suffix) in [("Child", "_default"), ("Grandchild", "_inherited_default")] {
            for field in ["value", "run", "holds"] {
                let helper = name(&format!("{record}.{field}.{suffix}"));
                assert!(
                    matches!(
                        engine.environment().find(&helper),
                        Some(fln::ConstantInfo::Defn(_))
                    ),
                    "a data or proof default stays a checked definition: {helper:?}",
                );
                assert_eq!(
                    known_status(engine.environment(), &helper).unwrap(),
                    Some(Reducibility::Semireducible),
                );
            }
        }
        assert!(matches!(
            engine.environment().find(&name("Parent.holds")),
            Some(fln::ConstantInfo::Thm(_))
        ));
        engine
            .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            engine
                .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits().source)
                .is_err()
        );
    }
    aliases::reference_import(
        &built,
        &format!("prelude\nimport Main\nnoncomputable section\n{probe}"),
        true,
    );
    aliases::reference_import(&built, &format!("prelude\nimport Main\n{bad}"), false);
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

#[test]
fn a_copied_parent_is_a_non_subobject_parent_the_pin_reads() {
    let base = "prelude\ninductive Token where | left | right\n\
        structure Root where\n  root : Token\n\
        structure Left extends Root where\n  left : Token\n\
        structure Right extends Root where\n  right : Token\n";
    let child = "prelude\nimport Base\nstructure Both extends Left, Right where\n  both : Token\n";
    let built = compiled(&[
        ("Main", "prelude\nimport Child"),
        ("Child", child),
        ("Base", base),
    ]);
    let structures = metadata(&built.artifacts[1].bytes).structures;
    assert_eq!(structures.len(), 1);
    let both = &structures[0];
    // The pin's `withStruct`: `Right` overlaps `Left` in `root`, so it is copied: its new
    // field `right` joins the record, and `Both.toRight` is a definition, not a field.
    assert_eq!(
        both.fields
            .iter()
            .map(|field| (field.name.clone(), field.subobject.clone()))
            .collect::<Vec<_>>(),
        [
            (name("toLeft"), Some(name("Left"))),
            (name("right"), None),
            (name("both"), None)
        ]
    );
    assert_eq!(
        both.parents
            .iter()
            .map(|parent| (
                parent.name.clone(),
                parent.projection.clone(),
                parent.subobject
            ))
            .collect::<Vec<_>>(),
        [
            (name("Left"), name("Both.toLeft"), true),
            (name("Right"), name("Both.toRight"), false)
        ]
    );
    aliases::reference_import(
        &built,
        "prelude\nimport Main\n\
        theorem copied (P : Token -> Prop) (h : P Token.right) :\n\
          P (({ root := Token.left, left := Token.left, right := Token.right, both := Token.left } : Both).toRight.right) := h\n\
        theorem shared (P : Token -> Prop) (h : P Token.left) :\n\
          P (({ root := Token.left, left := Token.right, right := Token.right, both := Token.right } : Both).toRight.root) := h\n",
        true,
    );
    aliases::reference_import(
        &built,
        "prelude\nimport Main\n\
        theorem wrong (P : Token -> Prop) (h : P Token.left) :\n\
          P (({ root := Token.left, left := Token.left, right := Token.right, both := Token.left } : Both).toRight.right) := h\n",
        false,
    );
}
