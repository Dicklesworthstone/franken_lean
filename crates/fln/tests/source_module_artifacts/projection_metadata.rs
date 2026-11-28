//! Generated projection descriptors preserve class reduction after physical imports.
#![forbid(unsafe_code)]
use super::*;
use source_extensions::{DiscrTreeKey as Key, ProjectionEntry};

fn private(declaration: &str) -> Name {
    Name::num(name("_private.Main"), 0).append_core(&name(declaration))
}

fn projection(
    declaration: &str,
    constructor: &str,
    num_params: u32,
    field_index: u32,
    from_class: bool,
) -> ProjectionEntry {
    ProjectionEntry {
        declaration: name(declaration),
        constructor: name(constructor),
        num_params,
        field_index,
        from_class,
    }
}

#[test]
fn projection_maps_preserve_logical_indices_receiver_provenance_and_visibility() {
    let source = r#"module
prelude
public section
inductive ProjectionToken where
  | left
  | right
class ProjectionClass (A : Type) (p : Prop) where
  evidence : p
  apply : A -> A
structure ProjectionRecord (A : Type) where
  apply : A -> A
private structure ProjectionHidden where
  value : ProjectionToken
"#;
    let built = compiled(&[("Main", source)]);
    let artifact = &built.artifacts[0];
    let mut expected = vec![
        projection("ProjectionClass.evidence", "ProjectionClass.mk", 2, 0, true),
        projection("ProjectionClass.apply", "ProjectionClass.mk", 2, 1, true),
        projection("ProjectionRecord.apply", "ProjectionRecord.mk", 1, 0, false),
    ];
    expected.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
    assert_eq!(metadata(&artifact.bytes).projections, expected);
    let parts = artifact.companions.as_ref().unwrap();
    let hidden = ProjectionEntry {
        declaration: private("ProjectionHidden.value"),
        constructor: private("ProjectionHidden.mk"),
        num_params: 0,
        field_index: 0,
        from_class: false,
    };
    let mut complete = expected.clone();
    complete.push(hidden.clone());
    complete.sort_by(|left, right| left.declaration.quick_cmp(&right.declaration));
    assert_eq!(metadata(&parts.private).projections, complete);
    assert_eq!(metadata(&parts.server).projections, expected);
    let receipt = imported(&built);
    let good = "theorem projected (A : Type) (p : Prop) (hp : p) (P : A -> Prop) (x : A) (h : P x) : P (@ProjectionClass.apply A p (ProjectionClass.mk hp (fun x => x)) x) := h";
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        engine
            .check_source_files(&[good.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
    }
    // The ordinary field keeps its creation-time bit after the pin registers
    // its structure as a class. This does not retroactively change its receiver.
    aliases::reference_import(
        &built,
        r#"module
import Lean
public import Main
attribute [class] ProjectionRecord
open Lean in
run_cmd do
  let env ← getEnv
  for (decl, ctor, params, index, fromClass) in #[
      (`ProjectionClass.evidence, `ProjectionClass.mk, 2, 0, true),
      (`ProjectionClass.apply, `ProjectionClass.mk, 2, 1, true),
      (`ProjectionRecord.apply, `ProjectionRecord.mk, 1, 0, false)] do
    let some row := env.getProjectionFnInfo? decl | throwError "missing projection {decl}"
    unless row.ctorName == ctor && row.numParams == params && row.i == index && row.fromClass == fromClass do
      throwError "wrong projection {decl}: {repr row}"
  unless (env.getProjectionFnInfo? (mkPrivateNameCore `Main `ProjectionHidden.value)).isNone do
    throwError "private projection metadata escaped its module"
"#,
        true,
    );
}

#[test]
fn reducible_ofnat_projection_keeps_literal_instance_selection_after_physical_import() {
    let source = r#"prelude
universe u
inductive Nat where
  | zero
  | succ (n : Nat)
inductive Bool where
  | false
  | true
@[reducible] def outParam (A : Sort u) : Sort u := A
class OfNat (A : Type u) (_ : Nat) where
  ofNat : A
instance instOfNatNat (n : Nat) : OfNat Nat n := OfNat.mk n
attribute [reducible] OfNat.ofNat
class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat 7 := D.mk 7
instance high : D Bool Bool.true := D.mk 99
class Root where
  value : Nat
instance root {A : Type} {a : A} [warm : D A a] [fixed : D Nat 7] : Root := Root.mk fixed.value
abbrev inferRoot [i : Root] : Root := i
abbrev inferD {A : Type} {a : A} [i : D A a] : D A a := i
"#;
    let built = compiled(&[("Main", source)]);
    let metadata = metadata(&built.artifacts[0].bytes);
    assert!(
        metadata
            .projections
            .contains(&projection("OfNat.ofNat", "OfNat.mk", 2, 0, true))
    );
    let row = |declaration: &str| {
        metadata
            .instances
            .iter()
            .find(|row| row.declaration == name(declaration))
            .unwrap()
    };
    assert_eq!(
        row("low").keys,
        [
            Key::Const(name("D"), 2),
            Key::Const(name("Nat"), 0),
            Key::Lit(fln::Literal::Nat(fln::NatLit::from_u64(7)))
        ]
    );
    assert_eq!(
        row("high").keys,
        [
            Key::Const(name("D"), 2),
            Key::Const(name("Bool"), 0),
            Key::Const(name("Bool.true"), 0)
        ]
    );
    assert_eq!(row("root").keys, [Key::Const(name("Root"), 0)]);
    assert_eq!(row("root").synth_order, [2, 3]);
    for declaration in ["low", "high"] {
        assert_eq!(row(declaration).priority, 1000);
        assert!(row(declaration).synth_order.is_empty());
    }
    let receipt = imported(&built);
    let selected = "def result : Root := inferRoot\ntheorem correct (P : Nat -> Prop) (h : P 7) : P result.value := h";
    let newest = "instance newest : D Nat 7 := D.mk 42\ndef result : Root := inferRoot\ntheorem correct (P : Nat -> Prop) (h : P 42) : P result.value := h";
    let rejected = "def rejected : D Nat 7 := inferD (A := Nat) (a := 7)";
    let wrong = "def result : Root := inferRoot\ntheorem wrong (P : Nat -> Prop) (h : P 99) : P result.value := h";
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        let original = engine.logical_root(&KVMap::new());
        for consumer in [selected, newest] {
            engine
                .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
                .unwrap()
                .into_complete()
                .unwrap();
        }
        for consumer in [rejected, wrong] {
            let error = match engine.check_source_files(
                &[consumer.as_bytes()],
                &KVMap::new(),
                limits().source,
            ) {
                Err(error) => error,
                Ok(_) => panic!("the typed numeral output or wrong dictionary value was accepted"),
            };
            assert_eq!(error.disposition(), ("elaboration", false, 1));
        }
        assert_eq!(engine.logical_root(&KVMap::new()), original);
        for uncommitted in ["result", "newest", "rejected", "wrong"] {
            assert!(!engine.environment().contains(&name(uncommitted)));
        }
    }
    for (consumer, accepted) in [
        (selected, true),
        (newest, true),
        (rejected, false),
        (wrong, false),
    ] {
        aliases::reference_import(
            &built,
            &format!("prelude\nimport Main\nnoncomputable section\n{consumer}"),
            accepted,
        );
    }
}
