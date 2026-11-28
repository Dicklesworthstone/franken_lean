//! Literal keys retain selection order across source and physical module imports.
#![forbid(unsafe_code)]
use super::*;
use source_extensions::DiscrTreeKey as Key;

const NUMERALS: &str = r#"prelude
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
"#;

#[test]
fn numeral_instance_keys_preserve_output_reconciliation_after_physical_imports() {
    for numeral in ["7", "(7 : Nat)"] {
        let source = format!(
            r#"{NUMERALS}
class D (A : outParam Type) (a : outParam A) where
  value : Nat
instance low : D Nat {numeral} := D.mk 7
instance high : D Bool Bool.true := D.mk 99
class Root where
  value : Nat
instance root {{A : Type}} {{a : A}} [warm : D A a] [fixed : D Nat 7] : Root := Root.mk fixed.value
abbrev inferRoot [i : Root] : Root := i
abbrev inferD {{A : Type}} {{a : A}} [i : D A a] : D A a := i
"#
        );
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).instances;
        let low = rows
            .iter()
            .find(|row| row.declaration == name("low"))
            .unwrap();
        assert_eq!(
            low.keys,
            [
                Key::Const(name("D"), 2),
                Key::Const(name("Nat"), 0),
                Key::Lit(fln::Literal::Nat(fln::NatLit::from_u64(7))),
            ]
        );
        let high = rows
            .iter()
            .find(|row| row.declaration == name("high"))
            .unwrap();
        assert_eq!(
            high.keys,
            [
                Key::Const(name("D"), 2),
                Key::Const(name("Bool"), 0),
                Key::Const(name("Bool.true"), 0),
            ]
        );
        for row in [low, high] {
            assert_eq!(row.priority, 1000);
            assert!(row.synth_order.is_empty());
        }
        let root = rows
            .iter()
            .find(|row| row.declaration == name("root"))
            .unwrap();
        assert_eq!(root.keys, [Key::Const(name("Root"), 0)]);
        assert_eq!(root.synth_order, [2, 3]);
        let receipt = imported(&built);
        let selected = "def result : Root := inferRoot\ntheorem correct (P : Nat -> Prop) (h : P 7) : P result.value := h";
        let newest = "instance newest : D Nat 7 := D.mk 42\ndef result : Root := inferRoot\ntheorem correct (P : Nat -> Prop) (h : P 42) : P result.value := h";
        let rejected = "def rejected : D Nat 7 := inferD (A := Nat) (a := 7)";
        for engine in [&built.checked.checked.engine, &receipt.engine] {
            let original = engine.logical_root(&KVMap::new());
            for consumer in [selected, newest] {
                engine
                    .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
                    .unwrap_or_else(|error| panic!("{numeral}\n{consumer}: {error:?}"))
                    .into_complete()
                    .unwrap();
            }
            let error = match engine.check_source_files(
                &[rejected.as_bytes()],
                &KVMap::new(),
                limits().source,
            ) {
                Err(error) => error,
                Ok(_) => panic!("{numeral}: the Bool root output must not fall back to low"),
            };
            assert_eq!(error.disposition(), ("elaboration", false, 1));
            assert_eq!(engine.logical_root(&KVMap::new()), original);
            for uncommitted in ["result", "newest", "rejected"] {
                assert!(!engine.environment().contains(&name(uncommitted)));
            }
        }
        for (consumer, accepted) in [(selected, true), (rejected, false)] {
            aliases::reference_import(
                &built,
                &format!("prelude\nimport Main\nnoncomputable section\n{consumer}"),
                accepted,
            );
        }
    }
}
