//! Structures with Type-valued fields through the drop-in `lean` door
//! (fln-lvdh). A type-valued field is runtime-irrelevant and a field typed by
//! it is a boxed polymorphic slot; before this, the record catalog abandoned
//! the whole shape and ingress refused the constructor (UnknownConstant).
//!
//! Every expected stdout below is what the pinned Reference (`lean` v4.32.0,
//! commit 8c9756b2) prints for the same program, with exit 0 and no stderr.
#![forbid(unsafe_code)]
use std::io::Write;
use std::process::{Command, Stdio};

const PACKAGE: &str = "structure Package where\n  carrier : Type\n  value : carrier\n";

fn lean(source: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg("--stdin")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(stderr.is_empty(), "{stderr}");
    String::from_utf8(output.stdout).unwrap()
}

/// The bead's first reproduction, with the evaluation it asked for.
#[test]
fn a_boxed_field_of_a_nat_carrier_prints_its_value() {
    let source = format!("{PACKAGE}def packed : Package := Package.mk Nat 7\n#eval packed.value\n");
    assert_eq!(lean(&source), "7\n");
}

/// The bead's second reproduction: a structure whose only field is a type.
#[test]
fn a_structure_holding_only_a_type_compiles_and_is_consumed() {
    let source = "structure Box where\n  carrier : Type\ndef b : Box := Box.mk String\ndef width (x : Box) : Nat := match x with\n  | Box.mk _ => 1\n#eval width b\ndef boxes : Nat := width (Box.mk Nat) + width b\n#eval boxes\n";
    assert_eq!(lean(source), "1\n2\n");
}

/// Plain, erased, boxed and proof fields in one layout. `total` projects the
/// fields after the erased and boxed slots from a runtime parameter, so a
/// dropped or shifted slot reads the wrong field.
#[test]
fn plain_erased_boxed_and_proof_fields_keep_their_positions() {
    let source = "structure Mixed where\n  label : String\n  carrier : Type\n  value : carrier\n  count : Nat\n  ok : count = count\ndef m : Mixed := Mixed.mk \"tag\" String \"inner\" 5 rfl\ndef total (x : Mixed) : Nat := x.count + String.length x.label\n#eval total m\n#eval m.label\n#eval (m.value : String)\n";
    assert_eq!(lean(source), "8\n\"tag\"\n\"inner\"\n");
}

/// A boxed value read from a nested record, and carried through functions
/// whose receiver is a runtime parameter, so no projection can be folded.
#[test]
fn boxed_values_survive_nested_records_and_parameter_receivers() {
    let source = format!(
        "{PACKAGE}structure Outer where\n  inner : Package\n  count : Nat\ndef outer : Outer := Outer.mk (Package.mk String \"nested\") 3\n#eval outer.inner.value\ndef depth (o : Outer) : Nat := o.count + 1\n#eval depth outer\ndef rewrap (p : Package) : Package := Package.mk p.carrier p.value\ndef twice (p : Package) : Package := rewrap (rewrap p)\n#eval (twice outer.inner).value\ndef wrap (n : Nat) : Package := Package.mk Nat (n + 1)\n#eval (rewrap (wrap 41)).value\n"
    );
    assert_eq!(lean(&source), "\"nested\"\n4\n\"nested\"\n42\n");
}

/// Heap (big Nat, String) and Float values in the same boxed slot.
#[test]
fn boxed_slots_carry_heap_and_float_values() {
    let source = format!(
        "{PACKAGE}def big : Package := Package.mk Nat 123456789012345678901234567890\n#eval big.value\ndef real : Package := Package.mk Float 2.5\n#eval real.value\ndef text : Package := Package.mk String \"heap\"\ndef rewrap (p : Package) : Package := Package.mk p.carrier p.value\ndef twice (p : Package) : Package := rewrap (rewrap p)\n#eval (twice text).value\n#eval (twice big).value\n"
    );
    assert_eq!(
        lean(&source),
        "123456789012345678901234567890\n2.500000\n\"heap\"\n123456789012345678901234567890\n"
    );
}

/// A type field beside a type parameter, and a Prop-valued field whose proof
/// field is erased like any other proof.
#[test]
fn parametric_and_prop_valued_type_fields() {
    let source = "structure Tagged (α : Type) where\n  carrier : Type\n  value : carrier\n  tag : α\ndef t : Tagged String := Tagged.mk Nat 9 \"label\"\n#eval t.value\ndef tagOf (x : Tagged String) : String := x.tag\n#eval tagOf t\nstructure Claim where\n  prop : Prop\n  proof : prop\n  count : Nat\ndef c : Claim := Claim.mk (1 = 1) rfl 5\ndef twice (x : Claim) : Nat := x.count + x.count\n#eval twice c\n";
    assert_eq!(lean(source), "9\n\"label\"\n10\n");
}
