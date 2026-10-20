//! Static datatype parameters do not become runtime inputs to generated fields.
#![forbid(unsafe_code)]
use fln::{
    Budget, ClosedVmValue, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name,
    SourceCheckLimits, closed_vm_value,
};
use std::sync::OnceLock;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> &'static Engine {
    static BASE: OnceLock<Engine> = OnceLock::new();
    BASE.get_or_init(|| {
        let limits = limits();
        Engine::with_source_seed(limits)
            .unwrap()
            .into_complete()
            .unwrap()
            .check_source_files(
                &[br#"
noncomputable def hidden : Nat := 5
structure ParamRecord (n : Nat) where
  value : Nat
def record : ParamRecord hidden := { value := 42 }
structure MultiRecord (n m : Nat) where
  value : Nat
structure ProofRecord (n : Nat) where
  evidence : n = n
  value : Nat
structure CallbackRecord (n : Nat) where
  apply : Nat -> Nat
structure GenericRecord (A : Type) (n : Nat) where
  value : A
def callback : CallbackRecord hidden := { apply := fun x => x + 1 }
noncomputable def hiddenRecord : ParamRecord hidden := record
def ordinary (n : Nat) (r : ParamRecord n) : Nat := r.value
namespace ParamRecord
def lookalike (n : Nat) (r : ParamRecord n) : Nat := r.value
end ParamRecord
"#],
                &KVMap::new(),
                SourceCheckLimits::new(limits),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine
    })
}
fn returns(source: &str, expected: usize) {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let result = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(
        closed_vm_value(&result.executions.last().unwrap().exit).unwrap(),
        Some(ClosedVmValue::Scalar(expected)),
        "{source}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
fn refuses(source: &str, dependency: &str) {
    let engine = engine();
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .expect_err("a live noncomputable dependency must not execute");
    let message = error.to_string();
    assert!(
        message.contains("noncomputable") && message.contains(dependency),
        "{source}: {error:?}"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn generated_field_projects_an_erased_noncomputable_parameter() {
    for source in [
        "#eval record.value",
        "#eval @ParamRecord.value hidden record",
    ] {
        returns(source, 42);
    }
}
#[test]
fn partial_projection_preserves_its_remaining_receiver_interface() {
    returns(
        "#eval let get : ParamRecord hidden -> Nat := @ParamRecord.value hidden; get record",
        42,
    );
    returns(
        "#eval (fun (get : ParamRecord hidden -> Nat) => get record) (@ParamRecord.value hidden)",
        42,
    );
}
#[test]
fn multiple_and_captured_parameters_remain_static() {
    returns("#eval (@MultiRecord.mk hidden (hidden + 1) 42).value", 42);
    returns(
        "#eval (fun (n : Nat) => (@MultiRecord.mk (n + hidden) hidden 42).value) 7",
        42,
    );
}
#[test]
fn dependent_proofs_and_polymorphic_carriers_keep_original_types() {
    returns(
        "#eval (@ProofRecord.mk hidden (Eq.refl hidden) 42).value",
        42,
    );
    returns("#eval (@GenericRecord.mk Nat hidden 42).value", 42);
}
#[test]
fn callable_fields_keep_overapplied_arguments_live() {
    returns("#eval callback.apply 41", 42);
    returns("#eval @CallbackRecord.apply hidden callback 41", 42);
    refuses("#eval callback.apply hidden", "hidden");
}
#[test]
fn receivers_fields_and_strict_let_values_still_require_executable_code() {
    for (source, dependency) in [
        ("#eval hiddenRecord.value", "hiddenRecord"),
        ("#eval (@ParamRecord.mk hidden hidden).value", "hidden"),
        (
            "#eval let n : Nat := hidden; (@ParamRecord.mk n 42).value",
            "hidden",
        ),
        (
            "noncomputable section\n#eval hiddenRecord.value\nend",
            "hiddenRecord",
        ),
    ] {
        refuses(source, dependency);
    }
    returns("#eval record.value", 42);
}
#[test]
fn ordinary_projection_shaped_functions_do_not_erase_their_arguments() {
    refuses("#eval ordinary hidden record", "hidden");
    refuses("#eval ParamRecord.lookalike hidden record", "hidden");
}
#[test]
fn definitions_using_generated_fields_are_compiled_without_mutating_the_base() {
    let root = engine().logical_root(&KVMap::new());
    returns("def projected : Nat := record.value\n#eval projected", 42);
    assert!(
        !engine()
            .environment()
            .contains(&Name::from_components(["projected"]))
    );
    assert_eq!(engine().logical_root(&KVMap::new()), root);
}

const HIDDEN_LAYOUTS: &str = r#"
structure LayoutCell (A : Type) where
  value : A
structure LayoutSlot (A : Type) where
  value : Option A
structure LayoutPacket where
  carrier : Type
  value : carrier
  handler : LayoutSlot (carrier -> Nat)
"#;

#[test]
fn projection_only_functions_discover_hidden_container_layouts() {
    returns(
        &format!(
            r#"{HIDDEN_LAYOUTS}
def read (p : LayoutPacket) : Nat := match p.handler.value with
  | .none => 0
  | .some f => f p.value
def packet : LayoutPacket :=
  {{ carrier := Nat, value := 17,
     handler := LayoutSlot.mk (Option.some (fun n => n + 25)) }}
#eval read packet"#
        ),
        42,
    );
}

#[test]
fn nested_parameterized_fields_preserve_hidden_callback_signatures() {
    returns(
        &format!(
            r#"{HIDDEN_LAYOUTS}
structure NestedLayouts where
  carrier : Type
  value : carrier
  handler : LayoutCell (LayoutCell (carrier -> Nat))
def read (p : NestedLayouts) : Nat := p.handler.value.value p.value
def packet : NestedLayouts :=
  {{ carrier := String, value := "abcd",
     handler := LayoutCell.mk (LayoutCell.mk (fun s => s.length + 38)) }}
#eval read packet"#
        ),
        42,
    );
}

#[test]
fn layout_selection_keeps_distinct_specializations_of_the_same_family() {
    returns(
        &format!(
            r#"{HIDDEN_LAYOUTS}
structure MixedLayouts where
  carrier : Type
  value : carrier
  direct : LayoutCell Nat
  indirect : LayoutCell (carrier -> Nat)
def read (p : MixedLayouts) : Nat := p.direct.value + p.indirect.value p.value
def packet : MixedLayouts :=
  {{ carrier := String, value := "abcd", direct := LayoutCell.mk 30,
     indirect := LayoutCell.mk (fun s => s.length + 8) }}
#eval read packet"#
        ),
        42,
    );
}

#[test]
fn hidden_layouts_survive_let_and_captured_lambda_telescope() {
    returns(
        &format!(
            r#"{HIDDEN_LAYOUTS}
def read (p : LayoutPacket) : Nat :=
  let slot : LayoutSlot (p.carrier -> Nat) := p.handler
  (fun (s : LayoutSlot (p.carrier -> Nat)) =>
    match s.value with
    | .none => 0
    | .some f => f p.value) slot
def packet : LayoutPacket :=
  {{ carrier := Nat, value := 17,
     handler := LayoutSlot.mk (Option.some (fun n => n + 25)) }}
#eval read packet"#
        ),
        42,
    );
}

#[test]
fn hidden_layouts_keep_dependent_proof_slots_erased() {
    returns(
        r#"structure CheckedCell (A : Type) where
  value : A
  evidence : value = value
  measure : A -> Nat
structure CheckedLayout where
  carrier : Type
  cell : CheckedCell carrier
def read (p : CheckedLayout) : Nat := p.cell.measure p.cell.value
def packet : CheckedLayout :=
  { carrier := Nat, cell := { value := 40, evidence := rfl, measure := fun n => n + 2 } }
#eval read packet"#,
        42,
    );
}
