//! Defaults produce ordinary helper applications checked by K1 and the council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};
use fln_core::name::Name;
use fln_elab::records::defaults::{RecordDefault, RecordDefaults, helper_name, register_defaults};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(e: &Engine, text: &str) -> fln::SourceFileCheck {
    let result = e.check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{text}\n{result:?}"
    );
    result.unwrap().into_complete().unwrap()
}

#[test]
fn omitted_defaults_use_actual_preceding_values_and_updates_preserve_copies() {
    check(
        &engine(),
        "structure Config where\n  base : Nat := 3\n  twice : Nat := base + base\n  transform (x : Nat) : Nat := x + twice\ndef standard : Config := {}\ndef custom : Config := { base := 7 }\ndef copied := { custom with base := 20 }\ntheorem a : standard.twice = 6 := by rfl\ntheorem b : custom.twice = 14 := by rfl\ntheorem c : copied.twice = 14 := by rfl\ntheorem d : custom.transform 2 = 16 := by rfl\ntheorem e : copied.transform 2 = 16 := by rfl",
    );
}
#[test]
fn dependent_types_proofs_and_method_parameters_are_closed_in_order() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type := Nat\n  value : carrier\n  copy : carrier := value\n  proof : value = value := rfl\n  ident (x : carrier) : carrier := x\ndef p : Package := { value := 9 }\ndef q : Package := { carrier := String, value := \"hi\" }\ntheorem p_ok : p.copy = 9 := by rfl\ntheorem q_ok : q.ident q.copy = \"hi\" := by rfl",
    );
}
#[test]
fn defaults_use_explicit_record_instance_parameters() {
    check(
        &engine(),
        "structure Box (A : Type) [Inhabited A] where\n  value : A := default\ndef make {A : Type} [Inhabited A] : Box A := {}\ninstance chosen : Inhabited Nat := Inhabited.mk 17\ndef b : Box Nat := {}\ntheorem ok : b.value = 17 := by rfl",
    );
}
#[test]
fn class_dictionaries_can_be_constructed_entirely_from_defaults() {
    check(
        &engine(),
        "class Config where\n  value : Nat := 7\n  twice : Nat := value + value\ninstance automatic : Config := {}\ndef result : Nat := Config.twice\ntheorem ok : result = 14 := by rfl\ndef explicit : Config := { value := 11 }\ntheorem other : explicit.twice = 22 := by rfl",
    );
}
#[test]
fn nested_record_literals_and_let_defaults_are_elaborated_natively() {
    check(
        &engine(),
        "structure Inner where\n  value : Nat := 8\nstructure Outer where\n  inner : Inner := {}\n  num : Nat := let n := inner.value; n + 1\ndef result : Outer := {}\ntheorem ok : result.num = 9 := by rfl",
    );
}
#[test]
fn invalid_defaults_are_rejected_even_when_never_used() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for text in [
        "structure Bad where\n  value : Nat := \"wrong\"",
        "structure Bad where\n  carrier : Type\n  value : carrier := 7",
        "structure Bad where\n  value : Nat := (1 : String)",
        "structure Bad where\n  value : Nat := let unused := (1 : String); 0",
    ] {
        let refusal = e
            .check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err("invalid default is not optional evidence");
        assert_eq!(
            refusal.disposition(),
            ("kernel-rejection", true, 1),
            "{text}: {refusal:?}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn forward_defaults_missing_required_fields_and_unresolved_values_refuse() {
    let e = engine();
    let root = e.logical_root(&KVMap::new());
    for text in [
        "structure Bad where\n  x : Nat := later\n  later : Nat := 3",
        "structure Bad where\n  x : Nat := _",
        "structure Bad where\n  x : Nat := x",
        "structure Needs where\n  first : Nat\n  second : Nat := first\ndef incomplete : Needs := {}",
    ] {
        assert!(
            e.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(e.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn helper_like_names_do_not_register_defaults() {
    let e = check(
        &engine(),
        "structure Plain where\n  value : Nat\ndef Plain.value._default : Nat := 91",
    )
    .engine;
    assert!(
        e.check_source_files(
            &[b"def absent : Plain := {}"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    check(&e, "def explicit : Plain := { value := 4 }");
}
#[test]
fn helper_collision_leaves_no_record_projection_or_registration_prefix() {
    let e = check(&engine(), "def Clash.value._default : Nat := 5").engine;
    let root = e.logical_root(&KVMap::new());
    assert!(
        e.check_source_files(
            &[b"structure Clash where\n  value : Nat := 7"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
    assert_eq!(e.logical_root(&KVMap::new()), root);
    assert!(!e.environment().contains(&Name::from_components(["Clash"])));
    assert!(
        RecordDefaults::read(e.environment())
            .unwrap()
            .helper(&Name::from_components(["Clash"]), 0)
            .is_none()
    );
}
#[test]
fn registration_checks_helper_signatures_and_rejects_duplicates_atomically() {
    let e = check(&engine(), "structure Good where\n  value : Nat := 8\nstructure Wrong where\n  value : Nat\ndef Wrong.value._default : String := \"not Nat\"").engine;
    let root = e.logical_root(&KVMap::new());
    let row = |name: &str| {
        let record = Name::from_components([name]);
        RecordDefault {
            helper: helper_name(&record, &Name::from_components(["value"])),
            record,
            field: 0,
        }
    };
    assert!(register_defaults(e.environment(), &[row("Good")]).is_err());
    assert!(register_defaults(e.environment(), &[row("Wrong")]).is_err());
    assert_eq!(e.logical_root(&KVMap::new()), root);
}
#[test]
fn ordered_files_share_only_successful_default_registrations() {
    let e = engine();
    let prefix = b"structure Count where\n  value : Nat := 23";
    let good = b"def n : Count := {}\ntheorem ok : n.value = 23 := by rfl";
    let bad = b"def n : Count := {}\ntheorem wrong : n.value = 24 := by rfl";
    for (suffix, success) in [
        (good.as_slice(), true),
        (bad.as_slice(), false),
        (good.as_slice(), true),
    ] {
        let result = e.check_source_files(
            &[prefix, suffix],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert_eq!(
            matches!(result, Ok(Outcome::Complete(_))),
            success,
            "{result:?}"
        );
    }
}

#[test]
fn admission_root_includes_the_default_registration_and_helpers() {
    let e = engine();
    let result = e
        .admit_source_command(
            b"structure Count where\n  value : Nat := 23",
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.base_logical_root, e.logical_root(&KVMap::new()));
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&KVMap::new())
    );
    assert_ne!(
        result.result_logical_root,
        result.admissions.last().unwrap().result_logical_root
    );
    let record = Name::from_components(["Count"]);
    let helper = helper_name(&record, &Name::from_components(["value"]));
    assert_eq!(
        RecordDefaults::read(result.engine.environment())
            .unwrap()
            .helper(&record, 0),
        Some(&helper)
    );
    assert!(result.engine.environment().contains(&helper));
    assert_eq!(result.admissions.len(), 3);
}
