//! Pattern-matrix copies of one local partial declaration share a checked
//! closure without sharing the branch's captured values. Positive fixtures and
//! group shapes were checked against Lean 8c9756b28d64dab099da31a4c09229a9e6a2ef35.
#![forbid(unsafe_code)]

use fln::{
    BinderInfo, Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, ExprNode, KVMap,
    Name, SourceCheckLimits, VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::OnceLock;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    static SEED: OnceLock<Engine> = OnceLock::new();
    SEED.get_or_init(|| {
        Engine::with_source_seed(limits())
            .unwrap()
            .into_complete()
            .unwrap()
    })
    .clone()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("both checkers completed")
    .engine
}

fn values(base: &Engine, source: &str) -> Vec<String> {
    let batch = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completed");
    batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &batch.executions[index].exit else {
                panic!("expected a returned Nat: {:?}", batch.executions[index]);
            };
            fln_vm::interpreter::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

fn helper_inventory(engine: &Engine, owner: &str, expected: &[&str]) {
    let prefix = format!("{owner}.");
    let mut actual: Vec<_> = engine
        .environment()
        .constants()
        .map(|(name, _)| name.to_display_string())
        .filter(|name| name.starts_with(&prefix))
        .collect();
    actual.sort();
    let mut expected = expected.to_vec();
    expected.sort();
    assert_eq!(actual, expected, "{owner}: one published local closure");
}

fn ordinary_owner(engine: &Engine, owner: &str) {
    assert!(matches!(
        engine.environment().find(&name(owner)),
        Some(ConstantInfo::Defn(definition)) if definition.safety == DefinitionSafety::Safe
    ));
    assert!(
        !engine
            .environment()
            .contains(&name(&format!("{owner}._unsafe_rec")))
    );
}

fn partial_group(engine: &Engine, members: &[&str]) {
    let logical: Vec<_> = members.iter().map(|member| name(member)).collect();
    let executable: Vec<_> = logical
        .iter()
        .map(|member| Name::str(member.clone(), "_unsafe_rec"))
        .collect();
    for (member, companion) in logical.iter().zip(&executable) {
        let Some(ConstantInfo::Opaque(header)) = engine.environment().find(member) else {
            panic!("missing checked opaque interface {member:?}");
        };
        let Some(ConstantInfo::Defn(body)) = engine.environment().find(companion) else {
            panic!("missing checked partial implementation {companion:?}");
        };
        assert!(!header.is_unsafe);
        assert_eq!(header.all, logical);
        assert_eq!(body.safety, DefinitionSafety::Partial);
        assert_eq!(body.all, executable);
        assert_eq!(body.base.type_, header.base.type_);
        assert_eq!(body.base.level_params, header.base.level_params);
    }
}

fn binder_shapes(engine: &Engine, declaration: &str, expected: &[(&str, &str)]) {
    let info = engine.environment().find(&name(declaration)).unwrap();
    let mut type_ = &info.constant_val().type_;
    for (binder, domain) in expected {
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            body,
            ..
        } = type_.node()
        else {
            panic!("missing capture in {declaration}");
        };
        assert_eq!(
            binder_name,
            &name(binder),
            "{declaration}: source capture name"
        );
        assert_eq!(*binder_info, BinderInfo::Default);
        assert!(
            matches!(binder_type.node(), ExprNode::Const { name: actual, levels }
            if actual == &name(domain) && levels.is_empty())
        );
        type_ = body;
    }
    assert!(
        matches!(type_.node(), ExprNode::Const { name: actual, levels }
        if actual == &name("Nat") && levels.is_empty())
    );
}

fn refuses(base: &Engine, source: &str, owner: &str) {
    let before = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err(),
        "accepted {source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
    assert!(!base.environment().contains(&name(owner)));
    assert!(
        !base
            .environment()
            .contains(&name(&format!("{owner}._unsafe_rec")))
    );
}

const SIMPLE: &str = r#"
partial def choose (a b : Bool) (target : Nat) : Nat :=
  match a, b with
  | true, true => 99
  | _, _ =>
    let rec loop (i : Nat) : Nat :=
      if i == target then 42 else loop (i + 1)
    loop 0
"#;

const CAPTURED: &str = r#"
inductive Packet where
  | item (tag : Bool) (payload : Nat)
  | empty
partial def withPayload (packet : Packet) (canonicalOnly : Bool) : Nat :=
  match packet, canonicalOnly with
  | .item true _, true => 99
  | .item _ payload, _ =>
    let rec loop (i : Nat) : Nat :=
      if i == payload then
        if canonicalOnly then Nat.add i 100 else Nat.add i 200
      else loop (i + 1)
    loop 0
  | _, _ => 0
partial def cyclicFallback (packet : Packet) (canonicalOnly : Bool) : Nat :=
  match packet, canonicalOnly with
  | .item true value, true => value
  | .item _ payload, _ =>
    let rec loop (i : Nat) : Nat :=
      if i == payload then
        cyclicFallback (.item true (if canonicalOnly then Nat.add i 100 else Nat.add i 200)) true
      else loop (i + 1)
    loop 0
  | _, _ => 0
"#;

#[test]
fn repeated_wildcard_fallback_publishes_one_local_partial_closure() {
    let base = seed();
    let before = base.logical_root(&KVMap::new());
    let result = checked(&base, SIMPLE);
    ordinary_owner(&result, "choose");
    helper_inventory(
        &result,
        "choose",
        &["choose.loop", "choose.loop._unsafe_rec"],
    );
    partial_group(&result, &["choose.loop"]);
    binder_shapes(&result, "choose.loop", &[("target", "Nat"), ("i", "Nat")]);
    assert_eq!(
        values(
            &result,
            "#eval choose true true 3\n#eval choose true false 3\n#eval choose false true 4\n#eval choose false false 5"
        ),
        ["99", "42", "42", "42"]
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn nested_fallback_captures_each_branch_and_keeps_owner_helper_cycles_complete() {
    let result = checked(&seed(), CAPTURED);
    ordinary_owner(&result, "withPayload");
    helper_inventory(
        &result,
        "withPayload",
        &["withPayload.loop", "withPayload.loop._unsafe_rec"],
    );
    partial_group(&result, &["withPayload.loop"]);
    binder_shapes(
        &result,
        "withPayload.loop",
        &[("canonicalOnly", "Bool"), ("payload", "Nat"), ("i", "Nat")],
    );
    helper_inventory(
        &result,
        "cyclicFallback",
        &[
            "cyclicFallback._unsafe_rec",
            "cyclicFallback.loop",
            "cyclicFallback.loop._unsafe_rec",
        ],
    );
    partial_group(&result, &["cyclicFallback.loop", "cyclicFallback"]);
    binder_shapes(
        &result,
        "cyclicFallback.loop",
        &[("canonicalOnly", "Bool"), ("payload", "Nat"), ("i", "Nat")],
    );
    assert_eq!(
        values(
            &result,
            r#"
#eval withPayload (.item true 3) true
#eval withPayload (.item true 3) false
#eval withPayload (.item false 4) true
#eval withPayload (.item false 5) false
#eval withPayload .empty true
#eval withPayload .empty false
#eval cyclicFallback (.item true 3) true
#eval cyclicFallback (.item true 3) false
#eval cyclicFallback (.item false 4) true
#eval cyclicFallback (.item false 5) false
#eval cyclicFallback .empty true
#eval cyclicFallback .empty false
"#
        ),
        [
            "99", "203", "104", "205", "0", "0", "3", "203", "104", "205", "0", "0"
        ]
    );
}

#[test]
fn fallback_closure_names_are_deterministic_and_real_collisions_remain_atomic() {
    let base = seed();
    let source = format!("{SIMPLE}\n{CAPTURED}");
    let first = checked(&base, &source);
    let second = checked(&base, &source);
    assert_eq!(
        first.logical_root(&KVMap::new()),
        second.logical_root(&KVMap::new())
    );
    for (label, value) in first.environment().constants() {
        assert_eq!(second.environment().find(label), Some(value));
    }
    for collision in ["choose.loop", "choose.loop._unsafe_rec"] {
        let occupied = checked(&base, &format!("def {collision} (n : Nat) : Nat := n"));
        refuses(&occupied, SIMPLE, "choose");
        assert_eq!(values(&occupied, &format!("#eval {collision} 42")), ["42"]);
    }
    // Two written declarations have different source sites. Matching bodies
    // cannot authorize their reuse as one exported helper in this bounded path.
    refuses(
        &base,
        r#"
partial def writtenTwice (a : Bool) (target : Nat) : Nat :=
  match a with
  | true =>
    let rec loop (i : Nat) : Nat :=
      if i == target then 42 else loop (i + 1)
    loop 0
  | false =>
    let rec loop (i : Nat) : Nat :=
      if i == target then 42 else loop (i + 1)
    loop 0
"#,
        "writtenTwice",
    );
    assert_eq!(values(&first, "#eval choose false false 3"), ["42"]);
}
