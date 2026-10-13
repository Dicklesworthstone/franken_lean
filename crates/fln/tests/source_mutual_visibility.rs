//! Visibility and documentation must not block native mutual partial declarations.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, Outcome,
    SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(budget()))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn private(module: &str, name: &str) -> Name {
    Name::num(n(&format!("_private.{module}")), 0).append_core(&n(name))
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}
fn run(base: &Engine, source: &str, expected: &str) {
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(budget()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let [execution] = result.executions.as_slice() else {
        panic!("{result:?}")
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{execution:?}")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
}
const DOCUMENTED: &str = r#"
mutual
  /-- This is a real declaration comment, not an ordinary lexer comment. -/
  partial def left (n : Nat) : Nat :=
    if n == 0 then 7 else right (n - 1)

  /-- Keywords `end`, `mutual`, and `partial def` here are not commands. -/
  partial def right (n : Nat) : Nat :=
    if n == 0 then 13 else left (n - 1)
end
"#;
const PRIVATE: &str = r#"module
prelude
namespace Local
mutual
  /-- A private member with a forward reference. -/
  private partial def left (n : Nat) : Nat :=
    if n == 0 then 7 else right (n - 1)
  private partial def right (n : Nat) : Nat :=
    if n == 0 then 13 else left (n - 1)
end
def localUse : Nat := left 5
end Local
"#;
fn module(base: &Engine, source: &str) -> fln::source_check::modules::SourceModuleCheck {
    let name = n("Main");
    base.check_source_modules(
        &[SourceModuleInput {
            name: &name,
            source: source.as_bytes(),
        }],
        &name,
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(budget()))),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
}

#[test]
fn documented_mutual_definitions_execute_without_changing_logical_opacity() {
    let base = engine();
    let compiled = checked(&base, DOCUMENTED);
    run(&compiled, "#eval left 4", "7");
    run(&compiled, "#eval left 5", "13");
    assert!(
        compiled
            .check_source_files(
                &[b"theorem invalid : left 0 = 7 := by rfl"],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
            )
            .is_err()
    );
    run(&base, "#eval 19", "19");
}
#[test]
fn explicit_private_members_resolve_their_peers_inside_the_module() {
    let base = engine();
    let result = module(&base, PRIVATE);
    for member in ["left", "right"] {
        let logical = private("Main", &format!("Local.{member}"));
        assert!(matches!(result.checked.engine.environment().find(&logical),
            Some(ConstantInfo::Opaque(value)) if !value.is_unsafe && value.all.len()==2));
        assert!(
            matches!(result.checked.engine.environment().find(&Name::str(logical.clone(),"_unsafe_rec")),
            Some(ConstantInfo::Defn(value)) if value.safety==DefinitionSafety::Partial)
        );
        assert!(
            !result
                .checked
                .engine
                .environment()
                .contains(&n(&format!("Local.{member}")))
        );
    }
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&private("Main", "Local.localUse"))
    );
    assert!(!base.environment().contains(&private("Main", "Local.left")));
}
#[test]
fn explicit_private_members_capture_section_variables_before_closure() {
    let source = r#"module
prelude
section
variable (base : Nat)
mutual
  private partial def left (n : Nat) : Nat := if n == 0 then base else right (n - 1)
  /-- Documentation must stay attached to its own member. -/
  private partial def right (n : Nat) : Nat := left n
end
end
def result : Nat := left 29 3
"#;
    let result = module(&engine(), source);
    assert!(
        result
            .checked
            .engine
            .environment()
            .contains(&private("Main", "result"))
    );
    let value = result
        .checked
        .engine
        .environment()
        .find(&private("Main", "left"))
        .unwrap();
    let mut ty = &value.constant_val().type_;
    let mut binders = 0;
    while let fln::ExprNode::ForallE { body, .. } = ty.node() {
        binders += 1;
        ty = body;
    }
    assert_eq!(binders, 2);
    assert!(!value.constant_val().type_.has_fvar());
}
#[test]
fn private_mutual_names_do_not_escape_an_import_or_become_public() {
    let base = engine();
    for use_ in [
        "Local.left 0",
        "_private.Lib.0.Local.left 0",
        "_private.Lib.0.Local.left._unsafe_rec 0",
    ] {
        let main = n("Main");
        let lib = n("Lib");
        let source = format!("prelude\nimport Lib\ndef leak : Nat := {use_}");
        assert!(
            base.check_source_modules(
                &[
                    SourceModuleInput {
                        name: &main,
                        source: source.as_bytes()
                    },
                    SourceModuleInput {
                        name: &lib,
                        source: PRIVATE.as_bytes()
                    }
                ],
                &main,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                    budget()
                ))),
            )
            .is_err()
        );
    }
    let main = n("Main");
    let lib = n("Lib");
    assert!(matches!(
        base.check_source_modules(
            &[
                SourceModuleInput {
                    name: &main,
                    source: b"prelude\nimport Lib"
                },
                SourceModuleInput {
                    name: &lib,
                    source: PRIVATE.as_bytes()
                }
            ],
            &main,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
                budget()
            ))),
        )
        .unwrap(),
        Outcome::Complete(_)
    ));
}
#[test]
fn unsupported_modifiers_and_mixed_groups_cannot_be_silently_discarded() {
    let base = engine();
    for source in [
        "mutual\npartial def left : Nat := 7\n/-- not a partial -/\ndef right : Nat := 13\nend",
        "mutual\npartial def left : Nat := 7\nunsafe def right : Nat := 13\nend",
        "mutual\n@[simp] partial def left (n : Nat) : Nat := n\nend",
        "mutual\npartial def left : Nat := 7\nnamespace Hidden\nend\nend",
        "mutual\npartial def left : Nat := 7\naxiom right : Nat\nend",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(EngineAdmissionLimits::new(budget())),
            )
            .is_err(),
            "{source}"
        );
        assert!(!base.environment().contains(&n("left")));
    }
    checked(&base, "def recovered : Nat := 19");
}
