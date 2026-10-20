//! Checked alternate bodies and explicit safe replacements keep their authority.
#![forbid(unsafe_code)]
use super::*;
use fln::{
    BinderInfo, CheckerAdmissionGround, Declaration, EngineAdmissionLimits, EngineExecutionLimits,
    Expr, SourceCheckLimits,
};

const PROBE: &str = r#"
def arrayAuthorityRun (xs : Array Nat) (initial : Nat) : Id Nat :=
  Array.forIn' (m := Id) xs initial
    (fun value _ acc => Pure.pure (ForInStep.yield (acc + value)))
-- FLN_EXPECT_NAT 23
#eval arrayAuthorityRun (List.toArray [1, 2, 3]) 17
"#;

fn without_declaration(engine: &Engine, omitted: &Name) -> Environment {
    let original = engine.environment();
    let mut environment = Environment::new();
    for (label, _) in original.constants() {
        if label != omitted {
            environment = environment
                .with_entry(original.entry(label).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in original.extensions() {
        environment = environment
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            environment = environment
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    environment
}

fn changed_checked_definition(engine: &Engine, label: &str) -> Engine {
    let target = name(label);
    let Some(ConstantInfo::Defn(value)) = engine.environment().find(&target) else {
        panic!("the pin supplies a definition for {label}");
    };
    assert_eq!(value.safety, DefinitionSafety::Safe);
    let original_digest = engine.environment().entry(&target).unwrap().digest();
    let mut value = value.clone();
    // Different serialized computational body, same checked type and behavior.
    // Runtime model authority requires exact admitted bytes, not beta equality.
    value.value = Expr::app(
        Expr::lam(
            name("preserveArrayCheckedBody"),
            value.base.type_.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        value.value,
    );
    let admitted = Engine::from_environment(without_declaration(engine, &target))
        .admit_declaration(
            Declaration::Defn(value),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("{label}: changed body passes both checkers: {error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
    );
    assert_ne!(
        admitted
            .engine
            .environment()
            .entry(&target)
            .unwrap()
            .digest(),
        original_digest
    );
    admitted.engine
}

fn refused_after_checks(engine: &Engine, label: &str) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    // Declaration admission does not process #eval. Check the exact definition
    // prefix here, then execute the full unchanged probe with checks below.
    let declarations = PROBE
        .strip_suffix("#eval arrayAuthorityRun (List.toArray [1, 2, 3]) 17\n")
        .expect("the fixed authority probe keeps its exact final evaluation");
    engine
        .check_source_files(
            &[declarations.as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        )
        .unwrap_or_else(|error| panic!("{label}: probe remains well typed: {error:?}"))
        .into_complete()
        .unwrap();
    let error = engine
        .execute_source_commands_with_checks(
            PROBE.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect_err("an altered exact Array dependency must not execute its native adapter");
    let diagnostic = format!("{error:?}");
    assert!(
        diagnostic.contains("Array iteration dependency differs from the exact pinned model"),
        "{label}: {diagnostic}",
    );
    assert_eq!(engine.logical_root(&options), before);
    assert!(!engine.environment().contains(&name("arrayAuthorityRun")));
}

pub(super) fn checked_bodies_and_safe_override(engine: &Engine) {
    super::execution::program(engine, "canonical Array authority control", PROBE, 1);
    for label in ["Array.forIn'", "List.forIn'"] {
        let changed = changed_checked_definition(engine, label);
        refused_after_checks(&changed, label);
    }

    // implemented_by compares the stored interfaces without reducing them.
    // Preserve the pin's Membership.mem application; spelling its reducible
    // Array.Mem body directly is well typed but has a different interface.
    let safe = r#"
universe u v w
def arraySafeReplacement {A : Type u} {B : Type v} {M : Type v -> Type w}
    [Monad M] (xs : Array A) (initial : B)
    (_callback : (x : A) -> x ∈ xs -> B -> M (ForInStep B)) : M B :=
  Pure.pure initial
"#;
    let admitted = engine
        .check_source_files(
            &[safe.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        )
        .expect("the alternate safe implementation is an ordinary admitted definition")
        .into_complete()
        .unwrap();
    let overridden = fln_elab::implemented_by::register(
        admitted.engine.environment(),
        &name("Array.forIn'"),
        &name("arraySafeReplacement"),
    )
    .expect("the safe alternative has the same dependent interface");
    let overridden = Engine::from_environment(overridden);
    assert_eq!(
        fln_elab::implemented_by::ImplementedByTable::read(overridden.environment())
            .unwrap()
            .get(&name("Array.forIn'")),
        Some(&name("arraySafeReplacement")),
    );
    let source = PROBE.replace("-- FLN_EXPECT_NAT 23", "-- FLN_EXPECT_NAT 17");
    super::execution::program(
        &overridden,
        "explicit safe Array replacement executes its own body",
        &source,
        1,
    );
    // Success above does not publish the private adapter or either source probe
    // into the original immutable logical environment.
    assert!(
        !engine
            .environment()
            .contains(&name("_fln_runtime_array_forIn"))
    );
    assert!(!engine.environment().contains(&name("arraySafeReplacement")));
}
