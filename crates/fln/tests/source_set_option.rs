//! `set_option` through the source path (bead `fln-set-option-t69b`): admitted only through the
//! option table, scoped as the pin scopes it, and refused by name otherwise.
//!
//! The verdicts are the pinned v4.32.0's on the same shapes, with Init's own `Monad` and
//! `MonadLiftT` in place of the seed classes below: inside `section … set_option autoLift false`
//! and under `set_option autoLift false in`, a bind that needs a lift is a `Type mismatch`; after
//! `end`, and for the command after the `in` one, it is accepted. `Unknown option `foo.bar`` and
//! `set_option value type mismatch` are errors there too.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, SourceCheckLimits, VmExit,
};

const CLASSES: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class MonadLiftT (m n : Type -> Type) where
  monadLift : {A : Type} -> m A -> n A
def liftM {m n : Type -> Type} [inst : MonadLiftT m n] {A : Type} (x : m A) : n A := @MonadLiftT.monadLift m n inst A x
"#;

/// A bind of an `M` action in an `N` block: accepted only through an inserted lift.
const LIFTED: &str = "def lifted {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] {A : Type} (action : M A) : N A := do\n  let x ← action\n  return x\n";

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn seed() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn run(base: &Engine, source: &str) -> Result<fln::SourceFileCheck, String> {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .map_err(|error| error.to_string())?
        .into_complete()
        .map_err(|outcome| format!("{outcome:?}"))
}

fn lift_definition(body: &str) -> String {
    format!(
        "def lifted {{M N : Type -> Type}} [Pure N] [Bind N] [MonadLiftT M N] \
         {{A : Type}} (action : M A) : N A := {body}\n"
    )
}

fn elaboration_refusal(base: &Engine, source: &str) -> String {
    let root = base.logical_root(&KVMap::new());
    let result = base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits());
    let error = result.expect_err("the scoped option must refuse this source");
    assert_eq!(error.disposition(), ("elaboration", false, 1), "{error:?}");
    assert_eq!(base.logical_root(&KVMap::new()), root);
    error.to_string()
}

#[test]
fn an_honored_option_changes_elaboration_and_ends_with_its_scope() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    // The control: the lift is inserted by default.
    run(&base, LIFTED).unwrap();
    let off = format!("section\nset_option autoLift false\n{LIFTED}end\n");
    assert!(run(&base, &off).is_err(), "{off}");
    let ended = format!("section\nset_option autoLift false\nend\n{LIFTED}");
    run(&base, &ended).unwrap();
    let only_in = format!("set_option autoLift false in\n{LIFTED}");
    assert!(run(&base, &only_in).is_err(), "{only_in}");
    let next = format!("set_option autoLift false in\ndef other : Nat := 1\n{LIFTED}");
    run(&base, &next).unwrap();
    // Set back to the default inside the scope, the lift returns.
    let restored =
        format!("section\nset_option autoLift false\nset_option autoLift true\n{LIFTED}end\n");
    run(&base, &restored).unwrap();
}

#[test]
fn term_options_control_actual_lifting_and_restore_the_surrounding_expression() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    let enabled = lift_definition("set_option autoLift true in do\n  let x ← action\n  return x");
    run(&base, &format!("set_option autoLift false\n{enabled}")).unwrap();
    let disabled = lift_definition("set_option autoLift false in do\n  let x ← action\n  return x");
    elaboration_refusal(&base, &disabled);

    let nested = lift_definition(
        "set_option autoLift false in\n  set_option autoLift true in do\n    let x ← action\n    return x",
    );
    run(&base, &nested).unwrap();

    // A successful override must end before a later expression in this very
    // definition, not merely before the next command is elaborated.
    let later = lift_definition(
        "let enabled : N A := (set_option autoLift true in do { let x ← action; return x }); do { let x ← action; return x }",
    );
    elaboration_refusal(&base, &format!("set_option autoLift false\n{later}"));
    run(&base, LIFTED).unwrap();
}

#[test]
fn tactic_options_control_lifting_and_restore_after_failed_alternatives() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    let enabled = lift_definition(
        "by\n  set_option autoLift true in\n    exact do\n      let x ← action\n      return x",
    );
    run(&base, &format!("set_option autoLift false\n{enabled}")).unwrap();
    let disabled = lift_definition(
        "by\n  set_option autoLift false in\n    exact do\n      let x ← action\n      return x",
    );
    elaboration_refusal(&base, &disabled);

    let retried = lift_definition(
        "by\n  first\n  | set_option autoLift false in\n      exact do\n        let x ← action\n        return x\n  | exact do\n      let x ← action\n      return x",
    );
    run(&base, &retried).unwrap();
    let nested = lift_definition(
        "by\n  set_option autoLift false in\n    set_option autoLift true in\n      exact do\n        let x ← action\n        return x",
    );
    run(&base, &nested).unwrap();

    // A wrong value type for a known option is an ordinary elaboration
    // failure, so the surrounding tactic alternative may recover from it.
    for source in [
        "theorem recovered : 1 = 1 := by\n  first\n  | set_option autoLift 1 in rfl\n  | rfl",
        "theorem recovered : 1 = 1 := by\n  rfl\n  first\n  | set_option autoLift 1 in skip\n  | skip",
        "theorem recovered : 1 = 1 := by\n  rfl\n  try set_option autoLift 1 in skip\n  skip",
    ] {
        run(&base, source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
    // Refusals for options outside this implementation's admitted policy
    // stay visible even when a later tactic alternative would succeed.
    for (option, name) in [("foo.bar true", "`foo.bar`"), ("pp.all true", "`pp.all`")] {
        let source = format!(
            "theorem refused : 1 = 1 := by\n  first\n  | set_option {option} in rfl\n  | rfl"
        );
        let error = elaboration_refusal(&base, &source);
        assert!(error.contains(name), "{source}\n{error}");
    }
}

#[test]
fn postponed_callbacks_keep_the_options_at_their_creation_site() {
    let base = run(
        &seed(),
        &format!("{CLASSES}\ndef applyLater {{A B : Type}} (f : A -> B) (x : A) : B := f x"),
    )
    .unwrap()
    .engine;
    // The partial application leaves f's type unknown until its final
    // argument, outside the option wrapper, has been checked. Its callback
    // must resume under the options where it was first elaborated.
    let enabled = "(set_option autoLift true in applyLater (fun f => do { let x ← f action; return x })) (fun (x : M A) => x)";
    run(
        &base,
        &format!("set_option autoLift false\n{}", lift_definition(enabled)),
    )
    .unwrap();
    let disabled = lift_definition(
        "(set_option autoLift false in applyLater (fun f => do { let x ← f action; return x })) (fun (x : M A) => x)",
    );
    elaboration_refusal(&base, &disabled);

    // Resuming a saved callback must also restore the caller's options when
    // it finishes, before another expression is elaborated.
    let later = lift_definition(&format!(
        "let enabled : N A := {enabled}; do {{ let x ← action; return x }}"
    ));
    elaboration_refusal(&base, &format!("set_option autoLift false\n{later}"));
}

#[test]
fn postponed_eliminators_keep_options_until_their_motive_is_known() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    let recursor =
        "Nat.rec (let lifted : N A := (do { let x ← action; return x }); 0) (fun _ ih => ih) 0";
    let theorem = |body: &str| {
        format!(
            "theorem liftedResult {{M N : Type -> Type}} [Pure N] [Bind N] [MonadLiftT M N] \
             {{A : Type}} (action : M A) : ({body}) = (0 : Nat) := by rfl"
        )
    };
    // The checked let in the minor premise requires an actual monad lift.
    // Establish that this delayed recursor succeeds precisely when lifting
    // is enabled, before testing opposite options in a smaller scope.
    run(&base, &theorem(recursor)).unwrap();
    elaboration_refusal(
        &base,
        &format!("set_option autoLift false\n{}", theorem(recursor)),
    );
    // The left side of equality has no expected type. The recursor waits for
    // the right side to determine its motive, after its option region closes.
    run(
        &base,
        &format!(
            "set_option autoLift false\n{}",
            theorem(&format!("set_option autoLift true in {recursor}"))
        ),
    )
    .unwrap();
    elaboration_refusal(
        &base,
        &theorem(&format!("set_option autoLift false in {recursor}")),
    );
}

#[test]
fn tactic_options_apply_to_all_goals_and_restore_before_the_next_tactic() {
    let base = run(
        &seed(),
        &format!("{CLASSES}\ninductive Pair (A : Type) where | mk (left : A) (right : A)"),
    )
    .unwrap()
    .engine;
    let header = "set_option autoLift false\ndef liftedPair {M N : Type -> Type} [Pure N] [Bind N] [MonadLiftT M N] {A : Type} (action : M A) : Pair (N A) := by\n  constructor\n";
    let all = format!(
        "{header}  set_option autoLift true in\n    all_goals\n      exact do\n        let x ← action\n        return x"
    );
    run(&base, &all).unwrap();

    // The option wrapper may solve one goal while leaving its sibling to the
    // surrounding tactic sequence. That sibling sees the original false.
    let leaked = format!(
        "{header}  set_option autoLift true in\n    exact do\n      let x ← action\n      return x\n  exact do\n    let x ← action\n    return x"
    );
    elaboration_refusal(&base, &leaked);
    let explicit = format!(
        "{header}  set_option autoLift true in\n    exact do\n      let x ← action\n      return x\n  exact liftM action"
    );
    run(&base, &explicit).unwrap();
}

#[test]
fn queued_case_bodies_run_before_the_following_option() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    let declaration = |body: &str| {
        format!(
            "def branches {{M N : Type -> Type}} [Pure N] [Bind N] [MonadLiftT M N] \
             {{A : Type}} (flag : Bool) (action : M A) : N A := by\n{body}"
        )
    };
    for branches in [
        "  cases flag with\n  | false => exact do { let x ← action; return x }\n  | true => exact do { let x ← action; return x }\n",
        "  exact match flag with\n    | false => do { let x ← action; return x }\n    | true => do { let x ← action; return x }\n",
    ] {
        let accepted = declaration(&format!("{branches}  set_option autoLift false in skip"));
        run(&base, &accepted).unwrap_or_else(|error| panic!("{accepted}\n{error}"));
        let refused = declaration(&format!("{branches}  set_option autoLift true in skip"));
        elaboration_refusal(&base, &format!("set_option autoLift false\n{refused}"));
    }
}

#[test]
fn scoped_options_at_the_start_of_case_scripts_stay_in_their_branch() {
    let base = run(&seed(), CLASSES).unwrap().engine;
    let declaration = |true_branch: &str| {
        let body = format!(
            "  cases flag with\n  | false => set_option autoLift true in exact do {{ let x ← action; return x }}\n  | true => {true_branch}"
        );
        format!(
            "set_option autoLift false\n\
             def branches {{M N : Type -> Type}} [Pure N] [Bind N] [MonadLiftT M N] \
             {{A : Type}} (flag : Bool) (action : M A) : N A := by\n{body}"
        )
    };
    run(
        &base,
        &declaration("set_option autoLift true in exact do { let x ← action; return x }"),
    )
    .unwrap();
    elaboration_refusal(&base, &declaration("exact do { let x ← action; return x }"));
}

#[test]
fn option_wrappers_return_unsolved_goals_and_allow_goal_free_bodies() {
    let base = seed();
    for source in [
        "theorem identity (P : Prop) : P -> P := by\n  set_option autoLift false in\n    intro p\n  exact p",
        "theorem identity (P : Prop) : P -> P := by\n  set_option autoLift false in skip\n  intro p\n  exact p",
        "theorem completeProof : 1 = 1 := by\n  rfl\n  set_option autoLift false in skip",
        "theorem completeProof : 1 = 1 := by\n  rfl\n  set_option autoLift false in all_goals rfl",
        "theorem completeProof : 1 = 1 := by\n  rfl\n  set_option autoLift false in\n    set_option autoLift true in skip",
        "theorem completeProof : 1 = 1 := by\n  rfl\n  set_option autoLift false in all_goals set_option foo.bar true in rfl",
    ] {
        run(&base, source).unwrap_or_else(|error| panic!("{source}\n{error}"));
    }
    elaboration_refusal(
        &base,
        "theorem unfinished (P : Prop) : P := by\n  set_option autoLift false in skip",
    );
    elaboration_refusal(
        &base,
        "theorem falseProof : 1 = 2 := by\n  set_option autoLift false in rfl",
    );
    elaboration_refusal(
        &base,
        "theorem completeProof : 1 = 1 := by\n  rfl\n  set_option autoLift false in rfl",
    );
}

#[test]
fn term_and_tactic_option_refusals_are_named_and_atomic_even_after_goals_close() {
    let base = seed();
    for (option, named) in [
        ("foo.bar true", "`foo.bar`"),
        ("maxHeartbeats true", "`maxHeartbeats`"),
        ("autoLift 1", "`autoLift`"),
        ("pp.all true", "`pp.all`"),
        ("maxHeartbeats 1000", "`maxHeartbeats`"),
    ] {
        for source in [
            format!("def value : Nat := set_option {option} in 1"),
            format!("theorem same : 1 = 1 := by\n  set_option {option} in rfl"),
            format!("theorem same : 1 = 1 := by\n  rfl\n  set_option {option} in skip"),
        ] {
            let error = elaboration_refusal(&base, &source);
            assert!(error.contains(named), "{source}\n{error}");
        }
    }
    run(&base, "theorem recovered : 1 = 1 := by rfl").unwrap();
}

#[test]
fn silenced_and_inert_options_are_admitted_and_change_nothing() {
    let base = seed();
    let plain = "def x : Nat := 1\ntheorem t : x = 1 := rfl\n";
    let with_options = format!(
        "set_option linter.unusedVariables false\nset_option warn.sorry false\n\
         set_option maxHeartbeats 400000\nset_option autoImplicit false\n\
         set_option pp.all false\nset_option maxRecDepth 2048\n\
         set_option linter.omit false\nset_option linter.unusedSectionVars false\n{plain}"
    );
    let checked = run(&base, &with_options).unwrap();
    assert_eq!(
        checked.result_logical_root,
        run(&base, plain).unwrap().result_logical_root
    );
    assert_eq!(checked.theorems, 1);
}

#[test]
fn unknown_mistyped_and_unimplemented_options_are_refused_by_name() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    for (source, named) in [
        ("set_option foo.bar true", "`foo.bar`"),
        ("set_option maxHeartbeats true", "`maxHeartbeats`"),
        ("set_option autoLift 1", "`autoLift`"),
        ("set_option pp.all true", "`pp.all`"),
        ("set_option maxHeartbeats 1000", "`maxHeartbeats`"),
        ("set_option linter.missingDocs true", "`linter.missingDocs`"),
        (
            "set_option trace.Meta.synthInstance true",
            "`trace.Meta.synthInstance`",
        ),
        ("set_option pp.all true in\ndef x : Nat := 1", "`pp.all`"),
    ] {
        let error = run(&base, &format!("{source}\ndef y : Nat := 2\n")).unwrap_err();
        assert!(error.contains(named), "{source}: {error}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn options_reach_golem_through_the_execution_path() {
    let run = |source: &str| {
        seed()
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap()
    };
    for source in [
        "set_option linter.unusedVariables false\n#eval 6 * 7\n",
        "set_option maxHeartbeats 400000 in\n#eval 6 * 7\n",
        "section\nset_option maxHeartbeats 0\n#eval 6 * 7\nend\n",
    ] {
        let execution = run(source);
        let VmExit::Returned(value) = &execution.executions.last().unwrap().exit else {
            panic!("{source}: Golem did not return");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some("42"),
            "{source}"
        );
    }
    let refused = seed().execute_source_definitions(
        &[b"set_option pp.all true in\n#eval 6 * 7\n"],
        &KVMap::new(),
        EngineExecutionLimits::new(limits().admission.kernel),
    );
    assert!(format!("{refused:?}").contains("pp.all"), "{refused:?}");
}
