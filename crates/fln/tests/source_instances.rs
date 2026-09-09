//! Source -> native instance search -> both ordinary checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_env::constants::ConstantInfo;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}
fn has_constant(expr: &Expr, name: &Name) -> bool {
    let mut pending = vec![expr];
    while let Some(term) = pending.pop() {
        match term.node() {
            ExprNode::Const { name: n, .. } if n == name => return true,
            ExprNode::App { f, a } => {
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(body);
                pending.push(binder_type);
            }
            _ => {}
        }
    }
    false
}
#[test]
fn scalar_default_instances_are_real_checked_values() {
    checked(
        &engine(),
        r#"theorem natDefault : default = 0 := by rfl
theorem stringDefault : default = "" := by rfl
theorem boolDefault : default = false := by rfl"#,
    );
}
#[test]
fn source_instance_binders_feed_calls_after_explicit_argument_inference() {
    checked(
        &engine(),
        "def choose {A : Type} [i : Inhabited A] (x : A) : A := default\ndef nested {A : Type} [Inhabited A] (x : A) : A := choose x",
    );
}
#[test]
fn newest_local_instance_wins_without_using_the_global_default() {
    let result = checked(
        &engine(),
        "def pick [first : Inhabited Nat] [second : Inhabited Nat] : Nat := default",
    );
    let Some(ConstantInfo::Defn(def)) = result.environment().find(&n("pick")) else {
        panic!("definition");
    };
    let mut value = &def.value;
    for _ in 0..2 {
        let ExprNode::Lam { body, .. } = value.node() else {
            panic!("lambda")
        };
        value = body;
    }
    let ExprNode::App { a, .. } = value.node() else {
        panic!("instance application")
    };
    assert!(matches!(a.node(), ExprNode::BVar { idx: 0 }));
    assert!(!has_constant(&def.value, &n("instInhabitedNat")));
}
#[test]
fn an_ordinary_hypothesis_does_not_become_an_instance() {
    checked(
        &engine(),
        "theorem ordinary (i : Inhabited Nat) : default = 0 := by rfl",
    );
    assert!(
        engine()
            .check_source_files(
                &[b"theorem wrong [i : Inhabited Nat] : default = 0 := by rfl"],
                &KVMap::new(),
                limits()
            )
            .is_err()
    );
}
#[test]
fn nonclasses_and_missing_instances_are_visible_refusals() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for text in [
        "def bad [i : Nat] : Nat := i",
        "def missing (A : Type) : A := default",
        "def bad [i : Inhabited Nat -> Inhabited Nat] : Nat := 0",
    ] {
        assert!(
            base.check_source_files(&[text.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{text}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}
#[test]
fn registered_globals_are_priority_ordered_and_snapshot_local() {
    let base = checked(
        &engine(),
        "def seven : Inhabited Nat := Inhabited.mk 7\ndef nine : Inhabited Nat := Inhabited.mk 9",
    );
    let first =
        fln_elab::instances::register_instance(base.environment(), &n("seven"), 2000).unwrap();
    let second = fln_elab::instances::register_instance(&first, &n("nine"), 3000).unwrap();
    checked(
        &Engine::from_environment(first),
        "theorem picked : default = 7 := by rfl",
    );
    checked(
        &Engine::from_environment(second),
        "theorem picked : default = 9 := by rfl",
    );
    checked(&base, "theorem original : default = 0 := by rfl");
}
#[test]
fn failed_recursive_candidate_tries_the_next_global_without_state_leaks() {
    let base = checked(
        &engine(),
        "def recursive {A : Type} [i : Inhabited A] : Inhabited A := i",
    );
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("recursive"), 2000).unwrap();
    checked(
        &Engine::from_environment(env),
        "theorem fallback : default = 0 := by rfl",
    );
}
#[test]
fn recursive_instance_dependencies_are_synthesized() {
    let base = checked(
        &engine(),
        "def functionDefault {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)",
    );
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("functionDefault"), 2000)
            .unwrap();
    checked(
        &Engine::from_environment(env),
        "def use : Nat -> Nat := default\ntheorem actual : use 123 = 0 := by rfl",
    );
}
#[test]
fn class_metadata_participates_in_logical_roots() {
    let base = checked(&engine(), "def seven : Inhabited Nat := Inhabited.mk 7");
    let env =
        fln_elab::instances::register_instance(base.environment(), &n("seven"), 2000).unwrap();
    assert_ne!(
        base.logical_root(&KVMap::new()),
        env.logical_root(&KVMap::new())
    );
    assert!(fln_elab::instances::register_instance(&env, &n("seven"), 3000).is_err());
}
#[test]
fn instance_binder_syntax_preserves_original_source_bytes() {
    for source in [
        "def f {A : Type} [i : Inhabited A] (x : A) : A := default",
        "def f [Inhabited Nat] : Nat := default",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}
#[test]
fn instance_source_does_not_turn_kernel_exhaustion_into_rejection() {
    let base = engine();
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    let result = base.check_source_files(&[b"def f : Nat := default"], &KVMap::new(), low);
    assert!(
        matches!(result, Ok(Outcome::Inconclusive(_)))
            || result
                .as_ref()
                .is_err_and(|error| error.disposition().2 == 3)
    );
}

#[test]
fn source_instance_registration_is_visible_to_later_commands_and_files() {
    let base = engine();
    let result = base
        .check_source_files(
            &[
                b"instance seven : Inhabited Nat := Inhabited.mk 7",
                b"theorem observed : default = 7 := by rfl",
            ],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.commands, 2);
    assert_ne!(result.base_logical_root, result.result_logical_root);
    let rows = fln_elab::instances::InstanceRegistry::read(result.engine.environment()).unwrap();
    assert_eq!(rows.candidates(&n("Inhabited"))[0].declaration, n("seven"));
    checked(&base, "theorem unchanged : default = 0 := by rfl");
}

#[test]
fn source_instance_priority_and_equal_priority_recency_choose_the_dictionary() {
    checked(
        &engine(),
        "instance (priority := 2000) seven : Inhabited Nat := Inhabited.mk 7\ninstance (priority := 1001) nine : Inhabited Nat := Inhabited.mk 9\ntheorem higher : default = 7 := by rfl\ninstance (priority := 2000) newest : Inhabited Nat := Inhabited.mk 11\ntheorem recent : default = 11 := by rfl",
    );
}

#[test]
fn recursive_source_instance_declarations_drive_real_computation() {
    checked(
        &engine(),
        "instance functionDefault {A : Type} [Inhabited A] : Inhabited (Nat -> A) := Inhabited.mk (fun x => default)\ndef f : Nat -> Nat -> Nat := default\ntheorem result : f 1 2 = 0 := by rfl",
    );
}

#[test]
fn source_instances_are_not_registered_on_kernel_rejection_or_late_failure() {
    let base = engine();
    let before = base.logical_root(&KVMap::new());
    for source in [
        "instance invalid : Inhabited Nat := 1",
        "instance bad : Nat := 1",
        "instance seven : Inhabited Nat := Inhabited.mk 7\ntheorem false : default = 0 := by rfl",
        "instance seven : Inhabited Nat := Inhabited.mk 7\ninstance seven : Inhabited Nat := Inhabited.mk 8",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(before, base.logical_root(&KVMap::new()));
    }
}

#[test]
fn named_instance_syntax_is_canonical_and_lossless_and_bounded() {
    for source in [
        "instance x : Inhabited Nat := Inhabited.mk 1",
        "instance (priority := 7) x [Inhabited Nat] : Inhabited Nat := Inhabited.mk default",
    ] {
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        assert!(
            fln_elab::source::instance_registration(parsed.syntax())
                .unwrap()
                .is_some()
        );
        assert!(fln_parse::parse_nat_definition(source.as_bytes()).is_err());
        assert!(fln_parse::parse_source_command(source.as_bytes()).is_err());
    }
    for source in [
        "instance : Inhabited Nat := Inhabited.mk 1",
        "instance (priority := -1) x : Inhabited Nat := Inhabited.mk 1",
        "instance (priority := 4294967296) x : Inhabited Nat := Inhabited.mk 1",
    ] {
        assert!(
            engine()
                .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
    }
}

#[test]
fn explicit_instance_admission_binds_the_registered_successor_root() {
    let base = engine();
    let options = KVMap::new();
    let result = base
        .admit_source_declaration(
            b"instance high : Inhabited Nat := Inhabited.mk 13",
            &options,
            limits().admission,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.base_logical_root, base.logical_root(&options));
    assert_eq!(
        result.result_logical_root,
        result.engine.logical_root(&options)
    );
    checked(&result.engine, "theorem seen : default = 13 := by rfl");
}
