//! Section data and defaults are admitted by the ordinary kernel council.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{BinderInfo, ExprNode};
use fln_elab::records::defaults::{RecordDefaults, helper_name};

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
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap()
        .engine
}
fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn binders(engine: &Engine, name: &str) -> Vec<(String, BinderInfo)> {
    let mut ty = engine
        .environment()
        .find(&n(name))
        .unwrap()
        .constant_val()
        .type_
        .clone();
    let mut result = Vec::new();
    while let ExprNode::ForallE {
        binder_name,
        binder_info,
        body,
        ..
    } = ty.node()
    {
        result.push((binder_name.to_display_string(), *binder_info));
        ty = body.clone();
    }
    result
}
fn names(engine: &Engine, name: &str) -> Vec<String> {
    binders(engine, name)
        .into_iter()
        .map(|(name, _)| name)
        .collect()
}
const CONFIG: &str = "section\nvariable {A : Type u} (fallback : A) (unused : String)\nstructure Config where\n  value : A := fallback\nend\n";

#[test]
fn default_only_section_values_parameterize_the_record_and_its_helpers() {
    let e = checked(
        &engine(),
        &format!(
            "{CONFIG}
        def config : Config 7 := {{}}
        theorem value : config.value = 7 := by rfl"
        ),
    );
    assert_eq!(names(&e, "Config"), ["A", "fallback"]);
    assert_eq!(names(&e, "Config.value._default"), ["A", "fallback"]);
    assert_eq!(
        binders(&e, "Config.value._default")[1].1,
        BinderInfo::Implicit
    );
    assert_eq!(
        RecordDefaults::read(e.environment())
            .unwrap()
            .helper(&n("Config"), 0),
        Some(&helper_name(&n("Config"), &n("value")))
    );
    assert!(!e.environment().contains(&n("fallback")));
}

#[test]
fn late_default_dependencies_parameterize_every_helper() {
    let e = checked(
        &engine(),
        "section
        variable (offset : Nat) (unused : String)
        structure Config where
          early : Nat := 1
          late : Nat := early + offset
          run (x : Nat) : Nat := x + late
        end
        def standard : Config 20 := {}
        def custom : Config 20 := { early := 3 }
        theorem first : standard.run 21 = 42 := by rfl
        theorem second : custom.run 19 = 42 := by rfl",
    );
    assert_eq!(names(&e, "Config"), ["offset"]);
    assert_eq!(names(&e, "Config.early._default"), ["offset"]);
    assert_eq!(
        names(&e, "Config.run._default"),
        ["offset", "early", "late", "x"]
    );
}

#[test]
fn dependent_field_domains_and_methods_close_type_dependencies_in_order() {
    let e = checked(
        &engine(),
        "section
        variable {A : Type u} (P : A -> Type v) (x : A) (unused : Nat)
        structure Witness (tag : Nat) where
          value : P x
          echo (other : P x) : P x := other
        end
        def witness : Witness (A := Nat) (fun n => Bool) 7 0 := { value := true }
        theorem works : witness.echo false = false := by rfl",
    );
    assert_eq!(names(&e, "Witness"), ["A", "P", "x", "tag"]);
    assert_eq!(
        names(&e, "Witness.echo._default"),
        ["A", "P", "x", "tag", "value", "other"]
    );
    assert_eq!(
        binders(&e, "Witness.echo._default")[3].1,
        BinderInfo::Implicit
    );
    let levels = &e
        .environment()
        .find(&n("Witness"))
        .unwrap()
        .constant_val()
        .level_params;
    assert!(levels.contains(&n("u")) && levels.contains(&n("v")));
}

#[test]
fn section_instances_used_by_defaults_become_real_class_parameters() {
    let e = checked(
        &engine(),
        "section
        variable {A : Type} [inh : Inhabited A] (unused : Nat)
        class Selected where
          value : A := default
        end
        instance selectedNat : Selected (A := Nat) := {}
        def answer : Nat := Selected.value
        theorem chosen : answer = 0 := by rfl",
    );
    assert_eq!(names(&e, "Selected"), ["A", "inh"]);
    assert_eq!(binders(&e, "Selected")[1].1, BinderInfo::InstImplicit);
    assert_eq!(
        binders(&e, "Selected.value._default")[1].1,
        BinderInfo::InstImplicit
    );
}

#[test]
fn inherited_aliases_and_defaults_share_the_generalized_parent_telescope() {
    let e = checked(
        &engine(),
        "
        structure Parent (A : Type) where
          value : A
        section
        variable (A : Type) (fallback : A) (unused : Nat)
        structure Child extends Parent A where
          copy : A := value
          preferred : A := fallback
        end
        def child : Child Nat 7 := { value := 11 }
        theorem inherited : child.value = 11 := by rfl
        theorem copied : child.copy = 11 := by rfl
        theorem preferred : child.preferred = 7 := by rfl",
    );
    assert_eq!(names(&e, "Child"), ["A", "fallback"]);
    assert_eq!(names(&e, "Child.copy._default")[..2], ["A", "fallback"]);
    assert!(e.environment().contains(&n("Child.toParent")));
}

#[test]
fn generalized_class_inheritance_publishes_working_parent_instances() {
    checked(
        &engine(),
        "
        class Parent (A : Type) where
          value : A
        section
        variable (A : Type)
        class Child extends Parent A where
          extra : Nat := 1
        end
        instance child : Child Nat := { value := 41 }
        def answer : Nat := Parent.value
        theorem chosen : answer = 41 := by rfl",
    );
}

#[test]
fn dependent_proof_fields_and_method_shadowing_preserve_local_identity() {
    let e = checked(
        &engine(),
        "namespace Outer
        variable (A : Type u) (unused : False)
        include unused
        structure Box (A : Type v) where
          value : A
          echo (unused : A) : A := unused
        end Outer
        def box : Outer.Box Nat := { value := 7 }
        theorem correct : box.echo 42 = 42 := by rfl",
    );
    assert_eq!(names(&e, "Outer.Box"), ["A"]);
    assert_eq!(
        names(&e, "Outer.Box.echo._default"),
        ["A", "value", "unused"]
    );
    assert_eq!(
        e.environment()
            .find(&n("Outer.Box"))
            .unwrap()
            .constant_val()
            .level_params,
        [n("v")]
    );
    checked(
        &engine(),
        "section
        variable (A : Type) (f : A -> Nat)
        structure Certified where
          value : A
          proof : f value = f value := by rfl
        end
        def cert : Certified Nat (fun x => x + 1) := { value := 41 }
        theorem correct : cert.value = 41 := by rfl",
    );
}

#[test]
fn unused_instances_and_section_scopes_do_not_inflate_record_types() {
    let e = checked(
        &engine(),
        "section
        variable (A : Type u) [inh : Inhabited A]
        structure Bit where
          value : Bool := true
        section
        variable (B : Type v)
        structure Pair where
          first : A
          second : B
        end
        structure Box where
          value : A
        end",
    );
    assert!(names(&e, "Bit").is_empty());
    assert!(names(&e, "Bit.value._default").is_empty());
    assert_eq!(names(&e, "Pair"), ["A", "B"]);
    assert_eq!(names(&e, "Box"), ["A"]);
}

#[test]
fn generalized_defaults_match_explicit_checked_worlds() {
    let base = engine();
    let section = checked(&base, CONFIG);
    let explicit = checked(
        &base,
        "structure Config {A : Type u} (fallback : A) where\n  value : A := fallback",
    );
    assert_eq!(
        section.logical_root(&KVMap::new()),
        explicit.logical_root(&KVMap::new())
    );
}

#[test]
fn invalid_unused_defaults_and_late_helper_collisions_publish_nothing() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "variable (A : Type) (fallback : A)\nstructure Bad where\n  value : A := fallback\n  wrong : Nat := (1 : String)",
        "variable (A : Type) (fallback : A)\nstructure Bad where\n  value : A := fallback\n  wrong : Nat := let ignored : String := 1; 7",
        "variable (A : Type)\nstructure Bad where\n  value : A := 7",
        "variable (A : Type)\nstructure Bad where\n  value : A\n  wrong : False := by rfl",
        "def Bad.value._default : Nat := 1\nvariable (A : Type) (fallback : A)\nstructure Bad where\n  value : A := fallback",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(root, base.logical_root(&KVMap::new()));
        assert!(!base.environment().contains(&n("Bad")));
        assert!(
            RecordDefaults::read(base.environment())
                .unwrap()
                .helper(&n("Bad"), 0)
                .is_none()
        );
    }
    checked(&base, CONFIG);
}

#[test]
fn generalized_parameters_count_toward_the_generator_budget() {
    use fln_elab::records::RecordBudget;
    use fln_elab::source::scope::{self, SourceScope};
    use fln_parse::command_scope::ScopeCommand;
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let Some(ScopeCommand::Variable(syntax)) =
        fln_parse::command_scope::parse(b"variable (A : Type) (fallback : A)").unwrap()
    else {
        panic!("variable command")
    };
    let mut scope = SourceScope::default();
    scope.variables = scope::variables::declare(
        &syntax,
        base.environment(),
        limits().admission.kernel,
        &scope,
    )
    .unwrap();
    let parsed =
        fln_parse::parse_definition(b"structure Config where\n  value : A := fallback").unwrap();
    for budget in [
        RecordBudget {
            max_binders: 2,
            ..RecordBudget::default()
        },
        RecordBudget {
            max_nodes: 0,
            ..RecordBudget::default()
        },
    ] {
        assert!(
            scope::elaborate_record(
                parsed.syntax(),
                base.environment(),
                limits().admission.kernel,
                budget,
                &scope
            )
            .is_err()
        );
    }
    assert!(
        scope::elaborate_record(
            parsed.syntax(),
            base.environment(),
            limits().admission.kernel,
            RecordBudget::default(),
            &scope
        )
        .is_ok()
    );
    assert_eq!(root, base.logical_root(&KVMap::new()));
}

#[test]
fn stopped_section_record_checking_is_a_nonanswer_and_retryable() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let mut low = limits();
    low.admission.kernel = low.admission.kernel.narrowed(0, 32);
    match base.check_source_files(&[CONFIG.as_bytes()], &KVMap::new(), low) {
        Ok(Outcome::Inconclusive(_)) => {}
        Err(e) => assert!(
            matches!(e.disposition(), ("resource" | "inconclusive", false, 3)),
            "{e:?}"
        ),
        other => panic!("exhaustion is not a verdict: {other:?}"),
    }
    assert_eq!(root, base.logical_root(&KVMap::new()));
    checked(&base, CONFIG);
}

#[test]
fn imported_default_registrations_reuse_invalidate_and_recover_as_checked_modules() {
    use fln::SourceModuleInput;
    use fln::source_check::modules::{
        SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
    };
    let names = [n("Data"), n("Main")];
    let mut session = SourceModuleSession::new(
        engine(),
        KVMap::new(),
        SourceModuleCheckLimits::new(limits()),
        SourceModuleCacheLimits::default(),
    );
    let data = "section\nvariable (fallback : Nat)\nstructure Config where\n  value : Nat := fallback\nend";
    let main =
        "import Data\ndef config : Config 41 := {}\ntheorem correct : config.value = 41 := by rfl";
    let check = |session: &mut SourceModuleSession, data: &str, main: &str| {
        session.check_with_cancel(
            &[
                SourceModuleInput {
                    name: &names[0],
                    source: data.as_bytes(),
                },
                SourceModuleInput {
                    name: &names[1],
                    source: main.as_bytes(),
                },
            ],
            &names[1],
            None,
        )
    };
    let cold = check(&mut session, data, main)
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = check(&mut session, data, main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((cold.reused_modules, cold.elaborated_modules), (0, 2));
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (2, 0));
    assert_eq!(
        cold.checked.checked.result_logical_root,
        warm.checked.checked.result_logical_root
    );
    let revised = data.replace(":= fallback", ":= fallback + 0");
    let changed = check(&mut session, &revised, main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((changed.reused_modules, changed.elaborated_modules), (0, 2));
    assert_ne!(
        changed.checked.checked.result_logical_root,
        cold.checked.checked.result_logical_root
    );
    let invalid = revised.replace(":= fallback + 0", ":= (1 : String)");
    assert!(check(&mut session, &invalid, main).is_err());
    let recovered = check(&mut session, &revised, main)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 2);
    assert_eq!(
        recovered.checked.checked.result_logical_root,
        changed.checked.checked.result_logical_root
    );
    assert!(
        check(
            &mut session,
            &revised,
            "import Data\ndef leaked : Nat := fallback"
        )
        .is_err()
    );
}

#[test]
fn generalized_checked_records_execute_and_replay_native_closures() {
    use fln::{EngineExecutionLimits, VmExit};
    let base = checked(
        &engine(),
        "section\nvariable (A : Type)\nstructure Handler where\n  run : A -> Nat\nend",
    );
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = b"def use (h : Handler String) : Nat := h.run \"hello\" + 37\n#eval use { run := String.length }";
    let compile = || {
        base.execute_source_definitions(
            &[source],
            &options,
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
    };
    let one = compile();
    let two = compile();
    let bytes = &one.executions.last().unwrap().flbc_artifact;
    assert_eq!(bytes, &two.executions.last().unwrap().flbc_artifact);
    let program =
        fln_comp::flbc::decode_canonical(bytes, fln_comp::flbc::CodecLimits::default()).unwrap();
    let Outcome::Complete(VmExit::Returned(value)) = fln_vm::interpreter::execute(
        &program,
        fln_vm::interpreter::ExecutionLimits::default(),
        None,
    ) else {
        panic!("replay did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn checked_source_example_uses_the_public_record_pipeline() {
    checked(
        &engine(),
        include_str!("../../../examples/native_section_records.lean"),
    );
}

#[test]
fn result_sort_normalization_cannot_discard_invalid_source_annotations() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "structure Bad : (Type : Nat) where\n  value : Nat",
        "structure Bad : (let unused : String := 1; Type) where\n  value : Nat",
        "variable (A : Type)\nstructure Bad : (Type : Nat) where\n  value : A",
        "variable (A : Type)\nstructure Bad : (let unused : String := 1; Type) where\n  value : A",
    ] {
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err("discarding an invalid annotation is not validation");
        assert_eq!(
            error.disposition(),
            ("kernel-rejection", true, 1),
            "{source}: {error:?}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "variable (A : Type)\nstructure Good : (let unused : Nat := 1; Type) where\n  value : A",
    );
}
