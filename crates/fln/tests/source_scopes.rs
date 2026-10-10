//! File scopes use the real parser, native elaborator, and both checking engines.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    SourceCheckLimits, SourceCommandBatchExecution, VmExit,
};
use fln_core::name::Name;
use fln_elab::instances::InstanceRegistry;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{source}: {e:?}"))
    .into_complete()
    .expect("both checkers must answer")
    .engine
}

fn executed(base: &Engine, source: &str) -> SourceCommandBatchExecution {
    base.execute_source_commands_with_checks(
        source.as_bytes(),
        &KVMap::new(),
        EngineExecutionLimits::new(limits().kernel),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    .into_complete()
    .expect("source controls and execution must complete")
}

fn evaluated(completed: &SourceCommandBatchExecution) -> Vec<usize> {
    completed
        .batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let exit = &completed.batch.executions[index].exit;
            let VmExit::Returned(returned) = exit else {
                panic!("expected a Nat return, got {exit:?}");
            };
            fln_vm::interpreter::nat_decimal(&returned.value)
                .unwrap_or_else(|| panic!("expected a Nat result, got {exit:?}"))
                .parse()
                .expect("these fixtures return small natural numbers")
        })
        .collect()
}

#[test]
fn executable_files_apply_the_same_attributes_and_sections_as_check_only_files() {
    let base = engine();
    // Every file is accepted by the pinned Reference in reference_differential.tsv.
    // The runtime previously stopped at its first section-variable or standalone
    // attribute command even though check-source implemented the command.
    for source in [
        include_str!("../../../examples/native_instance_attributes.lean"),
        include_str!("../../../examples/native_scoped_instances.lean"),
        include_str!("../../../examples/native_default_simp.lean"),
        include_str!("../../../examples/native_section_records.lean"),
        include_str!("../../../examples/native_section_inductives.lean"),
    ] {
        let checked = checked(&base, source);
        let completed = executed(&base, source);
        assert_eq!(
            completed.batch.engine.logical_root(&KVMap::new()),
            checked.logical_root(&KVMap::new()),
            "both paths must retain the same declarations and metadata: {source}"
        );
    }
}

#[test]
fn section_variables_generalize_runtime_definitions_and_restore_after_end() {
    let base = engine();
    let source = "section\nvariable {A : Type} (x : A)\ndef identity := x\nend\n#eval identity 41\nsection\nvariable (n : Nat) (h : n = n)\ninclude h\ntheorem withProof : n = n := by exact h\nomit h\ntheorem withoutProof : n = n := by rfl\nend\n#eval identity 42";
    let completed = executed(&base, source);
    assert_eq!(evaluated(&completed), [41, 42]);
    assert!(!completed.batch.engine.environment().contains(&n("x")));
    assert!(!completed.batch.engine.environment().contains(&n("h")));
    checked(
        &completed.batch.engine,
        "theorem useIncluded : withProof 7 rfl = rfl := by rfl\ntheorem useOmitted : withoutProof 7 = rfl := by rfl",
    );
    assert!(
        base.execute_source_commands_with_checks(
            b"section\nvariable (x : Nat)\nend\n#eval x",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .is_err()
    );
}

#[test]
fn scoped_instance_activation_changes_runtime_values_and_ends_with_the_section() {
    let completed = executed(
        &engine(),
        "class Selection where\n  value : Nat\ndef selected [Selection] : Nat := Selection.value\ndef fallbackSelection : Selection := Selection.mk 1\nattribute [instance] fallbackSelection\nnamespace Alternative\ndef dictionary : Selection := Selection.mk 7\nattribute [scoped instance] dictionary\nend Alternative\n#eval selected\nsection\nopen scoped Alternative\n#eval (selected)\nend\n#eval selected",
    );
    assert_eq!(evaluated(&completed), [1, 7, 1]);
    assert_eq!(completed.batch.source_evaluation_indices.len(), 3);
}

#[test]
fn bare_evaluations_synthesize_consecutive_instances_and_refuse_missing_dictionaries() {
    let missing = checked(
        &engine(),
        "class FirstChoice where\n  value : Nat\nclass SecondChoice where\n  value : Nat\ndef combined [FirstChoice] [SecondChoice] : Nat := FirstChoice.value + SecondChoice.value\ndef firstDictionary : FirstChoice := FirstChoice.mk 17\nattribute [instance] firstDictionary\ndef secondDictionary : SecondChoice := SecondChoice.mk 25",
    );
    let parsed = fln_parse::parse_source_command(b"#eval combined").unwrap();
    assert!(matches!(
        fln_elab::elaborate_evaluation_in_with_budget(
            parsed.syntax(),
            Name::num(Name::anonymous(), 0),
            missing.environment(),
            limits().kernel,
        ),
        Err(fln_elab::NatDefinitionElabError::Inference(
            fln_elab::source::SourceInferenceError::InstanceSynthesisRequired
        ))
    ));
    let registered = checked(&missing, "attribute [instance] secondDictionary");
    assert_eq!(
        evaluated(&executed(&registered, "#eval combined\n#eval (combined)")),
        [42, 42]
    );
}

#[test]
fn instance_query_insertion_preserves_explicit_and_polymorphic_function_values() {
    let base = checked(
        &engine(),
        "class Selection where\n  value : Nat\ndef selected [Selection] : Nat := Selection.value\ndef dictionary : Selection := Selection.mk 7\nattribute [instance] dictionary\ndef explicitFunction (x : Nat) : Nat := x\ndef polymorphic {A : Type} (x : A) : A := x\ndef strict ⦃A : Type⦄ (x : A) : A := x\ndef ordinaryImplicit {A : Type} : Nat := 0\ndef remaining [Selection] {A : Type} (x : A) : Nat := Selection.value",
    );
    let candidate = |source: &str| {
        let parsed = fln_parse::parse_source_command(source.as_bytes()).unwrap();
        let name = Name::num(Name::anonymous(), 0);
        let declaration = if parsed.kind() == fln_parse::SourceCommandKind::Check {
            fln_elab::elaborate_check_in_with_budget(
                parsed.syntax(),
                name,
                base.environment(),
                limits().kernel,
            )
        } else {
            fln_elab::elaborate_evaluation_in_with_budget(
                parsed.syntax(),
                name,
                base.environment(),
                limits().kernel,
            )
        }
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(matches!(
            fln_kernel::check(base.environment(), &declaration, limits().kernel),
            fln::Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
        ));
        let fln::Declaration::Defn(definition) = declaration else {
            panic!("query must produce a definition candidate");
        };
        definition
    };
    for (source, name) in [
        ("#eval @selected", "selected"),
        ("#eval (@selected)", "selected"),
        ("#check selected", "selected"),
        ("#eval explicitFunction", "explicitFunction"),
        ("#eval polymorphic", "polymorphic"),
        ("#eval strict", "strict"),
        ("#eval ordinaryImplicit", "ordinaryImplicit"),
        ("#check @polymorphic", "polymorphic"),
    ] {
        assert_eq!(
            candidate(source).base.type_,
            base.environment()
                .find(&n(name))
                .unwrap()
                .constant_val()
                .type_,
            "{source} must retain the checked function type"
        );
    }
    let remaining = candidate("#eval remaining");
    assert!(matches!(
        remaining.base.type_.node(),
        fln::ExprNode::ForallE {
            binder_info: fln::BinderInfo::Implicit,
            ..
        }
    ));
    assert_eq!(
        remaining.value,
        fln::Expr::app(
            fln::Expr::const_(n("remaining"), vec![]),
            fln::Expr::const_(n("dictionary"), vec![]),
        )
    );
    let computed = candidate("#eval let paid : Nat := 40 + 2; fun (x : Nat) => x");
    assert!(matches!(
        computed.value.node(),
        fln::ExprNode::LetE { body, .. }
            if matches!(body.node(), fln::ExprNode::Lam { .. })
    ));
}

#[test]
fn executable_attribute_failure_exposes_no_prefix_and_keeps_file_ownership() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def choice : Inhabited Nat := Inhabited.mk 7\nattribute [instance] choice Missing\n#eval (default : Nat)",
        "def wrap (n : Nat) := n\ntheorem unwrap (n : Nat) : wrap n = n := by rfl\nattribute [simp] unwrap Missing",
        "def alias := Nat\nattribute [reducible] alias Missing\n#eval (31 : alias)",
    ] {
        assert!(
            base.execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    let own_file = executed(
        &base,
        "def alias := Nat\nattribute [reducible] alias\n#eval (31 : alias)",
    );
    assert_eq!(evaluated(&own_file), [31]);
    let predecessor = executed(&base, "def alias := Nat").batch.engine;
    let error = predecessor
        .execute_source_commands_with_checks(
            b"attribute [reducible] alias",
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("has not been defined in this file")
    );
    assert_eq!(evaluated(&executed(&base, "#eval 42")), [42]);
}

#[test]
fn executable_scope_limits_remain_resource_stops() {
    let base = engine();
    let source = "section\n".repeat(257);
    let error = base
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_err();
    assert!(matches!(
        &error,
        EngineExecutionError::BatchCommand { index: 256, error, .. }
            if matches!(error.as_ref(), EngineExecutionError::SourceScopeLimit {
                resource: "scope depth", limit: 256,
            })
    ));
    let classified = fln::source_check::SourceCheckError::Command {
        file: 0,
        command: 256,
        offset: 256 * "section\n".len(),
        error: Box::new(error),
    };
    assert_eq!(classified.disposition(), ("resource", false, 3));
}

#[test]
fn flattened_source_files_restore_scope_and_protect_predecessor_reducibility() {
    let base = engine();
    let execution_limits = EngineExecutionLimits::new(limits().kernel);
    let completed = base
        .execute_source_definitions(
            &[
                b"namespace First\nvariable (x : Nat)\ndef identity := x",
                b"def answer : Nat := First.identity 42",
            ],
            &KVMap::new(),
            execution_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(completed.engine.environment().contains(&n("answer")));
    assert!(!completed.engine.environment().contains(&n("First.answer")));
    let opened = base
        .execute_source_definitions(
            &[
                b"namespace Local\ndef value : Nat := 7\nend Local",
                b"open Local in def chosen : Nat := value",
            ],
            &KVMap::new(),
            execution_limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    // Expanding the first command of the next file revisits that command's
    // index. Resetting its scope a second time would lose `open Local`.
    checked(&opened.engine, "theorem chosen_ok : chosen = 7 := by rfl");
    for sources in [
        [
            b"variable (x : Nat)".as_slice(),
            b"def leaked := x".as_slice(),
        ],
        [
            b"def alias := Nat".as_slice(),
            b"attribute [reducible] alias".as_slice(),
        ],
    ] {
        assert!(
            base.execute_source_definitions(&sources, &KVMap::new(), execution_limits)
                .is_err()
        );
    }
}

#[test]
fn source_module_execution_preserves_file_boundaries_for_control_commands() {
    let base = engine();
    let first = n("First");
    let main = n("Main");
    let modules = [
        fln::SourceModuleInput {
            name: &first,
            source: b"namespace Library\nvariable (x : Nat)\ndef identity := x",
        },
        fln::SourceModuleInput {
            name: &main,
            source: b"import First\ndef answer : Nat := Library.identity 42",
        },
    ];
    let completed = base
        .execute_source_modules(
            &modules,
            &main,
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(completed.engine.environment().contains(&n("answer")));
    assert!(
        !completed
            .engine
            .environment()
            .contains(&n("Library.answer"))
    );
}
#[test]
fn nested_namespaces_reopen_and_resolve_relative_and_absolute_names() {
    let result = checked(
        &engine(),
        "def value : Nat := 1\nnamespace A\ndef value : Nat := 7\nnamespace B\ndef answer : Nat := value + _root_.value\nend B\nend A\nnamespace A.B\ntheorem answer_ok : answer = 8 := by rfl\nend A.B\ntheorem outside : A.B.answer = 8 := by rfl",
    );
    assert!(result.environment().contains(&n("A.B.answer")));
    assert!(!result.environment().contains(&n("answer")));
}
#[test]
fn section_open_state_is_restored_but_checked_declarations_survive() {
    let base = checked(
        &engine(),
        "namespace A\ndef a : Nat := 7\nend A\nsection Local\nopen A\ndef inside : Nat := a\nend Local\ntheorem persisted : inside = A.a := by rfl",
    );
    assert!(
        base.check_source_files(
            &[b"def bad : Nat := a"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
#[test]
fn universe_commands_work_in_bodies_and_restore_with_scope_exit() {
    let result = checked(
        &engine(),
        "section\nuniverse u\ndef lifted : Type (u + 1) := Type u\nnamespace A\nuniverse v\ndef identity (B : Sort v) (b : B) : B := b\nend A\nend\ntheorem value : A.identity Nat 7 = 7 := by rfl",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("lifted"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("u")]
    );
    assert_eq!(
        result
            .environment()
            .find(&n("A.identity"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("v")]
    );
    assert!(
        result
            .check_source_files(
                &[b"def bad := Type u"],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}
#[test]
fn namespaced_recursive_families_and_functions_use_canonical_constructor_names() {
    checked(
        &engine(),
        "namespace Lists\ninductive Seq (A : Type) where\n  | nil\n  | cons (head : A) (tail : Seq A)\ndef size {A : Type} (xs : Seq A) : Nat := match xs with | Seq.nil => 0 | Seq.cons x rest => size rest + 1\ndef sample : Seq Nat := Seq.cons 7 Seq.nil\ntheorem length : size sample = 1 := by rfl\nend Lists\nopen Lists\ntheorem outside : size sample = 1 := by rfl",
    );
}
#[test]
fn namespaced_records_inheritance_and_field_access_compute() {
    checked(
        &engine(),
        "namespace Data\nstructure Base where\n  value : Nat\nstructure Child extends Base where\n  backup : Nat := value\ndef chosen : Child := { value := 23 }\ntheorem qualified : chosen.value = 23 := by rfl\ntheorem inherited : chosen.backup = 23 := by rfl\nend Data\nopen Data\ntheorem outside : chosen.value = 23 := by rfl",
    );
}
#[test]
fn namespaced_class_registrations_and_explicit_universe_applications_compute() {
    let result = checked(
        &engine(),
        "namespace Classes\nclass Chosen (A : Type) where\n  value : A\ninstance natural : Chosen Nat := Chosen.mk 31\ndef result : Nat := Chosen.value\ndef identity.{u} {A : Sort u} (a : A) : A := a\ntheorem result_ok : identity.{1} result = 31 := by rfl\nend Classes\nopen Classes\ntheorem outside : identity.{1} result = 31 := by rfl",
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .candidates(&n("Classes.Chosen"))
            .iter()
            .any(|row| row.declaration == n("Classes.natural"))
    );
}
#[test]
fn locals_shadow_namespaces_and_root_escape_changes_the_declaration_namespace() {
    let result = checked(
        &engine(),
        "namespace A\ndef x : Nat := 7\ndef loc (x : Nat) : Nat := x\ndef _root_.rootValue : Nat := A.x\nend A\ntheorem local_ok : A.loc 23 = 23 := by rfl\ntheorem root_ok : rootValue = 7 := by rfl",
    );
    assert!(!result.environment().contains(&n("A.rootValue")));
}
/// The pin matches a local only by the name as written, so `_root_.value` is the
/// global even under a local `value`, while the bare name stays the local.
#[test]
fn root_qualified_names_skip_shadowing_locals_and_bare_names_do_not() {
    let base = engine();
    let result = checked(
        &base,
        "def value : Nat := 1\ndef use (value : Bool) : Nat := _root_.value\ntheorem use_ok : use true = 1 := by rfl",
    );
    assert!(result.environment().contains(&n("use_ok")));
    let shadowed = base
        .check_source_files(
            &[b"def value : Nat := 1\ndef use (value : Bool) : Nat := value"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("the bare name is the Bool local");
    // The pin refuses it while elaborating (type mismatch); either stage is a
    // refusal of the Bool body, which is the point here.
    assert!(
        matches!(
            shadowed.disposition(),
            ("kernel-rejection", true, 1) | ("elaboration", false, 1)
        ) && format!("{shadowed:?}").contains("Bool"),
        "{shadowed:?}"
    );
}
#[test]
fn invalid_scopes_and_ambiguous_opens_never_publish_a_prefix() {
    let base = checked(
        &engine(),
        "namespace A\ndef value : Nat := 7\nend A\nnamespace B\ndef value : Nat := 9\nend B",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def pfx := 1\nend",
        "def pfx := 1\nnamespace A\nend B",
        "def pfx := 1\nnamespace A\nend",
        "def pfx := 1\nsection\nend A",
        "def pfx := 1\nopen Missing",
        "def pfx := 1\nopen A B\ndef bad := value",
        "def pfx := 1\nuniverse u u",
        "def pfx := 1\nsection\nuniverse u\nend\ndef bad := Type u",
        "def pfx := 1\nopen A in",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&n("prefix")));
    }
    checked(&base, "open A A\ntheorem recovery : value = 7 := by rfl");
}
#[test]
fn file_boundary_closes_scopes_without_discarding_declarations() {
    let result = engine()
        .check_source_files(
            &[
                b"namespace A\ndef value := 7",
                b"def rootValue := A.value\ntheorem root_ok : rootValue = 7 := by rfl",
            ],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.engine.environment().contains(&n("rootValue")));
    assert!(!result.engine.environment().contains(&n("A.rootValue")));
    assert_eq!(result.commands, 4);
}
#[test]
fn comments_only_files_and_scoped_command_limits_are_real_boundaries() {
    let base = engine();
    let result = base
        .check_source_files(
            &[b"/- namespace A -/", b"-- empty"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.commands, 0);
    let mut bound = SourceCheckLimits::new(limits());
    bound.max_commands = 2;
    assert!(
        base.check_source_files(
            &[b"section\nnamespace A\ndef over := 7"],
            &KVMap::new(),
            bound
        )
        .is_err()
    );
}

#[test]
fn used_scope_universes_keep_declaration_order_before_local_and_inferred_levels() {
    let result = checked(
        &engine(),
        "universe z a unused\ndef choose.{v} (A : Sort z) (B : Sort a) (C : Sort v) (D : Sort b) (x : A) : A := x",
    );
    assert_eq!(
        result
            .environment()
            .find(&n("choose"))
            .unwrap()
            .constant_val()
            .level_params,
        vec![n("z"), n("a"), n("v"), n("b")]
    );
}
#[test]
fn dotted_end_closes_only_its_named_suffix_and_anonymous_scopes_are_barriers() {
    let base = checked(
        &engine(),
        "namespace A.B\nend B\ndef outer := 7\nnamespace C.D\ndef inner := 9\nend C.D\nend A",
    );
    assert!(base.environment().contains(&n("A.outer")));
    assert!(base.environment().contains(&n("A.C.D.inner")));
    assert!(
        base.check_source_files(
            &[b"namespace A\nsection\nend A"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}
#[test]
fn scope_exhaustion_is_a_typed_non_rejection_and_does_not_publish() {
    let base = engine();
    let source = format!("{}def neverPublished := 7", "section\n".repeat(257));
    let error = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert!(!base.environment().contains(&n("neverPublished")));
    checked(&base, "def recovered := 7");
}

/// `open A in <command>` is the pin's `section open A <command> end` (`Lean.Parser.Command.in`
/// and its macro): the open reaches exactly the one command, then the scope is restored. The
/// pinned `lean` accepts the first file and rejects the second at the second use of `x`
/// (`Unknown identifier \`x\``), captured 2026-10-05.
#[test]
fn open_in_reaches_exactly_its_one_command() {
    let result = checked(
        &engine(),
        "namespace A\ndef x : Nat := 1\nend A\nopen A in\ndef y : Nat := x\nopen A in\nopen Nat in\ndef z : Nat := succ x\ntheorem w : z = y + 1 := by rfl",
    );
    assert!(result.environment().contains(&n("y")));
    assert!(result.environment().contains(&n("z")));
    // The open ended with its command: a later bare `x` is unknown again.
    assert!(
        engine()
            .check_source_files(
                &[b"namespace A\ndef x : Nat := 1\nend A\nopen A in def y : Nat := x\ndef w : Nat := x"],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
    // One command for the pin, one here: `open A in def …` is not two.
    let checked_files = engine()
        .check_source_files(
            &[b"namespace A\ndef x : Nat := 1\nend A\nopen A in\ndef y : Nat := x"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked_files.commands, 4);
}

/// Declaration modifiers parse to the pin's trees
/// (`crates/fln-parse/tests/reference_command_trees.rs`), but `private` and
/// `noncomputable` are not implemented: each is refused by the elaborator as syntax it
/// does not support, a typed, non-authoritative refusal, never admitted with the modifier
/// dropped. The pin accepts both files. `protected` is elaborated (bead `fln-eq4k`),
/// admitted and tagged, never admitted with the tag dropped. A nameless instance is
/// elaborated too, and the pin accepts it. Its name follows `mkInstanceName`
/// (`instance_name.rs`) except for one stated deviation. The base name
/// `instInhabitedNat` is taken by the seed's own instance, so the pin appends the main
/// module, `instInhabitedNat_<module>` (v4.32.0, measured 2026-10-07). FrankenLean does
/// not know the module and makes the base unused with a numeric suffix instead. Either
/// way the instance is new, and the seed's `instInhabitedNat` is never overwritten.
#[test]
fn parsed_modifiers_are_refused_until_elaborated_and_nameless_instances_are_admitted() {
    let protected = engine()
        .check_source_files(
            &[b"namespace Foo\nprotected def bar : Nat := 1\nend Foo"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        fln_elab::protected_names::ProtectedNames::read(protected.engine.environment())
            .unwrap()
            .contains(&Name::from_components(["Foo", "bar"])),
        "`protected` is recorded, not dropped"
    );
    let nameless = engine()
        .check_source_files(
            &[b"instance : Inhabited Nat := Inhabited.mk 0"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let seed = engine();
    let base = Name::from_components(["instInhabitedNat"]);
    assert_eq!(
        nameless
            .engine
            .environment()
            .find(&base)
            .map(|info| info.constant_val().type_.clone()),
        seed.environment()
            .find(&base)
            .map(|info| info.constant_val().type_.clone()),
        "the seed's own instInhabitedNat is untouched"
    );
    let added: Vec<String> = nameless
        .engine
        .environment()
        .constants()
        .filter(|(name, _)| !seed.environment().contains(name))
        .map(|(name, _)| name.to_display_string())
        .collect();
    assert!(
        added.len() == 1 && added[0].starts_with("instInhabitedNat_"),
        "exactly one new instance, named off the taken base: {added:?}"
    );
    for source in ["private def a : Nat := 1", "noncomputable def b : Nat := 2"] {
        let error = engine()
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        let (class, authority, _) = error.disposition();
        assert_eq!((class, authority), ("input", false), "{source}: {error}");
        assert!(
            error.to_string().contains("elaboration refused source"),
            "{source}: {error}"
        );
    }
}
