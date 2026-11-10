//! Reducibility attributes on a declaration, in the seed world: the status they set decides what
//! elaboration unfolds (`rfl` cannot see through an irreducible definition), and the pin's
//! `validate` transitions (vendored Lean/ReducibilityAttrs.lean) are refused as it refuses them.
//! These are the shapes of `fln-cli`'s `source_reducibility_attributes`, which runs each program
//! through the pinned `lean` v4.32.0 first, here without imports so they also run where the pin is
//! absent.
#![forbid(unsafe_code)]
use fln::source_check::modules::SourceModuleCheckLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput,
};
use fln_elab::reducibility::{Reducibility, ReducibilityTable};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<(), String> {
    match engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) {
        Ok(outcome) => {
            outcome.into_complete().unwrap();
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

#[test]
fn a_status_decides_what_rfl_unfolds() {
    for source in [
        "def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[reducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[implicit_reducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[irreducible] def g : Nat := 5\ntheorem t : g = g := rfl\n",
        "@[irreducible] def g : Nat := 5\ndef h : Nat := g + 1\n",
        "@[implicit_reducible, irreducible] def g : Nat := 5\n",
        "namespace A\n@[instance_reducible] def g : Nat := 5\nend A\ntheorem t : A.g = 5 := rfl\n",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        "@[irreducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
        "@[implicit_reducible, irreducible] def g : Nat := 5\ntheorem t : g = 5 := rfl\n",
    ] {
        assert!(check(source).is_err(), "accepted {source}");
    }
}

#[test]
fn transitions_the_pin_refuses_are_refused() {
    for (source, pin) in [
        (
            "@[irreducible, reducible] def f : Nat := 1\n",
            "`f` is not currently `[semireducible]`",
        ),
        (
            "@[reducible, reducible] def f : Nat := 1\n",
            "`f` is not currently `[semireducible]`",
        ),
        (
            "@[semireducible] def f : Nat := 1\n",
            "declarations are `[semireducible]` by default",
        ),
        (
            "@[reducible] abbrev A := Nat\n",
            "`A` is not currently `[semireducible]`",
        ),
        (
            "@[reducible] theorem t : 1 = 1 := Eq.refl 1\n",
            "`t` is not a definition",
        ),
        ("@[reducible] opaque o : Nat\n", "`o` is not a definition"),
        (
            "@[reducible 3] def f : Nat := 1\n",
            "This attribute takes no arguments",
        ),
        (
            "@[scoped reducible] def f : Nat := 1\n",
            "Scoped attributes must be used inside namespaces",
        ),
    ] {
        assert!(check(source).is_err(), "accepted {source} (the pin: {pin})");
    }
}

fn checked_from(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    .into_complete()
    .expect("both checking engines must answer")
    .engine
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

#[test]
fn local_transparency_follows_nested_sections_namespaces_and_command_scopes() {
    for source in [
        "def g : Nat := 5\nsection Outer\nattribute [local irreducible] g\n\
         theorem self : g = g := rfl\nsection Inner\n\
         attribute [local semireducible] g\ntheorem inside : g = 5 := rfl\n\
         end Inner\nend Outer\ntheorem outside : g = 5 := rfl",
        "def g : Nat := 5\nnamespace A.B\nattribute [local irreducible] _root_.g\n\
         end B\ntheorem restored : g = 5 := rfl\nend A",
        "@[irreducible] def g : Nat := 5\n\
         attribute [local semireducible] g in\ntheorem inside : g = 5 := rfl",
        "def g : Nat := 5\nsection\nattribute [local implicit_reducible] g\n\
         attribute [local irreducible] g\nattribute [local semireducible] g\n\
         theorem inside : g = 5 := rfl\nend\ntheorem outside : g = 5 := rfl",
        "def g : Nat := 5\nsection\nattribute [local instance_reducible] g\n\
         theorem inside : g = 5 := rfl\nend",
    ] {
        check(source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
    for source in [
        "def g : Nat := 5\nsection\nattribute [local irreducible] g\n\
         theorem blocked : g = 5 := rfl\nend",
        "def g : Nat := 5\nsection Outer\nattribute [local irreducible] g\n\
         section Inner\nattribute [local semireducible] g\n\
         theorem inside : g = 5 := rfl\nend Inner\n\
         theorem blocked : g = 5 := rfl\nend Outer",
        "@[irreducible] def g : Nat := 5\n\
         attribute [local semireducible] g in\ntheorem inside : g = 5 := rfl\n\
         theorem blocked : g = 5 := rfl",
    ] {
        assert!(
            check(source).is_err(),
            "local status escaped its scope: {source}"
        );
    }
}

#[test]
fn imported_definitions_accept_local_overrides_without_changing_their_journal() {
    let base = checked_from(
        &engine(),
        "@[irreducible] def hidden : Nat := 5\ndef ordinary : Nat := 7",
    );
    let journal = fln_elab::reducibility::journal_digest(base.environment());
    let checked = checked_from(
        &base,
        "attribute [local semireducible] hidden\n\
         theorem visibleHere : hidden = 5 := rfl\n\
         attribute [local irreducible] ordinary\n\
         theorem sameHere : ordinary = ordinary := rfl",
    );
    assert!(checked.environment().contains(&name("visibleHere")));
    assert_eq!(
        fln_elab::reducibility::journal_digest(checked.environment()),
        journal,
        "local overrides must never enter the admitted metadata"
    );
    let table = ReducibilityTable::effective(checked.environment()).unwrap();
    assert_eq!(table.status(&name("hidden")), Reducibility::Irreducible);
    assert_eq!(table.status(&name("ordinary")), Reducibility::Semireducible);
    assert!(
        checked
            .check_source_files(
                &[b"theorem hiddenAgain : hidden = 5 := rfl"],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
        "a later source file must not inherit local transparency"
    );
    checked_from(&checked, "theorem ordinaryAgain : ordinary = 7 := rfl");
}

#[test]
fn explicit_unsafe_reducibility_allows_imported_updates_and_scopes_the_option() {
    let base = checked_from(&engine(), "@[irreducible] def hidden : Nat := 5");
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[b"attribute [reducible] hidden"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .is_err()
    );
    let checked = checked_from(
        &base,
        "set_option allowUnsafeReducibility true in\nattribute [reducible] hidden\n\
         theorem visible : hidden = 5 := rfl",
    );
    assert_eq!(
        ReducibilityTable::read(checked.environment())
            .unwrap()
            .status(&name("hidden")),
        Reducibility::Reducible,
    );
    assert!(base.check_source_files(
        &[b"set_option allowUnsafeReducibility true in\nattribute [reducible] hidden\nattribute [irreducible] hidden"],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ).is_err(), "the option must not escape its command scope");
    checked_from(
        &base,
        "set_option allowUnsafeReducibility true\nattribute [semireducible] hidden\n\
         theorem visible : hidden = 5 := rfl\nattribute [irreducible] hidden",
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn file_boundaries_restore_local_overrides_inside_one_source_batch() {
    let base = engine();
    let result = base
        .check_source_files(
            &[
                b"def g : Nat := 5\nattribute [local irreducible] g",
                b"theorem restored : g = 5 := rfl",
            ],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(result.engine.environment().contains(&name("restored")));
    assert_eq!(
        ReducibilityTable::effective(result.engine.environment())
            .unwrap()
            .status(&name("g")),
        Reducibility::Semireducible
    );
}

#[test]
fn local_transition_validation_matches_the_pin_and_failure_preserves_the_base() {
    let base = checked_from(
        &engine(),
        "def ordinary : Nat := 5\n@[irreducible] def hidden : Nat := 7\n\
         abbrev transparent : Nat := 9\ntheorem proof : 1 = 1 := rfl",
    );
    let root = base.logical_root(&KVMap::new());
    for source in [
        "attribute [local reducible] ordinary",
        "attribute [local semireducible] ordinary",
        "attribute [local irreducible] hidden",
        "attribute [local implicit_reducible] hidden",
        "attribute [local irreducible] transparent",
        "attribute [local irreducible] proof",
        "attribute [local irreducible] ordinary missing",
        "attribute [local irreducible] ordinary ordinary",
        "attribute [local semireducible] hidden ordinary",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "invalid transition was accepted: {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked_from(&base, "theorem unchanged : ordinary = 5 := rfl");
}

#[test]
fn global_updates_validate_the_local_status_and_survive_the_end_of_its_scope() {
    let source = "@[irreducible] def g : Nat := 5\nsection\n\
                  attribute [local semireducible] g\nattribute [reducible] g\n\
                  theorem inside : g = 5 := rfl\nend\n\
                  theorem outside : g = 5 := rfl";
    let result = checked_from(&engine(), source);
    assert_eq!(
        ReducibilityTable::effective(result.environment())
            .unwrap()
            .status(&name("g")),
        Reducibility::Reducible,
        "ending a local scope must retain independently published global updates"
    );
    let invalid = "def g : Nat := 5\nattribute [local irreducible] g\nattribute [reducible] g";
    assert!(
        check(invalid).is_err(),
        "global validation must read the currently active local status"
    );
}

#[test]
fn execution_uses_the_same_local_transparency_without_publishing_it() {
    let base = checked_from(&engine(), "@[irreducible] def hidden : Nat := 5");
    let source = "section\nattribute [local semireducible] hidden\n\
                  theorem visible : hidden = 5 := rfl\nend\n#eval hidden";
    let executed = base
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        executed
            .batch
            .engine
            .environment()
            .contains(&name("visible"))
    );
    assert_eq!(executed.batch.source_evaluation_indices.len(), 1);
    let index = executed.batch.source_evaluation_indices[0];
    let fln::VmExit::Returned(result) = &executed.batch.executions[index].exit else {
        panic!("expected the checked definition to execute");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some("5")
    );
    assert_eq!(
        fln_elab::reducibility::journal_digest(executed.batch.engine.environment()),
        fln_elab::reducibility::journal_digest(base.environment())
    );
}

#[test]
fn public_headers_and_private_proofs_use_their_own_transparency_worlds() {
    let module = name("LocalTransparency");
    let source = r#"module
prelude
@[irreducible] def Hidden := Nat
attribute [local semireducible] Hidden
public theorem proof (x : Nat) : x = x := by
  have privateValue : Hidden := x
  exact rfl
public def visible : Nat := 5
"#;
    let base = engine();
    let result = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    assert!(result.checked.engine.environment().contains(&name("proof")));
    let hidden = Name::str(Name::num(name("_private.LocalTransparency"), 0), "Hidden");
    assert_eq!(
        ReducibilityTable::effective(result.checked.engine.environment())
            .unwrap()
            .status(&hidden),
        Reducibility::Irreducible
    );
    let client = name("Client");
    let imported = base
        .check_source_modules(
            &[
                SourceModuleInput {
                    name: &client,
                    source: b"module\nprelude\npublic import LocalTransparency\npublic theorem client : 1 = 1 := proof 1",
                },
                SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                },
            ],
            &client,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let exported = imported.checked.engine.environment();
    assert!(!exported.contains(&hidden));
    assert!(exported.contains(&name("proof")));
    assert!(exported.contains(&name("visible")));
}

#[test]
fn partial_codegen_publishes_failure_tags_without_local_transparency() {
    let base = checked_from(
        &engine(),
        "noncomputable def secret : Nat := 41\n@[irreducible] def hidden : Nat := 5",
    );
    for body in [
        "partial def bad (n : Nat) : Nat := if n == 0 then secret else bad (n - 1)\n",
        "mutual\npartial def bad (n : Nat) : Nat := if n == 0 then secret else peer (n - 1)\npartial def peer (n : Nat) : Nat := bad n\nend\n",
    ] {
        let source = format!(
            "noncomputable section\nattribute [local semireducible] hidden\n\
             theorem visible : hidden = 5 := rfl\n{body}end"
        );
        let next = checked_from(&base, &source);
        assert!(next.environment().contains(&name("visible")));
        let tags = fln_elab::noncomputable::read(next.environment()).unwrap();
        assert!(tags.contains(&name("bad._unsafe_rec")));
        if next.environment().contains(&name("peer")) {
            assert!(tags.contains(&name("peer._unsafe_rec")));
        }
        assert_eq!(
            ReducibilityTable::effective(next.environment())
                .unwrap()
                .status(&name("hidden")),
            Reducibility::Irreducible,
            "the code-generation context must not publish its local overrides"
        );
        assert!(
            next.check_source_files(
                &[b"theorem hiddenAgain : hidden = 5 := rfl"],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err()
        );
    }
}
