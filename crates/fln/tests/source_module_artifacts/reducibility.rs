//! Semireducible defaults are semantic policy, not explicit olean attributes.
#![forbid(unsafe_code)]
use super::*;
use fln_elab::reducibility::{Reducibility, known_status, table};
use fln_olean::source_extensions::ReducibilityStatus;

const SOURCE: &str = r#"prelude
axiom lcAny : Type
axiom lcErased : Type
universe u
def id {A : Sort u} (x : A) : A := x
inductive Token where | mk
class Choice where
  value : Token
instance dataChoice : Choice := Choice.mk Token.mk
class Law : Prop where
  proof : ∀ (P : Prop), P → P
instance proofLaw : Law := Law.mk (fun _ h => h)
structure WithDefault where
  value : Token := Token.mk
@[instance] def attributed : Choice := Choice.mk Token.mk
def manual : Choice := Choice.mk Token.mk
attribute [instance] manual
def explicit : Token := Token.mk
set_option allowUnsafeReducibility true
attribute [semireducible] explicit
"#;

#[test]
fn default_statuses_survive_cache_and_physical_import_without_inventing_attributes() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let module = name("Main");
    let inputs = [SourceModuleInput {
        name: &module,
        source: SOURCE.as_bytes(),
    }];
    let cold = session
        .compile(&inputs, &module, OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let warm = session
        .compile(&inputs, &module, OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (1, 0));
    assert_eq!(warm.artifacts[0].bytes, cold.artifacts[0].bytes);
    let rows = metadata(&warm.artifacts[0].bytes);
    for default in [
        "Choice.value",
        "WithDefault.value._default",
        "proofLaw",
        "attributed",
        "manual",
    ] {
        assert!(
            !rows
                .reducibility
                .iter()
                .any(|row| row.declaration == name(default)),
            "an unset default must stay absent from reducibilityCore: {default}"
        );
    }
    for (declaration, status) in [
        ("dataChoice", ReducibilityStatus::ImplicitReducible),
        ("explicit", ReducibilityStatus::Semireducible),
    ] {
        assert!(
            rows.reducibility
                .iter()
                .any(|row| row.declaration == name(declaration) && row.status == status),
            "the explicitly recorded status must survive: {declaration}"
        );
    }
    assert!(rows.reducibility_extra.is_empty());
    let loaded = imported(&warm);
    for engine in [&warm.checked.checked.engine, &loaded.engine] {
        let statuses = table(engine.environment()).unwrap();
        for declaration in [
            "Choice.value",
            "WithDefault.value._default",
            "proofLaw",
            "attributed",
            "manual",
            "explicit",
        ] {
            assert_eq!(
                statuses.status(&name(declaration)),
                Reducibility::Semireducible
            );
        }
        for declaration in ["Choice.value", "WithDefault.value._default"] {
            assert_eq!(
                known_status(engine.environment(), &name(declaration)).unwrap(),
                Some(Reducibility::Semireducible),
                "Abbrev hints must not permit reducible unfolding: {declaration}"
            );
        }
        assert_eq!(
            statuses.status(&name("dataChoice")),
            Reducibility::ImplicitReducible
        );
        engine
            .check_source_files(
                &[br#"
def selected : Choice := { value := Token.mk }
def fromDefault : WithDefault := {}
theorem projected (P : Token -> Prop) (h : P Token.mk) : P selected.value := h
theorem defaulted (P : Token -> Prop) (h : P Token.mk) : P fromDefault.value := h
theorem law (P : Prop) : P -> P := @Law.proof proofLaw P
"#],
                &KVMap::new(),
                limits().source,
            )
            .unwrap()
            .into_complete()
            .unwrap();
    }
}

#[test]
fn explicit_overrides_of_generated_defaults_survive_native_and_physical_imports() {
    let source = format!(
        "{SOURCE}\nattribute [semireducible] Choice.value\n\
         attribute [irreducible] WithDefault.value._default\n"
    );
    let built = compiled(&[("Main", &source)]);
    let rows = metadata(&built.artifacts[0].bytes);
    for (declaration, status) in [
        ("Choice.value", ReducibilityStatus::Semireducible),
        (
            "WithDefault.value._default",
            ReducibilityStatus::Irreducible,
        ),
    ] {
        assert!(
            rows.reducibility
                .iter()
                .any(|row| row.declaration == name(declaration) && row.status == status)
        );
    }
    let loaded = imported(&built);
    for engine in [&built.checked.checked.engine, &loaded.engine] {
        assert_eq!(
            known_status(engine.environment(), &name("Choice.value")).unwrap(),
            Some(Reducibility::Semireducible)
        );
        assert_eq!(
            known_status(engine.environment(), &name("WithDefault.value._default")).unwrap(),
            Some(Reducibility::Irreducible),
            "a later imported default marker must not erase explicit opacity"
        );
    }
}

#[test]
fn imported_semireducible_overrides_remain_ordered_extra_entries() {
    let built = compiled(&[
        (
            "Main",
            "prelude\nimport Lib\nset_option allowUnsafeReducibility true\n\
                  attribute [irreducible] Choice.value\n\
                  attribute [semireducible] Choice.value",
        ),
        ("Lib", SOURCE),
    ]);
    let rows = metadata(&built.artifacts[1].bytes);
    assert!(rows.reducibility.is_empty());
    assert_eq!(
        rows.reducibility_extra
            .iter()
            .map(|row| (row.declaration.clone(), row.status))
            .collect::<Vec<_>>(),
        [
            (name("Choice.value"), ReducibilityStatus::Irreducible),
            (name("Choice.value"), ReducibilityStatus::Semireducible),
        ]
    );
    let loaded = imported(&built);
    for engine in [&built.checked.checked.engine, &loaded.engine] {
        assert_eq!(
            known_status(engine.environment(), &name("Choice.value")).unwrap(),
            Some(Reducibility::Semireducible)
        );
    }
}

#[test]
fn imported_instance_attributes_preserve_existing_reducibility_without_new_status_rows() {
    let base = r#"prelude
class inductive Choice where | chosen
def ordinary : Choice := Choice.chosen
@[reducible] def transparent : Choice := Choice.chosen
@[irreducible] def opaqueChoice : Choice := Choice.chosen
instance existing : Choice := Choice.chosen
"#;
    for (registration, scope) in [
        ("attribute [instance] ordinary transparent opaqueChoice", ""),
        (
            "namespace Regional\nattribute [scoped instance] ordinary transparent opaqueChoice\nend Regional",
            "open scoped Regional\n",
        ),
    ] {
        let adapter = format!("prelude\nimport Base\n{registration}");
        let built = compiled(&[("Main", &adapter), ("Base", base)]);
        let artifact = built
            .artifacts
            .iter()
            .find(|artifact| artifact.name == name("Main"))
            .unwrap();
        assert_eq!(artifact.report.constants, 0);
        let rows = metadata(&artifact.bytes);
        assert_eq!(rows.instances.len(), 3);
        assert!(rows.reducibility.is_empty());
        assert!(rows.reducibility_extra.is_empty());
        let loaded = imported(&built);
        for engine in [&built.checked.checked.engine, &loaded.engine] {
            let statuses = table(engine.environment()).unwrap();
            for (declaration, status) in [
                ("ordinary", Reducibility::Semireducible),
                ("transparent", Reducibility::Reducible),
                ("opaqueChoice", Reducibility::Irreducible),
                ("existing", Reducibility::ImplicitReducible),
            ] {
                assert_eq!(statuses.status(&name(declaration)), status, "{declaration}");
            }
            engine
                .check_source_files(
                    &[format!(
                        "{scope}def selected [choice : Choice] : Choice := choice\n\
                         def use : Choice := selected"
                    )
                    .as_bytes()],
                    &KVMap::new(),
                    limits().source,
                )
                .unwrap()
                .into_complete()
                .unwrap();
        }
    }
}

#[test]
fn imported_default_helpers_keep_semireducible_symmetry_headers() {
    let source = r#"prelude
axiom lcAny : Type
axiom lcErased : Type
universe u
@[reducible] def id {A : Sort u} (x : A) : A := x
inductive Color where | red | blue
structure TelescopeDefault where
  alias : Color -> Color -> Type := fun _ _ => Color -> Color
axiom aliasResult (a b : Color) : TelescopeDefault.alias._default a b
attribute [symm] aliasResult
"#;
    let built = compiled(&[("Main", source)]);
    let helper = name("TelescopeDefault.alias._default");
    assert!(matches!(
        built.checked.checked.engine.environment().find(&helper),
        Some(fln::ConstantInfo::Defn(definition))
            if definition.hints == fln::ReducibilityHints::Abbrev
    ));
    let rows = metadata(&built.artifacts[0].bytes);
    assert!(
        rows.reducibility
            .iter()
            .all(|row| row.declaration != helper)
    );
    assert_eq!(rows.symms.len(), 1);
    let loaded = imported(&built);
    for engine in [&built.checked.checked.engine, &loaded.engine] {
        assert_eq!(
            known_status(engine.environment(), &helper).unwrap(),
            Some(Reducibility::Semireducible)
        );
        let symms = fln_elab::symm::read(engine.environment()).unwrap();
        assert_eq!(symms.len(), 1);
        assert_eq!(symms[0].lemma.declaration, name("aliasResult"));
        engine
            .check_source_files(
                &[b"noncomputable def useAlias (a b : Color) : TelescopeDefault.alias._default a b := aliasResult a b"],
                &KVMap::new(),
                limits().source,
            )
            .unwrap()
            .into_complete()
            .unwrap();
    }
}
