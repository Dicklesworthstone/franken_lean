//! Private structure fields retain their real names, module visibility, and
//! checked implementations through source execution and physical artifacts.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleIrLimits,
};
use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, KVMap,
    Name, OleanCheckLimits, OleanModuleInput, OleanWalkBudget, OleanWriteBudget, Outcome,
    SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_elab::records::imported::ImportedStructures;
use std::collections::BTreeMap;

const SECRET: &str = r#"structure Secret where
  publicField : Nat
  private hidden : Nat := 7
  deriving Inhabited
"#;

const METHODS: &str = r#"def make (n : Nat) : Secret := { publicField := n }
def reveal (s : Secret) : Nat := s.hidden
def revealIndex (s : Secret) : Nat := s.2
def change (s : Secret) : Secret := { s with hidden := 9 }
def publicChange (s : Secret) : Secret := { s with publicField := 11 }
def named : Secret := Secret.mk 5 13
def anonymous : Secret := ⟨5, 17⟩
def defaultReveal : Nat := (default : Secret).hidden
"#;

const MIXED: &str = r#"structure Mixed where
  private first : Nat := 3
  visible : Nat := first
  private last : Nat := visible
  deriving Inhabited
def mixedValue : Nat :=
  let s : Mixed := default
  Nat.add (Nat.add s.first s.visible) s.last
def mixedOverride : Nat :=
  let s : Mixed := { first := 5 }
  Nat.add (Nat.add s.first s.visible) s.last
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private_name(module: &str, text: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(text))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 << 20),
    )))
}

fn seed() -> Engine {
    let base = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    for prerequisite in ["PUnit", "Eq", "Eq.refl", "HEq", "HEq.refl"] {
        assert!(
            base.environment().contains(&name(prerequisite)),
            "{prerequisite}"
        );
    }
    // The source seed intentionally lacks this wrapper. Supply its actual
    // checked definition so the noConfusion publication assertions exercise
    // generated declarations rather than the bootstrap dependency guard.
    assert!(!base.environment().contains(&name("Eq.ndrec")));
    base.check_source_files(
        &[
            b"abbrev Eq.ndrec.{u, v} {A : Sort v} {a : A} {motive : A -> Sort u}\n\
            (m : motive a) {b : A} (h : Eq a b) : motive b := h.rec m\n",
        ],
        &KVMap::new(),
        limits().source,
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(16 << 20)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn check(
    base: &Engine,
    files: &[(&str, &str)],
) -> Result<Outcome<SourceModuleCheck>, SourceModuleCheckError> {
    let names: Vec<_> = files.iter().map(|(module, _)| name(module)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(&inputs, &names[0], &KVMap::new(), limits())
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    check(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .unwrap()
}

fn execute(engine: &Engine, source: &str, expected: &[&str]) {
    let before = engine.logical_root(&KVMap::new());
    let result = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().source.admission.kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let values: Vec<_> = result
        .executions
        .iter()
        .map(|execution| {
            let VmExit::Returned(returned) = &execution.exit else {
                panic!("unexpected record execution: {:?}", execution.exit);
            };
            fln::nat_decimal(&returned.value).unwrap()
        })
        .collect();
    assert_eq!(values, expected);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

fn assert_shape(env: &Environment, module: &str, modern: bool) {
    let constructor = if modern {
        private_name(module, "Secret.mk")
    } else {
        name("Secret.mk")
    };
    let Some(ConstantInfo::Induct(family)) = env.find(&name("Secret")) else {
        panic!("missing Secret family");
    };
    assert_eq!(family.ctors, [constructor.clone()]);
    assert!(matches!(
        env.find(&constructor),
        Some(ConstantInfo::Ctor(_))
    ));
    assert!(matches!(
        env.find(&name("Secret.publicField")),
        Some(ConstantInfo::Defn(_))
    ));
    let structures = ImportedStructures::read(env).unwrap();
    let entry = structures.get(&name("Secret")).unwrap();
    assert_eq!(
        entry
            .fields
            .iter()
            .map(|field| (field.name.clone(), field.projection.clone()))
            .collect::<Vec<_>>(),
        [
            (name("publicField"), name("Secret.publicField")),
            (name("hidden"), private_name(module, "Secret.hidden")),
        ]
    );
    assert!(!env.contains(&name("Secret.hidden")));
}

#[test]
fn private_fields_defaults_and_constructors_execute_in_the_defining_module() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let source = format!("module\nprelude\npublic section\n{SECRET}{METHODS}{MIXED}");
        let checked = complete(&base, &[("Api", &source)]);
        let env = checked.checked.engine.environment();
        assert_shape(env, "Api", true);
        for suffix in [
            "Secret.hidden",
            "Secret.hidden._default",
            "Secret.mk._flat_ctor",
            "Mixed.first",
            "Mixed.first._default",
            "Mixed.last",
            "Mixed.last._default",
        ] {
            assert!(
                matches!(
                    env.find(&private_name("Api", suffix)),
                    Some(ConstantInfo::Defn(_))
                ),
                "missing checked private implementation {suffix}"
            );
        }
        execute(
            &checked.checked.engine,
            "#eval reveal (make 5)\n#eval revealIndex named\n#eval reveal anonymous\n\
             #eval reveal (change (make 5))\n#eval (publicChange (make 5)).publicField\n\
             #eval defaultReveal\n#eval mixedValue\n#eval mixedOverride\n",
            &["7", "13", "17", "9", "11", "7", "9", "15"],
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("Secret")));
    });
}

#[test]
fn modern_imports_preserve_public_headers_and_import_all_private_access() {
    on_stack(|| {
        let base = seed();
        let source = format!("module\nprelude\npublic section\n{SECRET}{METHODS}{MIXED}");
        let owned = complete(&base, &[("Api", &source)]);
        let exported = complete(
            &base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\npublic def observe (s : Secret) : Nat := s.publicField\n\
                     public def inhabited : Secret := default\n",
                ),
                ("Api", &source),
            ],
        );
        let private = owned.checked.engine.environment();
        let public = exported.checked.engine.environment();
        assert_shape(public, "Api", true);
        for suffix in [
            "Secret.hidden",
            "Secret.hidden._default",
            "Secret.mk._flat_ctor",
        ] {
            assert!(
                !public.contains(&private_name("Api", suffix)),
                "leaked {suffix}"
            );
        }
        for declaration in [
            "Secret.recOn",
            "Secret.casesOn",
            "Secret.noConfusionType",
            "Secret.noConfusion",
            "instInhabitedSecret.default",
            "Mixed.visible._default",
            "instInhabitedMixed.default",
        ] {
            let declaration = name(declaration);
            let Some(ConstantInfo::Axiom(header)) = public.find(&declaration) else {
                panic!(
                    "public implementation must be a checked header: {declaration:?}; found {:?}",
                    public.find(&declaration)
                );
            };
            assert!(!header.is_unsafe);
            assert_eq!(
                &header.base,
                private.find(&declaration).unwrap().constant_val()
            );
            assert!(matches!(
                private.find(&declaration),
                Some(ConstantInfo::Defn(_))
            ));
        }
        assert!(matches!(
            public.find(&name("instInhabitedSecret")),
            Some(ConstantInfo::Defn(_))
        ));
        execute(
            &exported.checked.engine,
            "#eval observe (make 5)\n#eval reveal inhabited\n",
            &["5", "7"],
        );

        let all = complete(
            &base,
            &[
                (
                    "Main",
                    "module\nprelude\npublic import Api\nimport all Api\n\
                     public def peek (s : Secret) : Nat := s.hidden\n\
                     public def rebuilt : Secret := Secret.mk 5 23\n\
                     public def changed (s : Secret) : Secret := { s with hidden := 29 }\n\
                     public def recordPattern (s : Secret) : Nat := match s with | { hidden := n, .. } => n\n\
                     public def anonymousPattern (s : Secret) : Nat := match s with | ⟨_, n⟩ => n\n\
                     public def namedPattern (s : Secret) : Nat := match s with | Secret.mk _ n => n\n",
                ),
                ("Api", &source),
            ],
        );
        assert!(matches!(
            all.checked
                .engine
                .environment()
                .find(&private_name("Api", "Secret.hidden")),
            Some(ConstantInfo::Defn(_))
        ));
        execute(
            &all.checked.engine,
            "#eval peek (make 5)\n#eval peek rebuilt\n#eval peek (changed (make 5))\n\
             #eval recordPattern (make 5)\n#eval anonymousPattern rebuilt\n#eval namedPattern (changed (make 5))\n",
            &["7", "23", "29", "7", "23", "29"],
        );
    });
}

#[test]
fn foreign_private_projection_and_constructor_access_is_refused_atomically() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let source = format!("module\nprelude\npublic section\n{SECRET}");
        for import in ["public import Api\npublic section", "import Api"] {
            for forbidden in [
                "def bad (s : Secret) : Nat := Secret.hidden s",
                "def bad (s : Secret) : Nat := s.hidden",
                "def bad (s : Secret) : Nat := s.2",
                "def bad : Nat := Secret.hidden._default",
                "def bad : Secret := Secret.mk 5 9",
                "def bad : Secret := ⟨5, 9⟩",
                "def bad : Secret := { publicField := 5 }",
                "def bad : Secret := { publicField := 5, hidden := 9 }",
                "def bad (s : Secret) : Secret := { s with publicField := 5 }",
                "def bad (s : Secret) : Secret := { s with hidden := 9 }",
                "def bad (s : Secret) : Nat := match s with | { hidden := n, .. } => n",
                "def bad (s : Secret) : Nat := match s with | ⟨_, n⟩ => n",
                "def bad (s : Secret) : Nat := match s with | Secret.mk _ n => n",
            ] {
                let consumer = format!("module\nprelude\n{import}\n{forbidden}\n");
                let error =
                    check(&base, &[("Main", &consumer), ("Api", &source)]).expect_err(&consumer);
                assert_ne!(
                    error.disposition().0,
                    "internal-fault",
                    "{consumer}\n{error:?}"
                );
                assert_eq!(base.logical_root(&KVMap::new()), before);
                assert!(!base.environment().contains(&name("Secret")));
            }
        }
    });
}

#[test]
fn legacy_imports_keep_public_construction_without_granting_private_projection_access() {
    on_stack(|| {
        let base = seed();
        let source = format!("prelude\n{SECRET}{METHODS}");
        let checked = complete(
            &base,
            &[
                (
                    "Main",
                    "prelude\nimport Api\ndef foreign : Secret := { publicField := 5, hidden := 9 }\n\
                     def changed : Secret := { foreign with hidden := 11 }\n\
                     def publicChanged : Secret := { foreign with publicField := 19 }\n\
                     def defaulted : Secret := { publicField := 13 }\n\
                     def recordPattern (s : Secret) : Nat := match s with | { hidden := n, .. } => n\n\
                     def anonymousPattern (s : Secret) : Nat := match s with | ⟨_, n⟩ => n\n\
                     def namedPattern (s : Secret) : Nat := match s with | Secret.mk _ n => n\n",
                ),
                ("Api", &source),
            ],
        );
        assert_shape(checked.checked.engine.environment(), "Api", false);
        assert!(matches!(
            checked
                .checked
                .engine
                .environment()
                .find(&private_name("Api", "Secret.hidden")),
            Some(ConstantInfo::Defn(_))
        ));
        execute(
            &checked.checked.engine,
            "#eval reveal foreign\n#eval reveal changed\n#eval reveal defaulted\n\
             #eval defaulted.publicField\n#eval recordPattern foreign\n\
             #eval anonymousPattern changed\n#eval namedPattern defaulted\n\
             #eval reveal publicChanged\n#eval publicChanged.publicField\n",
            &["9", "11", "7", "13", "9", "11", "7", "9", "19"],
        );
        let before = base.logical_root(&KVMap::new());
        for forbidden in [
            "def bad (s : Secret) : Nat := s.hidden",
            "def bad (s : Secret) : Nat := s.2",
            "def bad (s : Secret) : Nat := Secret.hidden s",
            "def bad : Nat := Secret.hidden._default",
        ] {
            let consumer = format!("prelude\nimport Api\n{forbidden}\n");
            assert!(check(&base, &[("Main", &consumer), ("Api", &source)]).is_err());
            assert_eq!(base.logical_root(&KVMap::new()), before);
        }
    });
}

#[test]
fn exported_terms_and_invalid_visibility_cannot_publish_private_implementations() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let source = format!("module\nprelude\npublic section\n{SECRET}");
        for forbidden in [
            "@[expose] def bad (s : Secret) : Nat := s.hidden",
            "abbrev bad (s : Secret) : Nat := s.hidden",
            "def bad (s : Secret) (h : Eq s.hidden 7) : Nat := 0",
            "@[expose] def bad : Secret := { publicField := 5, hidden := 9 }",
        ] {
            let local = format!("{source}{forbidden}\n");
            assert!(check(&base, &[("Api", &local)]).is_err(), "{local}");
            let consumer = format!(
                "module\nprelude\npublic import Api\nimport all Api\npublic section\n{forbidden}\n"
            );
            assert!(
                check(&base, &[("Main", &consumer), ("Api", &source)]).is_err(),
                "{consumer}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
        }
        for declaration in [
            "public structure Wrong where\n  create ::\n  private hidden : Nat\n",
            "private structure Wrong where\n  private hidden : Nat\n",
            "public structure Wrong where\n  private hidden : Nat := true\n",
            "public structure Wrong where\n  private hidden : Nat\n  hidden : Nat\n",
            "def Hidden := Nat\npublic structure Wrong where\n  x : Hidden\n",
            // The pin permits a private field to use a private type. Exported
            // type sanitization is not implemented here; refusal must not turn
            // that private name into an invented auto-implicit parameter.
            "def Hidden := Nat\npublic structure Wrong where\n  private x : Hidden\n",
            "def Hidden := Nat\npublic structure Wrong where\n  private hidden : Nat\n  visible : Hidden\n",
        ] {
            let source = format!("module\nprelude\n{declaration}");
            assert!(check(&base, &[("Api", &source)]).is_err(), "{source}");
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(!base.environment().contains(&name("Wrong")));
        }
        for declaration in [
            "public structure Named where\n  private create ::\n  private hidden : Nat\n",
            "structure Named where\n  private hidden : Nat\n",
        ] {
            let source = format!("module\nprelude\n{declaration}");
            complete(&base, &[("Api", &source)]);
        }
        // An ordinary exposed derived comparison is supported. A private
        // constructor must not bypass its guard in the standalone command's
        // existing-target fast path, or in the declaration-suffix form.
        let exposed = "module\nprelude\n@[expose] public section\n";
        complete(
            &base,
            &[(
                "Api",
                &format!(
                    "{exposed}structure Visible where\n  value : Nat\nderiving instance BEq for Visible\n"
                ),
            )],
        );
        for deriving in ["deriving BEq", "deriving instance BEq for Wrong"] {
            let source =
                format!("{exposed}structure Wrong where\n  private value : Nat\n{deriving}\n");
            assert!(check(&base, &[("Api", &source)]).is_err(), "{source}");
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(!base.environment().contains(&name("Wrong")));
            assert!(!base.environment().contains(&name("instBEqWrong")));
        }
    });
}

fn decode_constants(bytes: &[u8], dependencies: &[&[u8]]) -> BTreeMap<Name, ConstantInfo> {
    let view = fln_olean::region::OleanView::parse_with_dependencies(bytes, dependencies).unwrap();
    fln_olean::decl::DeclDecoder::new(&view, OleanWalkBudget::default())
        .decode_module_constants()
        .unwrap()
        .into_iter()
        .map(|constant| (constant.name().clone(), constant))
        .collect()
}

#[test]
fn physical_private_record_artifacts_preserve_the_public_and_private_interfaces() {
    on_stack(|| {
        // Bool has a supported standalone IR carrier. The checked transport
        // prerequisite remains logical-only; the record's executable members
        // and all four generated logical wrappers retain their actual bodies.
        let source = r#"module
prelude
public section
axiom lcErased : Type
axiom lcAny : Type
axiom lcVoid : Type
universe u
set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit
inductive Eq {A : Sort u} : A → A → Prop where
  | refl (a : A) : Eq a a
noncomputable abbrev Eq.ndrec.{u1, u2} {A : Sort u2} {a : A} {motive : A → Sort u1}
    (m : motive a) {b : A} (h : Eq a b) : motive b := h.rec m
inductive HEq : {A : Sort u} → A → {B : Sort u} → B → Prop where
  | refl (a : A) : HEq a a
inductive Bool where | false | true
structure Secret where
  publicField : Bool
  private hidden : Bool := Bool.true
def make (value : Bool) : Secret := { publicField := value }
def reveal (s : Secret) : Bool := s.hidden
"#;
        let empty = Engine::builder().build_empty();
        let module = name("PrivateRecords");
        let mut built = empty
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                limits(),
                OleanWriteBudget::default(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let artifact = &mut built.artifacts[0];
        let encoded = artifact
            .compile_ir(SourceModuleIrLimits::new(EngineExecutionLimits::new(
                limits().source.admission.kernel,
            )))
            .unwrap()
            .into_complete()
            .unwrap();
        let companions = artifact.companions.as_ref().unwrap();
        let directory = std::env::temp_dir().join(format!(
            "fln-private-record-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let paths = [
            "PrivateRecords.olean",
            "PrivateRecords.olean.server",
            "PrivateRecords.olean.private",
        ];
        for (path, bytes) in
            paths
                .iter()
                .zip([&artifact.bytes, &companions.server, &companions.private])
        {
            std::fs::write(directory.join(path), bytes).unwrap();
        }
        std::fs::write(directory.join("PrivateRecords.ir"), &encoded.bytes).unwrap();
        let parts = paths.map(|path| std::fs::read(directory.join(path)).unwrap());
        let public = decode_constants(&parts[0], &[]);
        let server = decode_constants(&parts[1], &[&parts[0]]);
        let private = decode_constants(&parts[2], &[&parts[0], &parts[1]]);
        for interface in [&public, &server] {
            assert!(matches!(
                interface.get(&private_name("PrivateRecords", "Secret.mk")),
                Some(ConstantInfo::Ctor(_))
            ));
            assert!(matches!(
                interface.get(&name("Secret.publicField")),
                Some(ConstantInfo::Defn(_))
            ));
            for wrapper in [
                "Secret.recOn",
                "Secret.casesOn",
                "Secret.noConfusionType",
                "Secret.noConfusion",
            ] {
                assert!(
                    matches!(interface.get(&name(wrapper)), Some(ConstantInfo::Axiom(_))),
                    "{wrapper}: {:?}",
                    interface.get(&name(wrapper))
                );
            }
            for suffix in [
                "Secret.hidden",
                "Secret.hidden._default",
                "Secret.mk._flat_ctor",
            ] {
                assert!(
                    !interface.contains_key(&private_name("PrivateRecords", suffix)),
                    "leaked {suffix}"
                );
            }
        }
        for suffix in [
            "Secret.hidden",
            "Secret.hidden._default",
            "Secret.mk._flat_ctor",
        ] {
            assert!(matches!(
                private.get(&private_name("PrivateRecords", suffix)),
                Some(ConstantInfo::Defn(_))
            ));
        }
        let fresh = empty
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &module,
                    artifact: &parts[0],
                    server_artifact: Some(&parts[1]),
                    private_artifact: Some(&parts[2]),
                }],
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    16 << 20,
                    limits().source.admission.kernel,
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_shape(fresh.engine.environment(), "PrivateRecords", true);
        let consumer = name("Main");
        let all_source = "module\nprelude\nimport all PrivateRecords\n\
            noncomputable def selected : Bool := ({ publicField := Bool.false } : Secret).hidden\n\
            theorem checkedDefault (P : Bool -> Prop) (h : P Bool.true) : P selected := h\n";
        for text in [
            "module\nprelude\npublic import PrivateRecords\npublic def observe (s : Secret) : Bool := s.publicField\n",
            all_source,
        ] {
            fresh
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source: text.as_bytes(),
                    }],
                    &consumer,
                    &KVMap::new(),
                    limits(),
                    None,
                )
                .unwrap_or_else(|error| panic!("{text}\n{error:?}"))
                .into_complete()
                .unwrap();
        }
        let forbidden = "module\nprelude\npublic import PrivateRecords\n\
            def leak (s : Secret) : Bool := s.hidden\n";
        assert!(
            fresh
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source: forbidden.as_bytes()
                    }],
                    &consumer,
                    &KVMap::new(),
                    limits(),
                    None,
                )
                .is_err()
        );
        assert!(empty.environment().is_empty());

        // The pin is an independent reader of the native files, never a source
        // fallback or runtime component. Even a noncomputable import-all
        // consumer requires the producer's genuine emitted IR companion.
        if let Some(compiler) = std::env::var_os("FLN_REFERENCE_LEAN") {
            let consumer_path = directory.join("Consumer.lean");
            std::fs::write(&consumer_path, all_source).unwrap();
            let output = std::process::Command::new(compiler)
                .arg(&consumer_path)
                .current_dir(&directory)
                .env("LEAN_PATH", &directory)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "pin could not use native private record metadata:\n{}\n{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        } else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "exact pin executable required"
            );
            eprintln!("SKIP: pin physical private-record consumer (FLN_REFERENCE_LEAN absent)");
        }
    });
}
