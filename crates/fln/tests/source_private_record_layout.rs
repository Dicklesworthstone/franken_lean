//! Real Prelude record layouts, inherited metadata, checked default helpers,
//! and executable private defaults complement the private-field access matrix.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{
    SourceModuleCheck, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, Expr, KVMap, Level,
    Name, OleanCheckLimits, OleanModuleInput, OleanWalkBudget, OleanWriteBudget, Outcome,
    SourceCheckLimits, SourceModuleInput, VmExit,
};
use fln_elab::records::defaults::RecordDefaults;
use fln_elab::records::imported::ImportedStructures;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use std::sync::OnceLock;

const STACK: usize = 128 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn private_name(module: &str, text: &str) -> Name {
    Name::num(name(&format!("_private.{module}")), 0).append_core(&name(text))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

fn on_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

fn prelude() -> &'static SourceOleanImport {
    static PRELUDE: OnceLock<SourceOleanImport> = OnceLock::new();
    PRELUDE.get_or_init(|| {
        // Import the real checked dependencies of Macro.State: Name,
        // MacroScope, Prod, List, and the deriving/default interfaces.
        // The fresh PrivateAudit.State family below is always source built.
        let module = name("Init.Prelude");
        let inputs = [OleanModuleInput {
            name: &module,
            artifact: include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean"),
            server_artifact: Some(include_bytes!(
                "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
            )),
            private_artifact: Some(include_bytes!(
                "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
            )),
        }];
        Engine::builder()
            .build_empty()
            .import_olean_modules_for_source(
                &inputs,
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .unwrap()
    })
}

fn modules(
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
    base.check_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
    )
}

fn complete(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    modules(base, files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .expect("both checking seats complete")
}

fn modules_with_prelude(
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
    prelude().check_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        None,
    )
}

fn complete_with_prelude(files: &[(&str, &str)]) -> SourceModuleCheck {
    modules_with_prelude(files)
        .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
        .into_complete()
        .expect("both checking seats complete")
}

fn values(engine: &Engine, source: &str) -> Vec<String> {
    let checked = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("native execution completes");
    checked
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let VmExit::Returned(value) = &checked.executions[index].exit else {
                panic!("expected returned Nat: {:?}", checked.executions[index]);
            };
            fln::nat_decimal(&value.value).expect("Nat result")
        })
        .collect()
}

const METHODS: &str = r#"
def ownQualified (s : State) : Nat := (State.expandedMacroDecls s).length
def ownDot (s : State) : Nat := s.expandedMacroDecls.length
def ownConstruct : State := {
  macroScope := 7,
  expandedMacroDecls := List.cons Name.anonymous List.nil
}
def ownNamedCtor : State := State.mk (macroScope := 9) (traceMsgs := List.nil)
  (expandedMacroDecls := List.cons Name.anonymous List.nil)
def ownUpdate (s : State) : State := {
  s with expandedMacroDecls := List.cons Name.anonymous (List.cons Name.anonymous List.nil)
}
def ownAnonymous : State := ⟨11, List.nil, List.cons Name.anonymous List.nil⟩
def ownDotted : State := .mk 13 List.nil (List.cons Name.anonymous List.nil)
def ownPattern (s : State) : Nat := match s with | ⟨scope, _, _⟩ => scope
def ownNamedPattern (s : State) : Nat := match s with | { macroScope := scope, .. } => scope
public def make (n : Nat) : State := { macroScope := n }
public def count (s : State) : Nat := s.expandedMacroDecls.length
public def setScope (s : State) (n : Nat) : State := { s with macroScope := n }
public def ownSnapshot : Nat :=
  Nat.add (Nat.add (ownQualified ownConstruct) (ownDot ownNamedCtor))
    (ownDot (ownUpdate ownConstruct))
public def sugarSnapshot : Nat := Nat.add (ownPattern ownAnonymous) (ownNamedPattern ownDotted)
theorem ownCount : Eq (ownQualified ownConstruct) 1 := Eq.refl 1
theorem ownSugar : Eq sugarSnapshot 24 := Eq.refl 24
"#;

fn provider() -> String {
    let prelude = include_str!("../../../vendor/lean4-src/src/Init/Prelude.lean");
    let start = prelude
        .find("structure State where")
        .expect("the pin declares Macro.State");
    let declaration = &prelude[start..];
    let end = declaration
        .find("\n\nend Macro")
        .expect("the full Macro.State command includes deriving Inhabited");
    format!(
        "module\nprelude\npublic import Init.Prelude\nnamespace PrivateAudit\nopen Lean\npublic {}\n{METHODS}\nend PrivateAudit\n",
        &declaration[..end]
    )
}

const CONSUMER: &str = r#"module
prelude
public import PrivateFields
open PrivateAudit
public def publicRead (s : State) : Nat := s.macroScope
public def publicDefault : State := default
public def caseCount (s : State) : Nat :=
  List.length (State.casesOn (motive := fun _ => List Lean.Name) s (fun _ _ names => names))
"#;

fn check_layout(environment: &Environment, exported: bool) {
    let record = name("PrivateAudit.State");
    let constructor = private_name("PrivateFields", "PrivateAudit.State.mk");
    let projection = private_name("PrivateFields", "PrivateAudit.State.expandedMacroDecls");
    let private_default = Name::str(projection.clone(), "_default");
    let Some(ConstantInfo::Induct(family)) = environment.find(&record) else {
        panic!("the source structure's logical family must survive export");
    };
    assert_eq!(family.ctors, std::slice::from_ref(&constructor));
    assert!(matches!(
        environment.find(&constructor),
        Some(ConstantInfo::Ctor(info)) if info.num_fields == 3 && info.induct == record
    ));
    assert!(!environment.contains(&name("PrivateAudit.State.mk")));
    assert!(!environment.contains(&name("PrivateAudit.State.expandedMacroDecls")));

    let structures = ImportedStructures::read(environment).unwrap();
    let structure = structures
        .get(&record)
        .expect("retained structure identity");
    assert_eq!(
        structure
            .fields
            .iter()
            .map(|field| field.name.clone())
            .collect::<Vec<_>>(),
        [
            name("macroScope"),
            name("traceMsgs"),
            name("expandedMacroDecls")
        ]
    );
    assert_eq!(
        structure.fields[0].projection,
        name("PrivateAudit.State.macroScope")
    );
    assert_eq!(
        structure.fields[1].projection,
        name("PrivateAudit.State.traceMsgs")
    );
    assert_eq!(structure.fields[2].projection, projection);
    let defaults = RecordDefaults::read(environment).unwrap();
    for field in 0..3 {
        assert_eq!(
            defaults.helper(&record, field),
            None,
            "declared defaults use ordinary dependency-pruned helpers"
        );
    }
    let names = Expr::const_(name("Lean.Name"), vec![]);
    let message = Expr::app(
        Expr::app(
            Expr::const_(name("Prod"), vec![Level::zero(), Level::zero()]),
            names.clone(),
        ),
        Expr::const_(name("String"), vec![]),
    );
    let list_type = |element| Expr::app(Expr::const_(name("List"), vec![Level::zero()]), element);
    let public_default = environment
        .find(&name("PrivateAudit.State.traceMsgs._default"))
        .expect("the public field retains its checked default helper");
    assert_eq!(public_default.constant_val().type_, list_type(message));
    assert!(public_default.constant_val().level_params.is_empty());
    if exported {
        assert!(matches!(public_default, ConstantInfo::Axiom(_)));
        assert!(!environment.contains(&projection));
        assert!(!environment.contains(&private_default));
        assert!(!environment.contains(&Name::str(constructor, "_flat_ctor")));
    } else {
        assert!(matches!(
            public_default,
            ConstantInfo::Defn(info) if info.safety == DefinitionSafety::Safe
        ));
        for declaration in [
            projection,
            private_default.clone(),
            Name::str(constructor, "_flat_ctor"),
        ] {
            assert!(matches!(
                environment.find(&declaration),
                Some(ConstantInfo::Defn(_))
            ));
        }
        let Some(ConstantInfo::Defn(info)) = environment.find(&private_default) else {
            panic!("the defining module retains the private default body");
        };
        assert_eq!(info.safety, DefinitionSafety::Safe);
        assert!(info.base.level_params.is_empty());
        assert_eq!(info.base.type_, list_type(names));
    }
    for suffix in ["rec", "recOn", "casesOn"] {
        assert!(environment.contains(&name(&format!("PrivateAudit.State.{suffix}"))));
    }
}

#[test]
fn the_actual_macro_state_shape_keeps_private_members_and_complete_logical_layout() {
    on_stack(|| {
        let base = &prelude().engine;
        let before = base.logical_root(&KVMap::new());
        let imported_structure = ImportedStructures::read(base.environment())
            .unwrap()
            .get(&name("Lean.Macro.State"))
            .expect("the actual imported Macro.State metadata exists")
            .clone();
        let source = provider();
        let checked = complete_with_prelude(&[("PrivateFields", &source)]);
        check_layout(checked.checked.engine.environment(), false);
        assert_eq!(
            ImportedStructures::read(checked.checked.engine.environment())
                .unwrap()
                .get(&imported_structure.name),
            Some(&imported_structure),
            "source registration cannot invalidate inherited private-field metadata"
        );
        assert!(matches!(
            checked
                .checked
                .engine
                .environment()
                .find(&private_name("PrivateFields", "PrivateAudit.ownCount")),
            Some(ConstantInfo::Thm(_))
        ));
        assert_eq!(
            values(
                &checked.checked.engine,
                "#eval PrivateAudit.ownSnapshot\n#eval PrivateAudit.sugarSnapshot"
            ),
            ["4", "24"]
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(!base.environment().contains(&name("PrivateAudit.State")));
    });
}

#[test]
fn public_imports_keep_methods_defaults_and_logical_cases_without_private_projections() {
    on_stack(|| {
        let base = &prelude().engine;
        let before = base.logical_root(&KVMap::new());
        let source = provider();
        let checked = complete_with_prelude(&[("Consumer", CONSUMER), ("PrivateFields", &source)]);
        check_layout(checked.checked.engine.environment(), true);
        // The pin permits casesOn to expose the logical field. Source privacy
        // never erases constructor arguments or grants a new proof boundary.
        assert_eq!(
            values(
                &checked.checked.engine,
                r#"
#eval PrivateAudit.ownSnapshot
#eval publicRead (PrivateAudit.make 42)
#eval publicRead publicDefault
#eval PrivateAudit.count publicDefault
#eval caseCount (PrivateAudit.make 42)
#eval publicRead (PrivateAudit.setScope (PrivateAudit.make 1) 17)
"#,
            ),
            ["4", "42", "0", "0", "0", "17"]
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn public_field_types_and_defaults_cannot_depend_on_private_predecessors() {
    on_stack(|| {
        let base = &prelude().engine;
        let before = base.logical_root(&KVMap::new());
        for source in [
            "private inductive Hidden where | token\npublic structure InvalidState where\n  value : Hidden\n  private secret : Nat := 0\n",
            "private def hidden : Nat := 7\npublic structure InvalidState where\n  value : Nat := hidden\n  private secret : Nat := 0\n",
        ] {
            let source = format!(
                "module\nprelude\npublic import Init.Prelude\npublic def sentinelPrefix : Nat := 99\n{source}"
            );
            assert!(
                modules_with_prelude(&[("InvalidFields", &source)]).is_err(),
                "{source}"
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            for absent in ["sentinelPrefix", "InvalidState", "stolen"] {
                assert!(!base.environment().contains(&name(absent)));
            }
            assert!(
                !base
                    .environment()
                    .contains(&private_name("InvalidFields", "InvalidState"))
            );
        }
    });
}

#[test]
fn private_record_defaults_survive_a_fresh_physical_module_import() {
    on_stack(|| {
        // Declared defaults are emitted as ordinary dependency-pruned helpers.
        // Reimport the physical artifact and execute the public method whose
        // implementation uses a private default distinct from the public field.
        let source = r#"module
prelude
universe u
public axiom lcErased : Type
public axiom lcAny : Type
public axiom lcVoid : Type
public def id {α : Sort u} (x : α) : α := x
public abbrev optParam (α : Sort u) (default : α) : Sort u := α
public inductive Token where | first | second
public structure Packet where
  value : Token
  private secret : Token := Token.second
public def defaultValue : Token := ({ value := Token.first } : Packet).secret
theorem ownDefault (P : Token → Prop) (h : P Token.second) :
    P (({ value := Token.first } : Packet).secret) := h
"#;
        let base = Engine::builder().build_empty();
        let before = base.logical_root(&KVMap::new());
        let module = name("PrivateDefaultArtifact");
        let checked = complete(&base, &[("PrivateDefaultArtifact", source)]);
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("Packet"))
        );
        assert_eq!(checked.checked.theorems, 1);
        assert!(
            checked
                .checked
                .engine
                .environment()
                .contains(&name("defaultValue"))
        );
        assert_eq!(
            RecordDefaults::read(checked.checked.engine.environment())
                .unwrap()
                .helper(&name("Packet"), 1),
            None,
            "the public result does not expose the private default helper"
        );
        let built = base
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                OleanWriteBudget::default(),
            )
            .unwrap()
            .into_complete()
            .expect("ordinary declared defaults have a complete artifact encoding");
        assert_eq!(built.artifacts.len(), 1);
        let artifact = &built.artifacts[0];
        let companions = artifact.companions.as_ref().expect("modern module regions");
        let loaded = base
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &module,
                    artifact: &artifact.bytes,
                    server_artifact: Some(&companions.server),
                    private_artifact: Some(&companions.private),
                }],
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .expect("both checkers admit the private-default artifact");
        let env = loaded.engine.environment();
        let constructor = private_name("PrivateDefaultArtifact", "Packet.mk");
        let projection = private_name("PrivateDefaultArtifact", "Packet.secret");
        let Some(ConstantInfo::Induct(family)) = env.find(&name("Packet")) else {
            panic!("the imported record family is present");
        };
        assert_eq!(family.ctors, std::slice::from_ref(&constructor));
        assert!(matches!(
            env.find(&constructor),
            Some(ConstantInfo::Ctor(_))
        ));
        let hidden_members = [
            projection.clone(),
            Name::str(projection.clone(), "_default"),
            Name::str(constructor, "_flat_ctor"),
        ];
        // The retained receipt owns the complete checked companion closure.
        // Its public region and ordinary source imports enforce visibility;
        // the complete implementations remain necessary for later execution.
        let public_view =
            fln_olean::region::OleanView::parse_with_dependencies(&artifact.bytes, &[]).unwrap();
        let public_constants =
            fln_olean::decl::DeclDecoder::new(&public_view, OleanWalkBudget::default())
                .decode_module_constants()
                .unwrap();
        for hidden in &hidden_members {
            assert!(
                matches!(env.find(hidden), Some(ConstantInfo::Defn(_))),
                "missing checked implementation {}",
                hidden.to_display_string()
            );
            assert!(
                public_constants.iter().all(|info| info.name() != hidden),
                "private implementation leaked into the physical public region: {}",
                hidden.to_display_string()
            );
        }
        let structures = ImportedStructures::read(env).unwrap();
        let structure = structures.get(&name("Packet")).unwrap();
        assert_eq!(structure.fields.len(), 2);
        assert_eq!(structure.fields[0].projection, name("Packet.value"));
        assert_eq!(structure.fields[1].projection, projection);
        assert_eq!(
            RecordDefaults::read(env)
                .unwrap()
                .helper(&name("Packet"), 1),
            None
        );

        let imported_root = loaded.engine.logical_root(&KVMap::new());
        let consumer = name("DefaultConsumer");
        let consumer_source = b"module\nprelude\npublic import PrivateDefaultArtifact\npublic def observedDefault : Token := defaultValue\npublic def observedFirst : Token := Token.first\n";
        let checked = loaded
            .check_source_modules(
                &[SourceModuleInput {
                    name: &consumer,
                    source: consumer_source,
                }],
                &consumer,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                None,
            )
            .unwrap()
            .into_complete()
            .expect("a fresh consumer can use the imported public default-backed method");
        for hidden in &hidden_members {
            assert!(
                !checked.checked.engine.environment().contains(hidden),
                "ordinary import exposed {}",
                hidden.to_display_string()
            );
        }
        let forbidden = b"module\nprelude\npublic import PrivateDefaultArtifact\n\
            public def sentinel : Token := Token.first\n\
            public def stolen (p : Packet) : Token := p.secret\n";
        assert!(
            loaded
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source: forbidden,
                    }],
                    &consumer,
                    &KVMap::new(),
                    SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                    None,
                )
                .is_err()
        );
        assert!(!loaded.engine.environment().contains(&name("sentinel")));
        assert!(!loaded.engine.environment().contains(&name("stolen")));
        let executed = checked
            .checked
            .engine
            .execute_source_definitions(
                &[b"#eval observedDefault\n#eval observedFirst"],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().kernel),
            )
            .unwrap()
            .into_complete()
            .expect("imported private default execution completes");
        let returned: Vec<_> = executed
            .source_evaluation_indices
            .iter()
            .map(|&index| {
                let VmExit::Returned(value) = &executed.executions[index].exit else {
                    panic!("the imported default-backed method must return");
                };
                fln::vm_value_kind(&value.value)
            })
            .collect();
        assert_eq!(
            returned,
            [
                fln_vm::interpreter::ValueKind::Ctor(1),
                fln_vm::interpreter::ValueKind::Ctor(0),
            ]
        );
        assert_eq!(loaded.engine.logical_root(&KVMap::new()), imported_root);
        assert!(base.environment().is_empty());
        assert_eq!(base.logical_root(&KVMap::new()), before);
    });
}

#[test]
fn private_constructors_preserve_public_tactic_quotation_bodies_after_import() {
    on_stack(|| {
        let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
        else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Init.Tactics dependencies are required"
            );
            eprintln!("SKIP: pinned Init.Tactics artifacts (FLN_REFERENCE_LIB absent)");
            return;
        };
        // These are genuine retained imports, including the declarations of
        // autoParam and rfl syntax. No fabricated Syntax representation or raw
        // environment insertion can conceal a missing quotation predecessor.
        let names = ["Init.Prelude", "Init.Coe", "Init.Notation", "Init.Tactics"].map(name);
        let bytes: Vec<_> = names
            .iter()
            .map(|module| {
                let path = library
                    .join(module.to_display_string().replace('.', "/"))
                    .with_extension("olean");
                [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ]
            })
            .collect();
        let mut imports: Vec<_> = names
            .iter()
            .zip(&bytes)
            .map(|(module, parts)| OleanModuleInput {
                name: module,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            })
            .collect();
        let base = Engine::builder().build_empty();
        let before = base.logical_root(&KVMap::new());
        let dependencies = base
            .import_olean_modules_for_source(
                &imports,
                std::slice::from_ref(&names[3]),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .expect("the actual tactic prerequisites pass both checking seats");
        let module = name("HeaderQuote");
        let source = br#"module
prelude
public import Init.Tactics
public structure HeaderProof where
  private build ::
  value : Nat
  proof : Eq Nat.zero Nat.zero := by rfl
public def make : HeaderProof := { value := 42 }
"#;
        let built = dependencies
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source,
                }],
                &module,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                OleanWriteBudget::default(),
            )
            .unwrap()
            .into_complete()
            .expect("the checked public header quotation has an artifact encoding");
        let quotation = name("HeaderProof.proof._autoParam");
        let Some(ConstantInfo::Defn(original)) =
            built.checked.checked.engine.environment().find(&quotation)
        else {
            panic!("the defining module publishes the exact tracked quotation");
        };
        assert_eq!(original.safety, DefinitionSafety::Safe);
        assert_eq!(
            original.base.type_,
            Expr::const_(name("Lean.Syntax"), vec![])
        );
        assert!(original.base.level_params.is_empty());
        assert!(!original.value.has_fvar());
        assert!(!original.value.has_expr_mvar());
        assert!(!original.value.has_level_mvar());
        let expected = ConstantInfo::Defn(original.clone());
        assert_eq!(built.artifacts.len(), 1);
        let artifact = &built.artifacts[0];
        let companions = artifact.companions.as_ref().expect("modern module regions");
        imports.push(OleanModuleInput {
            name: &module,
            artifact: &artifact.bytes,
            server_artifact: Some(&companions.server),
            private_artifact: Some(&companions.private),
        });
        let loaded = base
            .import_olean_modules_for_source(
                &imports,
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .expect("the fresh physical import retains the public quotation body");
        assert_eq!(
            loaded.engine.environment().find(&quotation),
            Some(&expected)
        );
        let consumer = name("QuoteConsumer");
        let consumer_source = b"module\nprelude\npublic import HeaderQuote\n\
            public def observe (p : HeaderProof) : Nat := p.value\n";
        let checked = loaded
            .check_source_modules(
                &[SourceModuleInput {
                    name: &consumer,
                    source: consumer_source,
                }],
                &consumer,
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
                None,
            )
            .unwrap()
            .into_complete()
            .expect("ordinary consumers retain closed public quotation data");
        assert_eq!(
            checked.checked.engine.environment().find(&quotation),
            Some(&expected)
        );
        assert_eq!(
            values(&checked.checked.engine, "#eval observe make"),
            ["42"]
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(base.environment().is_empty());
    });
}
