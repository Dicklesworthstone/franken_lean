//! The actual pinned Prelude supplies structure identities and method defaults.
//! No seed replacement or fabricated class inventory participates in this test.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, CheckerAdmissionGround, ConstantInfo, Engine, EngineAdmissionLimits,
    EngineExecutionLimits, Environment, FlbcExecutionLimits, IndependentReading, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanModuleInput, SourceCheckLimits, VmExit,
};
use fln_comp::flbc::{CodecLimits, decode_canonical, encode_canonical};
use fln_core::expr::BinderInfo;
use fln_elab::records::imported::{
    ImportedStructures, StructureEntry, StructureField, StructureParent,
};
use std::path::PathBuf;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 64 * 1024 * 1024;
const SOURCE: &str = include_str!("source_imported_structure_parents.lean");
const HEADER: &str = "prelude\nimport Init.Prelude\nimport Init.Tactics\n\n";
const PROBES: [(&str, &str, &str); 27] = [
    ("importedPureValue", "importedPureRun 42", "42"),
    ("importedBindValue", "importedBindRun 40", "42"),
    ("importedFunctorValue", "importedFunctorRun 41", "42"),
    ("importedMapConstValue", "importedMapConstRun 42", "42"),
    ("importedSeqValue", "importedSeqRun 40", "42"),
    ("importedSeqLeftValue", "importedSeqLeftRun 42", "42"),
    ("importedSeqRightValue", "importedSeqRightRun 42", "42"),
    (
        "importedApplicativeValue",
        "importedApplicativeRun 42",
        "42",
    ),
    ("importedMonadPureValue", "importedMonadPureRun 42", "42"),
    ("importedMonadBindValue", "importedMonadBindRun 40", "42"),
    ("importedMonadPartsValue", "importedMonadPartsRun 40", "42"),
    ("importedMonadMixedValue", "importedMonadMixedRun 40", "42"),
    (
        "importedDefaultMapValue",
        "(importedDefaultMap 40).value",
        "42",
    ),
    (
        "importedDefaultMapStamp",
        "(importedDefaultMap 40).stamp",
        "37",
    ),
    (
        "importedReorderedMapStamp",
        "(importedReorderedMap 40).stamp",
        "37",
    ),
    (
        "importedOverrideMapValue",
        "(importedOverrideMap 40).value",
        "42",
    ),
    (
        "importedOverrideMapStamp",
        "(importedOverrideMap 40).stamp",
        "99",
    ),
    (
        "importedDefaultMapConstStamp",
        "(importedDefaultMapConst 42).stamp",
        "37",
    ),
    (
        "importedOverrideMapConstStamp",
        "(importedOverrideMapConst 42).stamp",
        "99",
    ),
    (
        "importedDefaultSeqValue",
        "(importedDefaultSeq 40).value",
        "42",
    ),
    (
        "importedDefaultSeqStamp",
        "(importedDefaultSeq 40).stamp",
        "57",
    ),
    (
        "importedOverrideSeqStamp",
        "(importedOverrideSeq 40).stamp",
        "119",
    ),
    (
        "importedDefaultSeqLeftStamp",
        "(importedDefaultSeqLeft 42).stamp",
        "57",
    ),
    (
        "importedDefaultSeqRightStamp",
        "(importedDefaultSeqRight 42).stamp",
        "23",
    ),
    (
        "importedDefaultPureStamp",
        "(importedDefaultPure 42).stamp",
        "7",
    ),
    (
        "importedLocalParentStamp",
        "(importedLocalParentMapConst 42).stamp",
        "88",
    ),
    (
        "importedGlobalParentStamp",
        "(importedGlobalParentMapConst 42).stamp",
        "77",
    ),
];

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}

fn checked(engine: &Engine, source: &str) -> fln::SourceFileCheck {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("ordinary source checking completes within the explicit bounds")
}

fn actual_prelude() -> Engine {
    let library = PathBuf::from(
        std::env::var_os("FLN_REFERENCE_LIB")
            .expect("actual pinned Prelude is mandatory; set FLN_REFERENCE_LIB"),
    );
    let path = library.join("Init/Prelude.olean");
    let parts = [
        std::fs::read(&path).expect("actual exported Prelude"),
        std::fs::read(path.with_extension("olean.server")).expect("actual server Prelude"),
        std::fs::read(path.with_extension("olean.private")).expect("actual private Prelude"),
    ];
    assert!(parts.iter().map(Vec::len).sum::<usize>() <= BYTES);
    for part in &parts {
        fln_olean::pin::check_pinned_header(part).expect("the exact pinned artifact header");
    }
    assert!(
        fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES))
            .expect("the actual Prelude import graph")
            .is_empty(),
        "the single real Prelude is its complete import closure",
    );
    let module = name("Init.Prelude");
    let inputs = [OleanModuleInput {
        name: &module,
        artifact: &parts[0],
        server_artifact: Some(&parts[1]),
        private_artifact: Some(&parts[2]),
    }];
    let original = Engine::from_environment(Environment::new());
    let original_root = original.logical_root(&KVMap::new());
    let imported = original
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&module),
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .expect("actual Prelude declarations and metadata pass ordinary admission")
        .into_complete()
        .expect("K1 and independent checker both accept the complete real Prelude");
    assert_eq!(imported.modules.len(), 1);
    assert_eq!(imported.modules[0].module, module);
    assert_eq!(imported.modules[0].structures, 101);
    assert_eq!(imported.checked.modules.len(), 1);
    let observed = &imported.checked.modules[0];
    assert!(matches!(
        &observed.decoded.independent,
        IndependentReading::Read(_)
    ));
    assert!(observed.decoded.constants.len() > 2000);
    assert_eq!(
        observed.declarations.len(),
        observed.decoded.constants.len()
    );
    assert!(observed.declarations.iter().all(|declaration| matches!(
        declaration.checker.schema,
        "fln.checker-admission/1" | "fln-checker/v1"
    )));
    assert_eq!(original.logical_root(&KVMap::new()), original_root);
    assert_eq!(original.environment().constants().count(), 0);
    eprintln!(
        "FLN_IMPORTED_STRUCTURE_ADMISSION: {} real declarations; 101 original structure rows",
        observed.declarations.len(),
    );
    imported.engine
}

fn assert_interfaces(engine: &Engine) {
    let registry = ImportedStructures::read(engine.environment())
        .expect("the activated imported structure registry");
    let cases: [(&str, &[&str], &[&str]); 8] = [
        ("Functor", &["map", "mapConst"], &[]),
        ("Pure", &["pure"], &[]),
        ("Bind", &["bind"], &[]),
        ("Seq", &["seq"], &[]),
        ("SeqLeft", &["seqLeft"], &[]),
        ("SeqRight", &["seqRight"], &[]),
        (
            "Applicative",
            &["toFunctor", "toPure", "toSeq", "toSeqLeft", "toSeqRight"],
            &["Functor", "Pure", "Seq", "SeqLeft", "SeqRight"],
        ),
        (
            "Monad",
            &["toApplicative", "toBind"],
            &["Applicative", "Bind"],
        ),
    ];
    for (root, fields, parents) in cases {
        let expected = StructureEntry {
            name: name(root),
            fields: fields
                .iter()
                .map(|field| {
                    let subobject = field
                        .strip_prefix("to")
                        .filter(|parent| parents.contains(parent))
                        .map(name);
                    StructureField {
                        name: name(field),
                        projection: name(&format!("{root}.{field}")),
                        binder_info: if subobject.is_some() {
                            BinderInfo::InstImplicit
                        } else {
                            BinderInfo::Default
                        },
                        subobject,
                    }
                })
                .collect(),
            parents: parents
                .iter()
                .map(|parent| StructureParent {
                    name: name(parent),
                    subobject: true,
                    projection: name(&format!("{root}.to{parent}")),
                })
                .collect(),
        };
        assert_eq!(registry.get(&name(root)), Some(&expected), "{root}");
        let Some(ConstantInfo::Induct(info)) = engine.environment().find(&name(root)) else {
            panic!("actual structure family {root} is absent");
        };
        assert_eq!(info.ctors.len(), 1);
        let Some(ConstantInfo::Ctor(constructor)) = engine.environment().find(&info.ctors[0])
        else {
            panic!("actual constructor for {root} is absent");
        };
        assert_eq!(constructor.induct, name(root));
        for field in &expected.fields {
            assert!(
                matches!(
                    engine.environment().find(&field.projection),
                    Some(ConstantInfo::Defn(_))
                ),
                "the actual checked projection {} is present",
                field.projection.to_display_string(),
            );
        }
    }
}

fn assert_nat(exit: &VmExit, expected: &str, expression: &str) {
    let VmExit::Returned(result) = exit else {
        panic!("{expression} did not return: {exit:?}");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&result.value).as_deref(),
        Some(expected),
        "{expression}",
    );
}

fn check_and_replay(engine: &Engine) {
    let before = engine.logical_root(&KVMap::new());
    let body = SOURCE
        .strip_prefix(HEADER)
        .expect("the exact explicit pin import header");
    let admitted = checked(engine, body);
    assert_eq!(admitted.theorems, PROBES.len());
    let candidate = admitted.engine;
    let candidate_root = candidate.logical_root(&KVMap::new());
    for (proof, expression, expected) in PROBES {
        let line = format!("theorem {proof} : {expression} = {expected} := by rfl");
        assert!(SOURCE.lines().any(|source| source == line), "{proof}");
        assert!(candidate.environment().contains(&name(proof)));
        let source = format!("#eval {expression}");
        let completed = candidate
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|error| panic!("{proof}: {error:?}"))
            .into_complete()
            .expect("checked source execution completes");
        assert_eq!(completed.batch.source_evaluation_indices.len(), 1);
        let execution = &completed.batch.executions[completed.batch.source_evaluation_indices[0]];
        assert_eq!(execution.checker.schema, "fln.checker-admission/1");
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
        );
        assert_nat(&execution.exit, expected, expression);
        let module = decode_canonical(&execution.flbc_artifact, CodecLimits::default())
            .expect("independent FLBC validation");
        assert_eq!(
            encode_canonical(&module, CodecLimits::default()).expect("canonical FLBC encoding"),
            execution.flbc_artifact,
        );
        let replay = fln::execute_flbc_artifact(
            &execution.flbc_artifact,
            &KVMap::new(),
            FlbcExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{proof}: replay: {error:?}"))
        .into_complete()
        .expect("independent replay completes");
        assert_nat(&replay, expected, expression);
        assert_eq!(candidate.logical_root(&KVMap::new()), candidate_root);
    }
    for (source, valid, diagnostic) in [
        (
            "def rejectedImportedRecord : Monad ImportedTagged := { pure := @importedRecordPure, bind := @importedTaggedBind }",
            "def rejectedImportedRecord : Monad ImportedTagged := { pure := @importedTaggedPure, bind := @importedTaggedBind }",
            None,
        ),
        (
            "def rejectedImportedRecord : Monad ImportedTagged := { puure := @importedTaggedPure, bind := @importedTaggedBind }",
            "def rejectedImportedRecord : Monad ImportedTagged := { pure := @importedTaggedPure, bind := @importedTaggedBind }",
            Some("UnknownField"),
        ),
        (
            "def rejectedImportedRecord : Monad ImportedTagged := { toApplicative := importedApplicativeDictionary, bind := @importedTaggedBind }",
            "def rejectedImportedRecord : Monad ImportedTagged := { toApplicative := @Monad.toApplicative ImportedTagged importedDefaultMonad, bind := @importedTaggedBind }",
            None,
        ),
        (
            "def rejectedImportedRecord : Bind ImportedTagged := {}",
            "def rejectedImportedRecord : Bind ImportedTagged := { bind := @importedTaggedBind }",
            None,
        ),
        (
            "def rejectedImportedRecord : Nat := let ignored : Monad ImportedTagged := { pure := @importedRecordPure, bind := @importedTaggedBind }; 42",
            "def rejectedImportedRecord : Nat := let ignored : Monad ImportedTagged := { pure := @importedTaggedPure, bind := @importedTaggedBind }; 42",
            None,
        ),
    ] {
        fln_parse::parse_definition(source.as_bytes())
            .expect("the negative fixture reaches elaboration");
        checked(&candidate, valid);
        let staged = format!("def uncommittedImportedRecord : Nat := 77\n{source}");
        let error = candidate
            .check_source_files(&[staged.as_bytes()], &KVMap::new(), limits())
            .expect_err("malformed imported record source remains rejected");
        let detail = format!("{error:?}");
        assert!(detail.contains("Elaborate"), "{detail}");
        if let Some(diagnostic) = diagnostic {
            assert!(detail.contains(diagnostic), "{detail}");
        }
        for declaration in ["uncommittedImportedRecord", "rejectedImportedRecord"] {
            assert!(!candidate.environment().contains(&name(declaration)));
        }
        assert_eq!(candidate.logical_root(&KVMap::new()), candidate_root);
    }
    checked(
        &candidate,
        "def importedStructureRecovery : Nat := (importedDefaultMap 40).value\ntheorem importedStructureRecoveryValue : importedStructureRecovery = 42 := by rfl",
    );
    assert_eq!(candidate.logical_root(&KVMap::new()), candidate_root);
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert!(!engine.environment().contains(&name("ImportedRecordBox")));
    eprintln!(
        "FLN_IMPORTED_STRUCTURE_SOURCE: 27 checked values and independent replays; 5 refusal/recovery controls"
    );
}

#[test]
fn actual_prelude_parents_and_defaults_check_execute_and_replay() {
    std::thread::Builder::new()
        .name("actual-imported-structure-parents".to_owned())
        .stack_size(STACK)
        .spawn(|| {
            let engine = actual_prelude();
            assert_interfaces(&engine);
            check_and_replay(&engine);
        })
        .expect("actual Prelude admission worker")
        .join()
        .expect("actual imported structure behavior");
}
