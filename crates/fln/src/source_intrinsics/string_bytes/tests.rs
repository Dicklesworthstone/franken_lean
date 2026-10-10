//! Actual artifact comparison data, not admission of an imported module graph.
//! Every executed source candidate and changed helper body is separately
//! checked by both ordinary declaration checkers. No Reference code executes.

use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 64 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const MODULES: [&str; 13] = [
    "Init/Prelude",
    "Init/Core",
    "Init/Data/List/Basic",
    "Init/Data/UInt/BasicAux",
    "Init/GetElem",
    "Init/Data/ByteArray/Bootstrap",
    "Init/Data/ByteArray/Basic",
    "Init/Data/String/Defs",
    "Init/SimpLemmas",
    "Init/Data/ByteArray/Lemmas",
    "Init/Data/Char/Basic",
    "Init/Data/Repr",
    "Init/Data/String/Bootstrap",
];

struct Fixture {
    environment: Environment,
    externs: BTreeMap<Name, Vec<ExternEntry>>,
}

fn inventory() -> BTreeMap<Name, &'static str> {
    let mut rows = BTreeMap::new();
    for line in DEPENDENCIES.lines() {
        let (encoded, digest) = line.split_once('\t').unwrap();
        let label = dependency_name(encoded, &mut 0, IngressLimits::default()).unwrap();
        assert!(rows.insert(label, digest).is_none());
    }
    rows
}

/// Reachability is recomputed from decoded constants, including erased proof
/// bodies, recursor rules, and complete constructor/mutual membership.
fn dependencies(lookup: impl Fn(&Name) -> Option<ConstantInfo>, roots: &[&str]) -> BTreeSet<Name> {
    let mut pending: Vec<_> = roots.iter().map(|root| name(root)).collect();
    let mut found = BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        let info = lookup(&label)
            .unwrap_or_else(|| panic!("missing actual dependency {}", label.to_display_string()));
        let mut expressions = vec![&info.constant_val().type_];
        match &info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.ctors.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                pending.extend(value.all.iter().cloned());
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
            }
            ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
        }
        while let Some(expression) = expressions.pop() {
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => expressions.extend([binder_type, body]),
                ExprNode::LetE {
                    type_, value, body, ..
                } => expressions.extend([type_, value, body]),
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    found
}

fn fixture() -> Option<&'static Fixture> {
    static FIXTURE: OnceLock<Option<Fixture>> = OnceLock::new();
    FIXTURE
        .get_or_init(|| {
            let library = std::env::var_os("FLN_REFERENCE_LIB")
                .map(PathBuf::from)
                .or_else(|| {
                    std::env::var_os("HOME").map(|home| {
                        PathBuf::from(home)
                            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
                    })
                })
                .filter(|library| library.is_dir());
            let Some(library) = library else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "the actual pinned Reference library is required"
                );
                eprintln!("SKIP: pinned Reference lib/lean absent");
                return None;
            };
            let mut constants = BTreeMap::new();
            let mut actual_externs = BTreeMap::new();
            for module in MODULES {
                let path = library.join(module).with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                let view = if decoded.module.is_module {
                    fln_olean::region::OleanView::parse_with_dependencies(
                        &parts[2],
                        &[parts[0].as_slice(), parts[1].as_slice()],
                    )
                } else {
                    fln_olean::region::OleanView::parse(&parts[0])
                }
                .unwrap();
                let blocks = view
                    .extension_payloads(OleanWalkBudget::default(), BYTES)
                    .unwrap();
                let extensions =
                    metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
                for row in extensions.externs {
                    let entries: Vec<_> = row
                        .entries
                        .into_iter()
                        .map(|entry| match entry {
                            metadata::ExternEntry::Adhoc { backend } => {
                                ExternEntry::Adhoc { backend }
                            }
                            metadata::ExternEntry::Inline { backend, pattern } => {
                                ExternEntry::Inline { backend, pattern }
                            }
                            metadata::ExternEntry::Standard { backend, symbol } => {
                                ExternEntry::Standard { backend, symbol }
                            }
                            metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                        })
                        .collect();
                    if let Some(previous) = actual_externs.insert(row.declaration, entries.clone())
                    {
                        assert_eq!(previous, entries, "conflicting actual extern entries");
                    }
                }
                for info in decoded.constants {
                    // Preserve the extractor's first occurrence, including real
                    // proof bodies. Never select declarations by expected digest.
                    constants.entry(info.name().clone()).or_insert(info);
                }
            }
            let roots: Vec<_> = HELPERS
                .into_iter()
                .chain([
                    "String.ofList",
                    // The native ofList adapter independently checks its
                    // actual Bootstrap String.push implementation.
                    "String.push",
                    "Char.ofNat",
                    "String.toByteArray",
                    // Runtime decision erasure checks the complete True
                    // family used as its closed proposition representative.
                    // This actual recursor is not a backwards dependency of
                    // the logical byte/string constructor contract.
                    "True.rec",
                    // Complete imported Nat/List recursion recognition also
                    // checks these actual family recursors. Their logical
                    // callers do not otherwise reference the recursor rows.
                    "PUnit.rec",
                    "PProd.rec",
                    // Char's actual word conversion computes a modulus from
                    // Nat.pow. Complete native arithmetic recognition binds
                    // the literal dictionary's recursor as well as its fields.
                    "OfNat.rec",
                ])
                .collect();
            let needed = dependencies(|label| constants.get(label).cloned(), &roots);
            let mut environment = Environment::new();
            for label in &needed {
                environment = environment
                    .add_decl(constants.get(label).unwrap().clone())
                    .unwrap();
            }
            actual_externs.retain(|label, _| needed.contains(label));
            for helper in HELPERS.into_iter().chain(["String.push"]) {
                assert!(actual_externs.contains_key(&name(helper)), "{helper}");
            }
            assert!(actual_externs.len() > HELPERS.len());
            for (label, entries) in &actual_externs {
                environment = externs::register(&environment, label, entries.clone()).unwrap();
            }
            Some(Fixture {
                environment,
                externs: actual_externs,
            })
        })
        .as_ref()
}

fn with_fixture(test: impl FnOnce(&Fixture) + Send + 'static) {
    std::thread::Builder::new()
        .name("fln-string-bytes-fixture".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            if let Some(fixture) = fixture() {
                test(fixture);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn selected(environment: &Environment) -> Result<bool, IngressError> {
    matches(
        environment,
        &name("String.ofByteArray"),
        &mut None,
        &mut 0,
        IngressLimits::default(),
    )
}

fn rebuild(fixture: &Fixture, missing: Option<&Name>, omit_extern: Option<&Name>) -> Environment {
    let mut environment = Environment::new();
    for (label, _) in fixture.environment.constants() {
        if missing != Some(label) {
            environment = environment
                .with_entry(fixture.environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (label, entries) in &fixture.externs {
        if missing != Some(label) && omit_extern != Some(label) {
            environment = externs::register(&environment, label, entries.clone()).unwrap();
        }
    }
    environment
}

fn restore_extern(fixture: &Fixture, environment: &Environment, label: &Name) -> Environment {
    fixture.externs.get(label).map_or_else(
        || environment.clone(),
        |entries| externs::register(environment, label, entries.clone()).unwrap(),
    )
}

fn execute_and_replay(environment: &Environment, source: &str, expected: &[(&str, Option<&str>)]) {
    let engine = Engine::from_environment(environment.clone());
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap_or_else(|error| panic!("checked String bytes source {source}: {error:?}"))
        .into_complete()
        .unwrap();
    let indices = &completed.batch.source_evaluation_indices;
    assert_eq!(indices.len(), expected.len());
    for (&index, (expected, expected_row)) in indices.iter().zip(expected) {
        let execution = &completed.batch.executions[index];
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        // Retain precise evidence for each selected path: the independent
        // native ofList operation uses String.push, while direct checked
        // constructors must still cross the packed-byte conversion.
        for row in ["extern:String.ofByteArray", "extern:String.push"] {
            assert_eq!(
                execution
                    .flbc_artifact
                    .windows(row.len())
                    .any(|bytes| bytes == row.as_bytes()),
                *expected_row == Some(row),
                "expected selected row {expected_row:?}, inspecting {row}",
            );
        }
        let program = fln_comp::flbc::decode_canonical(
            &execution.flbc_artifact,
            fln_comp::flbc::CodecLimits::default(),
        )
        .unwrap();
        assert_eq!(
            fln_comp::flbc::encode_canonical(&program, Default::default()).unwrap(),
            execution.flbc_artifact
        );
        let replay = execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
            .unwrap()
            .into_complete()
            .unwrap();
        for exit in [&execution.exit, &replay] {
            assert_eq!(
                closed_vm_value(exit).unwrap(),
                Some(ClosedVmValue::String((*expected).to_owned()))
            );
        }
    }
    assert_eq!(engine.logical_root(&options), before);
}

fn two_argument_body(type_: &Expr, result: Expr) -> Expr {
    let mut type_ = type_;
    let mut binders = Vec::new();
    loop {
        match type_.node() {
            ExprNode::MData { expr, .. } => type_ = expr,
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                type_ = body;
            }
            _ => break,
        }
    }
    assert_eq!(binders.len(), 2);
    binders
        .into_iter()
        .rev()
        .fold(result, |body, (label, type_, info)| {
            Expr::lam(label, type_, body, info)
        })
}

#[test]
fn actual_string_bytes_inventory_binds_the_full_layout_proof_and_packing_closure() {
    with_fixture(|fixture| {
        let rows = inventory();
        assert_eq!(rows.len(), 318);
        assert_eq!(
            dependencies(|label| fixture.environment.find(label).cloned(), &HELPERS),
            rows.keys().cloned().collect()
        );
        for (label, digest) in rows {
            assert_eq!(
                fixture.environment.entry(&label).unwrap().digest().to_hex(),
                digest
            );
        }
        assert!(!fixture.environment.contains(&name("USize")));
        assert!(!fixture.environment.contains(&name("IO.RealWorld")));
        assert!(!fixture.environment.contains(&name("IO.Error")));
        for recursor in [
            "Decidable.rec",
            "False.rec",
            "True.rec",
            "PUnit.rec",
            "PProd.rec",
            "OfNat.rec",
        ] {
            assert!(matches!(
                fixture.environment.find(&name(recursor)),
                Some(ConstantInfo::Rec(_))
            ));
        }
        let mut visited = 0;
        assert!(
            crate::source_intrinsics::imported_nat_recursion_matches(
                &fixture.environment,
                &mut visited,
                IngressLimits::default(),
            )
            .unwrap()
        );
        assert!(
            crate::source_intrinsics::imported_list_recursion_matches(
                &fixture.environment,
                &mut visited,
                IngressLimits::default(),
            )
            .unwrap()
        );
        for operation in [
            "Nat.pred", "Nat.mul", "Nat.pow", "Nat.sub", "Nat.beq", "Nat.ble",
        ] {
            assert!(
                crate::source_intrinsics::imported_nat_matches(
                    &fixture.environment,
                    &name(operation),
                    &mut visited,
                    IngressLimits::default(),
                )
                .unwrap(),
                "complete actual {operation} model"
            );
        }
        assert!(selected(&fixture.environment).unwrap());
        assert!(
            !matches(
                &fixture.environment,
                &name("String.ofList"),
                &mut None,
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap()
        );
    });
}

#[test]
fn checked_strings_execute_unicode_nul_empty_and_partial_constructors_and_replacements() {
    with_fixture(|fixture| {
        execute_and_replay(
            &fixture.environment,
            r#"
def fromChars (cs : List Char) : String :=
  String.ofByteArray (List.utf8Encode cs) (ByteArray.IsValidUTF8.intro cs rfl)
#eval String.ofList []
#eval String.ofList ['λ', '\x00', 'é', '😀']
#eval fromChars []
#eval fromChars ['λ', '\x00', 'é', '😀']
#eval (let buildString := String.ofByteArray; buildString (List.utf8Encode ['λ']) (ByteArray.IsValidUTF8.intro ['λ'] rfl))
#eval (let buildLater := String.ofByteArray (List.utf8Encode ['é']); buildLater (ByteArray.IsValidUTF8.intro ['é'] rfl))
#eval fromChars ['a', 'b']
"#,
            &[
                ("", Some("extern:String.push")),
                ("λ\0é😀", Some("extern:String.push")),
                ("", Some("extern:String.ofByteArray")),
                ("λ\0é😀", Some("extern:String.ofByteArray")),
                ("λ", Some("extern:String.ofByteArray")),
                ("é", Some("extern:String.ofByteArray")),
                ("ab", Some("extern:String.ofByteArray")),
            ],
        );

        let options = KVMap::new();
        let limits = EngineAdmissionLimits::for_stack_bytes(STACK);
        let engine = Engine::from_environment(fixture.environment.clone());
        let before = engine.logical_root(&options);
        assert!(engine.check_source_files(
            &[b"def invalidValidity : String := String.ofByteArray (List.utf8Encode []) (ByteArray.IsValidUTF8.intro ['a'] rfl)"],
            &options,
            SourceCheckLimits::new(limits),
        ).is_err(), "an invalid UTF-8 witness must fail before proof erasure");
        assert_eq!(engine.logical_root(&options), before);

        let Some(ConstantInfo::Ctor(original)) =
            fixture.environment.find(&name("String.ofByteArray"))
        else {
            panic!("actual String constructor");
        };
        let target = name("alternateStringConstructor");
        let mut base = original.base.clone();
        base.name = target.clone();
        let replacement = DefinitionVal {
            value: two_argument_body(
                &base.type_,
                Expr::lit(fln_core::expr::Literal::Str("replacement".to_owned())),
            ),
            base,
            hints: fln_env::constants::ReducibilityHints::Abbrev,
            safety: fln_env::constants::DefinitionSafety::Safe,
            all: vec![target.clone()],
        };
        let admitted = engine
            .admit_declaration(Declaration::Defn(replacement), &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let replaced = fln_elab::implemented_by::register(
            admitted.engine.environment(),
            &name("String.ofByteArray"),
            &target,
        )
        .unwrap();
        execute_and_replay(
            &replaced,
            r#"
theorem logicalConstructor (b : ByteArray) (h : ByteArray.IsValidUTF8 b) :
  (String.ofByteArray b h).toByteArray = b := rfl
#eval (let buildString := String.ofByteArray; buildString (List.utf8Encode []) (ByteArray.IsValidUTF8.intro [] rfl))
#eval (let buildLater := String.ofByteArray (List.utf8Encode []); buildLater (ByteArray.IsValidUTF8.intro [] rfl))
"#,
            &[("replacement", None), ("replacement", None)],
        );
    });
}

#[test]
fn string_bytes_missing_changed_or_foreign_contracts_and_work_exhaustion_refuse() {
    with_fixture(|fixture| {
        let root = name("String.ofByteArray");
        assert!(!selected(&rebuild(fixture, None, Some(&root))).unwrap());
        assert!(!selected(&rebuild(fixture, Some(&root), None)).unwrap());
        for label in [
            "ByteArray.IsValidUTF8",
            "ByteArray.IsValidUTF8.intro",
            "ByteArray.push",
            "UInt8.ofBitVec",
            "Bool.false",
        ] {
            assert!(
                matches!(
                    selected(&rebuild(fixture, Some(&name(label)), None)),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
        }
        for label in HELPERS {
            if label != "String.ofByteArray" {
                assert!(
                    matches!(
                        selected(&rebuild(fixture, None, Some(&name(label)))),
                        Err(IngressError::UnsupportedNode { .. })
                    ),
                    "{label}"
                );
            }
            for entry in [
                ExternEntry::Opaque,
                ExternEntry::Standard {
                    backend: name("all"),
                    symbol: "foreign_string_bytes_contract".to_owned(),
                },
            ] {
                let environment =
                    externs::register(&fixture.environment, &name(label), vec![entry]).unwrap();
                assert!(
                    matches!(
                        selected(&environment),
                        Err(IngressError::UnsupportedNode { .. })
                    ),
                    "{label}"
                );
            }
        }
        // These are deliberately malformed comparison inputs, not purported
        // admitted declarations. The whole constructor/proof shape is bound.
        for label in ["String.ofByteArray", "ByteArray.IsValidUTF8.intro"] {
            let target = name(label);
            let Some(ConstantInfo::Ctor(original)) = fixture.environment.find(&target) else {
                panic!("actual constructor {label}");
            };
            let mut changed = original.clone();
            changed.num_fields = changed.num_fields.checked_sub(1).unwrap();
            let environment = rebuild(fixture, Some(&target), None)
                .add_decl(ConstantInfo::Ctor(changed))
                .unwrap();
            let environment = restore_extern(fixture, &environment, &target);
            assert!(matches!(
                selected(&environment),
                Err(IngressError::UnsupportedNode { .. })
            ));
        }

        let target = name("ByteArray.push");
        let Some(ConstantInfo::Defn(original)) = fixture.environment.find(&target) else {
            panic!("actual ByteArray.push");
        };
        let mut changed = original.clone();
        changed.value = two_argument_body(&changed.base.type_, Expr::bvar(1).unwrap());
        let admitted = Engine::from_environment(rebuild(fixture, Some(&target), None))
            .admit_declaration(
                Declaration::Defn(changed),
                &KVMap::new(),
                EngineAdmissionLimits::for_stack_bytes(STACK),
            )
            .expect("returning the original byte array has the exact helper type")
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let environment = restore_extern(fixture, admitted.engine.environment(), &target);
        assert!(matches!(
            selected(&environment),
            Err(IngressError::UnsupportedNode { .. })
        ));
        let changed = Engine::from_environment(environment);
        assert!(matches!(
            changed.execute_source_definition(
                b"def changedBytes : String := String.ofList ['a']",
                &KVMap::new(),
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            ),
            Err(EngineExecutionError::Ingress(
                IngressError::UnsupportedNode { .. }
            ))
        ));

        let mut measured = 0;
        assert!(
            matches(
                &fixture.environment,
                &root,
                &mut None,
                &mut measured,
                IngressLimits::default()
            )
            .unwrap()
        );
        assert!(measured > inventory().len());
        let error = matches(
            &fixture.environment,
            &root,
            &mut None,
            &mut 0,
            IngressLimits {
                max_nodes: measured - 1,
                ..IngressLimits::default()
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            }
        ));
        assert!(error.is_resource_exhaustion());
        assert!(selected(&fixture.environment).unwrap());
    });
}
