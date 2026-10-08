//! Native references execute only behind the admitted ST/EST contracts.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    BinderInfo, Budget, CheckerAdmissionGround, ClosedVmValue, ConstantInfo, ConstantVal,
    Declaration, DefinitionExecution, DefinitionVal, Engine, EngineAdmissionLimits,
    EngineExecutionError, EngineExecutionLimits, Environment, Expr, IndependentReading,
    IngressError, KVMap, Literal, Name, NatLit, OleanCheckLimits, OleanDecodeLimits,
    OleanFrontierJobs, OleanModuleInput, OleanWalkBudget, SourceCheckLimits, SourceModuleInput,
};
use fln_env::constants::{DefinitionSafety, ReducibilityHints};
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const EXTERNS: [(&str, &str); 5] = [
    ("Void.mk", "lean_void_mk"),
    ("ST.Prim.mkRef", "lean_st_mk_ref"),
    ("ST.Prim.Ref.get", "lean_st_ref_get"),
    ("ST.Prim.Ref.set", "lean_st_ref_set"),
    ("ST.Prim.Ref.swap", "lean_st_ref_swap"),
];

#[path = "runtime_st_authority/payloads.rs"]
mod payloads;

fn name(spelling: &str) -> Name {
    Name::from_components(spelling.split('.'))
}

fn constant(spelling: &str) -> Expr {
    Expr::const_(name(spelling), vec![])
}

fn small_limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn canonical(symbol: &str) -> fln_elab::externs::ExternEntry {
    fln_elab::externs::ExternEntry::Standard {
        backend: name("all"),
        symbol: symbol.to_owned(),
    }
}

fn ordinary_fixture(target: &str) -> Engine {
    let limits = small_limits();
    let base = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    // This is deliberately an unrelated, ordinary source definition. It is
    // never presented as a miniature model of an opaque mutable reference.
    let source = format!("def {target} (value : Nat) : Nat := Nat.succ value\n");
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits.admission()),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}

fn ordinary_query(target: &str) -> Declaration {
    let label = name("stAuthorityProbe");
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: label.clone(),
            level_params: vec![],
            type_: constant("Nat"),
        },
        value: Expr::app(
            constant(target),
            Expr::lit(Literal::Nat(NatLit::from_u64(41))),
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![label],
    })
}

fn assert_scalar(execution: &DefinitionExecution, expected: usize) {
    assert_eq!(execution.checker.schema, "fln.checker-admission/1");
    assert_eq!(
        execution.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    assert_eq!(
        fln::closed_vm_value(&execution.exit).unwrap(),
        Some(ClosedVmValue::Scalar(expected)),
        "{:?}",
        execution.declaration
    );
}

fn rejected(
    engine: &Engine,
    query: &Declaration,
    limits: EngineExecutionLimits,
) -> EngineExecutionError {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let error = engine
        .execute_definition(query.clone(), &options, limits)
        .expect_err("an unsupported contract must not acquire native state operations");
    assert_eq!(engine.logical_root(&options), before);
    error
}

#[test]
fn familiar_st_names_execute_their_ordinary_checked_bodies_without_externs() {
    for target in ["runST", "runEST"]
        .into_iter()
        .chain(EXTERNS.map(|(target, _)| target))
    {
        let engine = ordinary_fixture(target);
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let query = ordinary_query(target);
        let run = || {
            engine
                .execute_definition(query.clone(), &options, small_limits())
                .unwrap_or_else(|error| panic!("{target}: {error:?}"))
                .into_complete()
                .unwrap()
        };
        let first = run();
        assert_scalar(&first, 42);
        let repeated = run();
        assert_scalar(&repeated, 42);
        assert_eq!(first.flbc_artifact, repeated.flbc_artifact, "{target}");
        assert_eq!(engine.logical_root(&options), root);
        assert!(!engine.environment().contains(&name("stAuthorityProbe")));
    }
}

#[test]
fn canonical_st_extern_names_do_not_authorize_unrelated_checked_definitions() {
    for (target, symbol) in EXTERNS {
        let ordinary = ordinary_fixture(target);
        let engine = Engine::from_environment(
            fln_elab::externs::register(
                ordinary.environment(),
                &name(target),
                vec![canonical(symbol)],
            )
            .unwrap(),
        );
        let error = rejected(&engine, &ordinary_query(target), small_limits());
        assert!(
            matches!(
                error,
                EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
            ),
            "{target}: {error:?}"
        );
    }
}

type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

fn reference_library() -> Option<PathBuf> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    if library.is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    library
}

fn artifacts(library: &Path, root: &Name) -> BTreeMap<Name, Parts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let path = library
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
        let optional = |path: PathBuf| match std::fs::read(&path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("{}: {error}", path.display()),
        };
        modules.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    modules
}

fn rebuild_environment(
    engine: &Engine,
    without_declaration: Option<&Name>,
    without_extern: Option<&Name>,
) -> Environment {
    let original = engine.environment();
    let mut environment = Environment::new();
    for (name, _) in original.constants() {
        if without_declaration != Some(name) {
            environment = environment
                .with_entry(original.entry(name).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in original.extensions() {
        environment = environment
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            if journal == &fln_elab::externs::journal_name()
                && without_extern.is_some_and(|omitted| {
                    fln_elab::externs::decode_entry(&entry.payload).unwrap().0 == *omitted
                })
            {
                continue;
            }
            environment = environment
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    environment
}

fn changed_opaque_model(engine: &Engine, target: &str) -> Engine {
    let target = name(target);
    let Some(ConstantInfo::Opaque(value)) = engine.environment().find(&target) else {
        panic!("the pin supplies an opaque primitive: {target:?}")
    };
    let mut value = value.clone();
    // The identity application is well typed, but is a different serialized
    // body. The supported opaque model must match exactly, not merely by name
    // or type. This does not invent a source implementation of mutable state.
    value.value = Expr::app(
        Expr::lam(
            name("retainCheckedBody"),
            value.base.type_.clone(),
            Expr::bvar(0).expect("zero is a valid de Bruijn index"),
            BinderInfo::Default,
        ),
        value.value,
    );
    let admitted = Engine::from_environment(rebuild_environment(engine, Some(&target), None))
        .admit_declaration(
            Declaration::Opaque(value),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("the alternate model body remains well typed under both checkers")
        .into_complete()
        .unwrap();
    assert_eq!(
        admitted.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    admitted.engine
}

// The only hand-written lift below is ordinary, checked source code over the
// imported constructors. All mutable effects still use the real opaque Prim
// declarations and the pin's explicit extern metadata.
const PROGRAM: &str = r#"
prelude
import Init.System.ST

def stResult (result : Except Nat Nat) : Nat :=
  match result with
  | .ok value => value
  | .error code => Nat.add 1000 code

def liftState {sigma alpha : Type} (action : ST sigma alpha) : EST Nat sigma alpha :=
  fun state =>
    match action state with
    | .mk value state => EST.Out.ok value state

#eval runST (fun sigma =>
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 42)
    (fun reference => ST.Prim.Ref.get reference))

#eval runST (fun sigma =>
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 10) (fun reference =>
    let alias := reference
    ST.bind (ST.Prim.Ref.set reference 20) (fun _ =>
      ST.bind (ST.Prim.Ref.swap alias 22) (fun previous =>
        ST.bind (ST.Prim.Ref.get reference) (fun current =>
          ST.pure (Nat.add (Nat.mul previous 100) current))))))

#eval runST (fun sigma =>
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 7) (fun first =>
    ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 7) (fun second =>
      ST.bind (ST.Prim.Ref.set first 42) (fun _ =>
        ST.bind (ST.Prim.Ref.get first) (fun changed =>
          ST.bind (ST.Prim.Ref.get second) (fun untouched =>
            ST.pure (Nat.add (Nat.mul changed 100) untouched)))))))

#eval runST (fun sigma =>
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 10) (fun reference =>
    let read := ST.Prim.Ref.get reference
    ST.bind read (fun before =>
      ST.bind (ST.Prim.Ref.set reference 20) (fun _ =>
        ST.bind read (fun after =>
          ST.pure (Nat.add (Nat.mul before 100) after))))))

#eval runST (fun sigma =>
  let allocate := ST.Prim.mkRef (σ := sigma) (α := Nat) 0
  ST.bind allocate (fun first =>
    ST.bind allocate (fun second =>
      ST.bind (ST.Prim.Ref.set first 99) (fun _ => ST.Prim.Ref.get second))))

#eval stResult (runEST (fun sigma => (EST.pure 42 : EST Nat sigma Nat)))

#eval stResult (runEST (fun sigma =>
  EST.bind (EST.throw 7 : EST Nat sigma Nat) (fun value =>
    EST.pure (Nat.add value 100))))

#eval stResult (runEST (fun sigma =>
  EST.tryCatch (EST.throw 37 : EST Nat sigma Nat) (fun code =>
    EST.pure (Nat.add code 5))))

#eval stResult (runEST (fun sigma =>
  EST.bind (liftState (ST.Prim.mkRef (σ := sigma) (α := Nat) 0)) (fun reference =>
    EST.tryCatch
      (EST.bind (liftState (ST.Prim.Ref.set reference 7)) (fun _ =>
        EST.bind (EST.throw 5 : EST Nat sigma Nat) (fun _ =>
          EST.bind (liftState (ST.Prim.Ref.set reference 99)) (fun _ => EST.pure 0))))
      (fun code =>
        EST.bind (liftState (ST.Prim.Ref.get reference)) (fun current =>
          EST.pure (Nat.add (Nat.mul current 100) code))))))

#eval stResult (runEST (fun sigma =>
  EST.bind (liftState (ST.Prim.mkRef (σ := sigma) (α := Nat) 0)) (fun reference =>
    EST.bind
      (EST.tryCatch (EST.pure 41) (fun _ =>
        EST.bind (liftState (ST.Prim.Ref.set reference 99)) (fun _ => EST.pure 0)))
      (fun value =>
        EST.bind (liftState (ST.Prim.Ref.get reference)) (fun current =>
          EST.pure (Nat.add (Nat.mul current 100) value))))))

#eval runST (fun sigma =>
  let base : Nat := 18446744073709551616
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) (Nat.add base 20)) (fun reference =>
    ST.bind (ST.Prim.Ref.get reference) (fun snapshot =>
      ST.bind (ST.Prim.Ref.swap reference (Nat.add base 22)) (fun old =>
        ST.bind (ST.Prim.Ref.set reference (Nat.add base 42)) (fun _ =>
          ST.bind (ST.Prim.Ref.get reference) (fun current =>
            ST.pure (Nat.add
              (Nat.mul (Nat.sub snapshot base) 10000)
              (Nat.add (Nat.mul (Nat.sub old base) 100)
                (Nat.sub current base)))))))))
"#;

/// Debugging fixture only: these imported declarations have NOT passed the
/// module council. The authoritative integration test below never calls this
/// helper and still reads and admits the complete artifact closure itself.
fn decoded_st_fixture(library: &Path) -> Engine {
    let root = name("Init.System.ST");
    let artifacts = artifacts(library, &root);
    let module_count = artifacts.len();
    let mut constants = BTreeMap::<Name, ConstantInfo>::new();
    let mut root_externs = None;
    for (module, (public, server, private)) in &artifacts {
        let decoded = fln::decode_olean_module_artifacts(
            public,
            server.as_deref().unwrap_or_default(),
            private.as_deref().unwrap_or_default(),
            OleanDecodeLimits::new(BYTES),
        )
        .unwrap();
        if module == &root {
            let view = if decoded.module.is_module {
                fln_olean::region::OleanView::parse_with_dependencies(
                    private.as_deref().expect("module private part"),
                    &[
                        public.as_slice(),
                        server.as_deref().expect("module server part"),
                    ],
                )
            } else {
                fln_olean::region::OleanView::parse(public)
            }
            .unwrap();
            let blocks = view
                .extension_payloads(OleanWalkBudget::default(), BYTES)
                .unwrap();
            root_externs = Some(
                fln_olean::source_extensions::decode(
                    &blocks,
                    fln_olean::source_extensions::DecodeLimits::default(),
                )
                .unwrap()
                .externs,
            );
        }
        for info in decoded.constants {
            let replace = if let Some(previous) = constants.get(info.name()) {
                if previous == &info {
                    false
                } else {
                    // The pin repeats theorem names with different proof
                    // bodies. Keep an actual theorem only when its entire
                    // statement and mutual-name envelope agree exactly. This
                    // fixture convenience grants no import/admission receipt.
                    assert_eq!(previous.constant_val(), info.constant_val());
                    match (previous, &info) {
                        (ConstantInfo::Thm(first), ConstantInfo::Thm(second)) => {
                            assert_eq!(first.all, second.all);
                            false
                        }
                        (ConstantInfo::Axiom(first), ConstantInfo::Thm(second))
                            if !first.is_unsafe
                                && second.all.as_slice()
                                    == std::slice::from_ref(&second.base.name) =>
                        {
                            true
                        }
                        (ConstantInfo::Thm(first), ConstantInfo::Axiom(second))
                            if !second.is_unsafe
                                && first.all.as_slice()
                                    == std::slice::from_ref(&first.base.name) =>
                        {
                            false
                        }
                        _ => panic!("unsupported raw-fixture duplicate: {:?}", info.name()),
                    }
                }
            } else {
                true
            };
            if replace {
                constants.insert(info.name().clone(), info);
            }
        }
    }
    drop(artifacts);
    let constant_count = constants.len();
    let mut environment = Environment::new();
    for info in constants.into_values() {
        environment = environment.add_decl(info).unwrap();
    }
    // The explicit Prim/ST.bind programs need the ST module's real extern
    // data; no MonadLift/instance registration is synthesized for this probe.
    for attribute in root_externs.expect("actual ST module metadata") {
        let entries = attribute
            .entries
            .into_iter()
            .map(|entry| {
                use fln_elab::externs::ExternEntry as Native;
                use fln_olean::source_extensions::ExternEntry as Artifact;
                match entry {
                    Artifact::Adhoc { backend } => Native::Adhoc { backend },
                    Artifact::Inline { backend, pattern } => Native::Inline { backend, pattern },
                    Artifact::Standard { backend, symbol } => Native::Standard { backend, symbol },
                    Artifact::Opaque => Native::Opaque,
                }
            })
            .collect();
        environment =
            fln_elab::externs::register(&environment, &attribute.declaration, entries).unwrap();
    }
    let table = fln_elab::externs::ExternTable::read(&environment).unwrap();
    for (target, symbol) in EXTERNS {
        assert_eq!(
            table.get(&name(target)),
            Some([canonical(symbol)].as_slice())
        );
    }
    eprintln!(
        "DECODED RAW ST FIXTURE, NOT MODULE ADMISSION: {module_count} modules, {constant_count} declarations"
    );
    Engine::from_environment(environment)
}

#[test]
fn decoded_st_fixture_debugs_native_actions_without_import_admission() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let engine = decoded_st_fixture(&library);
            let options = KVMap::new();
            let root = engine.logical_root(&options);
            let source = PROGRAM
                .strip_prefix("\nprelude\nimport Init.System.ST\n")
                .expect("remove only the module header for the raw-fixture probe");
            let completed = engine
                .execute_source_commands_with_checks(
                    source.as_bytes(),
                    &options,
                    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let expected = [42, 2022, 4207, 1020, 0, 42, 1007, 42, 705, 41, 202042];
            assert_eq!(
                completed.batch.source_evaluation_indices.len(),
                expected.len()
            );
            for (&index, expected) in completed
                .batch
                .source_evaluation_indices
                .iter()
                .zip(expected)
            {
                assert_scalar(&completed.batch.executions[index], expected);
            }
            assert_eq!(engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn admitted_st_and_est_execute_reference_actions_in_order_and_refuse_counterfeit_contracts() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let module = name("Init.System.ST");
            let artifacts = artifacts(&library, &module);
            let inputs: Vec<_> = artifacts
                .iter()
                .map(|(name, (public, server, private))| OleanModuleInput {
                    name,
                    artifact: public,
                    server_artifact: server.as_deref(),
                    private_artifact: private.as_deref(),
                })
                .collect();
            let options = KVMap::new();
            let mut admission = SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            ));
            admission.jobs = OleanFrontierJobs {
                threads: NonZeroUsize::new(1).unwrap(),
                worker_stack_bytes: STACK,
            };
            let mut imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &options,
                    admission,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(imported.checked.modules.len(), inputs.len());
            assert_eq!(imported.modules.len(), inputs.len());
            for checked in &imported.checked.modules {
                assert!(
                    matches!(&checked.decoded.independent, IndependentReading::Read(_)),
                    "{} must be decoded independently from the actual bytes",
                    checked.name.to_display_string()
                );
                assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
                assert!(
                    checked
                        .declarations
                        .iter()
                        .all(|declaration| matches!(
                            declaration.checker.schema,
                            "fln.checker-admission/1" | "fln-checker/v1"
                        )),
                    "fresh admissions and independently checked repeated rows retain their exact schema"
                );
            }
            for (target, _) in EXTERNS {
                let row = imported
                    .checked
                    .modules
                    .iter()
                    .find(|checked| checked.name == module)
                    .unwrap()
                    .declarations
                    .iter()
                    .find(|declaration| declaration.name == name(target))
                    .unwrap();
                assert_eq!(row.checker.schema, "fln.checker-admission/1", "{target}");
                assert_eq!(
                    row.checker.ground,
                    CheckerAdmissionGround::BodyCheckedAgainstDeclaredType,
                    "{target}"
                );
            }
            let table =
                fln_elab::externs::ExternTable::read(imported.engine.environment()).unwrap();
            for (target, symbol) in EXTERNS {
                assert_eq!(
                    table.get(&name(target)),
                    Some([canonical(symbol)].as_slice()),
                    "the real artifacts supply the {target} contract"
                );
            }
            drop(table);
            drop(inputs);
            drop(artifacts);
            // Execution consults the private checked import contexts, not
            // these public report payloads. Their independent readings and
            // declaration observations have all been asserted above.
            drop(std::mem::take(&mut imported.checked.modules));
            eprintln!("ST closure admitted: {} modules", imported.modules.len());

            let root = imported.engine.logical_root(&options);
            let entry = name("STAuthority");
            let modules = [SourceModuleInput {
                name: &entry,
                source: PROGRAM.as_bytes(),
            }];
            let limits = SourceProgramLimits::new(EngineExecutionLimits::new(
                Budget::for_stack_bytes(STACK),
            ));
            let run = || {
                imported
                    .execute_source_modules(&modules, &entry, &options, limits, None)
                    .unwrap()
                    .into_complete()
                    .unwrap()
            };
            let first = run();
            assert_eq!(first.modules.len(), 1);
            let batch = &first.modules[0].commands.batch;
            let evaluations: Vec<_> = batch
                .source_evaluation_indices
                .iter()
                .map(|&index| &batch.executions[index])
                .collect();
            let expected = [42, 2022, 4207, 1020, 0, 42, 1007, 42, 705, 41, 202042];
            assert_eq!(evaluations.len(), expected.len());
            for (execution, expected) in evaluations.iter().zip(expected) {
                assert_scalar(execution, expected);
            }
            // The alias/swap query invokes every supported mutable primitive.
            // Void.mk is checked separately and constructs a scalar world; it
            // does not claim a generated VM extern row.
            for (target, _) in &EXTERNS[1..] {
                let row = format!("extern:{target}");
                assert!(
                    evaluations[1]
                        .flbc_artifact
                        .windows(row.len())
                        .any(|bytes| bytes == row.as_bytes()),
                    "the compiled program must invoke {target}"
                );
            }
            let query = evaluations[1].declaration.clone();
            let bytecode: Vec<_> = evaluations
                .iter()
                .map(|execution| execution.flbc_artifact.clone())
                .collect();
            drop(evaluations);
            drop(first);
            let repeated = run();
            let batch = &repeated.modules[0].commands.batch;
            assert_eq!(batch.source_evaluation_indices.len(), expected.len());
            for ((&index, expected), bytecode) in batch
                .source_evaluation_indices
                .iter()
                .zip(expected)
                .zip(&bytecode)
            {
                let execution = &batch.executions[index];
                assert_scalar(execution, expected);
                assert_eq!(&execution.flbc_artifact, bytecode);
            }
            drop(repeated);
            assert_eq!(imported.engine.logical_root(&options), root);
            let engine = imported.engine.clone();
            drop(imported);

            payloads::check_payloads(&engine);

            for (target, symbol) in EXTERNS {
                let missing = Engine::from_environment(rebuild_environment(
                    &engine,
                    None,
                    Some(&name(target)),
                ));
                let error = rejected(&missing, &query, limits.execution);
                assert!(
                    matches!(error, EngineExecutionError::Ingress(_)),
                    "missing {target} extern: {error:?}"
                );
                drop(missing);

                let changed = changed_opaque_model(&engine, target);
                let error = rejected(&changed, &query, limits.execution);
                assert!(
                    matches!(
                        error,
                        EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
                    ),
                    "changed {target} model: {error:?}"
                );
                drop(changed);

                for entry in [
                    fln_elab::externs::ExternEntry::Standard {
                        backend: name("c"),
                        symbol: symbol.to_owned(),
                    },
                    canonical("different_native_symbol"),
                ] {
                    let changed = Engine::from_environment(
                        fln_elab::externs::register(
                            engine.environment(),
                            &name(target),
                            vec![entry],
                        )
                        .unwrap(),
                    );
                    let error = rejected(&changed, &query, limits.execution);
                    assert!(
                        matches!(
                            error,
                            EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
                        ),
                        "changed {target} extern: {error:?}"
                    );
                }
            }
            let clean = engine
                .execute_definition(query, &options, limits.execution)
                .unwrap()
                .into_complete()
                .unwrap();
            assert_scalar(&clean, 2022);
            assert_eq!(engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}
