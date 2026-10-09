//! Dual-checked selected IO declarations, never full IO module admission.
//!
//! The actual IO metadata is used only to elaborate and discover dependencies.
//! Every discovered fixture declaration is admitted again over the selected,
//! independently byte-read pin declarations before its explicit evaluation.
use super::*;
use fln::{
    Declaration, ExprNode, IndependentReading, OleanFrontierJobs, OleanModuleInput,
    SourceCheckLimits,
};
use std::collections::{BTreeSet, HashSet};
use std::num::NonZeroUsize;

#[path = "export.rs"]
mod export;

fn references(expression: &Expr, output: &mut BTreeSet<Name>) {
    let mut pending = vec![expression];
    let mut seen = HashSet::new();
    while let Some(expression) = pending.pop() {
        if !seen.insert(std::ptr::from_ref(expression.node())) {
            continue;
        }
        assert!(seen.len() <= 1_000_000, "bounded fixture dependency walk");
        match expression.node() {
            ExprNode::Const { name, .. } => {
                output.insert(name.clone());
            }
            ExprNode::App { f, a } => pending.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_, value, body]),
            ExprNode::MData { expr, .. } => pending.push(expr),
            ExprNode::Proj {
                struct_name, expr, ..
            } => {
                output.insert(struct_name.clone());
                pending.push(expr);
            }
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
}

fn dependencies(info: &ConstantInfo, environment: &Environment) -> BTreeSet<Name> {
    let mut output = BTreeSet::new();
    references(&info.constant_val().type_, &mut output);
    match info {
        ConstantInfo::Defn(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Thm(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Opaque(value) => {
            references(&value.value, &mut output);
            output.extend(value.all.iter().cloned());
        }
        ConstantInfo::Induct(value) => {
            output.extend(value.all.iter().cloned());
            output.extend(value.ctors.iter().cloned());
            // Admission compares the complete actual generated recursor set.
            for (label, _) in environment.constants() {
                if let Some(ConstantInfo::Rec(recursor)) = environment.find(label)
                    && recursor.all == value.all
                {
                    output.insert(label.clone());
                }
            }
        }
        ConstantInfo::Ctor(value) => {
            output.insert(value.induct.clone());
        }
        ConstantInfo::Rec(value) => {
            output.extend(value.all.iter().cloned());
            for rule in &value.rules {
                output.insert(rule.ctor.clone());
                references(&rule.rhs, &mut output);
            }
        }
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
    }
    output
}

fn selected_names(raw: &Engine, base: &Engine, fixtures: &[Declaration]) -> BTreeSet<Name> {
    let mut pending: BTreeSet<Name> = [
        "IO.RealWorld.nonemptyType",
        "IO.RealWorld",
        "BaseIO",
        "EIO",
        "IO",
        "IO.Error",
    ]
    .map(name)
    .into_iter()
    .collect();
    for declaration in fixtures {
        let Declaration::Defn(value) = declaration else {
            panic!("ordinary fixture definition");
        };
        references(&value.base.type_, &mut pending);
        references(&value.value, &mut pending);
    }
    let fixture_names: BTreeSet<_> = fixtures
        .iter()
        .map(|declaration| {
            let Declaration::Defn(value) = declaration else {
                unreachable!()
            };
            value.base.name.clone()
        })
        .collect();
    let mut selected = BTreeSet::new();
    while let Some(label) = pending.pop_first() {
        if base.environment().contains(&label)
            || fixture_names.contains(&label)
            || !selected.insert(label.clone())
        {
            continue;
        }
        let info = raw
            .environment()
            .find(&label)
            .unwrap_or_else(|| panic!("missing actual pin declaration {label:?}"));
        pending.extend(dependencies(info, raw.environment()));
        assert!(
            selected.len() <= 10_000,
            "selected declaration fixture remains bounded"
        );
    }
    selected
}

fn fixture_declarations(raw: &Engine) -> Vec<Declaration> {
    let options = KVMap::new();
    let limits = SourceCheckLimits::new(
        EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)).admission(),
    );
    let mut fixtures = Vec::new();
    let mut sources: Vec<String> = PROGRAMS
        .iter()
        .map(|(_, source)| (*source).to_owned())
        .collect();
    sources.extend([
        "#eval (throw (IO.userError \"expected failure\") : IO Nat)".to_owned(),
        "#eval EIO.toIO IO.userError (throw \"expected failure\" : EIO String Nat)".to_owned(),
        "def ioUnsupportedGeneric := (pure 42 : EIO String Nat)".to_owned(),
    ]);
    for (index, source) in sources.into_iter().enumerate() {
        let source = source.replace("#eval ", &format!("def ioSelectedProbe{index} := "));
        let checked = raw
            .check_source_files(&[source.as_bytes()], &options, limits)
            .unwrap_or_else(|error| panic!("selected fixture {index}: {error:?}"))
            .into_complete()
            .unwrap();
        for (label, _) in checked.engine.environment().constants() {
            if raw.environment().contains(label) {
                continue;
            }
            let Some(ConstantInfo::Defn(value)) = checked.engine.environment().find(label) else {
                panic!("fixture creates only ordinary definitions: {label:?}");
            };
            fixtures.push(Declaration::Defn(value.clone()));
        }
    }
    // Environment iteration is not source order. Admit aliases before the
    // fixture definitions that use them, exactly as the original source did.
    let names: BTreeSet<_> = fixtures
        .iter()
        .map(|declaration| {
            let Declaration::Defn(value) = declaration else {
                unreachable!();
            };
            value.base.name.clone()
        })
        .collect();
    assert_eq!(names.len(), fixtures.len(), "unique source fixture names");
    let mut pending: BTreeMap<_, _> = fixtures
        .into_iter()
        .map(|declaration| {
            let Declaration::Defn(value) = &declaration else {
                unreachable!();
            };
            let mut dependencies = BTreeSet::new();
            references(&value.base.type_, &mut dependencies);
            references(&value.value, &mut dependencies);
            dependencies.retain(|label| names.contains(label));
            (value.base.name.clone(), (declaration, dependencies))
        })
        .collect();
    let mut ordered = Vec::new();
    while !pending.is_empty() {
        let next = pending
            .iter()
            .find(|(_, (_, dependencies))| dependencies.is_empty())
            .map(|(label, _)| label.clone())
            .expect("ordinary source fixture definitions are acyclic");
        let (declaration, _) = pending.remove(&next).unwrap();
        ordered.push(declaration);
        for (_, dependencies) in pending.values_mut() {
            dependencies.remove(&next);
        }
    }
    ordered
}

fn artifact_order(parts: &BTreeMap<Name, Parts>, root: &Name) -> Vec<Name> {
    let imports: BTreeMap<_, _> = parts
        .iter()
        .map(|(name, (public, _, _))| {
            (
                name.clone(),
                fln::olean_module_imports(public, OleanDecodeLimits::new(BYTES)).unwrap(),
            )
        })
        .collect();
    let mut seen = BTreeSet::new();
    let mut order = Vec::new();
    let mut pending = vec![(root.clone(), false)];
    while let Some((module, exit)) = pending.pop() {
        if exit {
            order.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        pending.push((module.clone(), true));
        pending.extend(
            imports[&module]
                .iter()
                .rev()
                .cloned()
                .map(|name| (name, false)),
        );
    }
    assert_eq!(order.len(), parts.len());
    order
}

fn admitted_st(library: &Path) -> Engine {
    let root = name("Init.System.ST");
    let parts = artifacts(library, &root);
    assert_eq!(parts.len(), 54);
    let inputs: Vec<_> = parts
        .iter()
        .map(|(name, (public, server, private))| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: server.as_deref(),
            private_artifact: private.as_deref(),
        })
        .collect();
    let mut limits =
        SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
    limits.jobs = OleanFrontierJobs {
        threads: NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: STACK,
    };
    let checked = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&root),
            &KVMap::new(),
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(checked.checked.modules.len(), 54);
    for module in &checked.checked.modules {
        assert!(matches!(
            module.decoded.independent,
            IndependentReading::Read(_)
        ));
        assert_eq!(module.declarations.len(), module.decoded.constants.len());
    }
    eprintln!("Actual complete ST closure admitted: 54 modules");
    checked.engine
}

pub(super) fn run(library: &Path) {
    let actual::SourceFixture {
        engine: raw,
        owners,
    } = actual::decoded_io_with_source_metadata(library);
    let fixtures = fixture_declarations(&raw);
    eprintln!(
        "Original source fixture declarations constructed: {}",
        fixtures.len()
    );
    let mut engine = admitted_st(library);
    let selected = selected_names(&raw, &engine, &fixtures);
    eprintln!(
        "Selected actual IO declaration dependency slice: {} declarations (not IO module admission)",
        selected.len()
    );
    let parts = artifacts(library, &name("Init.System.IO"));
    let order = artifact_order(&parts, &name("Init.System.IO"));
    let options = KVMap::new();
    let limits = OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK));
    let mut admitted = BTreeSet::new();
    let mut origins = Vec::new();
    for module in order {
        // These owners came from the first actual artifact reading. They only
        // avoid decoding unrelated modules a second time; every selected
        // declaration still crosses the independent reader and both checkers,
        // and the final admitted == selected assertion forbids omissions.
        if !owners[&module]
            .iter()
            .any(|label| selected.contains(label) && !engine.environment().contains(label))
        {
            continue;
        }
        let (public, server, private) = &parts[&module];
        let mut decoded = fln::decode_olean_module_artifacts(
            public,
            server.as_deref().unwrap_or_default(),
            private.as_deref().unwrap_or_default(),
            limits.decode,
        )
        .unwrap();
        decoded.constants.retain(|info| {
            selected.contains(info.name()) && !engine.environment().contains(info.name())
        });
        if decoded.constants.is_empty() {
            continue;
        }
        assert!(matches!(decoded.independent, IndependentReading::Read(_)));
        let checked = engine
            .check_decoded_olean(decoded.clone(), &options, limits)
            .unwrap_or_else(|error| panic!("selected declarations from {module:?}: {error:?}"))
            .into_complete()
            .unwrap();
        if module == name("Init.System.IO") {
            let before = engine.logical_root(&options);
            let mut incomplete = decoded.clone();
            let missing = name("IO.RealWorld.nonemptyType");
            assert!(!engine.environment().contains(&missing));
            incomplete.constants.retain(|info| info.name() != &missing);
            assert!(matches!(
                engine.check_decoded_olean(incomplete, &options, limits),
                Err(fln::OleanCheckError::MissingConstants { .. })
            ));
            assert_eq!(engine.logical_root(&options), before);

            let mut changed = decoded.clone();
            let ConstantInfo::Defn(alias) = changed
                .constants
                .iter_mut()
                .find(|info| info.name() == &name("IO"))
                .expect("actual IO alias")
            else {
                panic!("actual IO is a safe definition");
            };
            // Well-typed identity wrapping still differs from the independent
            // reading of the actual bytes. No altered model may be admitted.
            alias.value = Expr::app(
                Expr::lam(
                    Name::anonymous(),
                    alias.base.type_.clone(),
                    Expr::bvar(0).unwrap(),
                    fln::BinderInfo::Default,
                ),
                alias.value.clone(),
            );
            let refusal = engine
                .check_decoded_olean(changed, &options, limits)
                .expect_err("a changed primary reading cannot be admitted");
            let fln::OleanCheckError::Admission(mut error) = refusal else {
                panic!("a fresh declaration must reach its council: {refusal:?}");
            };
            while let fln::EngineAdmissionError::BatchDeclaration { error: nested, .. } = error {
                error = *nested;
            }
            let fln::EngineAdmissionError::CouncilHalted { summary } = error else {
                panic!("the independent reading must halt admission: {error:?}");
            };
            assert!(
                summary.contains("kernel_accepted=true")
                    && summary.contains(
                        "fln-checker's own reading of the .olean declares `IO` differently"
                    ),
                "the IO reading mismatch must cause the halt: {summary}"
            );
            assert_eq!(engine.logical_root(&options), before);
        }
        assert_eq!(checked.declarations.len(), checked.decoded.constants.len());
        origins.push((
            module.clone(),
            checked
                .declarations
                .iter()
                .map(|row| row.name.clone())
                .collect(),
        ));
        for row in &checked.declarations {
            assert_eq!(row.checker.schema, "fln.checker-admission/1");
            admitted.insert(row.name.clone());
        }
        engine = checked.engine;
    }
    assert_eq!(
        admitted, selected,
        "every selected pin declaration was independently read and admitted"
    );
    let externs = fln_elab::externs::ExternTable::read(raw.environment()).unwrap();
    for label in &selected {
        if let Some(entries) = externs.get(label) {
            engine = Engine::from_environment(
                fln_elab::externs::register(engine.environment(), label, entries.to_vec()).unwrap(),
            );
        }
    }
    // These definitions were elaborated using real metadata, but no raw
    // declaration is trusted: both checkers accept them again in this engine.
    let engine = engine
        .admit_declarations(&fixtures, &options, limits.admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    // Retain the checked declarations before execution. A runtime failure
    // must not discard this completed admission checkpoint; the artifact
    // claims declaration admission, never runtime success or full IO imports.
    export::retain(&engine, &selected, &fixtures, &parts, &origins);
    // The raw metadata environment checks the original source forms only.
    // All selected declarations and fixture bodies above were admitted again
    // in the separate engine used by the authoritative executions below.
    super::check_programs(&raw);
    eprintln!("Original IO source programs passed using raw metadata");
    check_selected_programs(engine);
}

pub(super) fn check_selected_programs(engine: Engine) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let foreign = Engine::from_environment(
        fln_elab::externs::register(
            engine.environment(),
            &name("IO"),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_io_alias_must_not_be_erased".to_owned(),
            }],
        )
        .unwrap(),
    );
    let foreign_root = foreign.logical_root(&options);
    let error = foreign
        .execute_source_commands_with_checks(
            b"#eval ioSelectedProbe0",
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect_err("an explicit foreign alias cannot acquire native IO entry authority");
    let fln::EngineExecutionError::BatchCommand { error, .. } = error else {
        panic!("expected bounded command refusal");
    };
    assert!(matches!(
        *error,
        fln::EngineExecutionError::Ingress(fln::IngressError::UnsupportedNode { .. })
    ));
    assert_eq!(foreign.logical_root(&options), foreign_root);
    assert_eq!(engine.logical_root(&options), before);

    let mut tight = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    tight.ingress.max_nodes = 1;
    let error = engine
        .execute_source_commands_with_checks(b"#eval ioSelectedProbe0", &options, tight)
        .expect_err("bounded IO entry preparation does not reset its work meter");
    let fln::EngineExecutionError::BatchCommand { error, .. } = error else {
        panic!("expected bounded command refusal");
    };
    assert!(
        matches!(*error, fln::EngineExecutionError::Ingress(ref error) if error.is_resource_exhaustion()),
        "{error:?}"
    );
    assert_eq!(engine.logical_root(&options), before);

    let dormant = engine
        .execute_source_definitions(
            &[b"def selectedDormant : IO Nat := ioSelectedProbe9"],
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(dormant.executions.len(), 1);
    assert_deferred(&dormant.executions[0]);
    assert_eq!(engine.logical_root(&options), before);
    assert_unsupported_command(&engine, "#eval ioUnsupportedGeneric");
    for index in 0..PROGRAMS.len() + 2 {
        let source = format!("#eval ioSelectedProbe{index}");
        let completed = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = &completed.batch.executions[completed.batch.source_evaluation_indices[0]];
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        match execution
            .io_evaluation_outcome()
            .unwrap()
            .expect("explicit IO evaluation")
        {
            IoEvaluationOutcome::Returned { runtime_type, exit } if index < PROGRAMS.len() => {
                let (expected_type, expected_value) = expected_success(index);
                assert_eq!(runtime_type, expected_type);
                assert_eq!(success_payload(&engine, &exit), expected_value);
            }
            IoEvaluationOutcome::Raised { runtime_type, .. } if index >= PROGRAMS.len() => {
                assert_eq!(runtime_type, Expr::const_(name("IO.Error"), vec![]));
            }
            result => panic!("selected probe {index}: {result:?}"),
        }
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        compare_packet(&engine, &execution.exit, &replay);
        assert_eq!(engine.logical_root(&options), before);
    }
}
