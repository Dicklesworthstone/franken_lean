//! Actual pinned Array/List admission and runtime integration.
//! The Reference is an artifact source and test oracle, never an execution backend.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ConstantInfo, DefinitionSafety, Engine, Environment, ExprNode, IndependentReading,
    KVMap, LeafView, Name, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput,
};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const ARRAY_IMPORT_HEADER: &str =
    "prelude\nimport Init.Data.Array.Basic\nimport Init.Data.List.Control\n\n";
const MODEL_ROOTS: [&str; 8] = [
    "Array.forIn'",
    "Array.forIn'Unsafe",
    "List.forIn'",
    "Array",
    "Array.Mem",
    "ForInStep",
    "List",
    "Monad",
];

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn pinned_lib() -> PathBuf {
    std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|library| library.is_dir())
        .expect("actual pinned Reference library is mandatory; set FLN_REFERENCE_LIB")
}

fn read_parts(library: &Path, module: &Name) -> [Vec<u8>; 3] {
    let path = library
        .join(module.to_display_string().replace('.', "/"))
        .with_extension("olean");
    [
        std::fs::read(&path).expect("actual exported olean"),
        std::fs::read(path.with_extension("olean.server")).expect("actual server olean"),
        std::fs::read(path.with_extension("olean.private")).expect("actual private olean"),
    ]
}

fn collect_actual_imports(
    library: &Path,
    roots: &[Name],
    ordered: &mut Vec<Name>,
    artifacts: &mut BTreeMap<Name, [Vec<u8>; 3]>,
) {
    let mut pending: Vec<_> = roots.iter().cloned().map(|root| (root, false)).collect();
    let mut seen: BTreeSet<_> = artifacts.keys().cloned().collect();
    while let Some((module, finished)) = pending.pop() {
        if finished {
            ordered.push(module);
            continue;
        }
        if !seen.insert(module.clone()) {
            continue;
        }
        assert!(
            seen.len() <= 256,
            "the pinned Array/List import closure is bounded"
        );
        let parts = read_parts(library, &module);
        let imports = fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES))
            .expect("actual pinned import graph");
        artifacts.insert(module.clone(), parts);
        pending.push((module, true));
        pending.extend(
            imports
                .into_iter()
                .rev()
                .map(|dependency| (dependency, false)),
        );
    }
}

fn actual_array_import(library: &Path, include_strings: bool) -> Engine {
    let mut roots = vec![
        name("Init.Data.Array.Basic"),
        name("Init.Data.List.Control"),
    ];
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    collect_actual_imports(library, &roots, &mut ordered, &mut artifacts);
    assert_eq!(
        ordered.len(),
        74,
        "the complete pinned Array/List import closure"
    );
    if include_strings {
        // Admit the public String.append interface used by the shared String
        // probes after the unchanged Array model closure and declaration order.
        let string_root = name("Init.Data.String.Defs");
        collect_actual_imports(
            library,
            std::slice::from_ref(&string_root),
            &mut ordered,
            &mut artifacts,
        );
        roots.push(string_root);
    }
    assert!(roots.iter().all(|root| artifacts.contains_key(root)));
    let inputs: Vec<_> = ordered
        .iter()
        .map(|module| {
            let [exported, server, private] = &artifacts[module];
            OleanModuleInput {
                name: module,
                artifact: exported,
                server_artifact: Some(server),
                private_artifact: Some(private),
            }
        })
        .collect();
    eprintln!("FLN_ARRAY_MODULES_BEGIN");
    for module in &ordered {
        eprintln!("{}", module.to_display_string());
    }
    eprintln!("FLN_ARRAY_MODULES_END");
    eprintln!(
        "admitting {} actual Array/List modules, {} artifact bytes",
        inputs.len(),
        artifacts
            .values()
            .flat_map(|parts| parts.iter())
            .map(Vec::len)
            .sum::<usize>()
    );
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            &roots,
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            )),
        )
        .expect("the actual Array/List closure passes both ordinary admission seats")
        .into_complete()
        .expect("the actual Array/List import completes within explicit limits");
    assert_eq!(imported.modules.len(), ordered.len());
    for module in &imported.checked.modules {
        assert!(
            matches!(&module.decoded.independent, IndependentReading::Read(_)),
            "{} is independently decoded from its actual artifact bytes",
            module.name.to_display_string(),
        );
        assert_eq!(module.declarations.len(), module.decoded.constants.len());
        assert!(module.declarations.iter().all(|declaration| matches!(
            declaration.checker.schema,
            "fln.checker-admission/1" | "fln-checker/v1"
        )));
    }
    for root in MODEL_ROOTS {
        assert!(
            imported.engine.environment().contains(&name(root)),
            "{root}"
        );
    }
    if include_strings {
        assert!(
            imported
                .engine
                .environment()
                .contains(&name("String.append"))
        );
    }
    eprintln!(
        "admitted {} actual declarations and activated their source metadata",
        imported.engine.environment().constants().count()
    );
    imported.engine
}

fn with_actual_import(include_strings: bool, check: fn(&Engine)) {
    let library = pinned_lib();
    std::thread::Builder::new()
        .name("actual-imported-arrays".to_owned())
        .stack_size(STACK)
        .spawn(move || {
            let engine = actual_array_import(&library, include_strings);
            check(&engine);
        })
        .expect("Array admission worker")
        .join()
        .expect("Array admission and execution");
}

fn potential_companion(info: &ConstantInfo) -> Option<Name> {
    match info {
        ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe => {
            Some(Name::str(value.base.name.clone(), "_unsafe_rec"))
        }
        ConstantInfo::Opaque(value) if !value.is_unsafe => {
            Some(Name::str(value.base.name.clone(), "_unsafe_rec"))
        }
        _ => None,
    }
}

// Follow serialized types, bodies, recursor equations and mutual membership;
// erased propositions are dependencies too. Also follow selected replacement
// and recursive-companion bodies: their bytes are not bound by logical entries.
fn dependencies(
    environment: &Environment,
    implementation: &fln_elab::implemented_by::ImplementedByTable,
) -> BTreeSet<Name> {
    dependencies_from_roots(environment, implementation, &MODEL_ROOTS)
}

fn dependencies_from_roots(
    environment: &Environment,
    implementation: &fln_elab::implemented_by::ImplementedByTable,
    roots: &[&str],
) -> BTreeSet<Name> {
    let mut pending: Vec<_> = roots.iter().copied().map(name).collect();
    let mut found = BTreeSet::new();
    let mut nodes = 0usize;
    while let Some(label) = pending.pop() {
        if !found.insert(label.clone()) {
            continue;
        }
        assert!(found.len() <= 8192, "the fixed Array model is bounded");
        let info = environment
            .find(&label)
            .unwrap_or_else(|| panic!("missing actual dependency {}", label.to_display_string()));
        if let Some(target) = implementation.get(&label) {
            pending.push(target.clone());
        }
        if let Some(companion) = potential_companion(info)
            && environment.contains(&companion)
        {
            pending.push(companion);
        }
        // The runtime resolves a selected Partial companion back through the
        // logical parent's attributes before executing it. Bind that parent
        // even when an explicit replacement is our first edge to the sibling.
        if matches!(info, ConstantInfo::Defn(value)
            if value.safety == DefinitionSafety::Partial
                && matches!(label.leaf_view(), LeafView::Str("_unsafe_rec")))
        {
            pending.push(label.parent());
        }
        let mut expressions = vec![&info.constant_val().type_];
        match info {
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
            nodes += 1;
            assert!(
                nodes <= 4_000_000,
                "the fixed dependency expression graph is bounded"
            );
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => expressions.extend([f, a]),
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    expressions.extend([binder_type, body]);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    expressions.extend([type_, value, body]);
                }
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

fn encoded_name(label: &Name) -> String {
    let mut cursor = label.clone();
    let mut components = Vec::new();
    while !cursor.is_anonymous() {
        assert!(!cursor.component_overflowed());
        components.push(match cursor.leaf_view() {
            LeafView::Str(text) => {
                assert!(
                    !text.contains(['/', '\t', '\n']),
                    "fixed dependency name encoding"
                );
                format!("s:{text}")
            }
            LeafView::Num(number) => format!("n:{number}"),
            LeafView::Anonymous => unreachable!("nonanonymous dependency component"),
        });
        cursor = cursor.parent();
    }
    components.reverse();
    components.join("/")
}

fn print_root_debug(label: &str, info: &ConstantInfo) {
    // Bound line length without changing Unicode or the debug text. The
    // indexed chunks concatenate to the complete ConstantInfo, including
    // level parameter names, safety, type, value and inductive metadata.
    eprintln!("FLN_ARRAY_ROOT_DEBUG_BEGIN\t{label}");
    let text: Vec<_> = format!("{info:?}").chars().collect();
    for (index, chunk) in text.chunks(3000).enumerate() {
        eprintln!("{index:06}\t{}", chunk.iter().collect::<String>());
    }
    eprintln!("FLN_ARRAY_ROOT_DEBUG_END\t{label}");
}

#[test]
fn dump_pinned_array_iteration_model() {
    with_actual_import(false, |engine| {
        let environment = engine.environment();
        let implementation = fln_elab::implemented_by::ImplementedByTable::read(environment)
            .expect("actual implemented_by journal");
        assert_eq!(
            implementation.get(&name("Array.forIn'")),
            Some(&name("Array.forIn'Unsafe")),
        );
        for label in ["Array.forIn'", "List.forIn'"] {
            assert!(
                matches!(environment.find(&name(label)), Some(ConstantInfo::Defn(value))
                    if value.safety == DefinitionSafety::Safe),
                "{label} is an actual safe definition",
            );
        }
        assert!(
            matches!(environment.find(&name("Array.forIn'Unsafe")), Some(ConstantInfo::Defn(value))
                if value.safety == DefinitionSafety::Unsafe),
            "the pin selects an unsafe runtime body for Array iteration",
        );
        let found = match std::env::var("FLN_ARRAY_MODEL_ROOT").as_deref() {
            Ok("size") => dependencies_from_roots(environment, &implementation, &["Array.size"]),
            Ok("get") => {
                dependencies_from_roots(environment, &implementation, &["Array.getInternal"])
            }
            Ok("char") => dependencies_from_roots(environment, &implementation, &["Char.ofNatAux"]),
            Ok("word_lt") => dependencies_from_roots(
                environment,
                &implementation,
                &[
                    "USize.ofNatLT",
                    "USize.ofNat",
                    "USize.ofBitVec",
                    "USize.toNat",
                ],
            ),
            Err(std::env::VarError::NotPresent) => dependencies(environment, &implementation),
            _ => panic!("FLN_ARRAY_MODEL_ROOT must be absent, size, get, char or word_lt"),
        };
        let externs =
            fln_elab::externs::ExternTable::read(environment).expect("actual extern journal");
        let mut rows: Vec<_> = found
            .iter()
            .map(|label| {
                format!(
                    "{}\t{}",
                    encoded_name(label),
                    environment
                        .entry(label)
                        .expect("actual dependency entry")
                        .digest()
                        .to_hex(),
                )
            })
            .collect();
        rows.sort();
        assert_eq!(rows.len(), found.len());
        eprintln!("FLN_ARRAY_DEPENDENCIES_BEGIN");
        for row in rows {
            eprintln!("{row}");
        }
        eprintln!("FLN_ARRAY_DEPENDENCIES_END");
        eprintln!("FLN_ARRAY_DEPENDENCY_METADATA_BEGIN");
        for label in &found {
            if let Some(companion) = potential_companion(environment.find(label).unwrap()) {
                let selected = if environment.contains(&companion) {
                    encoded_name(&companion)
                } else {
                    "-".to_owned()
                };
                eprintln!("companion\t{}\t{selected}", encoded_name(label));
            }
            if let Some(target) = implementation.get(label) {
                eprintln!(
                    "implemented_by\t{}\t{}",
                    encoded_name(label),
                    encoded_name(target)
                );
            }
            if let Some(entries) = externs.get(label) {
                eprintln!("extern\t{}\t{entries:?}", encoded_name(label));
            }
        }
        eprintln!("FLN_ARRAY_DEPENDENCY_METADATA_END");
        for label in MODEL_ROOTS {
            print_root_debug(label, environment.find(&name(label)).unwrap());
        }
    });
}

#[path = "source_imported_arrays/authority.rs"]
mod authority;
#[path = "source_imported_arrays/execution.rs"]
mod execution;

// Each case keeps its complete source batch. A failure is reported and retained
// while independent batches run; no failed declaration is removed or ignored.
fn collect_case_failure(failures: &mut Vec<String>, label: &str, check: impl FnOnce()) {
    if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(check)) {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&str>()
                    .map(|message| (*message).to_owned())
            })
            .unwrap_or_else(|| "non-string panic payload".to_owned());
        eprintln!("{label}: failed: {message}");
        failures.push(format!("{label}: {message}"));
    }
}

#[test]
fn actual_imported_array_size_executes_replays_and_preserves_authority() {
    with_actual_import(false, |engine| {
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        let actual: BTreeSet<_> =
            dependencies_from_roots(engine.environment(), &implementations, &["Array.size"])
                .iter()
                .map(encoded_name)
                .collect();
        let expected: BTreeSet<_> =
            include_str!("../src/source_intrinsics/array_iteration/size_dependencies.txt")
                .lines()
                .map(|line| line.split('\t').next().unwrap().to_owned())
                .collect();
        assert!(!expected.is_empty());
        assert_eq!(
            actual, expected,
            "bind the full logical and selected size closure"
        );
        execution::program(
            engine,
            "actual imported Array sizes",
            include_str!("source_imported_arrays/sizes.lean")
                .strip_prefix(ARRAY_IMPORT_HEADER)
                .expect("the size fixture uses exactly the already-admitted Array/List imports"),
            8,
        );
    });
}

#[test]
fn actual_imported_array_get_executes_replays_and_preserves_authority() {
    with_actual_import(false, |engine| {
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        let actual: BTreeSet<_> = dependencies_from_roots(
            engine.environment(),
            &implementations,
            &["Array.getInternal"],
        )
        .iter()
        .map(encoded_name)
        .collect();
        let expected: BTreeSet<_> =
            include_str!("../src/source_intrinsics/array_iteration/get_dependencies.txt")
                .lines()
                .map(|line| line.split('\t').next().unwrap().to_owned())
                .collect();
        assert!(!expected.is_empty());
        assert_eq!(
            actual, expected,
            "bind every actual getter and selected dependency"
        );
        execution::program(
            engine,
            "actual imported Array getters",
            include_str!("source_imported_arrays/gets.lean")
                .strip_prefix(ARRAY_IMPORT_HEADER)
                .expect("getter probes use exactly the admitted Array/List imports"),
            12,
        );
        execution::program(
            engine,
            "Array size alongside getter support",
            include_str!("source_imported_arrays/sizes.lean")
                .strip_prefix(ARRAY_IMPORT_HEADER)
                .expect("all original size probes retain their import header"),
            8,
        );
        // This is a VM safety control, not an oracle parity claim: an
        // inconsistent user axiom must not manufacture an array element.
        // Every valid getter above has already executed and replayed.
        let options = KVMap::new();
        let before = engine.logical_root(&options);
        let invalid = "axiom invalidGetBound : 0 < (#[] : Array Nat).size\n#eval Array.getInternal (#[] : Array Nat) 0 invalidGetBound\n";
        let completed = engine
            .execute_source_commands_with_checks(
                invalid.as_bytes(),
                &options,
                fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .expect("the checked invalid bound reaches execution rather than a compiler refusal")
            .into_complete()
            .expect("the VM reports its own nonreturning exit");
        assert_eq!(completed.batch.source_evaluation_indices.len(), 1);
        let index = completed.batch.source_evaluation_indices[0];
        match &completed.batch.executions[index].exit {
            fln::VmExit::Panicked { usage, .. } | fln::VmExit::Refused { usage, .. } => {
                assert!(
                    usage.steps > 0,
                    "the invalid bound must enter the actual VM"
                );
            }
            exit => panic!("an impossible bound must never return an element: {exit:?}"),
        }
        assert_eq!(engine.logical_root(&options), before);
        assert!(!engine.environment().contains(&name("invalidGetBound")));
        execution::program(
            engine,
            "Array getter recovery after invalid bound",
            "-- FLN_EXPECT_NAT 4\n#eval Array.getInternal #[4] 0 (by decide)\n",
            1,
        );
        assert_eq!(engine.logical_root(&options), before);
    });
}

#[test]
fn actual_imported_char_construction_executes_and_replays() {
    with_actual_import(false, |engine| {
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        let actual: BTreeSet<_> =
            dependencies_from_roots(engine.environment(), &implementations, &["Char.ofNatAux"])
                .iter()
                .map(encoded_name)
                .collect();
        let expected: BTreeSet<_> =
            include_str!("../src/source_intrinsics/string_push/char_of_nat_dependencies.txt")
                .lines()
                .map(|line| line.split('\t').next().unwrap().to_owned())
                .collect();
        assert_eq!(expected.len(), 180, "the extracted full character closure");
        assert_eq!(actual, expected);
        execution::program(
            engine,
            "actual imported character construction",
            include_str!("source_imported_arrays/characters.lean")
                .strip_prefix(ARRAY_IMPORT_HEADER)
                .expect("the character probes use exactly the admitted imports"),
            12,
        );
    });
}

#[test]
fn actual_imported_bounded_word_construction_executes_and_replays() {
    with_actual_import(false, |engine| {
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        let actual: BTreeSet<_> = dependencies_from_roots(
            engine.environment(),
            &implementations,
            &[
                "USize.ofNatLT",
                "USize.ofNat",
                "USize.ofBitVec",
                "USize.toNat",
            ],
        )
        .iter()
        .map(encoded_name)
        .collect();
        let expected: BTreeSet<_> =
            include_str!("../src/source_intrinsics/io/fs/bytes/word/bounded_dependencies.txt")
                .lines()
                .map(|line| line.split('\t').next().unwrap().to_owned())
                .collect();
        assert_eq!(
            expected.len(),
            270,
            "the actual bounded-word and helper closure"
        );
        assert_eq!(actual, expected);
        execution::program(
            engine,
            "actual imported bounded word construction",
            include_str!("source_imported_arrays/bounded_words.lean")
                .strip_prefix(ARRAY_IMPORT_HEADER)
                .expect("bounded word probes use exactly the admitted imports"),
            8,
        );
    });
}

#[test]
fn actual_imported_array_iteration_executes_replays_and_preserves_authority() {
    with_actual_import(true, |engine| {
        let before = engine.logical_root(&KVMap::new());
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        let actual_dependencies: BTreeSet<_> = dependencies(engine.environment(), &implementations)
            .iter()
            .map(encoded_name)
            .collect();
        let expected_dependencies: BTreeSet<_> =
            include_str!("../src/source_intrinsics/array_iteration/dependencies.txt")
                .lines()
                .map(|line| line.split('\t').next().unwrap().to_owned())
                .collect();
        assert_eq!(
            actual_dependencies, expected_dependencies,
            "the exact runtime model must cover every actual logical and selected dependency",
        );
        let mut failures = Vec::new();
        for (label, source, count) in [
            (
                "dynamic Array programs",
                include_str!("source_imported_arrays/programs.lean"),
                23,
            ),
            (
                "observable Array effects",
                include_str!("source_imported_arrays/effects.lean"),
                20,
            ),
        ] {
            collect_case_failure(&mut failures, label, || {
                execution::program(engine, label, source, count);
            });
        }
        collect_case_failure(&mut failures, "checked bodies and safe override", || {
            authority::checked_bodies_and_safe_override(engine);
        });
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(
            failures.is_empty(),
            "all 43 Array evaluations and every authority control must succeed:\n{}",
            failures.join("\n"),
        );
    });
}

#[test]
fn dump_pinned_array_fold_model() {
    with_actual_import(false, |engine| {
        const ROOTS: [&str; 7] = [
            "Array.foldlM",
            "Array.foldlMUnsafe",
            "List.foldlM",
            "List.extract",
            "Array",
            "List",
            "Monad",
        ];
        let environment = engine.environment();
        let implementation = fln_elab::implemented_by::ImplementedByTable::read(environment)
            .expect("actual implemented_by journal");
        assert_eq!(
            implementation.get(&name("Array.foldlM")),
            Some(&name("Array.foldlMUnsafe")),
        );
        for label in ["Array.foldlM", "List.foldlM", "List.extract"] {
            assert!(
                matches!(environment.find(&name(label)), Some(ConstantInfo::Defn(value))
                    if value.safety == DefinitionSafety::Safe),
                "{label} is an actual safe definition",
            );
        }
        assert!(
            matches!(environment.find(&name("Array.foldlMUnsafe")), Some(ConstantInfo::Defn(value))
                if value.safety == DefinitionSafety::Unsafe),
            "the pin selects an unsafe runtime body for Array.foldlM",
        );
        let found = dependencies_from_roots(environment, &implementation, &ROOTS);
        let externs =
            fln_elab::externs::ExternTable::read(environment).expect("actual extern journal");
        let mut rows: Vec<_> = found
            .iter()
            .map(|label| {
                format!(
                    "{}\t{}",
                    encoded_name(label),
                    environment
                        .entry(label)
                        .expect("actual dependency entry")
                        .digest()
                        .to_hex(),
                )
            })
            .collect();
        rows.sort();
        assert_eq!(rows.len(), found.len());
        eprintln!("FLN_ARRAY_FOLD_DEPENDENCIES_BEGIN");
        for row in rows {
            eprintln!("{row}");
        }
        eprintln!("FLN_ARRAY_FOLD_DEPENDENCIES_END");
        eprintln!("FLN_ARRAY_FOLD_DEPENDENCY_METADATA_BEGIN");
        for label in &found {
            if let Some(companion) = potential_companion(environment.find(label).unwrap()) {
                let selected = if environment.contains(&companion) {
                    encoded_name(&companion)
                } else {
                    "-".to_owned()
                };
                eprintln!("companion\t{}\t{selected}", encoded_name(label));
            }
            if let Some(target) = implementation.get(label) {
                eprintln!(
                    "implemented_by\t{}\t{}",
                    encoded_name(label),
                    encoded_name(target)
                );
            }
            if let Some(entries) = externs.get(label) {
                eprintln!("extern\t{}\t{entries:?}", encoded_name(label));
            }
        }
        eprintln!("FLN_ARRAY_FOLD_DEPENDENCY_METADATA_END");
        for label in ROOTS {
            eprintln!("FLN_ARRAY_FOLD_ROOT_DEBUG_BEGIN\t{label}");
            let text: Vec<_> = format!("{:?}", environment.find(&name(label)).unwrap())
                .chars()
                .collect();
            for (index, chunk) in text.chunks(3000).enumerate() {
                eprintln!("{index:06}\t{}", chunk.iter().collect::<String>());
            }
            eprintln!("FLN_ARRAY_FOLD_ROOT_DEBUG_END\t{label}");
        }
    });
}

#[path = "source_imported_arrays/folds.rs"]
mod folds;

#[test]
fn actual_imported_array_folds_execute_replay_and_preserve_authority() {
    with_actual_import(true, |engine| {
        let before = engine.logical_root(&KVMap::new());
        folds::exact_model(engine);
        let implementations =
            fln_elab::implemented_by::ImplementedByTable::read(engine.environment()).unwrap();
        assert_eq!(
            implementations.get(&name("Array.foldlM")),
            Some(&name("Array.foldlMUnsafe")),
        );
        let mut failures = Vec::new();
        for (label, source, count) in [
            (
                "bounded and higher-order Array folds",
                include_str!("source_imported_arrays/folds.lean"),
                13,
            ),
            (
                "Array fold Monad sequencing and short-circuit",
                include_str!("source_imported_arrays/fold_effects.lean"),
                14,
            ),
        ] {
            collect_case_failure(&mut failures, label, || {
                execution::program(engine, label, source, count);
            });
        }
        collect_case_failure(&mut failures, "Array fold source rollback", || {
            folds::source_rollback(engine);
        });
        collect_case_failure(&mut failures, "Array fold VM budget and recovery", || {
            folds::execution_budget(engine);
        });
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        assert!(
            failures.is_empty(),
            "all 27 Array fold evaluations and every rollback/resource control must succeed:\n{}",
            failures.join("\n"),
        );
    });
}
