//! Nested-family layouts and recursor groups execute without a foreign runtime.
#![forbid(unsafe_code)]
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Mode, Name, OleanCheckLimits,
    OleanModuleInput,
};
use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::{
        OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

const STACK: usize = 128 * 1024 * 1024;
const TREE: &str =
    "inductive NestedTree where\n  | leaf (value : Nat)\n  | node (children : List NestedTree)\n";
const VALUE: &str = "NestedTree.node (List.cons (NestedTree.leaf 40) (List.cons (NestedTree.node (List.cons (NestedTree.leaf 2) List.nil)) List.nil))";
const MOTIVES: &str = "(fun (_ : NestedTree) => Nat) (fun (_ : List NestedTree) => Nat)";
const MINORS: &str = "(fun (n : Nat) => n) (fun (_ : List NestedTree) (ih : Nat) => ih) 0 (fun (_ : NestedTree) (_ : List NestedTree) (head tail : Nat) => head + tail)";

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))
}
fn with_fixture(test: impl FnOnce(&Engine, &Engine, &Path) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<(Engine, Engine, PathBuf)>> = OnceLock::new();
            let fixture = FIXTURE.get_or_init(|| {
                let row = include_str!("../../../SUITE.lock")
                    .lines()
                    .find(|line| line.starts_with("reference leanprover/lean4 "))
                    .unwrap();
                let field = |key: &str| {
                    row.split_whitespace()
                        .find_map(|word| word.strip_prefix(key))
                        .unwrap()
                };
                let library = std::env::var_os("FLN_REFERENCE_LIB")
                    .map(PathBuf::from)
                    .or_else(|| {
                        std::env::var_os("HOME").map(|home| {
                            PathBuf::from(home)
                                .join(".elan/toolchains")
                                .join(format!("leanprover--lean4---{}", field("tag=")))
                                .join("lib/lean")
                        })
                    })
                    .filter(|path| path.join("Init/Prelude.olean").is_file());
                let Some(library) = library else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "pinned Reference required"
                    );
                    eprintln!("SKIP: pinned Reference library absent");
                    return None;
                };
                let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
                let version = Command::new(&compiler).arg("--version").output().unwrap();
                let text = String::from_utf8(version.stdout).unwrap();
                assert!(
                    version.status.success()
                        && text.contains(field("tag=").trim_start_matches('v'))
                        && text.contains(field("commit=")),
                    "{text}"
                );
                let path = library.join("Init/Prelude.olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let module = Name::from_components(["Init", "Prelude"]);
                let inputs = [OleanModuleInput {
                    name: &module,
                    artifact: &parts[0],
                    server_artifact: Some(&parts[1]),
                    private_artifact: Some(&parts[2]),
                }];
                let import = |mode| {
                    Engine::builder()
                        .mode(mode)
                        .build_empty()
                        .import_olean_modules_for_source(
                            &inputs,
                            std::slice::from_ref(&module),
                            &KVMap::new(),
                            SourceOleanImportLimits::new(OleanCheckLimits::new(
                                STACK,
                                limits().kernel,
                            )),
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap()
                        .engine
                };
                Some((import(Mode::DEFAULT), import(Mode::Frontier), compiler))
            });
            if let Some((sound, frontier, compiler)) = fixture {
                test(sound, frontier, compiler);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
fn reference(compiler: &Path, source: &str, expected: &str) {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!("fln-nested-runtime-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join(format!("{}.lean", NEXT.fetch_add(1, Ordering::Relaxed)));
    std::fs::write(&path, source).unwrap();
    let output = Command::new(compiler).arg(path).output().unwrap();
    assert!(
        output.status.success(),
        "{source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        expected,
        "{source}"
    );
}
fn run(engine: &Engine, source: &str, expected: usize) -> u64 {
    run_value(engine, source, ClosedVmValue::Scalar(expected))
}
fn run_value(engine: &Engine, source: &str, expected: ClosedVmValue) -> u64 {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let execute = || {
        engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap()
    };
    let first = execute();
    let execution = first.executions.last().unwrap();
    assert_eq!(
        fln::closed_vm_value(&execution.exit).unwrap(),
        Some(expected.clone()),
        "{source}"
    );
    let replay = fln::execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(fln::closed_vm_value(&replay).unwrap(), Some(expected));
    let second = execute();
    assert_eq!(
        execution.flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(
        first.engine.logical_root(&options),
        second.engine.logical_root(&options)
    );
    assert_eq!(engine.logical_root(&options), root);
    let fln::VmExit::Returned(value) = &execution.exit else {
        panic!("returned value")
    };
    value.usage.steps
}

#[test]
fn ordinary_nested_matches_execute_from_the_imported_prelude() {
    with_fixture(|engine, _, compiler| {
        let defs = format!(
            "{TREE}def width : NestedTree -> Nat\n  | .leaf _ => 1\n  | .node children => List.length children\n"
        );
        for (value, expected) in [
            ("NestedTree.leaf 7", 1),
            ("NestedTree.node List.nil", 0),
            (VALUE, 2),
        ] {
            let source = format!("{defs}#eval width ({value})\n");
            reference(compiler, &source, &expected.to_string());
            run(engine, &source, expected);
        }
    });
}

#[test]
fn nested_folds_execute_the_original_and_auxiliary_members() {
    with_fixture(|_, engine, compiler| {
        for (entry, ty, value) in [
            ("NestedTree.rec", "NestedTree", VALUE),
            (
                "NestedTree.rec_1",
                "List NestedTree",
                "List.cons (NestedTree.leaf 40) (List.cons (NestedTree.leaf 2) List.nil)",
            ),
        ] {
            let def =
                format!("def total (value : {ty}) : Nat := @{entry} {MOTIVES} {MINORS} value\n");
            // Raw recursors are a Frontier execution surface: the pin checks
            // and reduces these definitions but will not compile them either.
            reference(
                compiler,
                &format!("{TREE}noncomputable {def}#reduce total ({value})\n"),
                "42",
            );
            run(engine, &format!("{TREE}{def}#eval total ({value})\n"), 42);
        }
    });
}

#[test]
fn nested_parameter_specializations_preserve_owned_fields() {
    with_fixture(|engine, _, compiler| {
        let source = r#"
universe u
inductive Rose (A : Type u) : Type u where
  | node (value : A) (children : List (Rose A))
def rootValue {A : Type u} (tree : Rose A) : A :=
  match tree with
  | .node value _ => value
"#;
        let number = format!("{source}#eval rootValue (Rose.node 42 List.nil)\n");
        reference(compiler, &number, "42");
        run(engine, &number, 42);
        let string = format!("{source}#eval rootValue (Rose.node \"hello\" List.nil)\n");
        reference(compiler, &string, "\"hello\"");
        run_value(engine, &string, ClosedVmValue::String("hello".into()));
    });
}

#[test]
fn repeated_container_heads_select_the_actual_auxiliary_instantiation() {
    with_fixture(|_, engine, compiler| {
        let data =
            "inductive Layers where\n | leaf (n : Nat)\n | nest (children : List (List Layers))\n";
        let motives = "(fun (_ : Layers) => Nat) (fun (_ : List (List Layers)) => Nat) (fun (_ : List Layers) => Nat)";
        let minors = "(fun (n : Nat) => n) (fun (_ : List (List Layers)) (ih : Nat) => ih) 0 (fun (_ : List Layers) (_ : List (List Layers)) (head tail : Nat) => head + tail) 0 (fun (_ : Layers) (_ : List Layers) (head tail : Nat) => head + tail)";
        let list = "List.cons (Layers.leaf 40) (List.cons (Layers.leaf 2) List.nil)";
        for (entry, ty, value) in [
            (
                "Layers.rec",
                "Layers",
                format!("Layers.nest (List.cons ({list}) List.nil)"),
            ),
            (
                "Layers.rec_1",
                "List (List Layers)",
                format!("List.cons ({list}) List.nil"),
            ),
            ("Layers.rec_2", "List Layers", list.to_owned()),
        ] {
            let def =
                format!("def total (value : {ty}) : Nat := @{entry} {motives} {minors} value\n");
            reference(
                compiler,
                &format!("{data}noncomputable {def}#reduce total ({value})\n"),
                "42",
            );
            run(engine, &format!("{data}{def}#eval total ({value})\n"), 42);
        }
    });
}

#[test]
fn nested_cases_return_callbacks_with_captured_owned_values() {
    with_fixture(|engine, _, compiler| {
        let source = format!(
            r#"{TREE}
def choose (offset : Nat) (tree : NestedTree) : Nat -> Nat :=
  match tree with
  | .leaf n => fun x => offset + n + x
  | .node children => fun x => offset + List.length children + x
#eval let f := choose 1 (NestedTree.leaf 36); f 5
"#
        );
        reference(compiler, &source, "42");
        run(engine, &source, 42);
        let source = format!(
            r#"{TREE}
def choose (label : String) (tree : NestedTree) : Nat -> String :=
  match tree with
  | .leaf _ => fun _ => label
  | .node _ => fun _ => "other"
#eval let f := choose "kept" (NestedTree.leaf 36); f 5
"#
        );
        reference(compiler, &source, "\"kept\"");
        run_value(engine, &source, ClosedVmValue::String("kept".into()));
    });
}

#[test]
fn nested_matches_keep_unselected_branches_lazy_and_selected_work_strict() {
    with_fixture(|engine, _, compiler| {
        let defs = format!(
            r#"{TREE}
partial def spin (n : Nat) : Nat := spin n
def choose : NestedTree -> Nat
  | .leaf n => n
  | .node _ => spin 0
"#
        );
        let source = format!("{defs}#eval choose (NestedTree.leaf 42)\n");
        reference(compiler, &source, "42");
        run(engine, &source, 42);
        for term in [
            "choose (NestedTree.node List.nil)",
            "let paid := spin 0; choose (NestedTree.leaf 42)",
        ] {
            let source = format!("{defs}#eval {term}\n");
            let mut low = limits();
            low.vm.max_steps = 256;
            let root = engine.logical_root(&KVMap::new());
            let result = engine
                .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), low)
                .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert!(
                matches!(result, fln::Outcome::Inconclusive(_)),
                "{result:?}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
        }
    });
}

#[test]
fn heterogeneous_nested_containers_keep_their_constructor_fields() {
    with_fixture(|engine, _, compiler| {
        let source = r#"
inductive Packet where
  | data (value : Nat)
  | group (children : Array Packet) (selected : Option Packet)
def inspect : Packet -> Nat
  | .data value => value
  | .group children selected =>
    match selected with
    | .none => match children with
      | .mk values => List.length values
    | .some child => match child with
      | .data value => value
      | .group _ _ => 7
#eval inspect (Packet.group (Array.mk (List.cons (Packet.data 12) List.nil)) (Option.some (Packet.data 42)))
"#;
        reference(compiler, source, "42");
        run(engine, source, 42);
    });
}

fn resource_error(error: &fln::EngineExecutionError) -> bool {
    match error {
        fln::EngineExecutionError::BatchCommand { error, .. } => resource_error(error),
        fln::EngineExecutionError::Ingress(fln::IngressError::ResourceLimit { .. }) => true,
        _ => false,
    }
}
#[test]
fn nested_runtime_limits_publish_nothing_and_retries_reproduce_the_bytecode() {
    with_fixture(|_, engine, _| {
        let source = format!(
            "{TREE}def total (value : NestedTree) : Nat := @NestedTree.rec {MOTIVES} {MINORS} value\n#eval total ({VALUE})\n"
        );
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        for which in 0..4 {
            let mut low = limits();
            match which {
                0 => low.ingress.max_nodes = 10,
                1 => low.ingress.fir.max_constructors = 1,
                2 => low.ingress.max_lambda_bindings = 1,
                _ => low.vm.max_steps = 1,
            }
            match engine.execute_source_definitions(&[source.as_bytes()], &options, low) {
                Ok(fln::Outcome::Inconclusive(_)) => {}
                Err(error) if resource_error(&error) => {}
                other => panic!("expected a resource stop at {which}: {other:?}"),
            }
            assert_eq!(engine.logical_root(&options), root);
            assert!(
                !engine
                    .environment()
                    .contains(&Name::from_components(["total"]))
            );
        }
        run(engine, &source, 42);
    });
}
