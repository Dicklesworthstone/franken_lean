//! Erased type growth must not create an infinite compiler specialization graph.
//! These source programs pass both admission engines and run on Golem. The
//! optional pinned oracle sees the identical programs and expected results.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    SourceCheckLimits, VmExit,
};
use fln_comp::ingress::{IngressError, IngressResource};
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn seed() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits().admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

fn evaluate(engine: &Engine, source: &str, expected: &str) -> Vec<u8> {
    let result = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let [execution] = result.executions.as_slice() else {
        panic!("one requested evaluation")
    };
    let VmExit::Returned(value) = &execution.exit else {
        panic!("{source}: {:?}", execution.exit)
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}",
    );
    execution.flbc_artifact.clone()
}

fn oracle(source: &str, expected: &str) {
    let reference = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .and_then(|library| library.parent()?.parent().map(|root| root.join("bin/lean")))
        .filter(|path| path.is_file());
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required but FLN_REFERENCE_LIB is unavailable",
        );
        return;
    };
    static SERIAL: AtomicUsize = AtomicUsize::new(0);
    let directory = loop {
        let candidate = std::env::temp_dir().join(format!(
            "fln-erased-recursion-{}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed),
        ));
        match std::fs::create_dir(&candidate) {
            Ok(()) => break candidate,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("could not create oracle fixture: {error}"),
        }
    };
    let file = directory.join("Main.lean");
    std::fs::write(&file, source).unwrap();
    let output = Command::new(reference)
        .arg("--memory=1024")
        .arg(&file)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{source}\nstdout={}\nstderr={}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
    assert!(output.stderr.is_empty());
}

const PAIR: &str = "structure Pair (A B : Type) where\n  first : A\n  second : B\n";

fn typed(next: &str) -> String {
    format!(
        "mutual\n\
         partial def typedLeft (A : Type) (n : Nat) : Nat :=\n\
           if n == 0 then 2 else typedRight {next} (n - 1)\n\
         partial def typedRight (A : Type) (n : Nat) : Nat :=\n\
           if n == 0 then 3 else typedLeft {next} (n - 1)\n\
         end\n"
    )
}

#[test]
fn growing_erased_types_compile_at_zero_and_run_recursive_calls() {
    let base = seed();
    let plain = "mutual\npartial def plainLeft (n : Nat) : Nat := if n == 0 then 2 else plainRight (n - 1)\npartial def plainRight (n : Nat) : Nat := if n == 0 then 3 else plainLeft (n - 1)\nend\n";
    let cases = [
        (plain.to_owned(), "plainLeft"),
        (typed("A"), "typedLeft Nat"),
        (format!("{PAIR}{}", typed("(Pair A A)")), "typedLeft Nat"),
        (typed("(A → A)"), "typedLeft Nat"),
    ];
    for (source, call) in cases {
        oracle(
            &format!("{source}#eval {call} 0\n#eval {call} 4\n#eval {call} 5\n"),
            "2\n2\n3\n",
        );
        let engine = checked(&base, &source);
        let root = engine.logical_root(&KVMap::new());
        for (input, expected) in [(0, "2"), (4, "2"), (5, "3")] {
            evaluate(&engine, &format!("#eval {call} {input}"), expected);
        }
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn represented_type_arguments_keep_their_distinct_values_and_callback_abis() {
    let source = "partial def keep (A : Type) (x : A) (n : Nat) : A :=\n  if n == 0 then x else keep A x (n - 1)\npartial def invoke (A : Type) (f : A → Nat) (x : A) (n : Nat) : Nat :=\n  if n == 0 then f x else invoke A f x (n - 1)\n";
    let queries = [
        ("#eval keep Nat 41 4", "41"),
        ("#eval String.length (keep String \"typed\" 4)", "5"),
        ("#eval invoke Nat (fun x => x + 1) 41 4", "42"),
        ("#eval invoke String String.length \"different\" 4", "9"),
    ];
    oracle(
        &format!(
            "{source}{}\n",
            queries
                .iter()
                .map(|(query, _)| *query)
                .collect::<Vec<_>>()
                .join("\n"),
        ),
        "41\n5\n42\n9\n",
    );
    let engine = checked(&seed(), source);
    for (query, expected) in queries {
        evaluate(&engine, query, expected);
    }
}

#[test]
fn a_phantom_looking_cycle_keeps_a_represented_callees_type_arguments() {
    // `forward` has only Nat runtime parameters/results. Its self edge is not
    // enough to prove its type argument phantom: the other edge passes it to
    // functions whose represented callback types depend on that argument.
    let source = "partial def keep (A : Type) (x : A) (n : Nat) : A :=\n  if n == 0 then x else keep A x (n - 1)\npartial def consume (B : Type) (x : B) (n : Nat) : Nat :=\n  if n == 0 then 1 else consume B x (n - 1) + 1\npartial def forward (A : Type) (n : Nat) : Nat :=\n  if n == 0 then consume (A → Nat → A) (keep A) 1 else forward A (n - 1) + 1\n";
    let same = "#eval forward Nat 2 + forward Nat 3";
    let different = "#eval forward Nat 2 + forward String 3";
    oracle(&format!("{source}{same}\n{different}\n"), "9\n9\n");
    let engine = checked(&seed(), source);
    let same = evaluate(&engine, same, "9");
    let different = evaluate(&engine, different, "9");
    let functions = |artifact: &[u8]| {
        fln_comp::flbc::decode_canonical(artifact, Default::default())
            .unwrap()
            .functions()
            .len()
    };
    assert!(
        functions(&different) > functions(&same),
        "a represented String callback must not reuse the Nat specialization",
    );
}

#[test]
fn erased_type_analysis_keeps_resource_stops_atomic_and_retries_deterministically() {
    let source = format!("{PAIR}{}", typed("(Pair A A)"));
    let engine = checked(&seed(), &source);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    let mut error = engine
        .execute_source_definitions(&[b"#eval typedLeft Nat 4"], &options, bounded)
        .unwrap_err();
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert!(matches!(
        error,
        EngineExecutionError::Ingress(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: 1,
            ..
        }),
    ));
    assert_eq!(engine.logical_root(&options), root);
    let first = evaluate(&engine, "#eval typedLeft Nat 4", "2");
    let second = evaluate(&engine, "#eval typedLeft Nat 4", "2");
    assert_eq!(first, second);
    assert_eq!(engine.logical_root(&options), root);
}
