//! Macro inlining is observable evaluation semantics across a compiled boundary.
#![forbid(unsafe_code)]
use super::*;
use fln_olean::source_extensions::{InlineEntry, InlineKind};

const BASE: &str = "prelude\n@[macro_inline] def keepFirst.{u} {A : Sort u} (x y : A) : A := x";
const MAIN: &str = concat!(
    "prelude\nimport Left\nimport Right\n",
    "@[noinline, macro_inline] def lastLazy.{u} {A : Sort u} (x y : A) : A := x\n",
    "@[macro_inline, noinline] def lastStrict.{u} {A : Sort u} (x y : A) : A := x\n",
);

fn files() -> [(&'static str, &'static str); 4] {
    [
        ("Main", MAIN),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", BASE),
    ]
}

#[test]
fn macro_inline_exports_only_owned_final_attributes_across_a_diamond() {
    let built = compiled(&files());
    let rows: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| (artifact.name.clone(), metadata(&artifact.bytes).inline))
        .collect();
    let tagged = |declaration| {
        vec![InlineEntry {
            declaration: name(declaration),
            kind: InlineKind::MacroInline,
        }]
    };
    assert_eq!(
        rows,
        [
            (name("Base"), tagged("keepFirst")),
            (name("Left"), vec![]),
            (name("Right"), vec![]),
            (name("Main"), tagged("lastLazy")),
        ]
    );
    let receipt = imported(&built);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|module| module.inline)
            .sum::<usize>(),
        2
    );
    let expected = std::collections::BTreeSet::from([name("keepFirst"), name("lastLazy")]);
    assert_eq!(
        fln_elab::macro_inline::read(receipt.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(
        fln_elab::macro_inline::read(built.checked.checked.engine.environment()).unwrap(),
        expected
    );
}

#[test]
fn macro_inline_artifacts_reuse_checked_cache_and_obey_aggregate_limits() {
    let names: Vec<_> = files().iter().map(|(module, _)| name(module)).collect();
    let sources = files();
    let inputs: Vec<_> = names
        .iter()
        .zip(&sources)
        .map(|(name, (_, source))| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let cold = session
        .compile(&inputs, &names[0], OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let exact = OleanWriteBudget {
        max_bytes: cold.artifacts.iter().map(|a| a.report.file_bytes).sum(),
        max_objects: cold
            .artifacts
            .iter()
            .map(|a| a.report.runtime_objects)
            .sum(),
    };
    for budget in [
        OleanWriteBudget {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
        OleanWriteBudget {
            max_objects: exact.max_objects - 1,
            ..exact
        },
    ] {
        let error = session.compile(&inputs, &names[0], budget).unwrap_err();
        assert_eq!(error.disposition(), ("resource", false, 3));
    }
    let warm = session
        .compile(&inputs, &names[0], exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (4, 0));
    for (a, b) in cold.artifacts.iter().zip(&warm.artifacts) {
        assert_eq!(a.bytes, b.bytes);
    }
    assert_eq!(
        fln_elab::macro_inline::read(imported(&warm).engine.environment()).unwrap(),
        std::collections::BTreeSet::from([name("keepFirst"), name("lastLazy")])
    );
}

#[test]
fn fresh_native_and_pinned_consumers_do_not_evaluate_discarded_arguments() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                std::path::PathBuf::from(home)
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned Prelude and runtime oracle are required"
        );
        eprintln!("SKIP: pinned v4.32.0 lib/lean is unavailable");
        return;
    };
    const STACK: usize = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let built = compiled(&files());
            let path = lib.join("Init/Prelude.olean");
            let exported = std::fs::read(&path).unwrap();
            let server = std::fs::read(path.with_extension("olean.server")).unwrap();
            let private = std::fs::read(path.with_extension("olean.private")).unwrap();
            let prelude = name("Init.Prelude");
            let mut inputs = vec![OleanModuleInput {
                name: &prelude,
                artifact: &exported,
                server_artifact: Some(&server),
                private_artifact: Some(&private),
            }];
            inputs.extend(built.artifacts.iter().map(|artifact| OleanModuleInput {
                name: &artifact.name,
                artifact: &artifact.bytes,
                server_artifact: None,
                private_artifact: None,
            }));
            let engine = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &inputs,
                    &[prelude.clone(), name("Main")],
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        STACK,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
            let source = concat!(
                "partial def spin (n : Nat) : Nat := spin n\n",
                "#eval keepFirst 7 (spin 0)\n",
                "#eval lastLazy 11 (spin 0)\n",
            );
            let mut bounded = fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
            bounded.vm.max_steps = 1000;
            let root = engine.logical_root(&KVMap::new());
            let run = engine
                .execute_source_commands_with_checks(source.as_bytes(), &KVMap::new(), bounded)
                .unwrap()
                .into_complete()
                .expect("discarded divergent arguments must not consume runtime fuel");
            let values: Vec<_> = run
                .batch
                .executions
                .iter()
                .map(|execution| fln::closed_vm_value(&execution.exit).unwrap())
                .collect();
            assert_eq!(
                values,
                [
                    Some(fln::ClosedVmValue::Scalar(7)),
                    Some(fln::ClosedVmValue::Scalar(11))
                ]
            );
            // The opposite final attribute retains ordinary strict evaluation.
            // This control ensures the compiler has not discarded all unused
            // arguments, nor substituted the partial definition's logical body.
            let strict = concat!(
                "partial def spin (n : Nat) : Nat := spin n\n",
                "#eval lastStrict 13 (spin 0)\n",
            );
            assert!(matches!(
                engine
                    .execute_source_commands_with_checks(strict.as_bytes(), &KVMap::new(), bounded)
                    .unwrap(),
                Outcome::Inconclusive(_)
            ));
            assert_eq!(engine.logical_root(&KVMap::new()), root);
            // The reference sees only our physical .olean files. Macro inlining
            // eliminates these calls before code generation, so the separate
            // compiled IR facet is unnecessary for this consumer.
            aliases::reference_import_stdout(
                &built,
                &format!("import Main\n{source}"),
                true,
                Some("7\n11\n"),
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
