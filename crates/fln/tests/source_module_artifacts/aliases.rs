//! Native artifacts carry the pin's actual alias extension, not a private shim.
#![cfg(test)]
#![forbid(unsafe_code)]
use super::*;

const LIB: &str = "prelude\nnamespace Original\ninductive Token where | mk\ndef identity (x : Token) : Token := x\nend Original\nexport Original (Token identity)";
const BRIDGE: &str = "prelude\nimport Lib\nnamespace Facade.Inner\nexport Original (Token identity)\nend Facade.Inner";
const MAIN: &str = "prelude\nimport Bridge\ndef rootUse (x : Token) : Token := identity x\nopen Facade.Inner\ndef facadeUse (x : Facade.Inner.Token) : Facade.Inner.Token := Facade.Inner.identity x";

#[test]
fn exported_aliases_survive_an_alias_only_module_and_a_fresh_physical_import() {
    let built = compiled(&[("Main", MAIN), ("Bridge", BRIDGE), ("Lib", LIB)]);
    let counts: Vec<_> = built
        .artifacts
        .iter()
        .map(|a| (a.name.clone(), metadata(&a.bytes).aliases.len()))
        .collect();
    assert_eq!(
        counts,
        vec![(name("Lib"), 2), (name("Bridge"), 2), (name("Main"), 0)]
    );
    assert_eq!(built.artifacts[1].report.constants, 0);
    let receipt = imported(&built);
    receipt
        .engine
        .check_source_files(
            &[b"def later (x : Facade.Inner.Token) : Token := Facade.Inner.identity x"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(receipt.modules.iter().map(|m| m.aliases).sum::<usize>(), 4);
}

#[test]
fn empty_namespaces_and_dotted_aliases_keep_distinct_physical_import_semantics() {
    let lib = "prelude\nnamespace Original.Inner\ninductive Token where | mk\nend Original.Inner\n\
        export Original (Inner.Token)\nnamespace Empty.Nested\nend Empty.Nested";
    let bridge = "prelude\nimport Lib\nnamespace View\nexport Original.Inner (Token)\nend View";
    let built = compiled(&[
        ("Main", "prelude\nimport Bridge"),
        ("Bridge", bridge),
        ("Lib", lib),
    ]);
    let lib_metadata = metadata(&built.artifacts[0].bytes);
    assert!(lib_metadata.namespaces.contains(&name("Empty.Nested")));
    assert!(lib_metadata.namespaces.contains(&name("Original.Inner")));
    assert!(!lib_metadata.namespaces.contains(&name("Inner")));
    assert_eq!(built.artifacts[1].report.constants, 0);
    assert_eq!(
        metadata(&built.artifacts[1].bytes).namespaces,
        vec![name("View")]
    );
    let engine = imported(&built).engine;
    let root = engine.logical_root(&KVMap::new());
    let good = "open Empty.Nested\nopen View (Token)\n\
        theorem same (P : Inner.Token -> Prop) (x : Token) (h : P x) : P x := h";
    engine
        .check_source_files(&[good.as_bytes()], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    reference_import(&built, &format!("prelude\nimport Main\n{good}"), true);
    for bad in ["open Inner", "export Inner (Token)", "open Empty.Missing"] {
        assert!(
            engine
                .check_source_files(&[bad.as_bytes()], &KVMap::new(), limits().source)
                .is_err(),
            "{bad}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
        reference_import(&built, &format!("prelude\nimport Main\n{bad}"), false);
    }
}

fn pinned_lean() -> Option<std::path::PathBuf> {
    use std::path::PathBuf;
    let row = include_str!("../../../../SUITE.lock")
        .lines()
        .find(|row| row.starts_with("reference leanprover/lean4 "))
        .unwrap();
    let field = |key: &str| {
        row.split_whitespace()
            .find_map(|word| word.strip_prefix(key))
            .unwrap()
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", field("tag=")))
                    .join("lib/lean")
            })
        });
    let executable = lib
        .and_then(|lib| Some(lib.parent()?.parent()?.join("bin/lean")))
        .filter(|p| p.is_file());
    let Some(executable) = executable else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required"
        );
        eprintln!("SKIP: pinned Reference absent");
        return None;
    };
    let version = std::process::Command::new(&executable)
        .arg("--version")
        .output()
        .unwrap();
    let text = String::from_utf8(version.stdout).unwrap();
    assert!(
        version.status.success()
            && text.contains(field("tag=").trim_start_matches('v'))
            && text.contains(field("commit=")),
        "{text}"
    );
    Some(executable)
}

pub(super) fn reference_import(built: &SourceModuleBuild, source: &str, accepted: bool) {
    reference_import_stdout(built, source, accepted, None);
}

pub(super) fn reference_import_stdout(
    built: &SourceModuleBuild,
    source: &str,
    accepted: bool,
    stdout: Option<&str>,
) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let Some(pin) = pinned_lean() else {
        return;
    };
    let directory = std::env::temp_dir().join(format!(
        "fln-alias-artifacts-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&directory).unwrap();
    for artifact in &built.artifacts {
        let path = artifact
            .name
            .to_display_string()
            .split('.')
            .fold(directory.clone(), |p, s| p.join(s))
            .with_extension("olean");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, &artifact.bytes).unwrap();
        assert!(
            !path.with_extension("lean").exists(),
            "the oracle must consume our artifact, not rebuild its source"
        );
    }
    let probe = directory.join("Probe.lean");
    std::fs::write(&probe, source).unwrap();
    let mut child = std::process::Command::new(pin)
        .arg(&probe)
        .current_dir(&directory)
        .env("LEAN_PATH", &directory)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    // A lost macro-inline tag can turn an untaken argument into an infinite
    // computation. Bound the oracle rather than hanging the regression suite.
    let started = std::time::Instant::now();
    while child.try_wait().unwrap().is_none() {
        if started.elapsed() > std::time::Duration::from_secs(30) {
            child.kill().unwrap();
            let output = child.wait_with_output().unwrap();
            panic!(
                "pinned artifact consumer timed out: {source}\n{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        std::thread::sleep(std::time::Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.success(),
        accepted,
        "{source}\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if let Some(expected) = stdout {
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            expected,
            "{source}"
        );
        assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    }
}

#[test]
fn the_pinned_compiler_reads_native_alias_artifacts_and_alias_only_namespaces() {
    let built = compiled(&[("Main", MAIN), ("Bridge", BRIDGE), ("Lib", LIB)]);
    // This facet emits logical .olean data, not the separate compiled IR.
    // The oracle must resolve aliases and kernel-check their definitional
    // behavior; compiling an executable consumer would test the absent IR facet.
    reference_import(
        &built,
        "prelude\nimport Main\nopen Facade.Inner\ntheorem importedUse (P : Token -> Prop) (x : Token) (h : P x) : P (identity x) := h\ntheorem qualifiedUse (P : Token -> Prop) (x : Facade.Inner.Token) (h : P x) : P (Facade.Inner.identity x) := h",
        true,
    );
    reference_import(
        &built,
        "prelude\nimport Main\ndef missing := Facade.Inner.notExported",
        false,
    );
}

#[test]
fn reexports_of_aliases_and_section_exports_survive_diamond_imports() {
    let left = "prelude\nimport Lib\nnamespace Left\nexport Original (Token identity)\nend Left";
    let right = "prelude\nimport Lib\nnamespace Right\nexport Original (Token identity)\nend Right";
    let main = "prelude\nimport Left\nimport Right\nsection\nnamespace Public\nexport Left (Token identity)\nend Public\nend\nexport Original (Token identity)";
    let built = compiled(&[
        ("Main", main),
        ("Right", right),
        ("Lib", LIB),
        ("Left", left),
    ]);
    let aliases = metadata(&built.artifacts.last().unwrap().bytes).aliases;
    assert_eq!(
        aliases.len(),
        2,
        "an imported pair exported again adds no duplicate journal row"
    );
    assert_eq!(aliases[0].alias, name("Public.Token"));
    assert_eq!(aliases[0].declaration, name("Original.Token"));
    let engine = imported(&built).engine;
    let probe = "open Public (Token identity)\ntheorem consume (P : Token -> Prop) (x : Token) (h : P x) : P (identity x) := h";
    engine
        .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    reference_import(&built, &format!("prelude\nimport Main\n{probe}"), true);
}

#[test]
fn warm_alias_artifacts_obey_aggregate_writer_limits_and_retry_exactly() {
    let names = [name("Main"), name("Bridge"), name("Lib")];
    let inputs: Vec<_> = names
        .iter()
        .zip([MAIN, BRIDGE, LIB])
        .map(|(name, source)| SourceModuleInput {
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
    let warm = session
        .compile(&inputs, &names[0], exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (3, 0));
    for (a, b) in cold.artifacts.iter().zip(&warm.artifacts) {
        assert_eq!(a.bytes, b.bytes);
    }
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
    let recovered = session
        .compile(&inputs, &names[0], exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 3);
    for (a, b) in cold.artifacts.iter().zip(&recovered.artifacts) {
        assert_eq!(a.bytes, b.bytes);
    }
    imported(&recovered);
}

#[test]
fn same_alias_with_distinct_targets_retains_ambiguity_after_import() {
    let source = "prelude\ninductive Red where | mk\nnamespace First\ndef choose (x : Red) : Red := x\nend First\nnamespace Second\ndef choose (x : Red) : Red := x\nend Second\nexport First (choose)\nexport Second (choose)";
    let built = compiled(&[("Main", source)]);
    let aliases = metadata(&built.artifacts[0].bytes).aliases;
    assert_eq!(
        aliases
            .iter()
            .map(|a| a.declaration.clone())
            .collect::<Vec<_>>(),
        [name("First.choose"), name("Second.choose")]
    );
    let probe = "theorem useRed (P : Red -> Prop) (x : Red) (h : P x) : P (choose x) := h";
    let receipt = imported(&built);
    let error = receipt
        .engine
        .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
        .unwrap_err();
    assert!(error.to_string().contains("Ambiguous term"), "{error:?}");
    reference_import(&built, &format!("prelude\nimport Main\n{probe}"), false);
    let explicit =
        "theorem explicit (P : Red -> Prop) (x : Red) (h : P x) : P (Second.choose x) := h";
    receipt
        .engine
        .check_source_files(&[explicit.as_bytes()], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    reference_import(&built, &format!("prelude\nimport Main\n{explicit}"), true);
}

#[test]
fn invalid_export_targets_and_later_bad_modules_return_no_artifacts() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    for bad in [
        "prelude\nimport Lib\nexport Original (missing)",
        "prelude\nimport Lib\nexport Original (Token identity)\ndef broken : Type := missing",
    ] {
        let error = build(
            &initial,
            &[("Main", bad), ("Lib", LIB)],
            OleanWriteBudget::default(),
        )
        .unwrap_err();
        assert!(
            matches!(
                error,
                SourceModuleBuildError::Check(SourceModuleCheckError::Source { .. })
            ),
            "{error:?}"
        );
        assert!(error.to_string().contains("missing"), "{error:?}");
        assert_eq!(initial.logical_root(&KVMap::new()), root);
    }
    let retry = build(
        &initial,
        &[("Main", MAIN), ("Bridge", BRIDGE), ("Lib", LIB)],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(retry.artifacts.len(), 3);
}
