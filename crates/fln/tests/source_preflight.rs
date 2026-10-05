//! `preflight_source_files` refuses exactly what the checked source path refuses
//! at parse time, with the same error, and needs no environment to do it (bead
//! `fln-parse-before-imports-j8p6`). Front doors run it before admitting an
//! import closure, so a malformed file is refused before any `.olean` is read.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::{SourceCheckError, preflight_source_files, preflight_source_module};
use fln::{
    Budget, DefinitionFrontendError, Engine, EngineAdmissionLimits, EngineExecutionError, KVMap,
    Name, Outcome, SourceCheckLimits, SourceModuleInput,
};

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(256 * 1024 * 1024))
}

fn engine() -> Engine {
    match Engine::with_coercion_seed(admission()).expect("seed engine") {
        Outcome::Complete(engine) => engine,
        other => panic!("seed engine did not complete: {other:?}"),
    }
}

/// Run the checked path on its own worker so deep elaboration has the stack the
/// CLI gives it.
fn checked(engine: &Engine, source: &[u8]) -> Result<(), SourceCheckError> {
    let engine = engine.clone();
    let source = source.to_vec();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            engine
                .check_source_files(
                    &[&source],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .map(|_| ())
        })
        .expect("spawn checker")
        .join()
        .expect("checker thread")
}

fn is_parse_refusal(error: &SourceCheckError) -> bool {
    matches!(
        error,
        SourceCheckError::Command { error, .. }
            if matches!(**error, EngineExecutionError::Frontend(DefinitionFrontendError::Parse(_)))
    )
}

/// Inputs no import could make parseable, each refused at a different stage:
/// the lexer, the command partition, a scope command, a declaration command.
const MALFORMED: &[&str] = &[
    "this is not lean @@@ garbage\n",
    // `⟨hp, hq⟩` itself now parses (Term.anonymousCtor); the doubled separator is refused, as
    // the pin refuses it ("unexpected token ','; expected '⟩'").
    "theorem t (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp,, hq⟩\n",
    "def a : Nat := 1\ndef b : Nat := (1 +\n",
    "def a : Nat := 1\nnamespace\n",
    "def a : Nat := 1\ntheorem t : a = 1 :=\n",
];

#[test]
fn every_preflight_refusal_is_the_checked_refusal_with_the_same_error() {
    let engine = engine();
    for source in MALFORMED {
        let preflight = preflight_source_files(&[source.as_bytes()])
            .expect_err(&format!("preflight admitted malformed source {source:?}"));
        assert!(is_parse_refusal(&preflight), "{source:?}: {preflight}");
        let checked = checked(&engine, source.as_bytes()).expect_err(&format!(
            "checked path admitted malformed source {source:?}"
        ));
        assert_eq!(preflight.to_string(), checked.to_string(), "{source:?}");
        assert_eq!(preflight.disposition(), checked.disposition(), "{source:?}");
    }
}

/// Every header-free example in the repository: whenever the checked path
/// refuses one at parse time, the preflight refuses it identically, and the
/// preflight never refuses one the checked path parses.
#[test]
fn the_preflight_agrees_with_the_checked_path_over_the_examples_corpus() {
    let examples = fln_core::checked_manifest_dir!().join("../../examples");
    let mut paths: Vec<_> = std::fs::read_dir(&examples)
        .expect("examples directory")
        .map(|entry| entry.expect("example entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "lean"))
        .collect();
    paths.sort();
    let engine = engine();
    let (mut corpus, mut parse_refusals, mut preflight_passes) = (0, 0, 0);
    for path in &paths {
        let source = std::fs::read(path).expect("read example");
        let text = String::from_utf8_lossy(&source);
        if text
            .lines()
            .any(|line| line.starts_with("import ") || line.trim() == "prelude")
        {
            continue;
        }
        corpus += 1;
        let preflight = preflight_source_files(&[&source]);
        let checked = checked(&engine, &source);
        match (&preflight, &checked) {
            (Err(early), Err(late)) => {
                if is_parse_refusal(late) {
                    parse_refusals += 1;
                    assert_eq!(early.to_string(), late.to_string(), "{}", path.display());
                }
            }
            (Err(early), Ok(())) => {
                panic!(
                    "{}: preflight refused source the checked path admits: {early}",
                    path.display()
                )
            }
            (Ok(()), Err(late)) => {
                assert!(
                    !is_parse_refusal(late),
                    "{}: the checked path refused at parse time but the preflight admitted: {late}",
                    path.display()
                );
                preflight_passes += 1;
            }
            (Ok(()), Ok(())) => preflight_passes += 1,
        }
    }
    eprintln!(
        "preflight corpus: {corpus} header-free examples, {parse_refusals} parse refusals, {preflight_passes} admitted by the preflight"
    );
    assert!(
        corpus >= 50,
        "examples corpus shrank to {corpus}: a broken scan, not a pass"
    );
    assert!(
        parse_refusals > 0 && preflight_passes > 0,
        "both directions must be exercised"
    );
}

#[test]
fn a_module_preflight_reports_the_module_checker_error_and_whole_module_offsets() {
    let name = Name::from_components(["Garbage"]);
    let source = b"prelude\ndef a : Nat := 1\nthis is not lean @@@\n";
    let preflight = preflight_source_module(&name, source).expect_err("garbage body");
    let engine = engine();
    let checked = engine
        .check_source_modules(
            &[SourceModuleInput {
                name: &name,
                source,
            }],
            &name,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(admission())),
        )
        .expect_err("the module checker refuses the same body");
    assert_eq!(preflight.to_string(), checked.to_string());
    assert_eq!(preflight.disposition(), checked.disposition());
    let header = b"prelude\n".len();
    let body_offset = match preflight_source_files(&[&source[header..]]) {
        Err(SourceCheckError::Command { offset, .. }) => offset,
        other => panic!("the body alone must be refused at a command: {other:?}"),
    };
    match preflight {
        fln::source_check::modules::SourceModuleCheckError::Source {
            module,
            error: SourceCheckError::Command { offset, .. },
        } => {
            assert_eq!(module, name);
            assert_eq!(
                offset,
                body_offset + header,
                "offsets count the header bytes"
            );
        }
        other => panic!("expected a module source refusal: {other:?}"),
    }

    let header_free_body = b"prelude\ndef a : Nat := 1\n";
    preflight_source_module(&name, header_free_body).expect("a parseable module passes");
    preflight_source_module(&name, b"prelude\n").expect("an empty body passes");
}
