//! General imported `autoParam` behavior over the actual pinned Syntax and
//! tactic declarations. Raw artifact installation is only a fixture: every
//! quotation, function, and theorem below passes normal source admission.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionError, Environment, KVMap,
    Name, OleanDecodeLimits, Outcome, SourceCheckError, SourceCheckLimits,
};
use fln_core::outcome::InconclusiveCause;
use fln_elab::NatDefinitionElabError;
use fln_elab::source::{SourceInferenceError, TacticError};
use std::path::PathBuf;
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;

// Explicit annotations exercise imported autoParam data without depending on
// the separate source-binder sugar `(value := by ...)`. These are ordinary
// safe Syntax definitions, not special declarations recognized by the engine.
const QUOTATIONS: &str = r#"
def autoNode (kind : Lean.Name) (children : List Lean.Syntax) : Lean.Syntax :=
  Lean.Syntax.node Lean.SourceInfo.none kind (Array.mk children)
def autoSequence (step : Lean.Syntax) : Lean.Syntax :=
  autoNode `Lean.Parser.Tactic.tacticSeq
    [autoNode `Lean.Parser.Tactic.tacticSeq1Indented [autoNode `null [step]]]
def autoAssumption : Lean.Syntax :=
  autoSequence (autoNode `Lean.Parser.Tactic.assumption [Lean.mkAtom "assumption"])
def autoIdentifier (raw : String) (value : Lean.Name)
    (resolved : List Lean.Syntax.Preresolved) : Lean.Syntax :=
  Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring raw) value resolved
def autoSlice (raw : String) (start stop : Nat) (value : Lean.Name)
    (resolved : List Lean.Syntax.Preresolved) : Lean.Syntax :=
  Lean.Syntax.ident Lean.SourceInfo.none
    (Substring.Raw.mk raw (String.Pos.Raw.mk start) (String.Pos.Raw.mk stop)) value resolved
def autoExact (value : Lean.Name) : Lean.Syntax :=
  autoSequence (autoNode `Lean.Parser.Tactic.exact
    [Lean.mkAtom "exact", autoIdentifier "" value []])
def inferredAuto {α : Type} (value : autoParam α autoAssumption) : α := value
"#;

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn check(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("complete source admission")
        .engine
}

fn fixture(test: impl FnOnce(&Engine) + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            static FIXTURE: OnceLock<Option<Engine>> = OnceLock::new();
            if let Some(engine) = FIXTURE.get_or_init(|| {
                let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
                    assert!(
                        std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                        "the actual pinned Reference library is required"
                    );
                    eprintln!("SKIP: pinned Reference lib/lean is absent");
                    return None;
                };
                let mut environment = Environment::new();
                for module in ["Init/Prelude", "Init/Core", "Init/Tactics"] {
                    let path = library.join(module).with_extension("olean");
                    let public = std::fs::read(&path).unwrap();
                    let server = std::fs::read(path.with_extension("olean.server")).unwrap();
                    let private = std::fs::read(path.with_extension("olean.private")).unwrap();
                    let decoded = fln::decode_olean_module_artifacts(
                        &public,
                        &server,
                        &private,
                        OleanDecodeLimits::new(STACK),
                    )
                    .unwrap();
                    for info in decoded.constants {
                        if !environment.contains(info.name()) {
                            environment = environment.add_decl(info).unwrap();
                        }
                    }
                }
                Some(check(&Engine::from_environment(environment), QUOTATIONS))
            }) {
                test(engine);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

fn theorem(engine: &Engine, label: &str) {
    assert!(
        matches!(
            engine.environment().find(&name(label)),
            Some(ConstantInfo::Thm(_))
        ),
        "missing checked theorem {label}"
    );
}

fn error(engine: &Engine, source: &str) -> NatDefinitionElabError {
    let SourceCheckError::Command { error, .. } = engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_err()
    else {
        panic!("expected a source command elaboration failure");
    };
    let mut error = *error;
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    let EngineExecutionError::Frontend(fln::NatDefinitionFrontendError::Elaborate(error)) = error
    else {
        panic!("expected a source elaboration error, got {error:?}");
    };
    error
}

#[test]
fn omitted_tactics_wait_for_result_types_and_later_named_arguments() {
    fixture(|engine| {
        // `assumption` sees Bool last. Running the tactic before α is fixed
        // would choose the wrong local; both applications must choose Nat.
        let engine = check(
            engine,
            r#"
def fromExpected (wanted : Nat) (distractor : Bool) : Nat := inferredAuto
def laterAuto {α : Type} (value : autoParam α autoAssumption) (witness : α) : α := value
def fromLater (wanted : Nat) (distractor : Bool) : Nat := laterAuto (witness := wanted)
theorem expected_value (wanted : Nat) (distractor : Bool) :
    fromExpected wanted distractor = wanted := rfl
theorem later_value (wanted : Nat) (distractor : Bool) :
    fromLater wanted distractor = wanted := rfl
"#,
        );
        theorem(&engine, "expected_value");
        theorem(&engine, "later_value");
    });
}

#[test]
fn defaults_keep_their_original_scope_and_explicit_applications_stay_partial() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
def rawAuto : Nat → Nat := @inferredAuto Nat
def explicitAuto : Nat := inferredAuto (value := Nat.succ Nat.zero)
def beforeEta (value : autoParam Nat autoAssumption) (later : Nat)
    (tail : optParam Nat Nat.zero) : Nat := value
def capturesOuter (wanted : Nat) : Nat → Nat := beforeEta
theorem raw_value (value : Nat) : rawAuto value = value := rfl
theorem explicit_value : explicitAuto = Nat.succ Nat.zero := rfl
theorem captured_value (wanted later : Nat) : capturesOuter wanted later = wanted := rfl
"#,
        );
        for label in ["raw_value", "explicit_value", "captured_value"] {
            theorem(&engine, label);
        }
        // The trailing optParam forces an eta binder after the autoParam.
        // It must not become an assumption available to the earlier tactic.
        assert!(matches!(
            error(&engine, "def forbiddenEta : Nat → Nat := beforeEta\n"),
            NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                TacticError::NoMatchingAssumption
            ))
        ));
        assert!(!engine.environment().contains(&name("forbiddenEta")));
    });
}

#[test]
fn quoted_identifiers_preserve_unicode_and_preresolved_global_names() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
def AutoParamTests.anchor : Nat := Nat.succ Nat.zero
def rootedQuote : Lean.Syntax :=
  autoSequence (autoNode `Lean.Parser.Tactic.exact
    [Lean.mkAtom "exact", autoIdentifier "π alias" `unboundAlias
      [Lean.Syntax.Preresolved.decl `AutoParamTests.anchor []]])
def rootedAuto (value : autoParam Nat rootedQuote) : Nat := value
def rootedCaller (anchor : Nat) : Nat := rootedAuto
theorem rooted_value (anchor : Nat) : rootedCaller anchor = Nat.succ Nat.zero := rfl
def slicedQuote : Lean.Syntax :=
  autoSequence (autoNode `Lean.Parser.Tactic.exact
    [Lean.mkAtom "exact", autoSlice "aβz" (Nat.succ Nat.zero)
      (Nat.succ (Nat.succ (Nat.succ Nat.zero))) `sliceAlias
      [Lean.Syntax.Preresolved.decl `AutoParamTests.anchor []]])
def slicedAuto (value : autoParam Nat slicedQuote) : Nat := value
def slicedCaller (anchor : Nat) : Nat := slicedAuto
theorem sliced_value (anchor : Nat) : slicedCaller anchor = Nat.succ Nat.zero := rfl
"#,
        );
        theorem(&engine, "rooted_value");
        theorem(&engine, "sliced_value");
    });
}

#[test]
fn quoted_identifier_ranges_reject_split_utf8_and_out_of_bounds_slices() {
    fixture(|engine| {
        for stop in [
            "Nat.succ (Nat.succ Nat.zero)",
            "Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))",
        ] {
            // The backing has four bytes. Stop 2 splits β; stop 5 is outside
            // the backing. Neither may be replaced with a valid full range.
            let engine = check(
                engine,
                &format!(
                    r#"def badSliceQuote : Lean.Syntax :=
  autoSequence (autoNode `Lean.Parser.Tactic.exact
    [Lean.mkAtom "exact", autoSlice "aβz" (Nat.succ Nat.zero)
      ({stop}) `Nat.zero []])
def badSliceDefault (value : autoParam Nat badSliceQuote) : Nat := value
"#
                ),
            );
            let rejected = error(&engine, "def badSliceResult : Nat := badSliceDefault\n");
            assert!(
                matches!(
                    rejected,
                    NatDefinitionElabError::UnexpectedSyntax {
                        expected: "closed quoted Lean.Syntax data for an autoParam tactic"
                    }
                ),
                "{rejected:?}"
            );
            assert!(!engine.environment().contains(&name("badSliceResult")));
        }
    });
}

#[test]
fn runtime_replacements_cannot_be_decoded_as_logical_quotations() {
    fixture(|engine| {
        let engine = check(
            engine,
            "def alternativeQuote : Lean.Syntax := autoAssumption\n",
        );
        let external = fln_elab::externs::register(
            engine.environment(),
            &name("autoAssumption"),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: name("all"),
                symbol: String::from("foreign_auto_parameter_quote"),
            }],
        )
        .unwrap();
        let replaced = fln_elab::implemented_by::register(
            engine.environment(),
            &name("autoAssumption"),
            &name("alternativeQuote"),
        )
        .unwrap();
        for environment in [external, replaced] {
            let engine = Engine::from_environment(environment);
            let rejected = error(
                &engine,
                "def foreignQuoteResult (witness : Nat) : Nat := inferredAuto\n",
            );
            assert!(
                matches!(
                    rejected,
                    NatDefinitionElabError::UnexpectedSyntax {
                        expected: "closed quoted Lean.Syntax data for an autoParam tactic"
                    }
                ),
                "{rejected:?}"
            );
            assert!(!engine.environment().contains(&name("foreignQuoteResult")));
        }
    });
}

#[test]
fn failed_malformed_nonconstant_and_unsafe_defaults_never_publish_a_value() {
    fixture(|engine| {
        assert!(matches!(
            error(engine, "def noWitness : Nat := inferredAuto\n"),
            NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                TacticError::NoMatchingAssumption
            ))
        ));
        let nonconstant = check(
            engine,
            "def nonconstantDefault (value : autoParam Nat (id autoAssumption)) : Nat := value\n",
        );
        let rejected = error(
            &nonconstant,
            "def nonconstantResult : Nat := nonconstantDefault\n",
        );
        assert!(
            matches!(
                rejected,
                NatDefinitionElabError::UnexpectedSyntax {
                    expected: "closed quoted Lean.Syntax data for an autoParam tactic"
                }
            ),
            "{rejected:?}"
        );
        let malformed = check(
            engine,
            "def missingQuote : Lean.Syntax := Lean.Syntax.missing\n\
             def malformedDefault (value : autoParam Nat missingQuote) : Nat := value\n",
        );
        let rejected = error(
            &malformed,
            "def malformedResult : Nat := malformedDefault\n",
        );
        assert!(
            matches!(
                rejected,
                NatDefinitionElabError::UnexpectedSyntax {
                    expected: "tactic sequence"
                }
            ),
            "{rejected:?}"
        );
        let unsafe_quote = check(
            engine,
            "unsafe def unsafeQuote : Lean.Syntax := autoAssumption\n\
             unsafe def unsafeDefault (value : autoParam Nat unsafeQuote) : Nat := value\n",
        );
        let rejected = error(
            &unsafe_quote,
            "unsafe def unsafeResult : Nat := unsafeDefault\n",
        );
        assert!(
            matches!(
                rejected,
                NatDefinitionElabError::UnexpectedSyntax {
                    expected: "closed quoted Lean.Syntax data for an autoParam tactic"
                }
            ),
            "{rejected:?}"
        );
        for label in [
            "noWitness",
            "nonconstantResult",
            "malformedResult",
            "unsafeResult",
        ] {
            assert!(!engine.environment().contains(&name(label)));
        }
        theorem(
            &check(engine, "theorem recovery (x : Nat) : x = x := rfl\n"),
            "recovery",
        );
    });
}

#[test]
fn recursive_default_elaboration_reports_a_typed_resource_stop() {
    fixture(|engine| {
        let mut source = String::from("def autoEnd : Nat := Nat.zero\n");
        for index in 0..10 {
            let target = if index == 0 {
                String::from("autoEnd")
            } else {
                format!("autoStep{}", index - 1)
            };
            source.push_str(&format!(
                "def quoteStep{index} : Lean.Syntax := autoExact `{target}\n\
                 def autoStep{index} (value : autoParam Nat quoteStep{index}) : Nat := value\n"
            ));
        }
        let engine = check(engine, &source);
        let outcome = engine
            .check_source_files(
                &[b"def tooDeep : Nat := autoStep9\n"],
                &KVMap::new(),
                limits(),
            )
            .expect("resource exhaustion is not a source rejection");
        let Outcome::Inconclusive(stopped) = outcome else {
            panic!("expected a typed resource stop");
        };
        let InconclusiveCause::ResourceExhausted { usage } = stopped.cause else {
            panic!("expected resource exhaustion, got {stopped:?}");
        };
        assert!(matches!(
            usage.reason,
            fln_core::diag::ResourceReason::RecursionDepth { .. }
        ));
        assert!(usage.is_genuine_exhaustion());
        assert!(!engine.environment().contains(&name("tooDeep")));
    });
}
