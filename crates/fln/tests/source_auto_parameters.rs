//! Source and imported `autoParam` behavior over the actual pinned Syntax and
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

fn checked_quote(engine: &Engine, label: &str) {
    let Some(ConstantInfo::Defn(quote)) = engine.environment().find(&name(label)) else {
        panic!("missing checked tactic quotation {label}");
    };
    assert_eq!(quote.safety, fln_env::constants::DefinitionSafety::Safe);
    assert_eq!(quote.hints, fln_env::constants::ReducibilityHints::Opaque);
    assert!(quote.base.level_params.is_empty());
    assert_eq!(
        quote.base.type_,
        fln_core::expr::Expr::const_(name("Lean.Syntax"), Vec::new())
    );
    assert!(!quote.value.has_fvar());
    assert!(!quote.value.has_expr_mvar());
    assert!(!quote.value.has_level_mvar());
}

#[test]
fn source_binder_tactics_wait_for_result_and_later_argument_constraints() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
def sourceAuto {α : Type} (value : α := by assumption) : α := value
def sourceImplicit (value : α := by assumption) : α := value
def sourceImplicitCaller (wanted : Nat) : Nat := sourceImplicit
def sourceLater {α : Type} (value : α := by assumption) (witness : α) : α := value
def sourceExpected (wanted : Nat) (_distractor : Bool) : Nat := sourceAuto
def sourceNamed (wanted : Nat) (_distractor : Bool) : Nat :=
  sourceLater (witness := wanted)
theorem source_implicit (wanted : Nat) : sourceImplicitCaller wanted = wanted := rfl
theorem source_expected (wanted : Nat) (distractor : Bool) :
    sourceExpected wanted distractor = wanted := rfl
theorem source_named (wanted : Nat) (distractor : Bool) :
    sourceNamed wanted distractor = wanted := rfl
"#,
        );
        theorem(&engine, "source_expected");
        theorem(&engine, "source_named");
        theorem(&engine, "source_implicit");
        checked_quote(&engine, "sourceImplicit._auto_1");
        assert!(
            !engine
                .environment()
                .contains(&name("sourceImplicit._auto_2"))
        );
        checked_quote(&engine, "sourceAuto._auto_1");
        checked_quote(&engine, "sourceLater._auto_1");
    });
}

#[test]
fn source_grouped_defaults_have_distinct_quotes_and_explicit_calls_stay_partial() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
def sourceGrouped
    (first : Nat := by exact Nat.zero)
    (left right : Nat := by exact Nat.succ Nat.zero) : Nat :=
  Nat.add first (Nat.add left right)
def sourceRaw : Nat → Nat → Nat → Nat := @sourceGrouped
def sourceOverride : Nat := sourceGrouped (right := Nat.zero)
def sourceBeforeEta (value : Nat := by assumption) (later : Nat)
    (tail : Nat := Nat.zero) : Nat := value
def sourceCaptures (wanted : Nat) : Nat → Nat := sourceBeforeEta
theorem source_grouped :
    sourceGrouped = Nat.succ (Nat.succ Nat.zero) := rfl
theorem source_raw :
    sourceRaw Nat.zero Nat.zero Nat.zero = Nat.zero := rfl
theorem source_override : sourceOverride = Nat.succ Nat.zero := rfl
theorem source_capture (wanted later : Nat) :
    sourceCaptures wanted later = wanted := rfl
"#,
        );
        for label in [
            "source_grouped",
            "source_raw",
            "source_override",
            "source_capture",
        ] {
            theorem(&engine, label);
        }
        for label in [
            "sourceGrouped._auto_1",
            "sourceGrouped._auto_3",
            "sourceGrouped._auto_5",
        ] {
            checked_quote(&engine, label);
        }
        assert!(matches!(
            error(
                &engine,
                "def sourceForbiddenEta : Nat → Nat := sourceBeforeEta\n"
            ),
            NatDefinitionElabError::Inference(SourceInferenceError::Tactic(
                TacticError::NoMatchingAssumption
            ))
        ));
    });
}

#[test]
fn source_quotes_preserve_call_site_identifiers_and_rooted_global_names() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
def sourceNamedDefault (value : Nat := by exact «π alias») : Nat := value
def sourceNamedCaller («π alias» : Nat) : Nat := sourceNamedDefault
theorem source_identifier («π alias» : Nat) :
    sourceNamedCaller «π alias» = «π alias» := rfl
namespace SourceAutoScope
def anchor : Nat := Nat.succ Nat.zero
def autoParam : Nat := Nat.zero
def rooted (value : Nat := by exact _root_.SourceAutoScope.anchor) : Nat := value
end SourceAutoScope
def sourceRootedCaller (anchor : Nat) : Nat := SourceAutoScope.rooted
theorem source_rooted (anchor : Nat) :
    sourceRootedCaller anchor = Nat.succ Nat.zero := rfl
"#,
        );
        theorem(&engine, "source_identifier");
        theorem(&engine, "source_rooted");
        checked_quote(&engine, "SourceAutoScope.rooted._auto_1");
    });
}

#[test]
fn source_tactic_failures_do_not_publish_the_owner_or_its_header_quotes() {
    fixture(|engine| {
        // A tactic default is not executed at definition time. It may be
        // overridden, while selecting the false default must fail.
        let engine = check(
            engine,
            r#"
def sourceBadDefault (_proof : Nat.zero = Nat.succ Nat.zero := by rfl) : Nat :=
  Nat.zero
def sourceExplicitProof (proof : Nat.zero = Nat.succ Nat.zero) : Nat :=
  sourceBadDefault proof
theorem source_explicit_proof (proof : Nat.zero = Nat.succ Nat.zero) :
    sourceExplicitProof proof = Nat.zero := rfl
"#,
        );
        checked_quote(&engine, "sourceBadDefault._auto_1");
        theorem(&engine, "source_explicit_proof");
        let root = engine.logical_root(&KVMap::new());
        let rejected = error(&engine, "def sourceFalseUse : Nat := sourceBadDefault\n");
        let refused = match &rejected {
            NatDefinitionElabError::Inference(SourceInferenceError::Tactic(_)) => true,
            NatDefinitionElabError::Inference(SourceInferenceError::ConversionRefused(verdict)) => {
                matches!(
                    verdict.as_ref(),
                    fln_kernel::verdict::Verdict::Rejected {
                        class: fln::RejectClass::NotDefEq,
                        ..
                    }
                )
            }
            _ => false,
        };
        assert!(refused, "{rejected:?}");
        assert!(
            engine
                .check_source_files(
                    &[b"def sourceBadBody (value : Nat := by exact Nat.zero) : Nat := True.intro\n"],
                    &KVMap::new(),
                    limits(),
                )
                .is_err()
        );
        for label in ["sourceFalseUse", "sourceBadBody", "sourceBadBody._auto_1"] {
            assert!(!engine.environment().contains(&name(label)));
        }
        assert_eq!(root, engine.logical_root(&KVMap::new()));
        theorem(
            &check(
                &engine,
                "theorem source_after_failure (n : Nat) : n = n := rfl\n",
            ),
            "source_after_failure",
        );
    });
}

#[test]
fn source_data_and_proof_defaults_execute_through_the_public_vm_path() {
    fixture(|engine| {
        let source = r#"
def sourceChoice (value : Nat := by exact Nat.succ Nat.zero) : Nat := value
def sourceProofChoice (value : Nat) (_proof : value = value := by rfl) : Nat := value
#eval sourceChoice
#eval sourceChoice (value := Nat.succ (Nat.succ Nat.zero))
#eval sourceProofChoice (Nat.succ Nat.zero)
"#;
        let report = engine
            .execute_source_commands_with_checks(
                source.as_bytes(),
                &KVMap::new(),
                fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
            )
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let prefix = report
            .batch
            .source_admissions
            .iter()
            .find(|row| row.command_index == 0)
            .expect("the quotation has a checked declaration predecessor receipt");
        let owner = report
            .batch
            .executions
            .iter()
            .find(|execution| {
                matches!(&execution.declaration, fln::Declaration::Defn(definition)
                    if definition.base.name == name("sourceChoice"))
            })
            .expect("the owning definition was executed through the public path");
        assert_eq!(prefix.admission.admissions.len(), 1);
        checked_quote(&prefix.admission.engine, "sourceChoice._auto_1");
        assert_eq!(
            prefix.admission.base_logical_root,
            engine.logical_root(&KVMap::new())
        );
        assert_eq!(
            prefix.admission.result_logical_root,
            owner.base_logical_root
        );
        assert_eq!(report.batch.source_evaluation_indices.len(), 3);
        for (index, expected) in report.batch.source_evaluation_indices.iter().zip([1, 2, 1]) {
            assert_eq!(
                fln::closed_vm_value(&report.batch.executions[*index].exit).unwrap(),
                Some(fln::ClosedVmValue::Scalar(expected))
            );
        }

        // Execute the identical program with the pin as a differential oracle.
        // Its compiler is never used by FrankenLean's source or VM path.
        use std::io::Write;
        use std::process::{Command, Stdio};
        let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
        let compiler = std::env::var_os("FLN_REFERENCE_BIN")
            .map(PathBuf::from)
            .unwrap_or_else(|| library.parent().unwrap().parent().unwrap().join("bin/lean"));
        let mut child = Command::new(compiler)
            .arg("--stdin")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child
            .stdin
            .take()
            .unwrap()
            .write_all(source.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert!(output.status.success(), "{output:?}");
        assert_eq!(String::from_utf8_lossy(&output.stdout), "1\n2\n1\n");
        assert!(output.stderr.is_empty(), "{output:?}");
    });
}

#[test]
fn public_module_headers_preserve_checked_tactic_quotation_predecessors() {
    fixture(|engine| {
        let module = name("SourceAutoModule");
        let consumer = name("SourceAutoConsumer");
        let inputs = [
            fln::SourceModuleInput {
                name: &module,
                source: b"module\nprelude\n\
                    public def moduleAuto (value : Nat := by exact Nat.succ Nat.zero) : Nat := value\n\
                    public theorem moduleAutoProof (n : Nat) (h : n = n := by rfl) : n = n := h\n\
                    @[expose] public def moduleExposed (value : Nat := by exact Nat.zero) : Nat := value\n",
            },
            fln::SourceModuleInput {
                name: &consumer,
                source: b"module\nprelude\npublic import SourceAutoModule\n\
                    public noncomputable def importedDefault : Nat := moduleAuto\n\
                    public theorem importedDefaultValue : moduleAuto = moduleAuto (value := Nat.succ Nat.zero) := rfl\n\
                    public theorem importedProof (n : Nat) : n = n := moduleAutoProof n\n\
                    public theorem importedExposed : moduleExposed = Nat.zero := rfl\n",
            },
        ];
        let checked = engine
            .check_source_modules(
                &inputs,
                &consumer,
                &KVMap::new(),
                fln::source_check::modules::SourceModuleCheckLimits::new(limits()),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let imported = &checked.checked.engine;
        for label in [
            "moduleAuto._auto_1",
            "moduleAutoProof._auto_1",
            "moduleExposed._auto_1",
        ] {
            checked_quote(imported, label);
        }
        // Modern imports hide ordinary public bodies. The quote must remain
        // full checked data even though its owning API is only a signature.
        for label in ["moduleAuto", "moduleAutoProof"] {
            assert!(matches!(
                imported.environment().find(&name(label)),
                Some(ConstantInfo::Axiom(_))
            ));
        }
        assert!(matches!(
            imported.environment().find(&name("moduleExposed")),
            Some(ConstantInfo::Defn(_))
        ));
        for label in ["importedDefaultValue", "importedProof", "importedExposed"] {
            theorem(imported, label);
        }
    });
}

#[test]
fn source_quotation_data_does_not_bypass_unsafe_constant_checks() {
    fixture(|engine| {
        let engine = check(
            engine,
            r#"
unsafe def sourceUnsafeValue : Nat := Nat.zero
def sourceUnsafeDefault (value : Nat := by exact sourceUnsafeValue) : Nat := value
unsafe def sourceUnsafeCaller : Nat := sourceUnsafeDefault
def sourceSafeOverride : Nat := sourceUnsafeDefault (value := Nat.succ Nat.zero)
theorem source_safe_override : sourceSafeOverride = Nat.succ Nat.zero := rfl
"#,
        );
        checked_quote(&engine, "sourceUnsafeDefault._auto_1");
        theorem(&engine, "source_safe_override");
        let root = engine.logical_root(&KVMap::new());
        assert!(
            engine
                .check_source_files(
                    &[b"def sourceUnsafeLeak : Nat := sourceUnsafeDefault\n"],
                    &KVMap::new(),
                    limits(),
                )
                .is_err()
        );
        assert!(!engine.environment().contains(&name("sourceUnsafeLeak")));
        assert_eq!(root, engine.logical_root(&KVMap::new()));
    });
}
