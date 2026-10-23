//! Explicit product measures use the pin's default lexicographic constructor
//! search and the checked arithmetic prover. Without `termination_by`, GuessLex's
//! search infers the product over Nat parameters.
#![forbid(unsafe_code)]
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Name, SourceCheckLimits};
use fln_core::outcome::{InconclusiveCause, Outcome};

// Independently evaluated by the pin with prelude, Init.WFComputable and
// Init.Omega. Init.Data.Repr serves only the oracle's #eval output.
const PROGRAMS: &[(&str, &str, &str, usize)] = &[
    (
        "lexCountAutomatic",
        r#"def lexCountAutomatic (a b : Nat) : Nat :=
  if hb : 0 < b then lexCountAutomatic a (b - 1) + 1
  else if ha : 0 < a then lexCountAutomatic (a - 1) 6 + 1 else 0
termination_by (a, b)"#,
        "lexCountAutomatic 5 7",
        42,
    ),
    (
        "ackermannAutomatic",
        r#"def ackermannAutomatic (a b : Nat) : Nat := match a with
  | 0 => b + 1
  | x + 1 => match b with
    | 0 => ackermannAutomatic x 1
    | y + 1 => ackermannAutomatic x (ackermannAutomatic (x + 1) y)
termination_by (a, b)"#,
        "ackermannAutomatic 2 2",
        7,
    ),
    (
        "nestedLexAutomatic",
        r#"def nestedLexAutomatic (a b c : Nat) : Nat :=
  if hc : 0 < c then nestedLexAutomatic a b (c - 1) + 1
  else if hb : 0 < b then nestedLexAutomatic a (b - 1) 2 + 1
  else if ha : 0 < a then nestedLexAutomatic (a - 1) 1 2 + 1 else 0
termination_by (a, (b, c))"#,
        "nestedLexAutomatic 2 1 2",
        17,
    ),
    (
        // The pin's generated proof resolves its library constructors and
        // selected clean_wf definitions independently of source shadowing.
        "namespaceAndLocalShadow",
        r#"namespace ShadowLex
def Prod.Lex.right (n : Nat) : Nat := n
def Prod.Lex.left (n : Nat) : Nat := n
def down (InvImage : Nat) (a b : Nat) : Nat :=
  if hb : 0 < b then down InvImage a (b - 1) + 1
  else if ha : 0 < a then down InvImage (a - 1) 2 + 1 else 0
termination_by (a, b)
end ShadowLex"#,
        "ShadowLex.down 17 1 1",
        4,
    ),
];

// The same programs without `termination_by`. The pin (prelude, Init.WFTactics,
// Init.Omega, Init.WFComputable) infers a lexicographic measure for each and
// evaluates it to the stated value. For `swappedLexInferred` it reports
// `termination_by (b, a)`: `a` grows at the first call, so `(a, b)` proves nothing
// and the search must take `b` first.
const INFERRED: &[(&str, &str, &str, usize)] = &[
    (
        "ackInferred",
        r#"def ackInferred : Nat → Nat → Nat
  | 0, y => y + 1
  | x + 1, 0 => ackInferred x 1
  | x + 1, y + 1 => ackInferred x (ackInferred (x + 1) y)"#,
        "ackInferred 2 3",
        9,
    ),
    (
        "lexCountInferred",
        r#"def lexCountInferred (a b : Nat) : Nat :=
  if hb : 0 < b then lexCountInferred a (b - 1) + 1
  else if ha : 0 < a then lexCountInferred (a - 1) 6 + 1 else 0"#,
        "lexCountInferred 5 7",
        42,
    ),
    (
        "swappedLexInferred",
        r#"def swappedLexInferred (a b : Nat) : Nat :=
  if hb : 0 < b then swappedLexInferred (a + 1) (b - 1) + 1
  else if ha : 0 < a then swappedLexInferred (a - 1) b + 1 else 0"#,
        "swappedLexInferred 2 2",
        6,
    ),
    (
        "nestedLexInferred",
        INFERRED_NESTED,
        "nestedLexInferred 2 3 4",
        25,
    ),
];

/// The pin infers `termination_by (a, b, c)` and computes 25 at (2, 3, 4).
/// This exhausted the ordinary elaboration budget on 2026-10-20; smart delta
/// now checks it within the unchanged limits. Keep the computation positive
/// and exercise exhaustion separately with an explicit caller work bound.
const INFERRED_NESTED: &str = r#"def nestedLexInferred (a b c : Nat) : Nat :=
  if hc : 0 < c then nestedLexInferred a b (c - 1) + 1
  else if hb : 0 < b then nestedLexInferred a (b - 1) 2 + 1
  else if ha : 0 < a then nestedLexInferred (a - 1) 1 2 + 1 else 0"#;

/// Inferred orders this search refuses, with the refusal's variant where it is the search's.
/// The pin finds no order for `notLex`, where no parameter decreases a call without
/// increasing another, nor for `stuck`, where `a` decreases the first call and nothing the
/// second ("Could not find a decreasing measure"). It accepts `needsDifference` with
/// `termination_by (b, n - i)`, from the hypothesis `i < n`: a measure this search does not
/// try, so its refusal says so rather than that no order exists.
const INFERRED_REFUSALS: &[(&str, &str, Option<&str>)] = &[
    (
        "notLex",
        r#"def notLex (a b : Nat) : Nat :=
  if h : 0 < b then notLex (a + 1) (b - 1) + notLex a (b + 1) else 0"#,
        None,
    ),
    (
        "stuck",
        r#"def stuck (a b : Nat) : Nat :=
  if h : 0 < a then stuck (a - 1) b + stuck a (b + 1) else 0"#,
        Some("WellFoundedMeasureSearchFailed"),
    ),
    (
        "needsDifference",
        r#"def needsDifference (i n b : Nat) : Nat :=
  if hb : 0 < b then needsDifference i n (b - 1)
  else if h : i < n then needsDifference (i + 1) n b else 0"#,
        Some("WellFoundedMeasureOrderUnsupported"),
    ),
];

const REFUSALS: &[(&str, &str)] = &[
    (
        "nondecreasingPair",
        r#"def nondecreasingLex (acc a b : Nat) : Nat :=
  if h : 0 < b then nondecreasingLex (acc + 1) a b else acc
termination_by (a, b)"#,
    ),
    (
        "increasingFirstCoordinate",
        r#"def increasingLex (a b : Nat) : Nat :=
  if h : 0 < b then increasingLex (a + 1) (b - 1) else 0
termination_by (a, b)"#,
    ),
    (
        "badSecondCall",
        r#"def mixedLex (a b : Nat) : Nat :=
  if h : 0 < b then mixedLex a (b - 1) + mixedLex (a + 1) (b - 1) else 0
termination_by (a, b)"#,
    ),
    (
        "opaqueSizeOfDictionary",
        r#"def hiddenSize : SizeOf Nat := ⟨fun n => n⟩
local instance : SizeOf Nat := hiddenSize
def hiddenSizeLex (a b : Nat) : Nat :=
  if hb : 0 < b then hiddenSizeLex a (b - 1) + 1
  else if ha : 0 < a then hiddenSizeLex (a - 1) 2 + 1 else 0
termination_by (a, b)"#,
    ),
];

pub(super) fn assert_automatic_lexicographic_proofs(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    for (label, definition, application, expected) in PROGRAMS.iter().chain(INFERRED) {
        let source = format!("{definition}\ndef automaticLexAnswer : Nat := {application}");
        let result = base
            .execute_source_definitions(
                &[source.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(super::limits().kernel),
            )
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap_or_else(|reason| panic!("{label}: incomplete execution: {reason:?}"));
        let values: Vec<_> = result
            .executions
            .iter()
            .filter_map(|execution| {
                fln::closed_vm_value(&execution.exit).expect("normal native VM exit")
            })
            .collect();
        assert_eq!(values, vec![ClosedVmValue::Scalar(*expected)], "{label}");
        assert!(
            result
                .engine
                .environment()
                .contains(&Name::from_components(["automaticLexAnswer"]))
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

pub(super) fn assert_automatic_lexicographic_refusals(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    let inferred = INFERRED_REFUSALS
        .iter()
        .map(|(label, definition, variant)| (*label, *definition, *variant));
    for (label, definition, variant) in REFUSALS
        .iter()
        .map(|(label, definition)| (*label, *definition, None))
        .chain(inferred)
    {
        // The first fixture changes an accumulator while leaving both measure
        // coordinates equal: it reaches a real decreasing obligation instead
        // of merely being rejected for having no varying argument. A valid
        // declaration earlier in each batch must also remain unpublished.
        let source = format!("def automaticLexPrepared : Nat := 42\n{definition}");
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(super::limits()),
            )
            .expect_err("default lexicographic proof cannot justify a nondecreasing call");
        assert!(
            !format!("{error:?}").contains("Frontend(Parse("),
            "{label}: the refusal must reach elaboration: {error:?}"
        );
        assert!(
            !matches!(
                error.disposition().0,
                "resource" | "inconclusive" | "internal-fault"
            ),
            "{label}: expected a semantic refusal: {error:?}"
        );
        if let Some(variant) = variant {
            assert!(
                format!("{error:?}").contains(variant),
                "{label}: expected {variant}: {error:?}"
            );
        }
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["automaticLexPrepared"]))
        );
    }
    // A resource control must not require a valid program to stay expensive.
    // The positive above uses ordinary limits; this genuine one-step kernel
    // bound must stop without becoming acceptance or a semantic rejection.
    let mut constrained = super::limits();
    constrained.kernel.steps = 1;
    let outcome = base.check_source_files(
        &[INFERRED_NESTED.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(constrained),
    );
    let resource_stop = match &outcome {
        Err(error) => error.disposition().0 == "resource",
        Ok(Outcome::Inconclusive(reason)) => matches!(
            &reason.cause,
            InconclusiveCause::ResourceExhausted { usage } if usage.is_genuine_exhaustion()
        ),
        Ok(_) => false,
    };
    assert!(
        resource_stop,
        "nestedLexInferred: expected a resource stop: {}",
        match &outcome {
            Err(error) => format!("{}: {error:?}", error.disposition().0),
            Ok(Outcome::Complete(_)) => "completed".to_string(),
            Ok(Outcome::Inconclusive(reason)) => format!("inconclusive: {:?}", reason.cause),
            Ok(Outcome::InternalFault(fault)) => format!("internal fault: {fault:?}"),
        }
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
}
