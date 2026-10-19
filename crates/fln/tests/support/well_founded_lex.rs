//! Explicit product measures use the pin's default lexicographic constructor
//! search and the checked arithmetic prover. The measure itself is supplied;
//! automatic inference of a lexicographic measure remains a separate feature.
#![forbid(unsafe_code)]
use fln::{ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Name, SourceCheckLimits};

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
    for (label, definition, application, expected) in PROGRAMS {
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
    for (label, definition) in REFUSALS {
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
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["automaticLexPrepared"]))
        );
    }
}
