//! Singleton Prop elimination uses checked rules after proof erasure.
//! These source-only regressions require no imported library or Reference process.
#![forbid(unsafe_code)]

use fln::{
    Budget, ConstantInfo, Engine, EngineAdmissionLimits, EngineExecutionLimits, ExprNode, KVMap,
    Name, SourceCheckLimits, VmExit,
};

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn checked(source: &str) -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn returned(exit: &VmExit, expected: &str) {
    let VmExit::Returned(value) = exit else {
        panic!("normal native return, got {exit:?}")
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
}

fn evaluate(base: &Engine, source: &str, expected: &[&str]) {
    let root = base.logical_root(&KVMap::new());
    let result = base
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(result.executions.len(), expected.len());
    assert_eq!(result.source_evaluation_indices.len(), expected.len());
    for (execution, expected) in result.executions.iter().zip(expected) {
        returned(&execution.exit, expected);
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        returned(&replay, expected);
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

const SOURCE: &str = r#"
structure Evidence where
  proof : True
structure TwoProofs where
  first : True
  second : True
structure EvidenceType : Type where
  proof : True
structure ValueRecord where
  proof : True
  value : Nat
class ProofScore (P : Prop) where
  score : P -> Nat
instance trueScore : ProofScore True where
  score _ := 23
def readEvidence (x : Evidence) : Nat :=
  match x with | .mk h => ProofScore.score h
def readTwoProofs (x : TwoProofs) : Nat :=
  match x with | .mk first second => ProofScore.score first + ProofScore.score second
def readEvidenceType (x : EvidenceType) : Nat :=
  match x with | .mk h => ProofScore.score h
def readValue (x : ValueRecord) : Nat :=
  match x with | .mk _ n => n
"#;

#[test]
fn singleton_proof_records_execute_the_selected_minor_and_replay() {
    let engine = checked(SOURCE);
    let Some(ConstantInfo::Induct(family)) = engine
        .environment()
        .find(&Name::from_components(["Evidence"]))
    else {
        panic!("checked source Evidence family")
    };
    assert!(matches!(family.base.type_.node(), ExprNode::Sort { level } if level.is_zero()));
    evaluate(
        &engine,
        "#eval readEvidence (Evidence.mk True.intro)\n#eval readTwoProofs (TwoProofs.mk True.intro True.intro)\n#eval readEvidenceType (EvidenceType.mk True.intro)\n#eval readValue (ValueRecord.mk True.intro 42)\n",
        &["23", "46", "23", "42"],
    );
}

#[test]
fn proof_elimination_preserves_owned_callback_results_and_captures() {
    let engine = checked(&format!(
        "{SOURCE}\n{}",
        r#"
def afterProof (offset : Nat) (x : Evidence) : Nat -> Nat :=
  match x with | .mk h => fun n => offset + n + ProofScore.score h
def applyResult (f : Nat -> Nat) : Nat := f 19
"#
    ));
    evaluate(
        &engine,
        "#eval (afterProof 0 (Evidence.mk True.intro)) 19\n#eval applyResult (afterProof 0 (Evidence.mk True.intro))\n#eval let f := afterProof 1 (Evidence.mk True.intro); f 18 + f 19\n",
        &["42", "42", "85"],
    );
}

#[test]
fn proof_majors_remain_erased_and_invalid_large_elimination_stays_rejected() {
    let engine = checked(&format!(
        "{SOURCE}\n{}",
        r#"
noncomputable def hiddenEvidence : Evidence := Evidence.mk True.intro
structure PredicateEvidence (P : Prop) where
  proof : P
def readPredicate (x : PredicateEvidence True) : Nat :=
  match x with | .mk h => ProofScore.score h
"#
    ));
    evaluate(
        &engine,
        "#eval readEvidence hiddenEvidence\n#eval readPredicate (PredicateEvidence.mk True.intro)\n",
        &["23", "23"],
    );
    let root = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_files(
                &[br#"inductive Forbidden : Prop where | left | right
def bad (x : Forbidden) : Nat := match x with | .left => 0 | .right => 1
"#],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .is_err()
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}
