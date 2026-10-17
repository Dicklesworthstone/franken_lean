//! Authored proof records retain checked singleton elimination and projections.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_elab::instances::InstanceRegistry;
use fln_elab::lctx::LocalContext;
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_env::constants::ConstantInfo;
use fln_kernel::Declaration;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("the complete generated record passes both checkers")
    .engine
}

#[test]
fn proof_records_and_polymorphic_classes_generate_checked_theorem_projections() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    let source = r#"
structure Witness (P : Prop) : Prop where
  proof : P
class Law (P : Prop) : Prop where
  proof : P
instance trueLaw : Law True := Law.mk True.intro
theorem chosen : True := Law.proof
def witness : Witness True := { proof := chosen }
theorem projected : True := witness.proof
universe u
class Reflexive (A : Sort u) : Prop where
  same (x : A) : x = x
instance reflexive {A : Sort u} : Reflexive A where
  same x := by rfl
theorem generic {A : Sort u} (x : A) : x = x := Reflexive.same x
"#;
    let result = checked(&base, source);
    for declaration in [
        "Witness.proof",
        "Law.proof",
        "Reflexive.same",
        "chosen",
        "generic",
    ] {
        assert!(
            matches!(
                result.environment().find(&name(declaration)),
                Some(ConstantInfo::Thm(_))
            ),
            "{declaration} must retain its checked theorem kind",
        );
    }
    let registry = InstanceRegistry::read(result.environment()).unwrap();
    assert!(registry.is_class(&name("Law")));
    assert!(registry.is_class(&name("Reflexive")));
    for declaration in ["Witness", "Law", "Reflexive"] {
        let info = result.environment().find(&name(declaration)).unwrap();
        let mut type_ = &info.constant_val().type_;
        while let ExprNode::ForallE { body, .. } = type_.node() {
            type_ = body;
        }
        assert!(matches!(type_.node(), ExprNode::Sort { level } if level.is_zero()));
    }
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&name("Witness")));
    let repeated = checked(&base, source);
    assert_eq!(
        result.logical_root(&KVMap::new()),
        repeated.logical_root(&KVMap::new())
    );
}

#[test]
fn dependent_proof_fields_and_inherited_laws_preserve_checked_domains() {
    let result = checked(
        &seed(),
        r#"
structure Dependent (P : Prop) : Prop where
  first : P
  second : first = first
def dependent : Dependent True := { first := True.intro, second := by rfl }
theorem second_ok : dependent.first = dependent.first := dependent.second
class BaseLaw (P : Prop) : Prop where
  holds : P
class MoreLaw (P : Prop) : Prop extends BaseLaw P where
  again : P
instance more : MoreLaw True where
  holds := True.intro
  again := True.intro
theorem inherited : True := BaseLaw.holds
theorem additional : True := MoreLaw.again
"#,
    );
    for projection in [
        "Dependent.first",
        "Dependent.second",
        "BaseLaw.holds",
        "MoreLaw.toBaseLaw",
        "MoreLaw.again",
    ] {
        assert!(
            matches!(
                result.environment().find(&name(projection)),
                Some(ConstantInfo::Thm(_))
            ),
            "{projection}"
        );
    }
}

#[test]
fn empty_proof_records_reconstruct_the_k_target_and_large_elimination() {
    let result = checked(
        &seed(),
        r#"
structure EmptyProof : Prop
theorem count_ok : EmptyProof.rec (motive := fun _ => Nat) 42 EmptyProof.mk = 42 := by rfl
"#,
    );
    let Some(ConstantInfo::Rec(recursor)) = result.environment().find(&name("EmptyProof.rec"))
    else {
        panic!("the admitted empty predicate has a recursor");
    };
    assert!(recursor.k);
    assert_eq!(recursor.base.level_params.len(), 1);
    assert_eq!(recursor.rules[0].nfields, 0);
}

#[test]
fn prop_record_data_fields_and_invalid_proofs_refuse_without_publishing_prefixes() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "structure Bad : Prop where\n  value : Nat",
        "class Bad : Prop where\n  carrier : Type",
        "structure Bad : Prop where\n  run : True -> Nat",
        "structure Bad : Prop where\n  witness : Nat\n  law : witness = witness",
        "structure Good : Prop where\n  proof : True\ndef bad : Good := { proof := (0 : Nat) }",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "an invalid proof record must not publish: {source}",
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        for declaration in ["Good", "Good.proof", "Bad", "Bad.value", "bad"] {
            assert!(!base.environment().contains(&name(declaration)));
        }
    }
    checked(
        &base,
        "structure Retry : Prop where\n  proof : True\ntheorem retry : True := (Retry.mk True.intro).proof",
    );
}

#[test]
fn unchecked_prop_record_candidates_cannot_grant_data_elimination_or_forge_k() {
    let base = seed();
    let root = base.logical_root(&KVMap::new());
    let mut fields = LocalContext::new();
    fields.add_param(
        FVarId(name("value")),
        name("value"),
        Expr::const_(name("Nat"), vec![]),
        BinderInfo::Default,
    );
    let spec = RecordSpec {
        name: name("Forged"),
        level_params: vec![],
        parameters: vec![],
        fields: fields.decls().to_vec(),
        result_level: Level::zero(),
        is_class: false,
    };
    let candidate = record_declarations(&spec, RecordBudget::default()).unwrap();
    assert!(matches!(candidate[1], Declaration::Thm(_)));
    assert!(!matches!(
        base.admit_declarations(&candidate, &KVMap::new(), limits()),
        Ok(Outcome::Complete(_))
    ));

    let mut empty = record_declarations(
        &RecordSpec {
            fields: vec![],
            ..spec
        },
        RecordBudget::default(),
    )
    .unwrap();
    let Declaration::Inductive(block) = &mut empty[0] else {
        unreachable!()
    };
    assert!(block.recursors[0].k);
    block.recursors[0].k = false;
    assert!(!matches!(
        base.admit_declarations(&empty, &KVMap::new(), limits()),
        Ok(Outcome::Complete(_))
    ));
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&name("Forged")));
}
