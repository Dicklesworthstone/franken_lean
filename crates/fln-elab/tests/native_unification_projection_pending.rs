//! A class projection must retain its receiver until pending synthesis runs.
//! The pin's `isDefEqApp` checkpoints failed congruence and retries the original
//! application through `isDefEqOnFailure` / `synthPending`.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{
    PendingAnswer, PendingSynthesis, UnificationBudget, UnificationError, UnificationTransparency,
};
use fln_elab::lctx::LocalDecl;
use fln_elab::mvar::MetavarKind;
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_elab::txn::ElabTxn;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.transparency = UnificationTransparency::Instances;
    budget
}
fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, budget().kernel) else {
        panic!("fixture admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture admission was rejected");
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => publication.environment,
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(publication))) => {
            publication.environment
        }
        other => panic!("fixture publication: {other:?}"),
    }
}
fn fixture() -> (ElabTxn, MVarId, Expr, Expr) {
    fixture_with_kind(MetavarKind::Natural)
}
fn fixture_with_kind(kind: MetavarKind) -> (ElabTxn, MVarId, Expr, Expr) {
    let mut env = fln_elab::seed::bootstrap_nat_environment(budget().kernel).unwrap();
    let class = RecordSpec {
        name: name("Carrier"),
        level_params: vec![],
        parameters: vec![],
        fields: vec![LocalDecl {
            id: FVarId(name("field")),
            user_name: name("field"),
            type_: constant("Nat"),
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        }],
        result_level: Level::one(),
        is_class: true,
    };
    for declaration in record_declarations(&class, RecordBudget::default()).unwrap() {
        env = publish(&env, declaration);
    }
    env = fln_elab::instances::register_class(&env, &name("Carrier")).unwrap();
    // This is the pin's ordinary class-field status. The named projection stays
    // folded at instances transparency until its dictionary receiver reduces.
    env = fln_elab::reducibility::register(
        &env,
        &name("Carrier.field"),
        fln_elab::reducibility::Reducibility::Semireducible,
    )
    .unwrap();
    let mut txn = ElabTxn::new(env, KVMap::new(), 93);
    let f = FVarId(name("f"));
    txn.lctx.add_param(
        f.clone(),
        f.0.clone(),
        Expr::forall_e(
            name("n"),
            constant("Nat"),
            constant("Nat"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let dictionary = MVarId(name("dictionary"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        Expr::forall_e(
            name("n"),
            constant("Nat"),
            constant("Carrier"),
            BinderInfo::Default,
        ),
        txn.lctx.clone(),
        kind,
        0,
        None,
    );
    let right = Expr::app(Expr::fvar(f), numeral(1));
    let left = Expr::app(
        constant("Carrier.field"),
        Expr::app(Expr::mvar(dictionary.clone()), numeral(0)),
    );
    (txn, dictionary, left, right)
}
fn answer(field: Expr) -> Expr {
    Expr::lam(
        name("n"),
        constant("Nat"),
        Expr::app(constant("Carrier.mk"), field),
        BinderInfo::Default,
    )
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}

struct Owner {
    answer: Result<Option<Expr>, UnificationError>,
    asked: Vec<MVarId>,
}
impl PendingSynthesis for Owner {
    fn synthesize(&mut self, _: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
        self.asked.push(goal.clone());
        PendingAnswer {
            result: self
                .answer
                .clone()
                .map(|answer| answer.map(|value| (value, name("Carrier")))),
            spent: 17,
        }
    }
}

#[test]
fn named_class_projection_keeps_its_pending_function_dictionary() {
    for (kind, reversed) in [
        (MetavarKind::Natural, false),
        (MetavarKind::Natural, true),
        (MetavarKind::SyntheticOpaque, false),
        (MetavarKind::SyntheticOpaque, true),
    ] {
        let (mut txn, dictionary, left, right) = fixture_with_kind(kind);
        let value = answer(right.clone());
        let mut owner = Owner {
            answer: Ok(Some(value.clone())),
            asked: vec![],
        };
        let equations = if reversed {
            [(right, left)]
        } else {
            [(left, right)]
        };
        let before = txn.clone();
        assert!(
            txn.clone()
                .unify_many_with(&equations, budget(), &|| false)
                .is_err()
        );
        let report = txn
            .unify_many_with_pending(&equations, budget(), &|| false, &mut owner)
            .unwrap();
        assert_eq!(owner.asked, vec![dictionary.clone()]);
        assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&value));
        assert_eq!(report.expression_assignments, vec![dictionary]);
        assert!(report.kernel_checks > 0);
        assert!(txn.budget.heartbeats_consumed >= before.budget.heartbeats_consumed + 17);
    }
}

#[test]
fn projection_synthesis_cannot_discard_the_original_application_equation() {
    let (mut txn, dictionary, left, right) = fixture();
    let wrong = Expr::app(Expr::fvar(FVarId(name("f"))), numeral(2));
    let mut owner = Owner {
        answer: Ok(Some(answer(wrong))),
        asked: vec![],
    };
    let before = txn.clone();
    assert!(
        txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
            .is_err()
    );
    assert_eq!(owner.asked, vec![dictionary]);
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed >= before.budget.heartbeats_consumed + 17);
}

#[test]
fn a_declined_or_exhausted_projection_synthesis_retains_its_outcome_and_work() {
    for stopped in [false, true] {
        let (mut txn, dictionary, left, right) = fixture();
        let mut owner = Owner {
            answer: if stopped {
                Err(UnificationError::HeartbeatLimit)
            } else {
                Ok(None)
            },
            asked: vec![],
        };
        let before = txn.clone();
        let error = txn
            .unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
            .unwrap_err();
        if stopped {
            assert_eq!(error, UnificationError::HeartbeatLimit);
        } else {
            assert!(matches!(error, UnificationError::Deferred(_)));
        }
        assert_eq!(owner.asked, vec![dictionary]);
        unchanged(&txn, &before);
        assert!(txn.budget.heartbeats_consumed >= before.budget.heartbeats_consumed + 17);
    }
}

#[test]
fn matching_projection_heads_keep_precise_dictionary_patterns_first() {
    let (mut txn, _, _, _) = fixture();
    // Keep the concrete receiver opaque so both projection heads reach congruence.
    let local = FVarId(name("knownDictionary"));
    txn.lctx.add_param(
        local.clone(),
        local.0.clone(),
        constant("Carrier"),
        BinderInfo::Default,
    );
    let dictionary = MVarId(name("directDictionary"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        constant("Carrier"),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let left = Expr::app(constant("Carrier.field"), Expr::mvar(dictionary.clone()));
    let right = Expr::app(constant("Carrier.field"), Expr::fvar(local));
    let mut owner = Owner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    let report = txn
        .unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
        .unwrap();
    assert!(owner.asked.is_empty());
    assert_eq!(report.expression_assignments, vec![dictionary]);
}

fn add_function_record(txn: &mut ElabTxn, record: &str, is_class: bool) {
    let spec = RecordSpec {
        name: name(record),
        level_params: vec![],
        parameters: vec![],
        fields: vec![LocalDecl {
            id: FVarId(name("run")),
            user_name: name("run"),
            type_: Expr::forall_e(
                name("n"),
                constant("Nat"),
                constant("Nat"),
                BinderInfo::Default,
            ),
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        }],
        result_level: Level::one(),
        is_class,
    };
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        txn.env = publish(&txn.env, declaration);
    }
    if is_class {
        txn.env = fln_elab::instances::register_class(&txn.env, &name(record)).unwrap();
    }
}

#[test]
fn nonclass_projective_heads_keep_singleton_inversion_before_synthesis() {
    let (mut txn, _, _, _) = fixture();
    add_function_record(&mut txn, "FunBox", false);
    let boxed = MVarId(name("boxed"));
    txn.mvars.declare(
        boxed.clone(),
        boxed.0.clone(),
        constant("FunBox"),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let left = Expr::app(
        Expr::proj(name("FunBox"), 0, Expr::mvar(boxed.clone())),
        numeral(0),
    );
    let f = Expr::fvar(FVarId(name("f")));
    let right = Expr::app(f.clone(), numeral(0));
    let mut owner = Owner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
        .unwrap();
    assert!(owner.asked.is_empty());
    assert_eq!(
        txn.mvars.get_assigned_expr(&boxed),
        Some(&Expr::app(constant("FunBox.mk"), f))
    );
}

#[test]
fn class_projective_heads_keep_precise_receiver_congruence() {
    let (mut txn, _, _, _) = fixture();
    add_function_record(&mut txn, "FunctionCarrier", true);
    let known = FVarId(name("knownFunctionCarrier"));
    txn.lctx.add_param(
        known.clone(),
        known.0.clone(),
        constant("FunctionCarrier"),
        BinderInfo::Default,
    );
    let dictionary = MVarId(name("functionCarrier"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        constant("FunctionCarrier"),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let receiver = Expr::fvar(known);
    let left = Expr::app(
        Expr::proj(name("FunctionCarrier"), 0, Expr::mvar(dictionary.clone())),
        numeral(0),
    );
    let right = Expr::app(
        Expr::proj(name("FunctionCarrier"), 0, receiver.clone()),
        numeral(0),
    );
    let mut owner = Owner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
        .unwrap();
    assert!(owner.asked.is_empty());
    assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&receiver));
}

#[test]
fn distinct_definitionally_equal_named_heads_reduce_before_synthesis() {
    for transparency in [
        UnificationTransparency::Instances,
        UnificationTransparency::Default,
    ] {
        let (mut txn, _, _, _) = fixture();
        for alias in ["fieldAliasA", "fieldAliasB"] {
            txn.env = publish(
                &txn.env,
                Declaration::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: name(alias),
                        level_params: vec![],
                        type_: Expr::forall_e(
                            name("dictionary"),
                            constant("Carrier"),
                            constant("Nat"),
                            BinderInfo::Default,
                        ),
                    },
                    value: Expr::lam(
                        name("dictionary"),
                        constant("Carrier"),
                        Expr::app(constant("Carrier.field"), Expr::bvar(0).unwrap()),
                        BinderInfo::Default,
                    ),
                    hints: ReducibilityHints::Regular(1),
                    safety: DefinitionSafety::Safe,
                    all: vec![name(alias)],
                }),
            );
            txn.env = fln_elab::reducibility::register(
                &txn.env,
                &name(alias),
                if transparency == UnificationTransparency::Instances {
                    fln_elab::reducibility::Reducibility::ImplicitReducible
                } else {
                    fln_elab::reducibility::Reducibility::Semireducible
                },
            )
            .unwrap();
        }
        let known = FVarId(name("knownCarrier"));
        txn.lctx.add_param(
            known.clone(),
            known.0.clone(),
            constant("Carrier"),
            BinderInfo::Default,
        );
        let dictionary = MVarId(name("aliasDictionary"));
        txn.mvars.declare(
            dictionary.clone(),
            dictionary.0.clone(),
            constant("Carrier"),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let receiver = Expr::fvar(known);
        let left = Expr::app(constant("fieldAliasA"), Expr::mvar(dictionary.clone()));
        let right = Expr::app(constant("fieldAliasB"), receiver.clone());
        let mut owner = Owner {
            answer: Err(UnificationError::Cancelled),
            asked: vec![],
        };
        let mut limits = budget();
        limits.transparency = transparency;
        txn.unify_many_with_pending(&[(left, right)], limits, &|| false, &mut owner)
            .unwrap();
        assert!(owner.asked.is_empty());
        assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&receiver));
    }
}

#[test]
fn flexible_function_heads_keep_precise_patterns_before_synthesis() {
    let (mut txn, _, _, _) = fixture();
    let local = FVarId(name("argument"));
    txn.lctx.add_param(
        local.clone(),
        local.0.clone(),
        constant("Nat"),
        BinderInfo::Default,
    );
    let function = MVarId(name("function"));
    txn.mvars.declare(
        function.clone(),
        function.0.clone(),
        Expr::forall_e(
            name("n"),
            constant("Nat"),
            constant("Nat"),
            BinderInfo::Default,
        ),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let argument = Expr::fvar(local);
    let left = Expr::app(Expr::mvar(function.clone()), argument.clone());
    let right = Expr::app(Expr::fvar(FVarId(name("f"))), argument);
    let mut owner = Owner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
        .unwrap();
    assert!(owner.asked.is_empty());
    assert!(txn.mvars.is_assigned(&function));
}

#[test]
fn extra_projection_arguments_can_determine_pending_instance_inputs() {
    struct NeedsInput {
        input: MVarId,
        dictionary: MVarId,
        value: Expr,
        decline: bool,
        observed_inputs: Vec<Option<Expr>>,
    }
    impl PendingSynthesis for NeedsInput {
        fn synthesize(&mut self, state: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
            assert_eq!(goal, &self.dictionary);
            let input = state.mvars.get_assigned_expr(&self.input).cloned();
            self.observed_inputs.push(input.clone());
            PendingAnswer {
                result: Ok((!self.decline && input == Some(numeral(0)))
                    .then(|| (self.value.clone(), name("FunctionAt")))),
                spent: 17,
            }
        }
    }
    // Preserve the native worklist's existing head/argument congruence. This
    // regression control does not assume the pin's different application
    // comparison order makes the same intermediate assignments.
    for decline in [false, true] {
        let (mut txn, _, _, _) = fixture();
        let spec = RecordSpec {
            name: name("FunctionAt"),
            level_params: vec![],
            parameters: vec![LocalDecl {
                id: FVarId(name("key")),
                user_name: name("key"),
                type_: constant("Nat"),
                value: None,
                binder_info: BinderInfo::Default,
                index: 0,
            }],
            fields: vec![LocalDecl {
                id: FVarId(name("run")),
                user_name: name("run"),
                type_: Expr::forall_e(
                    name("n"),
                    constant("Nat"),
                    constant("Nat"),
                    BinderInfo::Default,
                ),
                value: None,
                binder_info: BinderInfo::Default,
                index: 1,
            }],
            result_level: Level::one(),
            is_class: true,
        };
        for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
            txn.env = publish(&txn.env, declaration);
        }
        txn.env = fln_elab::instances::register_class(&txn.env, &name("FunctionAt")).unwrap();
        txn.env = fln_elab::reducibility::register(
            &txn.env,
            &name("FunctionAt.run"),
            fln_elab::reducibility::Reducibility::Semireducible,
        )
        .unwrap();
        let input = MVarId(name("input"));
        txn.mvars.declare(
            input.clone(),
            input.0.clone(),
            constant("Nat"),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let dictionary = MVarId(name("dependentDictionary"));
        txn.mvars.declare(
            dictionary.clone(),
            dictionary.0.clone(),
            Expr::app(constant("FunctionAt"), Expr::mvar(input.clone())),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let f = Expr::fvar(FVarId(name("f")));
        let value = Expr::app(Expr::app(constant("FunctionAt.mk"), numeral(0)), f.clone());
        let left = Expr::app(
            Expr::app(
                Expr::app(constant("FunctionAt.run"), Expr::mvar(input.clone())),
                Expr::mvar(dictionary.clone()),
            ),
            Expr::mvar(input.clone()),
        );
        let right = Expr::app(f, numeral(0));
        let mut owner = NeedsInput {
            input: input.clone(),
            dictionary: dictionary.clone(),
            value: value.clone(),
            decline,
            observed_inputs: vec![],
        };
        let before = txn.clone();
        let result = txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner);
        assert_eq!(owner.observed_inputs, vec![Some(numeral(0))]);
        if decline {
            assert!(matches!(result, Err(UnificationError::Deferred(_))));
            unchanged(&txn, &before);
        } else {
            let report = result.expect("the explicit argument fixes the instance input");
            assert!(report.kernel_checks > 0);
            assert_eq!(txn.mvars.get_assigned_expr(&input), Some(&numeral(0)));
            assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&value));
        }
        assert!(txn.budget.heartbeats_consumed >= before.budget.heartbeats_consumed + 17);
    }
}
