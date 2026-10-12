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

fn add_box_carrier(txn: &mut ElabTxn) {
    add_function_record(txn, "FunBox", false);
    let spec = RecordSpec {
        name: name("BoxCarrier"),
        level_params: vec![],
        parameters: vec![],
        fields: vec![LocalDecl {
            id: FVarId(name("box")),
            user_name: name("box"),
            type_: constant("FunBox"),
            value: None,
            binder_info: BinderInfo::Default,
            index: 0,
        }],
        result_level: Level::one(),
        is_class: true,
    };
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        txn.env = publish(&txn.env, declaration);
    }
    txn.env = fln_elab::instances::register_class(&txn.env, &name("BoxCarrier")).unwrap();
    txn.env = fln_elab::reducibility::register(
        &txn.env,
        &name("BoxCarrier.box"),
        fln_elab::reducibility::Reducibility::Semireducible,
    )
    .unwrap();
}

fn box_projection(receiver: Expr) -> Expr {
    Expr::app(constant("BoxCarrier.box"), receiver)
}

fn function_box(function: Expr) -> Expr {
    Expr::app(constant("FunBox.mk"), function)
}

fn box_dictionary(function: Expr) -> Expr {
    Expr::app(constant("BoxCarrier.mk"), function_box(function))
}

fn constant_function(value: Expr) -> Expr {
    Expr::lam(name("n"), constant("Nat"), value, BinderInfo::Default)
}

fn eta_fixture(kind: MetavarKind) -> (ElabTxn, MVarId, Expr, Expr, Expr) {
    let (mut txn, _, _, _) = fixture();
    add_box_carrier(&mut txn);
    let dictionary = MVarId(name("boxDictionary"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        Expr::forall_e(
            name("n"),
            constant("Nat"),
            constant("BoxCarrier"),
            BinderInfo::Default,
        ),
        txn.lctx.clone(),
        kind,
        0,
        None,
    );
    let selected = Expr::app(Expr::fvar(FVarId(name("f"))), numeral(1));
    let function = constant_function(selected);
    let left = box_projection(Expr::app(Expr::mvar(dictionary.clone()), numeral(0)));
    let right = function_box(function.clone());
    let answer = constant_function(box_dictionary(function));
    (txn, dictionary, left, right, answer)
}

struct BoxOwner {
    answer: Result<Option<Expr>, UnificationError>,
    asked: Vec<MVarId>,
}

impl PendingSynthesis for BoxOwner {
    fn synthesize(&mut self, _: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
        self.asked.push(goal.clone());
        PendingAnswer {
            result: self
                .answer
                .clone()
                .map(|answer| answer.map(|value| (value, name("BoxCarrier")))),
            spent: 17,
        }
    }
}

#[test]
fn nested_record_and_function_eta_keep_the_pending_dictionary_equation() {
    for (kind, reversed) in [
        (MetavarKind::Natural, false),
        (MetavarKind::Natural, true),
        (MetavarKind::SyntheticOpaque, false),
        (MetavarKind::SyntheticOpaque, true),
    ] {
        let (mut txn, dictionary, left, right, answer) = eta_fixture(kind);
        let mut owner = BoxOwner {
            answer: Ok(Some(answer.clone())),
            asked: vec![],
        };
        let equations = if reversed {
            [(right, left)]
        } else {
            [(left, right)]
        };
        let report = txn
            .unify_many_with_pending(&equations, budget(), &|| false, &mut owner)
            .unwrap();
        assert_eq!(owner.asked, vec![dictionary.clone()]);
        assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&answer));
        assert_eq!(report.expression_assignments, vec![dictionary]);
        assert!(report.kernel_checks > 0);
    }
}

#[test]
fn failed_nested_eta_synthesis_preserves_the_equation_and_resource_outcome() {
    for outcome in 0..3 {
        let (mut txn, dictionary, left, right, _) = eta_fixture(MetavarKind::Natural);
        let wrong = Expr::app(Expr::fvar(FVarId(name("f"))), numeral(2));
        let mut owner = BoxOwner {
            answer: match outcome {
                0 => Ok(None),
                1 => Ok(Some(constant_function(box_dictionary(constant_function(
                    wrong,
                ))))),
                _ => Err(UnificationError::HeartbeatLimit),
            },
            asked: vec![],
        };
        let before = txn.clone();
        let error = txn
            .unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
            .unwrap_err();
        if outcome == 2 {
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
fn record_eta_can_infer_the_precise_receiver_before_instance_search() {
    let (mut txn, _, _, _, _) = eta_fixture(MetavarKind::Natural);
    let known = FVarId(name("knownBoxCarrier"));
    txn.lctx.add_param(
        known.clone(),
        known.0.clone(),
        constant("BoxCarrier"),
        BinderInfo::Default,
    );
    let dictionary = MVarId(name("preciseBoxCarrier"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        constant("BoxCarrier"),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let receiver = Expr::fvar(known);
    let left = box_projection(Expr::mvar(dictionary.clone()));
    let right = function_box(Expr::proj(
        name("FunBox"),
        0,
        box_projection(receiver.clone()),
    ));
    let mut owner = BoxOwner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner)
        .unwrap();
    assert!(owner.asked.is_empty());
    assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&receiver));
}

#[test]
fn a_later_outer_equation_determines_the_record_receiver_before_search() {
    let (mut txn, _, _, _, _) = eta_fixture(MetavarKind::Natural);
    let dictionary = MVarId(name("laterBoxCarrier"));
    txn.mvars.declare(
        dictionary.clone(),
        dictionary.0.clone(),
        constant("BoxCarrier"),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let function = Expr::fvar(FVarId(name("f")));
    let left = box_projection(Expr::mvar(dictionary.clone()));
    let right = function_box(function.clone());
    let receiver = box_dictionary(function);
    let mut owner = BoxOwner {
        answer: Err(UnificationError::Cancelled),
        asked: vec![],
    };
    txn.unify_many_with_pending(
        &[
            (left, right),
            (Expr::mvar(dictionary.clone()), receiver.clone()),
        ],
        budget(),
        &|| false,
        &mut owner,
    )
    .unwrap();
    assert!(owner.asked.is_empty());
    assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&receiver));
}

fn add_indexed_box_records(txn: &mut ElabTxn) {
    let key = FVarId(name("key"));
    for (record, field, field_type, is_class) in [
        (
            "FunAt",
            "run",
            Expr::forall_e(
                name("n"),
                constant("Nat"),
                constant("Nat"),
                BinderInfo::Default,
            ),
            false,
        ),
        (
            "CarrierAt",
            "box",
            Expr::app(constant("FunAt"), Expr::fvar(key.clone())),
            true,
        ),
    ] {
        let spec = RecordSpec {
            name: name(record),
            level_params: vec![],
            parameters: vec![LocalDecl {
                id: key.clone(),
                user_name: key.0.clone(),
                type_: constant("Nat"),
                value: None,
                binder_info: BinderInfo::Default,
                index: 0,
            }],
            fields: vec![LocalDecl {
                id: FVarId(name(field)),
                user_name: name(field),
                type_: field_type,
                value: None,
                binder_info: BinderInfo::Default,
                index: 1,
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
    txn.env = fln_elab::reducibility::register(
        &txn.env,
        &name("CarrierAt.box"),
        fln_elab::reducibility::Reducibility::Semireducible,
    )
    .unwrap();
}

#[test]
fn failed_eta_trials_keep_input_assignments_before_owner_synthesis() {
    struct NeedsEtaInput {
        input: MVarId,
        dictionary: MVarId,
        value: Expr,
        decline: bool,
        observed: Vec<Option<Expr>>,
    }
    impl PendingSynthesis for NeedsEtaInput {
        fn synthesize(&mut self, state: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
            assert_eq!(goal, &self.dictionary);
            let input = state.mvars.get_assigned_expr(&self.input).cloned();
            self.observed.push(input.clone());
            PendingAnswer {
                result: Ok((!self.decline && input == Some(numeral(0)))
                    .then(|| (self.value.clone(), name("CarrierAt")))),
                spent: 17,
            }
        }
    }
    for decline in [false, true] {
        let (mut txn, _, _, _) = fixture();
        add_indexed_box_records(&mut txn);
        let input = MVarId(name("etaInput"));
        txn.mvars.declare(
            input.clone(),
            input.0.clone(),
            constant("Nat"),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let dictionary = MVarId(name("etaInputDictionary"));
        txn.mvars.declare(
            dictionary.clone(),
            dictionary.0.clone(),
            Expr::app(constant("CarrierAt"), Expr::mvar(input.clone())),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let left = Expr::app(
            Expr::app(constant("CarrierAt.box"), Expr::mvar(input.clone())),
            Expr::mvar(dictionary.clone()),
        );
        let right = Expr::app(
            Expr::app(constant("FunAt.mk"), numeral(0)),
            Expr::fvar(FVarId(name("f"))),
        );
        let receiver = Expr::app(
            Expr::app(constant("CarrierAt.mk"), numeral(0)),
            right.clone(),
        );
        let mut owner = NeedsEtaInput {
            input: input.clone(),
            dictionary: dictionary.clone(),
            value: receiver.clone(),
            decline,
            observed: vec![],
        };
        let before = txn.clone();
        let result = txn.unify_many_with_pending(&[(left, right)], budget(), &|| false, &mut owner);
        assert_eq!(owner.observed, vec![Some(numeral(0))]);
        if decline {
            assert!(matches!(result, Err(UnificationError::Deferred(_))));
            unchanged(&txn, &before);
        } else {
            result.unwrap();
            assert_eq!(txn.mvars.get_assigned_expr(&input), Some(&numeral(0)));
            assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&receiver));
        }
        assert!(txn.budget.heartbeats_consumed >= before.budget.heartbeats_consumed + 17);
    }
}

#[test]
fn record_eta_exposes_an_owned_dictionary_inside_the_constructor() {
    struct OtherOwner {
        unowned: MVarId,
        owned: MVarId,
        value: Expr,
        asked: Vec<MVarId>,
    }
    impl PendingSynthesis for OtherOwner {
        fn synthesize(&mut self, _: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
            self.asked.push(goal.clone());
            assert!(goal == &self.unowned || goal == &self.owned);
            PendingAnswer {
                result: Ok((goal == &self.owned).then(|| (self.value.clone(), name("Other")))),
                spent: 17,
            }
        }
    }
    for (reversed, hidden_in_let) in [(false, false), (true, false), (false, true), (true, true)] {
        let (mut txn, _, _, _, _) = eta_fixture(MetavarKind::Natural);
        add_function_record(&mut txn, "Other", true);
        txn.env = fln_elab::reducibility::register(
            &txn.env,
            &name("Other.run"),
            fln_elab::reducibility::Reducibility::Semireducible,
        )
        .unwrap();
        let known = FVarId(name("knownOtherBox"));
        txn.lctx.add_param(
            known.clone(),
            known.0.clone(),
            constant("BoxCarrier"),
            BinderInfo::Default,
        );
        let first = MVarId(name("unownedBox"));
        let second = MVarId(name("ownedOther"));
        for (id, type_) in [
            (&first, constant("BoxCarrier")),
            (&second, constant("Other")),
        ] {
            txn.mvars.declare(
                id.clone(),
                id.0.clone(),
                type_,
                txn.lctx.clone(),
                MetavarKind::Natural,
                0,
                None,
            );
        }
        let receiver = Expr::fvar(known);
        let value = Expr::app(
            constant("Other.mk"),
            Expr::proj(name("FunBox"), 0, box_projection(receiver.clone())),
        );
        let left = box_projection(Expr::mvar(first.clone()));
        let function = Expr::app(constant("Other.run"), Expr::mvar(second.clone()));
        let function = if hidden_in_let {
            let local = FVarId(name("hiddenOtherFunction"));
            txn.lctx.add_let(
                local.clone(),
                local.0.clone(),
                Expr::forall_e(
                    name("n"),
                    constant("Nat"),
                    constant("Nat"),
                    BinderInfo::Default,
                ),
                function,
            );
            Expr::fvar(local)
        } else {
            function
        };
        let right = function_box(function);
        let equations = if reversed {
            [(right, left)]
        } else {
            [(left, right)]
        };
        let mut owner = OtherOwner {
            unowned: first.clone(),
            owned: second.clone(),
            value: value.clone(),
            asked: vec![],
        };
        if hidden_in_let {
            let mut closed = txn.clone();
            let mut limits = budget();
            limits.zeta_delta = false;
            let error = closed
                .unify_many_with_pending(&equations, limits, &|| false, &mut owner)
                .unwrap_err();
            assert!(matches!(error, UnificationError::Deferred(_)), "{error:?}");
            assert!(!owner.asked.contains(&second), "{:?}", owner.asked);
            unchanged(&closed, &txn);
            owner.asked.clear();
        }
        txn.unify_many_with_pending(&equations, budget(), &|| false, &mut owner)
            .unwrap_or_else(|error| {
                panic!(
                    "reversed={reversed}, hidden_in_let={hidden_in_let}, asked={:?}: {error:?}",
                    owner.asked
                )
            });
        assert_eq!(
            owner.asked.iter().filter(|goal| *goal == &second).count(),
            1
        );
        assert_eq!(txn.mvars.get_assigned_expr(&first), Some(&receiver));
        assert_eq!(txn.mvars.get_assigned_expr(&second), Some(&value));
    }
}

#[test]
fn record_eta_exposes_owned_dictionaries_in_receiver_inputs_and_types() {
    struct InputOwner {
        receiver: MVarId,
        input: MVarId,
        receiver_value: Option<Expr>,
        asked: Vec<MVarId>,
    }
    impl PendingSynthesis for InputOwner {
        fn synthesize(&mut self, state: &ElabTxn, goal: &MVarId, _: u64) -> PendingAnswer {
            self.asked.push(goal.clone());
            let answer = if goal == &self.input {
                Some((
                    Expr::app(constant("Carrier.mk"), numeral(0)),
                    name("Carrier"),
                ))
            } else {
                assert_eq!(goal, &self.receiver);
                if state.mvars.is_assigned(&self.input) {
                    self.receiver_value
                        .clone()
                        .map(|value| (value, name("CarrierAt")))
                } else {
                    None
                }
            };
            PendingAnswer {
                result: Ok(answer),
                spent: 17,
            }
        }
    }
    for (in_type, reversed) in [(false, false), (false, true), (true, false), (true, true)] {
        let (mut txn, _, _, _) = fixture();
        add_indexed_box_records(&mut txn);
        let family = Expr::forall_e(
            name("n"),
            constant("Nat"),
            Expr::app(constant("CarrierAt"), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let known = FVarId(name("knownIndexedCarrier"));
        txn.lctx.add_param(
            known.clone(),
            known.0.clone(),
            family.clone(),
            BinderInfo::Default,
        );
        let input = MVarId(name("hiddenCarrierInput"));
        txn.mvars.declare(
            input.clone(),
            input.0.clone(),
            constant("Carrier"),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let index = Expr::app(constant("Carrier.field"), Expr::mvar(input.clone()));
        let receiver = MVarId(name("inputDependentReceiver"));
        let receiver_type = if in_type {
            Expr::app(constant("CarrierAt"), index.clone())
        } else {
            family
        };
        txn.mvars.declare(
            receiver.clone(),
            receiver.0.clone(),
            receiver_type,
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let known = Expr::fvar(known);
        let known_box = Expr::app(
            Expr::app(constant("CarrierAt.box"), numeral(0)),
            Expr::app(known.clone(), numeral(0)),
        );
        let right = Expr::app(
            Expr::app(constant("FunAt.mk"), numeral(0)),
            Expr::proj(name("FunAt"), 0, known_box),
        );
        let (left, receiver_value) = if in_type {
            // The second hole is absent from the neutral expression itself;
            // the receiver's declared type carries the unknown class input.
            (
                Expr::proj(name("CarrierAt"), 0, Expr::mvar(receiver.clone())),
                Some(Expr::app(
                    Expr::app(constant("CarrierAt.mk"), numeral(0)),
                    right.clone(),
                )),
            )
        } else {
            // Eta exposes the type equality that determines the receiver's
            // application argument, enabling precise aligned-head recovery.
            (
                Expr::app(
                    Expr::app(constant("CarrierAt.box"), index.clone()),
                    Expr::app(Expr::mvar(receiver.clone()), index),
                ),
                None,
            )
        };
        let expected_receiver = receiver_value.clone().unwrap_or(known);
        let equations = if reversed {
            [(right, left)]
        } else {
            [(left, right)]
        };
        let mut owner = InputOwner {
            receiver: receiver.clone(),
            input: input.clone(),
            receiver_value,
            asked: vec![],
        };
        txn.unify_many_with_pending(&equations, budget(), &|| false, &mut owner)
            .unwrap();
        assert_eq!(owner.asked.iter().filter(|goal| *goal == &input).count(), 1);
        assert_eq!(
            txn.mvars.get_assigned_expr(&receiver),
            Some(&expected_receiver)
        );
        assert_eq!(
            txn.mvars.get_assigned_expr(&input),
            Some(&Expr::app(constant("Carrier.mk"), numeral(0)))
        );
    }
}

#[test]
fn pending_local_let_blockers_respect_zeta_and_ignore_unrelated_arguments() {
    for (zeta_delta, wrapped) in [(true, false), (false, false), (true, true), (false, true)] {
        let (mut txn, dictionary, projection, _) = fixture();
        let hidden = FVarId(name("hiddenDictionaryField"));
        txn.lctx.add_let(
            hidden.clone(),
            hidden.0.clone(),
            constant("Nat"),
            projection,
        );
        let left = Expr::fvar(hidden);
        let left = if wrapped {
            // This rigid function does not reduce through its argument. A
            // dictionary hidden there must not be discovered by scanning it.
            Expr::app(Expr::fvar(FVarId(name("f"))), left)
        } else {
            left
        };
        let value = answer(numeral(7));
        let mut owner = Owner {
            answer: Ok(Some(value.clone())),
            asked: vec![],
        };
        let mut limits = budget();
        limits.zeta_delta = zeta_delta;
        let before = txn.clone();
        let result =
            txn.unify_many_with_pending(&[(left, numeral(7))], limits, &|| false, &mut owner);
        if zeta_delta && !wrapped {
            let report = result.unwrap();
            assert_eq!(owner.asked, vec![dictionary.clone()]);
            assert_eq!(txn.mvars.get_assigned_expr(&dictionary), Some(&value));
            assert!(report.kernel_checks > 0);
        } else {
            assert!(
                matches!(result, Err(UnificationError::Deferred(_))),
                "{result:?}"
            );
            assert!(owner.asked.is_empty(), "{:?}", owner.asked);
            unchanged(&txn, &before);
        }
    }
}
