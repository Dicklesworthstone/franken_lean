//! String and character value patterns over the retained, council-admitted Prelude.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, SourceModuleInput,
};
use std::sync::OnceLock;

const STACK: usize = 128 * 1024 * 1024;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn imported() -> &'static SourceOleanImport {
    static PRELUDE: OnceLock<SourceOleanImport> = OnceLock::new();
    PRELUDE.get_or_init(|| {
        let module = name("Init.Prelude");
        Engine::builder()
            .build_empty()
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &module,
                    artifact: include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean"
                    ),
                    server_artifact: Some(include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"
                    )),
                    private_artifact: Some(include_bytes!(
                        "../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"
                    )),
                }],
                std::slice::from_ref(&module),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    16 << 20,
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .expect("the real pinned Prelude chain decodes")
            .into_complete()
            .expect("both checking seats admit the retained Prelude")
    })
}

fn on_stack(test: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(test)
        .unwrap()
        .join()
        .unwrap();
}

fn run(source: &str) -> Vec<usize> {
    let module = name("TextPatterns");
    let result = imported()
        .execute_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK))),
            None,
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("the source executes completely");
    result
        .modules
        .iter()
        .flat_map(|module| {
            module
                .commands
                .batch
                .source_evaluation_indices
                .iter()
                .map(|index| {
                    match fln::closed_vm_value(&module.commands.batch.executions[*index].exit)
                        .unwrap()
                    {
                        Some(ClosedVmValue::Scalar(value)) => value,
                        other => panic!("expected a Nat evaluation, got {other:?}"),
                    }
                })
        })
        .collect()
}

#[test]
fn string_and_char_patterns_execute_from_admitted_definitions() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
def word : String -> Nat
  | "" => 0
  | "a\nb" => 7
  | "λ" => 9
  | _ => 11
def letter : Char -> Nat
  | 'a' => 1
  | '\n' => 2
  | 'λ' => 3
  | _ => 4
#eval word ""
#eval word "a\nb"
#eval word "λ"
#eval word "other"
#eval letter 'a'
#eval letter '\n'
#eval letter 'λ'
#eval letter '🙂'
"#),
            vec![0, 7, 9, 11, 1, 2, 3, 4]
        );
    });
}

#[test]
fn escaped_raw_and_unicode_values_keep_ordered_matrix_semantics() {
    on_stack(|| {
        assert_eq!(
            run(r##"
prelude
import Init.Prelude
def text : String -> Bool -> Nat
  | "a\nb", true => 1
  | r#"a
b"#, false => 2
  | "🙂", _ => 3
  | _, _ => 4
def character : Char -> Bool -> Nat
  | 'a', true => 5
  | '\x61', false => 6
  | '🙂', _ => 7
  | '\x00', _ => 8
  | _, _ => 9
#eval text "a\nb" true
#eval text "a\nb" false
#eval text "🙂" false
#eval text "a" false
#eval character 'a' true
#eval character 'a' false
#eval character '🙂' true
#eval character '\uD800' false
#eval character 'λ' false
"##),
            vec![1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
    });
}

#[test]
fn nested_payloads_captured_arguments_and_fallback_bindings_execute() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
def text : Option String -> Nat
  | .some "yes" => 1
  | .some _ => 2
  | .none => 3
def letter : Option Char -> Nat
  | .some 'y' => 4
  | .some _ => 5
  | .none => 6
def first (bias : Nat) (s : String) : Nat :=
  match s with
  | "yes" => bias
  | _ => bias + 1
def use (f : String -> Nat) : Nat := f "no"
#eval text (.some "yes")
#eval text (.some "no")
#eval text .none
#eval letter (.some 'y')
#eval letter (.some 'n')
#eval letter .none
#eval use (first 10)
#eval first 10 "yes"
"#),
            vec![1, 2, 3, 4, 5, 6, 11, 10]
        );
    });
}

#[test]
fn user_beq_and_decide_names_cannot_redefine_value_patterns() {
    on_stack(|| {
        assert_eq!(
            run(r#"
prelude
import Init.Prelude
instance : BEq String where
  beq _ _ := true
instance : BEq Char where
  beq _ _ := false
namespace Shadow
def decide (p : Prop) [Decidable p] : Bool := false
def word (decide : Nat) (s : String) : Nat :=
  match s with
  | "yes" => decide
  | _ => decide + 1
def letter : Char -> Nat
  | 'y' => 1
  | _ => 2
end Shadow
#eval Shadow.word 5 "yes"
#eval Shadow.word 5 "no"
#eval Shadow.letter 'y'
#eval Shadow.letter 'n'
"#),
            vec![5, 6, 1, 2]
        );
    });
}

#[test]
fn text_patterns_reject_uncovered_domains_ill_typed_rows_and_false_refinements() {
    on_stack(|| {
        let engine = &imported().engine;
        let before = engine.environment().logical_root(&KVMap::new());
        for source in [
            "def bad : String -> Nat | \"x\" => 1",
            "def bad : Char -> Nat | 'x' => 1",
            "def bad : Nat -> Nat | \"x\" => 1 | _ => 2",
            "def bad : String -> Nat | 'x' => 1 | _ => 2",
            "def bad : Char -> Nat | \"x\" => 1 | _ => 2",
            "def bad : Char -> Nat | 'x' => 1 | 0 => 2 | _ => 3",
            "def bad : String -> Nat | \"x\" => true | _ => 2",
            "def bad : String -> Nat | \"x\" => 1 | \"\\x78\" => 2 | _ => 3",
            "def bad : Char -> Nat | 'x' => 1 | '\\x78' => 2 | _ => 3",
            "def bad (s : String) : s = \"x\" := match s with | \"x\" => rfl | _ => rfl",
            "def bad (s : Char) : s = 'x' := match s with | 'x' => rfl | _ => rfl",
            "def bad (s : String) : Nat := match s with | \"x\" => 0 | _ => bad s",
        ] {
            let result = engine.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                )),
            );
            assert!(
                result.is_err(),
                "must reject rather than admit an uncovered or false row: {source}\n{result:?}"
            );
            assert_eq!(before, engine.environment().logical_root(&KVMap::new()));
        }
    });
}

#[test]
fn text_pattern_definitions_remain_kernel_checkable_without_native_evaluation() {
    on_stack(|| {
        let source = r#"
def text : String -> Nat | "x" => 1 | _ => 2
def character : Char -> Nat | 'x' => 1 | _ => 2
theorem text_proof (s : String) : True :=
  match s with | "x" => True.intro | _ => True.intro
theorem character_proof (s : Char) : True :=
  match s with | 'x' => True.intro | _ => True.intro
"#;
        let checked = imported()
            .engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(checked.theorems, 2);
    });
}

#[test]
fn computed_text_matches_are_definitional_proofs() {
    on_stack(|| {
        let source = r#"
def text : String -> Nat | "x" => 1 | _ => 2
example : text "x" = 1 := by rfl
example : text "y" = 2 := by rfl
"#;
        imported()
            .engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
                    Budget::for_stack_bytes(STACK),
                )),
            )
            .unwrap()
            .into_complete()
            .unwrap();
    });
}

struct TextRecursorProblem {
    txn: fln_elab::txn::ElabTxn,
    call: fln::Expr,
    answer: fln::Expr,
    id: fln_core::expr::MVarId,
    budget: fln_elab::constraint::unify::UnificationBudget,
}

fn recursor_problem(text: &str, function_valued: bool) -> TextRecursorProblem {
    use fln_core::expr::{BinderInfo, Expr, Literal, MVarId, NatLit};
    use fln_core::level::Level;
    use fln_elab::constraint::unify::{UnificationBudget, UnificationTransparency};
    use fln_elab::mvar::MetavarKind;
    use fln_elab::txn::ElabTxn;
    let constant = |text: &str| Expr::const_(name(text), vec![]);
    let lam = |label: &str, domain, body| Expr::lam(name(label), domain, body, BinderInfo::Default);
    let nat = constant("Nat");
    let mut txn = ElabTxn::new(imported().engine.environment().clone(), KVMap::new(), 77);
    let id = MVarId(name("minorResult"));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        nat.clone(),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let (result_type, result) = if function_valued {
        (
            Expr::forall_e(name("n"), nat.clone(), nat.clone(), BinderInfo::Default),
            lam("n", nat, Expr::mvar(id.clone())),
        )
    } else {
        (nat, Expr::mvar(id.clone()))
    };
    let motive = lam("s", constant("String"), result_type);
    let minor = lam(
        "bytes",
        constant("ByteArray"),
        lam(
            "valid",
            Expr::app(constant("ByteArray.IsValidUTF8"), Expr::bvar(0).unwrap()),
            result,
        ),
    );
    let mut call = Expr::const_(name("String.rec"), vec![Level::one()]);
    for arg in [motive, minor, Expr::lit(Literal::Str(text.into()))] {
        call = Expr::app(call, arg);
    }
    if function_valued {
        call = Expr::app(call, Expr::lit(Literal::Nat(NatLit::from_u64(41))));
    }
    let answer = Expr::lit(Literal::Nat(NatLit::from_u64(37)));
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(STACK));
    budget.transparency = UnificationTransparency::Default;
    TextRecursorProblem {
        txn,
        call,
        answer,
        id,
        budget,
    }
}

#[test]
fn string_recursor_reduction_solves_an_unknown_minor_result() {
    on_stack(|| {
        for (text, function_valued) in ["", "x", "λ🦀"]
            .into_iter()
            .flat_map(|text| [false, true].map(|f| (text, f)))
        {
            let TextRecursorProblem {
                mut txn,
                call,
                answer,
                id,
                budget,
            } = recursor_problem(text, function_valued);
            let report = txn
                .unify(&call, &answer, budget)
                .unwrap_or_else(|error| panic!("{text:?}: {error:?}"));
            assert_eq!(report.expression_assignments, vec![id.clone()]);
            assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&answer));
            assert_eq!(txn.env, *imported().engine.environment());
        }
    });
}

#[test]
fn string_projections_solve_an_unknown_utf8_payload() {
    on_stack(|| {
        use fln_core::expr::{Expr, Literal, MVarId, NatLit};
        use fln_core::level::Level;
        use fln_elab::constraint::unify::{UnificationBudget, UnificationTransparency};
        use fln_elab::mvar::MetavarKind;
        use fln_elab::txn::ElabTxn;
        let byte = Expr::const_(name("UInt8"), vec![]);
        let list_type = Expr::app(
            Expr::const_(name("List"), vec![Level::zero()]),
            byte.clone(),
        );
        for text in ["", "hello", "λ🦀", "\0é中🦀"] {
            let mut txn = ElabTxn::new(imported().engine.environment().clone(), KVMap::new(), 78);
            txn.budget.max_heartbeats = 2_000_000;
            let id = MVarId(name("bytePayload"));
            txn.mvars.declare(
                id.clone(),
                id.0.clone(),
                list_type.clone(),
                txn.lctx.clone(),
                MetavarKind::Natural,
                0,
                None,
            );
            let receiver = Expr::proj(name("String"), 0, Expr::lit(Literal::Str(text.into())));
            let array = Expr::proj(name("ByteArray"), 0, receiver);
            let expected = Expr::app(
                Expr::app(
                    Expr::const_(name("Array.mk"), vec![Level::zero()]),
                    byte.clone(),
                ),
                Expr::mvar(id.clone()),
            );
            let mut budget = UnificationBudget::new(Budget::for_stack_bytes(STACK));
            budget.transparency = UnificationTransparency::Default;
            // This test reduces the pin's logical UTF-8 model, not the native
            // String adapter. Its dependent payload conversion is expensive;
            // keep the production defaults unchanged and supply an explicit
            // caller budget for these structural comparison cells.
            budget.max_steps = 1_000_000;
            budget.max_visited_nodes = 5_000_000;
            let report = txn
                .unify(&array, &expected, budget)
                .unwrap_or_else(|error| panic!("{text:?}: {error:?}"));
            assert_eq!(report.expression_assignments, vec![id.clone()]);
            let actual = txn.mvars.get_assigned_expr(&id).unwrap().clone();
            let cons = Expr::app(
                Expr::const_(name("List.cons"), vec![Level::zero()]),
                byte.clone(),
            );
            let mut bytes = Expr::app(
                Expr::const_(name("List.nil"), vec![Level::zero()]),
                byte.clone(),
            );
            for value in text.bytes().rev() {
                let value = Expr::app(
                    Expr::const_(name("UInt8.ofNat"), vec![]),
                    Expr::lit(Literal::Nat(NatLit::from_u64(u64::from(value)))),
                );
                bytes = Expr::app(Expr::app(cons.clone(), value), bytes);
            }
            let apply =
                |function: Expr, args: Vec<Expr>| args.into_iter().fold(function, Expr::app);
            let type_ = apply(
                Expr::const_(name("Eq"), vec![Level::one()]),
                vec![list_type.clone(), actual.clone(), bytes],
            );
            let proof = apply(
                Expr::const_(name("Eq.refl"), vec![Level::one()]),
                vec![list_type.clone(), actual],
            );
            let theorem = fln_kernel::Declaration::Thm(fln_env::constants::TheoremVal {
                base: fln_env::constants::ConstantVal {
                    name: name("payloadVerification"),
                    level_params: vec![],
                    type_,
                },
                value: proof,
                all: vec![name("payloadVerification")],
            });
            assert!(
                matches!(
                    fln_kernel::check(&txn.env, &theorem, Budget::for_stack_bytes(STACK)),
                    fln_core::outcome::Outcome::Complete(
                        fln_kernel::verdict::Verdict::Accepted { .. }
                    )
                ),
                "{text:?}"
            );
            assert_eq!(txn.env, *imported().engine.environment());
        }
    });
}

fn unchanged_transaction(actual: &fln_elab::txn::ElabTxn, before: &fln_elab::txn::ElabTxn) {
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.lctx, before.lctx);
    assert_eq!(actual.options, before.options);
    assert_eq!(actual.seed, before.seed);
}

#[test]
fn string_inference_stops_without_publishing_speculative_assignments() {
    on_stack(|| {
        use fln_core::expr::{Expr, Literal, NatLit};
        use fln_elab::constraint::unify::{UnificationError, UnificationTransparency};
        let mut problem = recursor_problem("x", false);
        let before = problem.txn.clone();
        problem.budget.transparency = UnificationTransparency::None;
        assert!(matches!(
            problem
                .txn
                .unify(&problem.call, &problem.answer, problem.budget),
            Err(UnificationError::Deferred(_))
        ));
        unchanged_transaction(&problem.txn, &before);

        let mut problem = recursor_problem("x", false);
        let before = problem.txn.clone();
        problem.budget.max_steps = 1;
        assert!(matches!(
            problem
                .txn
                .unify(&problem.call, &problem.answer, problem.budget),
            Err(UnificationError::StepLimit { limit: 1 })
        ));
        unchanged_transaction(&problem.txn, &before);

        let mut problem = recursor_problem("x", false);
        problem.txn.budget.max_heartbeats = 1;
        let before = problem.txn.clone();
        assert!(matches!(
            problem
                .txn
                .unify(&problem.call, &problem.answer, problem.budget),
            Err(UnificationError::HeartbeatLimit)
        ));
        unchanged_transaction(&problem.txn, &before);

        let mut problem = recursor_problem(&"λ".repeat(2_000), false);
        let before = problem.txn.clone();
        problem.budget.max_visited_nodes = 200;
        assert!(matches!(
            problem
                .txn
                .unify(&problem.call, &problem.answer, problem.budget),
            Err(UnificationError::NodeLimit { .. })
        ));
        unchanged_transaction(&problem.txn, &before);

        let mut problem = recursor_problem(&"x".repeat(2_000), false);
        let before = problem.txn.clone();
        let calls = std::cell::Cell::new(0);
        assert!(matches!(
            problem
                .txn
                .unify_many_with(&[(problem.call, problem.answer)], problem.budget, &|| {
                    calls.set(calls.get() + 1);
                    calls.get() > 100
                }),
            Err(UnificationError::Cancelled)
        ));
        unchanged_transaction(&problem.txn, &before);

        let mut problem = recursor_problem("x", true);
        let before = problem.txn.clone();
        let numeral = |n| Expr::lit(Literal::Nat(NatLit::from_u64(n)));
        assert!(
            problem
                .txn
                .unify_many_with(
                    &[(problem.call, problem.answer), (numeral(1), numeral(2))],
                    problem.budget,
                    &|| false
                )
                .is_err()
        );
        unchanged_transaction(&problem.txn, &before);
        assert!(problem.txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    });
}

#[test]
fn incomplete_or_literal_returning_string_models_do_not_loop_or_infer() {
    on_stack(|| {
        use fln_core::expr::{Expr, ExprNode, Literal};
        use fln_elab::constraint::unify::UnificationError;
        use fln_env::constants::ConstantInfo;
        // Hostile comparison data, never installed in an executable engine or
        // passed off as a newly admitted environment. A successful prefix of a
        // literal expansion must not confer authority on an absent definition.
        for target in [
            "Char.ofNat",
            "String.ofList",
            "String.ofList.literal-return",
        ] {
            let mut problem = recursor_problem("", false);
            let original = problem.txn.env.clone();
            let selected = name(if target.ends_with("literal-return") {
                "String.ofList"
            } else {
                target
            });
            let mut env = fln::Environment::new();
            for (label, _) in original.constants() {
                if label != &selected {
                    env = env.with_entry(original.entry(label).unwrap()).unwrap();
                }
            }
            if target.ends_with("literal-return") {
                let Some(ConstantInfo::Defn(mut value)) = original.find(&selected).cloned() else {
                    panic!("known definition");
                };
                let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    binder_info,
                    ..
                } = value.value.node()
                else {
                    panic!("String.ofList lambda");
                };
                value.value = Expr::lam(
                    binder_name.clone(),
                    binder_type.clone(),
                    Expr::lit(Literal::Str(String::new())),
                    *binder_info,
                );
                env = env.add_decl(ConstantInfo::Defn(value)).unwrap();
            }
            problem.txn.env = env;
            let before = problem.txn.clone();
            assert!(
                matches!(
                    problem
                        .txn
                        .unify(&problem.call, &problem.answer, problem.budget),
                    Err(UnificationError::Deferred(_))
                ),
                "{target}"
            );
            unchanged_transaction(&problem.txn, &before);
        }
    });
}
