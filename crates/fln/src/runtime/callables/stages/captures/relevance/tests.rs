use super::*;
use fln_core::diag::ResourceReason;
use fln_core::outcome::InconclusiveCause;

fn c(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn signature(parameters: Vec<ValueType>, result: ValueType) -> ClosureSignature {
    ClosureSignature {
        parameter_ownership: borrowed_runtime_parameters(parameters.len()).unwrap(),
        parameters,
        result,
        result_ownership: result_ownership(result),
    }
}

fn stages(preparation: &mut Preparation<'_>) -> (ValueType, ValueType) {
    let tail = preparation
        .stage_interface(signature(vec![ValueType::Nat], ValueType::Nat))
        .unwrap();
    let staged = preparation
        .stage_interface(signature(vec![ValueType::Nat], tail))
        .unwrap();
    let flat = preparation
        .stage_interface(signature(vec![ValueType::Nat; 2], ValueType::Nat))
        .unwrap();
    (staged, flat)
}

fn lambda(preparation: &mut Preparation<'_>, label: Name, body: Expr, result: ValueType) -> Expr {
    let expression = Expr::lam(label, c("Nat"), body, BinderInfo::Default);
    preparation.lambdas.push(LambdaBinding {
        lambda: expression.clone(),
        parameters: vec![ValueType::Nat],
        parameter_ownership: borrowed_runtime_parameters(1).unwrap(),
        result,
        result_ownership: result_ownership(result),
        recursion: LambdaRecursion::NonRecursive,
    });
    expression
}

fn local(preparation: &mut Preparation<'_>, body: Expr, result: ValueType) -> Expr {
    let label = Name::num(name("_fln_runtime_local"), preparation.lambdas.len() as u64);
    lambda(preparation, label, body, result)
}

fn function(body: Expr, parameters: Vec<ValueType>) -> FunctionBinding {
    FunctionBinding {
        name: name("captureCatalog"),
        universe_arity: 0,
        parameter_ownership: borrowed_runtime_parameters(parameters.len()).unwrap(),
        parameters,
        result: ValueType::Nat,
        result_ownership: result_ownership(ValueType::Nat),
        body,
    }
}

fn scan(
    preparation: &mut Preparation<'_>,
    expression: &Expr,
    parameters: &[ValueType],
) -> Result<bool, IngressError> {
    let lambdas = LambdaIndex::new(preparation)?;
    contains_candidate(preparation, expression, parameters, &lambdas)
}

#[test]
fn catalog_scopes_still_propagate_required_capture_stages_through_fixed_lambdas() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let (staged, flat) = stages(&mut preparation);
    // The first local is beneath both an alias and a fixed lambda parameter.
    // The second argument must restore the function's original two captures.
    let first = local(&mut preparation, b(2), flat);
    let second = local(&mut preparation, b(1), flat);
    let fixed = lambda(&mut preparation, name("fixedBranch"), first, flat);
    let alias =
        |index, value| Expr::let_e(name("alias"), c("unusedAnnotation"), b(index), value, false);
    let body = Expr::app(
        Expr::app(
            c("unknownConsumer"),
            alias(
                1,
                Expr::proj(name("UnknownRecord"), 0, Expr::mdata(KVMap::new(), fixed)),
            ),
        ),
        alias(0, second),
    );
    let functions = [function(body, vec![staged, flat])];
    let original = functions.clone();
    assert!(
        scan(
            &mut preparation,
            &functions[0].body,
            &functions[0].parameters
        )
        .unwrap()
    );
    preparation.refine_function_captures(&functions).unwrap();
    assert_eq!(preparation.lambdas[0].result, staged);
    assert_eq!(preparation.lambdas[1].result, flat);
    assert_eq!(
        preparation.lambdas[2].result, flat,
        "a fixed callable ABI is not refined"
    );
    assert_eq!(functions, original);
    assert!(
        preparation
            .lambdas
            .iter()
            .all(|binding| binding.result_ownership == result_ownership(binding.result))
    );
}

#[test]
fn scalar_callback_catalogs_avoid_unused_interface_discovery_under_a_real_bound() {
    let environment = Environment::new();
    let limits = IngressLimits {
        max_nodes: 1_500,
        ..IngressLimits::default()
    };
    let mut preparation = Preparation::new(&environment, limits);
    // These are descriptive test rows, not declarations or execution authority.
    // Repeated scalar-result callbacks cannot refine any of them.
    preparation.interfaces = (2..=81)
        .map(|arity| signature(vec![ValueType::Nat; arity], ValueType::Nat))
        .collect();
    let selected = local(&mut preparation, b(0), ValueType::Nat);
    let body = (0..64).fold(c("unknownConsumer"), |head, _| {
        Expr::app(head, selected.clone())
    });
    let functions = [function(body, vec![])];
    let interfaces = preparation.interfaces.clone();
    let lambdas = preparation.lambdas.clone();
    preparation.refine_function_captures(&functions).unwrap();
    assert!(preparation.visited < limits.max_nodes);
    assert_eq!(preparation.interfaces, interfaces);
    assert_eq!(preparation.lambdas, lambdas);

    let mut full = Preparation::new(&environment, limits);
    full.interfaces = interfaces;
    full.lambdas = lambdas;
    let index = LambdaIndex::new(&mut full).unwrap();
    assert!(
        matches!(
            full.captured_result_in(&functions[0].body, &[], &index),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 1_500,
                observed: 1_501
            })
        ),
        "the comparison performs actual discarded type discovery under the same bound"
    );
}

#[test]
fn unknown_and_recursive_lambdas_keep_the_existing_representation_boundary() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    let (_, flat) = stages(&mut preparation);
    let nested = local(&mut preparation, b(1), flat);
    let unknown = Expr::lam(
        name("unregistered"),
        c("Nat"),
        nested.clone(),
        BinderInfo::Default,
    );
    assert!(!scan(&mut preparation, &unknown, &[]).unwrap());
    assert!(matches!(
        fln_comp::ingress::lower_closed_expr_with_lambdas(
            &Expr::app(unknown, nat::literal(0)),
            &[],
            &[],
            &[],
            &[],
            IngressLimits::default()
        ),
        Err(IngressError::UnknownLambda { .. })
    ));
    for recursion in [
        LambdaRecursion::SelfBinder,
        LambdaRecursion::MutualMember {
            group: 0,
            member: 0,
            members: 2,
        },
    ] {
        // This is a scope-analysis fixture only. Executable ingress remains
        // responsible for the whole recursive group and synthetic ABI.
        let recursive = lambda(&mut preparation, name("recursive"), nested.clone(), flat);
        preparation.lambdas.last_mut().unwrap().recursion = recursion;
        let original = preparation.lambdas.clone();
        preparation.limits.max_context_depth = 0;
        assert!(!scan(&mut preparation, &recursive, &[]).unwrap());
        preparation
            .refine_function_captures(&[function(recursive, vec![])])
            .unwrap();
        assert_eq!(preparation.lambdas, original);
        preparation.limits.max_context_depth = IngressLimits::default().max_context_depth;
    }
}

#[test]
fn skipped_bodies_still_check_incoming_depth_nested_scopes_spines_and_prefixes() {
    let environment = Environment::new();
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    preparation.limits.max_context_depth = 1;
    assert_eq!(
        scan(&mut preparation, &b(0), &[ValueType::Nat; 2]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 1,
            observed: 2,
        })
    );
    let fixed = lambda(&mut preparation, name("fixed"), b(0), ValueType::Nat);
    let nested = Expr::let_e(name("alias"), c("Nat"), b(0), fixed.clone(), false);
    preparation.limits.max_context_depth = 2;
    assert_eq!(
        scan(&mut preparation, &nested, &[ValueType::Nat]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ContextDepth,
            limit: 2,
            observed: 3,
        })
    );
    preparation.limits.max_context_depth = 3;
    assert!(!scan(&mut preparation, &nested, &[ValueType::Nat]).unwrap());

    preparation.limits.max_application_args = 1;
    let application = Expr::app(Expr::app(c("unknown"), nat::literal(0)), nat::literal(1));
    assert_eq!(
        scan(&mut preparation, &application, &[]),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ApplicationArguments,
            limit: 1,
            observed: 2,
        })
    );
    preparation.limits.max_application_args = 2;
    assert!(!scan(&mut preparation, &application, &[]).unwrap());

    preparation.lambdas[0].parameters.clear();
    assert_eq!(
        scan(&mut preparation, &fixed, &[]),
        Err(unsupported("empty captured callback signature"))
    );
    preparation.lambdas[0].parameters = vec![ValueType::Nat; 2];
    assert_eq!(
        scan(&mut preparation, &fixed, &[]),
        Err(unsupported("captured callback lambda spine"))
    );
    preparation.lambdas[0].parameters = vec![ValueType::Nat];
    assert!(!scan(&mut preparation, &fixed, &[]).unwrap());

    // Finding an earlier candidate cannot hide a later malformed sibling:
    // the positive scan falls back to the entire original capture analysis.
    let (_, flat) = stages(&mut preparation);
    let candidate = local(&mut preparation, b(0), flat);
    preparation.lambdas[0].parameters.clear();
    let body = Expr::app(Expr::app(c("unknown"), candidate), fixed);
    assert_eq!(
        preparation.refine_function_captures(&[function(body, vec![])]),
        Err(unsupported("empty captured callback signature"))
    );
}

#[test]
fn deep_negative_scans_use_bounded_heap_work_and_retry_without_metadata_changes() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let environment = Environment::new();
            let mut body = b(0);
            for _ in 0..2_000 {
                body = Expr::let_e(Name::anonymous(), c("Nat"), c("strictUnknown"), body, false);
            }
            let functions = [function(body, vec![])];
            let original = functions.clone();
            let mut measured = Preparation::new(&environment, IngressLimits::default());
            measured.refine_function_captures(&functions).unwrap();
            let required = measured.visited;
            assert!(required > 2_000);
            for max_nodes in [0, required - 1] {
                let mut bounded = Preparation::new(
                    &environment,
                    IngressLimits {
                        max_nodes,
                        ..IngressLimits::default()
                    },
                );
                assert_eq!(
                    bounded.refine_function_captures(&functions),
                    Err(IngressError::ResourceLimit {
                        resource: IngressResource::Nodes,
                        limit: max_nodes,
                        observed: max_nodes + 1,
                    })
                );
                assert!(bounded.interfaces.is_empty());
                assert!(bounded.lambdas.is_empty());
                bounded.limits.max_nodes = IngressLimits::default().max_nodes;
                bounded.refine_function_captures(&functions).unwrap();
                assert!(bounded.interfaces.is_empty());
                assert!(bounded.lambdas.is_empty());
            }
            assert_eq!(functions, original, "strict initializers are only scanned");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn global_aliases_and_captured_stages_keep_owned_results_strict_work_and_replay() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let definitions = r#"
def relevanceSpend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Nat.succ (relevanceSpend k)
def relevanceAlias (cost : Nat) (text : String) : String :=
  let paid : Nat := relevanceSpend cost
  let renderer : String -> String := String.append text
  let alias : String -> String := renderer
  String.append (alias "😀") (String.append "\x00" "done")
def relevanceStages (text : String) : String :=
  let f : String -> String -> String -> String := (by intro x; let a := text ++ x; intro y; let z := a ++ y; intro w; exact z ++ w)
  let g := f "😀"
  let keep : Nat -> String -> String -> String := (by let marker := String.length text; exact fun ignored => (let alias := g; alias))
  let h := keep 0
  h "\x00" "done"
"#;
    let engine = engine
        .check_source_files(
            &[definitions.as_bytes()],
            &options,
            SourceCheckLimits::new(limits.admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&options);
    let run = |source: &str| {
        let complete = engine
            .execute_source_definitions(&[source.as_bytes()], &options, limits)
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
        let execution = complete.executions.last().unwrap();
        assert_eq!(
            closed_vm_value(&execution.exit).unwrap(),
            Some(ClosedVmValue::String("λ😀\0done".to_owned()))
        );
        let VmExit::Returned(returned) = &execution.exit else {
            panic!("native string result");
        };
        let replay = execute_flbc_artifact(
            &execution.flbc_artifact,
            &options,
            FlbcExecutionLimits::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
        assert_eq!(
            closed_vm_value(&replay).unwrap(),
            Some(ClosedVmValue::String("λ😀\0done".to_owned()))
        );
        let VmExit::Returned(replayed) = replay else {
            panic!("canonical string replay");
        };
        assert_eq!(replayed.usage, returned.usage);
        (returned.usage.steps, execution.flbc_artifact.clone())
    };
    let idle_source = "#eval relevanceAlias 0 \"λ\"";
    let busy_source = "#eval relevanceAlias 30 \"λ\"";
    let (idle, artifact) = run(idle_source);
    let (busy, _) = run(busy_source);
    assert!(busy > idle + 30, "unused strict work still executes");
    assert_eq!(run(idle_source), (idle, artifact));
    let staged = "#eval relevanceStages \"λ\"";
    assert_eq!(run(staged), run(staged));
    let mut bounded = limits;
    bounded.vm.max_steps = idle;
    assert!(matches!(
        engine.execute_source_definitions(&[busy_source.as_bytes()], &options, bounded).unwrap(),
        Outcome::Inconclusive(stop) if matches!(&stop.cause,
            InconclusiveCause::ResourceExhausted { usage }
                if usage.reason == ResourceReason::ExecutionSteps
                    && usage.allowed == idle && usage.observed == idle + 1)
    ));
    assert_eq!(run(idle_source).0, idle);
    assert_eq!(engine.logical_root(&options), root);
}
