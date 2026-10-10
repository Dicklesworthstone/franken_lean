use super::*;
use fln_core::level::Level;
use fln_env::constants::{ConstantVal, ReducibilityHints};

fn nat_type() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}

fn b(index: usize) -> Expr {
    variable(index).unwrap()
}

fn arrow(result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), nat_type(), result, BinderInfo::Default)
}

fn lambda(body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), nat_type(), body, BinderInfo::Default)
}

fn call(label: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments
        .into_iter()
        .fold(Expr::const_(name(label), Vec::new()), Expr::app)
}

fn choose(result: Expr, condition: Expr, yes: Expr, no: Expr) -> Expr {
    let motive = Expr::lam(
        Name::anonymous(),
        Expr::const_(name("Bool"), Vec::new()),
        result,
        BinderInfo::Default,
    );
    [motive, no, yes, condition].into_iter().fold(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        Expr::app,
    )
}

fn pair(label: &str, type_: Expr, logical: Expr, value: Expr) -> (DefinitionVal, DefinitionVal) {
    let logical = DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: Vec::new(),
            type_: type_.clone(),
        },
        value: logical,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    };
    let executable_name = Name::str(logical.base.name.clone(), "_unsafe_rec");
    let executable = DefinitionVal {
        base: ConstantVal {
            name: executable_name.clone(),
            level_params: Vec::new(),
            type_,
        },
        value,
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Partial,
        all: vec![executable_name],
    };
    (logical, executable)
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn admit(pair: (DefinitionVal, DefinitionVal)) -> Engine {
    let engine = Engine::with_source_seed(limits().admission())
        .unwrap()
        .into_complete()
        .unwrap();
    extend(engine, pair)
}

fn extend(mut engine: Engine, pair: (DefinitionVal, DefinitionVal)) -> Engine {
    for declaration in [Declaration::Defn(pair.0), Declaration::Mutual(vec![pair.1])] {
        engine = engine
            .admit_declaration(declaration, &KVMap::new(), limits().admission())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    engine
}

fn recursive_producer() -> (DefinitionVal, DefinitionVal) {
    // make offset n does its recursion before returning the Nat -> Nat
    // callback. Each recursive prefix result is captured once by that callback.
    let callback_type = arrow(nat_type());
    let previous = call("make._unsafe_rec", [b(1), call("Nat.pred", [b(0)])]);
    let recursive = Expr::let_e(
        name("previous"),
        callback_type.clone(),
        previous,
        lambda(call("Nat.add", [Expr::app(b(1), b(0)), nat::literal(1)])),
        false,
    );
    let value = lambda(lambda(choose(
        callback_type,
        call("Nat.beq", [b(0), nat::literal(0)]),
        lambda(call("Nat.add", [b(2), b(0)])),
        recursive,
    )));
    pair(
        "make",
        arrow(arrow(arrow(nat_type()))),
        lambda(lambda(lambda(nat::literal(0)))),
        value,
    )
}

fn returned(engine: &Engine, source: &[u8], expected: &[&str]) {
    let root = engine.logical_root(&KVMap::new());
    let batch = engine
        .execute_source_definitions(&[source], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(batch.executions.len(), expected.len());
    for (execution, expected) in batch.executions.into_iter().zip(expected) {
        let replay =
            execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        for exit in [execution.exit, replay] {
            let VmExit::Returned(value) = exit else {
                panic!("staged producer must return")
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(*expected)
            );
        }
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn recursive_partial_globals_return_reusable_closures_and_replay() {
    let engine = admit(recursive_producer());
    returned(
        &engine,
        b"#eval make 10 3 29\n\
          #eval let f : Nat -> Nat := make 10 3; Nat.add (f 1) (f 2)\n\
          #eval let curried : Nat -> Nat -> Nat := make 10; curried 3 29\n\
          #eval let factory : Nat -> Nat -> Nat -> Nat := make; factory 10 3 29\n\
          #eval (fun f : Nat -> Nat => f 29) (make 10 3)",
        &["42", "29", "42", "42", "42"],
    );
    engine
        .check_source_files(
            &[b"theorem logicalMake : make 10 3 29 = 0 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn nonreturning_prefix_is_evaluated_even_when_the_returned_function_is_unused() {
    let callback_type = arrow(nat_type());
    let value = lambda(Expr::let_e(
        name("never"),
        callback_type.clone(),
        call("spin._unsafe_rec", [b(0)]),
        lambda(nat::literal(42)),
        false,
    ));
    let engine = admit(pair(
        "spin",
        arrow(callback_type),
        lambda(lambda(nat::literal(0))),
        value,
    ));
    let root = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 200;
    for source in [
        b"#eval let ignored : Nat -> Nat := spin 0; 42".as_slice(),
        b"#eval spin 0 5".as_slice(),
    ] {
        assert!(matches!(
            engine
                .execute_source_definitions(&[source], &KVMap::new(), bounded)
                .unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    returned(&engine, b"#eval 42", &["42"]);
}

#[test]
fn zero_argument_partial_prefix_executes_before_returning_its_callback() {
    let callback_type = arrow(nat_type());
    let value = Expr::let_e(
        name("captured"),
        nat_type(),
        call("Nat.add", [nat::literal(20), nat::literal(22)]),
        lambda(call("Nat.add", [b(1), b(0)])),
        false,
    );
    let engine = admit(pair(
        "factory",
        callback_type,
        lambda(nat::literal(0)),
        value,
    ));
    returned(
        &engine,
        b"#eval factory 0\n#eval let f : Nat -> Nat := factory; Nat.add (f 0) (f 1)",
        &["42", "85"],
    );
}

#[test]
fn a_diverging_zero_argument_prefix_cannot_be_delayed_by_an_unused_function_binding() {
    let callback_type = arrow(nat_type());
    let value = Expr::let_e(
        name("never"),
        callback_type.clone(),
        call("spinZero._unsafe_rec", []),
        lambda(nat::literal(42)),
        false,
    );
    let engine = admit(pair(
        "spinZero",
        callback_type,
        lambda(nat::literal(0)),
        value,
    ));
    let root = engine.logical_root(&KVMap::new());
    let mut bounded = limits();
    bounded.vm.max_steps = 200;
    assert!(matches!(
        engine
            .execute_source_definitions(
                &[b"#eval let ignored : Nat -> Nat := spinZero; 42"],
                &KVMap::new(),
                bounded,
            )
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    returned(&engine, b"#eval 42", &["42"]);
}

#[test]
fn universe_specialization_retains_runtime_captures_before_staging() {
    let universe = name("u");
    let carrier = Expr::sort(Level::succ(Level::param(universe.clone())).unwrap());
    let forall =
        |domain, body| Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default);
    let lam = |domain, body| Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default);
    // generic.{u} (A : Type u) (saved : A) (n : Nat) : A -> A
    let type_ = forall(carrier.clone(), forall(b(0), arrow(forall(b(2), b(3)))));
    let logical = lam(carrier.clone(), lam(b(0), lambda(lam(b(2), b(0)))));
    let body = lam(
        carrier,
        lam(
            b(0),
            lambda(Expr::let_e(
                name("paid"),
                nat_type(),
                call("Nat.add", [b(0), nat::literal(1)]),
                lam(b(3), b(3)),
                false,
            )),
        ),
    );
    let (mut logical, mut executable) = pair("generic", type_, logical, body);
    logical.base.level_params.push(universe.clone());
    executable.base.level_params.push(universe);
    let engine = admit((logical, executable));
    returned(
        &engine,
        b"#eval generic Nat 42 3 0\n\
          #eval generic Nat 7 3 0\n\
          #eval let f : Nat -> Nat := generic Nat 42 3; Nat.add (f 0) (f 1)\n\
          #eval let curried : Nat -> Nat -> Nat := generic Nat 42; curried 3 0",
        &["42", "7", "84", "42"],
    );
}

#[test]
fn stage_calls_bind_prefix_arguments_then_result_before_surplus_arguments() {
    let engine = admit(recursive_producer());
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let args = [
        call("firstOperand", [b(0)]),
        call("secondOperand", [b(1)]),
        call("lastOperand", [b(2)]),
    ];
    let value = preparation
        .partial_stage_call(&call("make._unsafe_rec", []), &args)
        .unwrap()
        .unwrap();
    let ExprNode::LetE { value, body, .. } = value.node() else {
        panic!("first operand")
    };
    assert_eq!(*value, call("firstOperand", [b(0)]));
    let ExprNode::LetE { value, body, .. } = body.node() else {
        panic!("second operand")
    };
    assert_eq!(*value, call("secondOperand", [b(2)]));
    let ExprNode::LetE { value, body, .. } = body.node() else {
        panic!("prefix result before the last operand")
    };
    let ExprNode::LetE { value: prefix, .. } = value.node() else {
        panic!("typed prefix result")
    };
    let (head, args) = preparation.spine(prefix).unwrap();
    assert!(matches!(head.node(), ExprNode::Const { name, .. }
        if preparation.is_partial_stage(name)));
    assert_eq!(args, [b(1), b(0)]);
    let ExprNode::LetE { value, .. } = body.node() else {
        panic!("last operand follows the prefix")
    };
    assert_eq!(*value, call("lastOperand", [b(5)]));
}

#[test]
fn failed_stage_capacity_does_not_publish_an_entry_and_retry_is_deterministic() {
    let engine = extend(
        admit(recursive_producer()),
        pair(
            "other",
            arrow(arrow(arrow(nat_type()))),
            lambda(lambda(lambda(nat::literal(0)))),
            lambda(lambda(call("make._unsafe_rec", [b(1), b(0)]))),
        ),
    );
    let head = call("make._unsafe_rec", []);
    let args = [nat::literal(10), nat::literal(3), nat::literal(29)];
    let mut bounded = IngressLimits::default();
    bounded.fir.max_functions = 1;
    let mut preparation = Preparation::new(engine.environment(), bounded);
    preparation
        .partial_stage_call(&head, &args)
        .unwrap()
        .unwrap();
    assert_eq!(preparation.partial_stages.entries.len(), 1);
    assert!(matches!(
        preparation.partial_stage_call(&call("other._unsafe_rec", []), &args),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: 1,
            observed: 2,
        })
    ));
    assert_eq!(preparation.partial_stages.entries.len(), 1);
    assert!(
        !preparation
            .partial_stages
            .origins
            .contains_key(&name("other._unsafe_rec"))
    );
    let mut fresh = Preparation::new(engine.environment(), IngressLimits::default());
    let first = fresh.partial_stage_call(&head, &args).unwrap().unwrap();
    assert_eq!(fresh.partial_stages.entries.len(), 1);
    let again = fresh.partial_stage_call(&head, &args).unwrap().unwrap();
    assert_eq!(first, again);
    assert_eq!(fresh.partial_stages.entries.len(), 1);
    let mut retry = Preparation::new(engine.environment(), IngressLimits::default());
    assert_eq!(
        first,
        retry.partial_stage_call(&head, &args).unwrap().unwrap()
    );
}

#[test]
fn generated_entry_collision_refuses_without_publishing_a_stage() {
    let mut engine = admit(recursive_producer());
    engine = engine
        .admit_declaration(
            Declaration::Axiom(fln_env::constants::AxiomVal {
                base: ConstantVal {
                    name: Name::num(name_of_stages(), 0),
                    level_params: Vec::new(),
                    type_: nat_type(),
                },
                is_unsafe: false,
            }),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = engine.logical_root(&KVMap::new());
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    assert!(matches!(
        preparation.partial_stage_call(
            &call("make._unsafe_rec", []),
            &[nat::literal(10), nat::literal(3), nat::literal(29)],
        ),
        Err(IngressError::UnsupportedNode {
            kind: "partial stage name collision"
        })
    ));
    assert!(preparation.partial_stages.entries.is_empty());
    assert!(preparation.partial_stages.origins.is_empty());
    assert!(preparation.partial_stages.names.is_empty());
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    returned(&engine, b"#eval 42", &["42"]);
}
