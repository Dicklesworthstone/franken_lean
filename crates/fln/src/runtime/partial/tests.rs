use super::*;
use fln_core::level::Level;
use fln_env::constants::{ConstantVal, OpaqueVal, ReducibilityHints};

pub(super) fn pair(label: &str) -> (OpaqueVal, DefinitionVal) {
    let logical = name(label);
    let type_ = Expr::forall_e(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        Expr::const_(name("Nat"), vec![]),
        BinderInfo::Default,
    );
    let body = |n| {
        Expr::lam(
            Name::anonymous(),
            Expr::const_(name("Nat"), vec![]),
            nat::literal(n),
            BinderInfo::Default,
        )
    };
    let executable = Name::str(logical.clone(), "_unsafe_rec");
    (
        OpaqueVal {
            base: ConstantVal {
                name: logical.clone(),
                level_params: vec![],
                type_: type_.clone(),
            },
            value: body(0),
            is_unsafe: false,
            all: vec![logical],
        },
        DefinitionVal {
            base: ConstantVal {
                name: executable.clone(),
                level_params: vec![],
                type_,
            },
            value: body(42),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Partial,
            all: vec![executable],
        },
    )
}

fn world(logical: OpaqueVal, executable: DefinitionVal) -> Environment {
    Environment::new()
        .add_decl(ConstantInfo::Opaque(logical))
        .unwrap()
        .add_decl(ConstantInfo::Defn(executable))
        .unwrap()
}

#[test]
fn executable_partial_body_never_becomes_a_logical_reduction() {
    let (logical, executable) = pair("loop");
    let environment = world(logical.clone(), executable.clone());
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    for label in [&logical.base.name, &executable.base.name] {
        assert_eq!(
            preparation.executable_definition(label).unwrap(),
            Some(executable.clone())
        );
        let term = Expr::app(Expr::const_(label.clone(), vec![]), nat::literal(1));
        assert_eq!(preparation.type_head(&term).unwrap(), term);
    }
    assert_ne!(logical.value, executable.value);
}

#[test]
fn partial_linkage_requires_both_checked_halves_and_exact_telescope() {
    let (logical, executable) = pair("loop");
    let environment = Environment::new()
        .add_decl(ConstantInfo::Opaque(logical.clone()))
        .unwrap();
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(&logical.base.name)
            .unwrap()
            .is_none()
    );
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(executable.clone()))
        .unwrap();
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(&executable.base.name)
            .unwrap()
            .is_none()
    );
    for mutation in 0..6 {
        let mut changed_logical = logical.clone();
        let mut changed_executable = executable.clone();
        match mutation {
            0 => changed_logical.is_unsafe = true,
            1 => changed_executable.safety = DefinitionSafety::Unsafe,
            2 => changed_executable.base.type_ = Expr::const_(name("Nat"), vec![]),
            3 => changed_executable.base.level_params.push(name("u")),
            4 => changed_executable.all = vec![name("unrelated")],
            5 => changed_logical.all.clear(),
            _ => unreachable!(),
        }
        let environment = world(changed_logical, changed_executable);
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert!(
            preparation
                .executable_definition(&logical.base.name)
                .unwrap()
                .is_none(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn mutual_partial_linkage_validates_every_member_before_selecting_code() {
    let (mut first, mut first_impl) = pair("first");
    let (mut second, mut second_impl) = pair("second");
    first.all.push(second.base.name.clone());
    second.all = first.all.clone();
    first_impl.all.push(second_impl.base.name.clone());
    second_impl.all = first_impl.all.clone();
    let environment = world(first.clone(), first_impl.clone())
        .add_decl(ConstantInfo::Opaque(second.clone()))
        .unwrap()
        .add_decl(ConstantInfo::Defn(second_impl.clone()))
        .unwrap();
    assert_eq!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(&first.base.name)
            .unwrap(),
        Some(first_impl.clone())
    );
    second_impl.base.type_ = Expr::sort(Level::one());
    let environment = world(first.clone(), first_impl)
        .add_decl(ConstantInfo::Opaque(second))
        .unwrap()
        .add_decl(ConstantInfo::Defn(second_impl))
        .unwrap();
    assert!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(&first.base.name)
            .unwrap()
            .is_none()
    );
}

#[test]
fn partial_linkage_is_metered_and_failed_lookup_does_not_change_the_world() {
    let (logical, executable) = pair("loop");
    let environment = world(logical.clone(), executable.clone());
    let limits = IngressLimits {
        max_nodes: 1,
        ..IngressLimits::default()
    };
    assert!(matches!(
        Preparation::new(&environment, limits).executable_definition(&logical.base.name),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
    assert_eq!(
        Preparation::new(&environment, IngressLimits::default())
            .executable_definition(&logical.base.name)
            .unwrap(),
        Some(executable)
    );
}

#[test]
fn admitted_mutual_partials_execute_real_bodies_and_budget_failures_are_atomic() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let mut engine = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let (mut first, mut first_impl) = pair("first");
    let (mut second, mut second_impl) = pair("second");
    first.all.push(second.base.name.clone());
    second.all = first.all.clone();
    first_impl.all.push(second_impl.base.name.clone());
    second_impl.all = first_impl.all.clone();
    let body = |next: Name, answer| {
        let n = Expr::bvar(0).unwrap();
        let call = Expr::app(
            Expr::const_(next, vec![]),
            Expr::app(Expr::const_(name("Nat.pred"), vec![]), n.clone()),
        );
        let nat_type = Expr::const_(name("Nat"), vec![]);
        let motive = Expr::lam(
            Name::anonymous(),
            Expr::const_(name("Bool"), vec![]),
            nat_type.clone(),
            BinderInfo::Default,
        );
        let decision = Expr::app(
            Expr::app(Expr::const_(name("Nat.beq"), vec![]), n),
            nat::literal(0),
        );
        let body = [motive, call, nat::literal(answer), decision]
            .into_iter()
            .fold(
                Expr::const_(name("Bool.rec"), vec![Level::one()]),
                Expr::app,
            );
        Expr::lam(Name::anonymous(), nat_type, body, BinderInfo::Default)
    };
    first_impl.value = body(second_impl.base.name.clone(), 17);
    second_impl.value = body(first_impl.base.name.clone(), 42);
    for logical in [first, second] {
        engine = engine
            .admit_declaration(Declaration::Opaque(logical), &options, limits.admission())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    let admission = engine
        .admit_declaration(
            Declaration::Mutual(vec![first_impl, second_impl]),
            &options,
            limits.admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        admission.checker.ground,
        CheckerAdmissionGround::PartialQuarantine
    );
    let engine = admission.engine;
    let root = engine.logical_root(&options);
    let source = b"#eval first 0\n#eval first 3\n#eval second 2";
    let run = || {
        engine
            .execute_source_definitions(&[source], &options, limits)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let execution = run();
    for (result, expected) in execution.executions.iter().zip(["17", "42", "42"]) {
        let VmExit::Returned(value) = &result.exit else {
            panic!("no result");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
    let mut bounded = limits;
    bounded.vm.max_steps = 100;
    assert!(matches!(
        engine
            .execute_source_definitions(&[b"#eval first 10000"], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
    let retry = run();
    assert_eq!(
        execution.executions[1].flbc_artifact,
        retry.executions[1].flbc_artifact
    );
}

#[test]
fn nonreturning_partial_prefix_is_not_delayed_until_its_callback_is_used() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let mut engine = Engine::with_source_seed(limits.admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let (mut logical, mut executable) = pair("makeStrict");
    let natural = Expr::const_(name("Nat"), vec![]);
    let callback = logical.base.type_.clone();
    logical.base.type_ = Expr::forall_e(
        Name::anonymous(),
        natural.clone(),
        callback,
        BinderInfo::Default,
    );
    logical.value = Expr::lam(
        Name::anonymous(),
        natural.clone(),
        logical.value,
        BinderInfo::Default,
    );
    executable.base.type_ = logical.base.type_.clone();
    // makeStrict n recurses before producing its Nat -> Nat result.
    // Binding that result must never turn into a returned 42 merely because
    // the caller does not subsequently invoke the callback.
    executable.value = Expr::lam(
        Name::anonymous(),
        natural,
        Expr::app(
            Expr::const_(executable.base.name.clone(), vec![]),
            Expr::bvar(0).unwrap(),
        ),
        BinderInfo::Default,
    );
    for declaration in [
        Declaration::Opaque(logical),
        Declaration::Mutual(vec![executable]),
    ] {
        engine = engine
            .admit_declaration(declaration, &options, limits.admission())
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    let root = engine.logical_root(&options);
    let error = engine
        .execute_source_definitions(
            &[b"#eval let ignored : Nat -> Nat := makeStrict 0; 42"],
            &options,
            limits,
        )
        .expect_err("a nonreturning partial prefix cannot produce an unused callback");
    let EngineExecutionError::BatchCommand { error, .. } = error else {
        panic!("unexpected refusal: {error:?}");
    };
    assert!(matches!(
        *error,
        EngineExecutionError::Ingress(IngressError::UnsupportedNode {
            kind: "partial function-producing stage"
        })
    ));
    assert_eq!(engine.logical_root(&options), root);
    let retry = engine
        .execute_source_definitions(&[b"#eval 42"], &options, limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &retry.executions[0].exit else {
        panic!("clean retry did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("42")
    );
}
