//! The pin also pairs safe total definitions with Partial executable companions.
//! Logical checking and native execution must keep their respective meanings.
use super::*;
use fln_env::constants::ReducibilityHints;

fn pair(label: &str) -> (DefinitionVal, DefinitionVal) {
    let (logical, executable) = super::tests::pair(label);
    (
        DefinitionVal {
            base: logical.base,
            value: logical.value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: logical.all,
        },
        executable,
    )
}

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn admitted(pairs: &[(DefinitionVal, DefinitionVal)]) -> Engine {
    let mut engine = Engine::with_source_seed(limits().admission())
        .unwrap()
        .into_complete()
        .unwrap();
    for (logical, executable) in pairs {
        for declaration in [
            Declaration::Defn(logical.clone()),
            Declaration::Mutual(vec![executable.clone()]),
        ] {
            engine = engine
                .admit_declaration(declaration, &KVMap::new(), limits().admission())
                .unwrap()
                .into_complete()
                .unwrap()
                .engine;
        }
    }
    engine
}

fn executed(engine: &Engine, source: &[u8], expected: &str) {
    let root = engine.logical_root(&KVMap::new());
    let batch = engine
        .execute_source_definitions(&[source], &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(!batch.executions.is_empty());
    for execution in batch.executions {
        for exit in [
            execution.exit,
            execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap(),
        ] {
            let VmExit::Returned(value) = exit else {
                panic!("native result")
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(expected)
            );
        }
    }
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn safe_recursive_companion_executes_and_replays_without_changing_logical_reduction() {
    let (logical, executable) = pair("total");
    let engine = admitted(&[(logical.clone(), executable.clone())]);
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let call = Expr::app(
        Expr::const_(logical.base.name.clone(), vec![]),
        nat::literal(7),
    );
    assert_eq!(preparation.type_head(&call).unwrap(), nat::literal(0));
    for requested in [&logical.base.name, &executable.base.name] {
        assert_eq!(
            preparation.executable_definition(requested).unwrap(),
            Some(executable.clone())
        );
    }
    engine
        .check_source_files(
            &[b"theorem logicalTotal : total 7 = 0 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    executed(
        &engine,
        b"#eval total 7\n#eval let f : Nat -> Nat := total; f 3",
        "42",
    );
}

#[test]
fn safe_companions_require_matching_safe_logical_and_partial_group_members() {
    let (logical, executable) = pair("total");
    let lone = Environment::new()
        .add_decl(ConstantInfo::Defn(logical.clone()))
        .unwrap();
    assert_eq!(
        Preparation::new(&lone, IngressLimits::default())
            .executable_definition(&logical.base.name)
            .unwrap(),
        Some(logical.clone())
    );
    for mutation in 0..7 {
        let mut logical = logical.clone();
        let mut executable = executable.clone();
        match mutation {
            0 => logical.safety = DefinitionSafety::Unsafe,
            1 => executable.safety = DefinitionSafety::Unsafe,
            2 => executable.base.type_ = Expr::const_(name("Nat"), vec![]),
            3 => executable.base.level_params.push(name("u")),
            4 => executable.all = vec![name("unrelated")],
            5 => logical.all.clear(),
            6 => {
                logical.all.push(name("missing"));
                executable.all.push(name("missing._unsafe_rec"));
            }
            _ => unreachable!(),
        }
        let environment = Environment::new()
            .add_decl(ConstantInfo::Defn(logical.clone()))
            .unwrap()
            .add_decl(ConstantInfo::Defn(executable.clone()))
            .unwrap();
        for requested in [&logical.base.name, &executable.base.name] {
            assert!(
                Preparation::new(&environment, IngressLimits::default())
                    .executable_definition(requested)
                    .unwrap()
                    .is_none(),
                "mutation {mutation}"
            );
        }
    }
}

#[test]
fn a_staged_logical_producer_cannot_bypass_a_mismatching_present_companion() {
    let (mut logical, executable) = pair("make");
    logical.base.type_ = Expr::forall_e(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        logical.base.type_,
        BinderInfo::Default,
    );
    logical.value = Expr::lam(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        Expr::let_e(
            Name::anonymous(),
            Expr::const_(name("Nat"), vec![]),
            nat::literal(0),
            logical.value,
            false,
        ),
        BinderInfo::Default,
    );
    let engine = admitted(&[(logical, executable)]);
    let error = engine
        .execute_source_definitions(&[b"#eval make 20 22"], &KVMap::new(), limits())
        .expect_err("a logical callback body cannot hide invalid executable linkage");
    assert!(format!("{error:?}").contains("invalid recursive executable companion"));
}

#[test]
fn recursive_body_references_observe_parent_implemented_by_and_detect_alias_cycles() {
    let (first, mut first_impl) = pair("first");
    let (second, mut second_impl) = pair("second");
    let (mut target, _) = pair("target");
    target.value = second_impl.value.clone();
    second_impl.value = Expr::lam(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        nat::literal(17),
        BinderInfo::Default,
    );
    first_impl.value = Expr::lam(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        Expr::app(
            Expr::const_(second_impl.base.name.clone(), vec![]),
            Expr::bvar(0).unwrap(),
        ),
        BinderInfo::Default,
    );
    let mut engine = admitted(&[(second.clone(), second_impl.clone()), (first, first_impl)]);
    engine = engine
        .admit_declaration(
            Declaration::Defn(target.clone()),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    engine.environment = fln_elab::implemented_by::register(
        engine.environment(),
        &second.base.name,
        &target.base.name,
    )
    .unwrap();
    executed(&engine, b"#eval first 3", "42");

    let mut cyclic = admitted(&[(second.clone(), second_impl.clone())]);
    cyclic.environment = fln_elab::implemented_by::register(
        cyclic.environment(),
        &second.base.name,
        &second_impl.base.name,
    )
    .unwrap();
    let error = cyclic
        .execute_source_definitions(&[b"#eval second 3"], &KVMap::new(), limits())
        .expect_err("companion alias edges participate in replacement cycle detection");
    assert!(format!("{error:?}").contains("implemented_by recursive companion cycle"));
}

#[test]
fn parent_extern_contracts_keep_precedence_over_recursive_companions() {
    let (logical, executable) = pair("total");
    let mut engine = admitted(&[(logical.clone(), executable)]);
    engine.environment = fln_elab::externs::register(
        engine.environment(),
        &logical.base.name,
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: "unavailable_foreign_total".to_owned(),
        }],
    )
    .unwrap();
    let error = engine
        .execute_source_definitions(&[b"#eval total 3"], &KVMap::new(), limits())
        .expect_err("an unknown parent extern cannot disappear behind a companion name");
    assert!(
        format!("{error:?}").contains("native extern attribute does not match the supported ABI")
    );

    let mut native = Engine::with_source_seed(limits().admission())
        .unwrap()
        .into_complete()
        .unwrap();
    let Some(ConstantInfo::Defn(add)) = native.environment().find(&name("Nat.add")) else {
        panic!("checked addition definition")
    };
    let mut companion = add.clone();
    companion.base.name = name("Nat.add._unsafe_rec");
    companion.safety = DefinitionSafety::Partial;
    companion.all = vec![companion.base.name.clone()];
    companion.value = Expr::lam(
        Name::anonymous(),
        Expr::const_(name("Nat"), vec![]),
        Expr::lam(
            Name::anonymous(),
            Expr::const_(name("Nat"), vec![]),
            nat::literal(7),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    native = native
        .admit_declaration(
            Declaration::Mutual(vec![companion]),
            &KVMap::new(),
            limits().admission(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    native.environment = fln_elab::externs::register(
        native.environment(),
        &name("Nat.add"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: "lean_nat_add".to_owned(),
        }],
    )
    .unwrap();
    executed(&native, b"#eval Nat.add 20 22", "42");
    let mut preparation = Preparation::new(native.environment(), IngressLimits::default());
    assert_eq!(
        preparation
            .recursive_companion_target(&name("Nat.add._unsafe_rec"))
            .unwrap(),
        Some(name("Nat.add"))
    );
    assert_eq!(
        preparation
            .recursive_companion_target(&name("Nat.add"))
            .unwrap(),
        None
    );
}
