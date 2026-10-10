//! Native Nat discrimination is independent of executable source equality.
use super::*;
use fln_env::constants::{DefinitionSafety, ReducibilityHints};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(4 * 1024 * 1024))
}

fn admit(engine: Engine, declaration: Declaration) -> Engine {
    engine
        .admit_declaration(declaration, &KVMap::new(), limits().admission())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn minimal_engine() -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::nat_pred_seed_declaration(),
    ] {
        engine = admit(engine, declaration);
    }
    engine
}

fn execute(engine: &Engine, source: &str, expected: &str) {
    let options = KVMap::new();
    let original = engine.logical_root(&options);
    let batch = engine
        .execute_source_definitions(&[source.as_bytes()], &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
    let execution = batch.executions.last().unwrap();
    let program =
        fln_comp::flbc::decode_canonical(&execution.flbc_artifact, Default::default()).unwrap();
    assert_eq!(
        fln_comp::flbc::encode_canonical(&program, Default::default()).unwrap(),
        execution.flbc_artifact
    );
    let replay = execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    for exit in [&execution.exit, &replay] {
        let VmExit::Returned(value) = exit else {
            panic!("expected native return: {exit:?}");
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected),
            "{source}"
        );
    }
    assert_eq!(engine.logical_root(&options), original);
}

#[test]
fn nat_recursion_needs_no_public_equality_or_boolean_family() {
    let engine = minimal_engine();
    assert!(!engine.environment().contains(&name("Nat.beq")));
    assert!(!engine.environment().contains(&name("Bool")));
    for (source, expected) in [
        ("#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => 99) 0", "42"),
        ("#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => 99) 1", "99"),
        ("#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => ih) 4", "42"),
        (
            "#eval @Nat.rec (fun _ => Nat -> Nat) (fun x => x) (fun n ih x => ih x) 4 42",
            "42",
        ),
        (
            "#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => n) 18446744073709551617",
            "18446744073709551616",
        ),
    ] {
        execute(&engine, source, expected);
    }
}

fn equality_with_companion() -> Engine {
    let mut engine = minimal_engine();
    for declaration in [
        fln_elab::seed::bool_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
        fln_elab::seed::rfl_seed_declaration(),
    ] {
        engine = admit(engine, declaration);
    }
    let nat = scalar(ValueType::Nat).unwrap();
    let bool_ = scalar(ValueType::Bool).unwrap();
    let type_ = Expr::forall_e(
        name("a"),
        nat.clone(),
        Expr::forall_e(name("b"), nat.clone(), bool_, BinderInfo::Default),
        BinderInfo::Default,
    );
    let value = |result| {
        Expr::lam(
            name("a"),
            nat.clone(),
            Expr::lam(
                name("b"),
                nat.clone(),
                Expr::const_(name(result), vec![]),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    let logical = DefinitionVal {
        base: ConstantVal {
            name: name("Nat.beq"),
            level_params: vec![],
            type_,
        },
        value: value("Bool.true"),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("Nat.beq")],
    };
    engine = admit(engine, Declaration::Defn(logical.clone()));
    let mut executable = logical;
    executable.base.name = name("Nat.beq._unsafe_rec");
    executable.value = value("Bool.false");
    executable.safety = DefinitionSafety::Partial;
    executable.all = vec![executable.base.name.clone()];
    admit(engine, Declaration::Mutual(vec![executable]))
}

#[test]
fn source_equality_companions_keep_their_meaning_without_controlling_nat_patterns() {
    let engine = equality_with_companion();
    engine
        .check_source_files(
            &[b"theorem logicalBeq : Nat.beq 0 0 = true := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    execute(&engine, "#eval Nat.beq 0 0", "0");
    execute(
        &engine,
        "#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => 99) 0",
        "42",
    );
    execute(
        &engine,
        "#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => 99) 3",
        "99",
    );
    let environment = fln_elab::externs::register(
        engine.environment(),
        &name("Nat.beq"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: "unavailable_foreign_equality".to_owned(),
        }],
    )
    .unwrap();
    let engine = Engine::from_environment(environment);
    execute(
        &engine,
        "#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => ih) 4",
        "42",
    );
    let error = engine
        .execute_source_definitions(&[b"#eval Nat.beq 0 0"], &KVMap::new(), limits())
        .expect_err("a direct source call still honors its foreign selected extern");
    assert!(
        format!("{error:?}").contains("native extern attribute does not match the supported ABI")
    );
}

#[test]
fn source_declarations_cannot_impersonate_the_private_nat_case() {
    let mut engine = minimal_engine();
    let collision = Name::num(name("_fln_runtime_nat_case"), 0);
    engine = admit(
        engine,
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: collision.clone(),
                level_params: vec![],
                type_: scalar(ValueType::Nat).unwrap(),
            },
            value: literal(0),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![collision],
        }),
    );
    let error = engine
        .execute_source_definitions(
            &[b"#eval @Nat.rec (fun _ => Nat) 42 (fun n ih => 99) 0"],
            &KVMap::new(),
            limits(),
        )
        .expect_err("a checked same-named declaration does not grant compiler authority");
    assert!(format!("{error:?}").contains("runtime case name collision"));
}
