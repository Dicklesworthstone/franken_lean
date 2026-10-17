//! Constructor lowering must not borrow the meaning of a public arithmetic
//! declaration. Every logical/partial/replacement body below is dual-admitted.
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
    admit(
        Engine::from_environment(Environment::new()),
        fln_elab::seed::nat_inductive_seed_declaration(),
    )
}

fn native_addition() -> Engine {
    let mut engine = minimal_engine();
    for declaration in fln_elab::seed::nat_add_support_seed_declarations()
        .into_iter()
        .chain([fln_elab::seed::nat_add_seed_declaration()])
    {
        engine = admit(engine, declaration);
    }
    engine
}

fn constant_function(label: &str, arity: usize, result: u64) -> DefinitionVal {
    let nat = scalar(ValueType::Nat).unwrap();
    let mut type_ = nat.clone();
    let mut value = literal(result);
    for _ in 0..arity {
        type_ = Expr::forall_e(Name::anonymous(), nat.clone(), type_, BinderInfo::Default);
        value = Expr::lam(Name::anonymous(), nat.clone(), value, BinderInfo::Default);
    }
    DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    }
}

fn execute(engine: &Engine, source: &str, expected: &[(&str, bool)]) {
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let completed = engine
        .execute_source_commands_with_checks(source.as_bytes(), &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"));
    assert_eq!(
        completed.batch.source_evaluation_indices.len(),
        expected.len()
    );
    for (&index, &(expected, native_add)) in completed
        .batch
        .source_evaluation_indices
        .iter()
        .zip(expected)
    {
        let execution = &completed.batch.executions[index];
        assert_eq!(
            execution.checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let program = fln_comp::flbc::decode_canonical(
            &execution.flbc_artifact,
            fln_comp::flbc::CodecLimits::default(),
        )
        .unwrap();
        assert_eq!(
            fln_comp::flbc::encode_canonical(&program, Default::default()).unwrap(),
            execution.flbc_artifact,
        );
        assert_eq!(
            program.functions().iter().flat_map(|function| &function.code).any(|instruction|
                matches!(instruction, fln_comp::flbc::Instruction::Intrinsic { row, .. }
                    if row == "extern:Nat.add")),
            native_add,
            "{source}",
        );
        let replay = execute_flbc_artifact(&execution.flbc_artifact, &options, Default::default())
            .unwrap()
            .into_complete()
            .unwrap();
        for exit in [&execution.exit, &replay] {
            let VmExit::Returned(returned) = exit else {
                panic!("native Nat return: {exit:?}");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
                Some(expected)
            );
        }
    }
    assert_eq!(engine.logical_root(&options), before);
}

fn contradictory_addition() -> Engine {
    // The pin's kernel reserves closed literal Nat.add reduction before
    // unfolding. Keep that exact logical model and contradict only its
    // independently admitted executable companion.
    let mut engine = native_addition();
    for declaration in [
        fln_elab::seed::eq_seed_declaration(),
        fln_elab::seed::rfl_seed_declaration(),
    ] {
        engine = admit(engine, declaration);
    }
    let Some(ConstantInfo::Defn(logical)) = engine.environment().find(&name("Nat.add")) else {
        panic!("exact admitted Nat.add model");
    };
    let mut companion = constant_function("Nat.add._unsafe_rec", 2, 7);
    companion.base.type_ = logical.base.type_.clone();
    companion.safety = DefinitionSafety::Partial;
    admit(engine, Declaration::Mutual(vec![companion]))
}

#[test]
fn successor_constructs_small_and_wide_naturals_without_a_public_addition() {
    let engine = minimal_engine();
    assert!(!engine.environment().contains(&name("Nat.add")));
    assert!(!engine.environment().contains(&name("Nat.pred")));
    assert!(!engine.environment().contains(&name("Bool")));
    execute(
        &engine,
        "#eval Nat.succ 0\n#eval Nat.succ 4\n#eval Nat.succ 18446744073709551615\n#eval Nat.succ 18446744073709551616\n#eval (let next := Nat.succ; next 4)",
        &[
            ("1", true),
            ("5", true),
            ("18446744073709551616", true),
            ("18446744073709551617", true),
            ("5", true),
        ],
    );
    let collision = admit(
        engine,
        Declaration::Defn(constant_function("_fln_runtime_nat_constructor_add", 2, 99)),
    );
    let error = collision
        .execute_source_definition(b"def next : Nat := Nat.succ 4", &KVMap::new(), limits())
        .expect_err("a logical declaration cannot impersonate the compiler's private helper");
    assert!(matches!(
        error,
        EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
    ));

    // Both public arithmetic and the private constructor operation occur in
    // each artifact. Their equivalent native row must be shared without
    // weakening ingress's duplicate-row validation, including escaped values.
    let native = native_addition();
    execute(
        &native,
        r#"
#eval Nat.add (Nat.succ 4) 2
#eval (let inc := Nat.succ; let plus := Nat.add; plus (inc 4) 2)
#eval (let inc := Nat.succ; let plus := Nat.add 2; inc (plus 4))
"#,
        &[("7", true), ("7", true), ("7", true)],
    );
}

#[test]
fn successor_ignores_public_addition_companions_replacements_and_foreign_externs() {
    let engine = contradictory_addition();
    execute(
        &engine,
        r#"
theorem logicalAdd : Nat.add 4 1 = 5 := rfl
#eval Nat.add 4 1
#eval (let add := Nat.add; add 4 1)
#eval Nat.succ 4
#eval (let next := Nat.succ; next 4)
"#,
        &[("7", false), ("7", false), ("5", true), ("5", true)],
    );
    let Some(ConstantInfo::Defn(logical)) = engine.environment().find(&name("Nat.add")) else {
        panic!("exact admitted Nat.add model");
    };
    let mut replacement = constant_function("otherAddition", 2, 9);
    replacement.base.type_ = logical.base.type_.clone();
    let engine = admit(engine, Declaration::Defn(replacement));
    let replaced = fln_elab::implemented_by::register(
        engine.environment(),
        &name("Nat.add"),
        &name("otherAddition"),
    )
    .unwrap();
    execute(
        &Engine::from_environment(replaced),
        r#"
theorem logicalAdd : Nat.add 4 1 = 5 := rfl
#eval Nat.add 4 1
#eval (let add := Nat.add; add 4 1)
#eval Nat.succ 4
"#,
        &[("9", false), ("9", false), ("5", true)],
    );
    let foreign = fln_elab::externs::register(
        engine.environment(),
        &name("Nat.add"),
        vec![fln_elab::externs::ExternEntry::Standard {
            backend: name("all"),
            symbol: "foreign_addition".to_owned(),
        }],
    )
    .unwrap();
    let foreign = Engine::from_environment(foreign);
    execute(&foreign, "#eval Nat.succ 4", &[("5", true)]);
    let error = foreign
        .execute_source_definition(
            b"def directAdd : Nat := Nat.add 4 1",
            &KVMap::new(),
            limits(),
        )
        .expect_err("a source add call must retain its explicit unsupported extern");
    assert!(matches!(
        error,
        EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })
    ));
}

#[test]
fn a_constructors_own_replacement_keeps_priority_for_applied_and_bare_heads() {
    let engine = contradictory_addition();
    let Some(ConstantInfo::Ctor(constructor)) = engine.environment().find(&name("Nat.succ")) else {
        panic!("exact Nat successor constructor");
    };
    let mut replacement = constant_function("otherSuccessor", 1, 13);
    replacement.base.type_ = constructor.base.type_.clone();
    let engine = admit(engine, Declaration::Defn(replacement));
    let replaced = fln_elab::implemented_by::register(
        engine.environment(),
        &name("Nat.succ"),
        &name("otherSuccessor"),
    )
    .unwrap();
    execute(
        &Engine::from_environment(replaced),
        r#"
theorem logicalSuccessor : Nat.succ 4 = 5 := rfl
#eval Nat.succ 4
#eval (let next := Nat.succ; next 4)
#eval Nat.add 4 1
"#,
        &[("13", false), ("13", false), ("7", false)],
    );
}
