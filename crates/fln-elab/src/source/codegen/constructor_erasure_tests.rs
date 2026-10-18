//! Regression boundary for fln-noncomputable-check-false-refusal-bhf2.
//! The pin's ToLCNF.visitCtor suppresses noncomputability in the first
//! ConstructorVal.numParams arguments, not in the constructor's fields.
use super::*;
use fln_env::constants::{
    AxiomVal, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal, InductiveVal,
    ReducibilityHints,
};
use fln_env::environment::Environment;

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}
fn number(value: u64) -> Expr {
    Expr::lit(fln_core::expr::Literal::Nat(
        fln_core::expr::NatLit::from_u64(value),
    ))
}
fn box_type(parameter: Expr) -> Expr {
    Expr::app(c("ParamBox"), parameter)
}
fn construct(parameter: Expr, field: Expr) -> Expr {
    Expr::app(Expr::app(c("ParamBox.mk"), parameter), field)
}
fn environment() -> Environment {
    let env = crate::seed::bootstrap_nat_environment(Budget::DEFAULT).unwrap();
    let env = env
        .add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("hidden"),
                level_params: vec![],
                type_: c("Nat"),
            },
            is_unsafe: false,
        }))
        .unwrap();
    let env = env
        .add_decl(ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: n("ParamBox"),
                level_params: vec![],
                type_: Expr::forall_e(
                    n("parameter"),
                    c("Nat"),
                    Expr::sort(Level::one()),
                    BinderInfo::Default,
                ),
            },
            num_params: 1,
            num_indices: 0,
            all: vec![n("ParamBox")],
            ctors: vec![n("ParamBox.mk")],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }))
        .unwrap();
    env.add_decl(ConstantInfo::Ctor(ConstructorVal {
        base: ConstantVal {
            name: n("ParamBox.mk"),
            level_params: vec![],
            type_: Expr::forall_e(
                n("parameter"),
                c("Nat"),
                Expr::forall_e(
                    n("field"),
                    c("Nat"),
                    box_type(Expr::bvar(1).unwrap()),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        },
        induct: n("ParamBox"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    }))
    .unwrap()
}
fn check(env: &Environment, term: &Typed) -> Result<bool, NatDefinitionElabError> {
    let mut context = Context::new(env, Budget::DEFAULT);
    let saved = context.txn.lctx.clone();
    let result = context.check_definition_codegen(term);
    assert_eq!(context.txn.lctx, saved);
    assert_eq!(&context.txn.env, env);
    result
}
fn assert_hidden(result: Result<bool, NatDefinitionElabError>) {
    assert!(matches!(result,
        Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name)))
        if name == n("hidden")));
}

#[test]
fn data_valued_constructor_parameters_do_not_require_executable_code() {
    let base = environment();
    let tagged = crate::noncomputable::register(&base, &n("hidden")).unwrap();
    for env in [&base, &tagged] {
        let term = Typed {
            type_: box_type(c("hidden")),
            value: construct(c("hidden"), number(9)),
        };
        assert_eq!(check(env, &term), Ok(false));
    }
}

#[test]
fn partially_applied_constructors_erase_supplied_parameters_too() {
    let env = environment();
    let term = Typed {
        type_: Expr::forall_e(
            n("field"),
            c("Nat"),
            box_type(c("hidden")),
            BinderInfo::Default,
        ),
        value: Expr::app(c("ParamBox.mk"), c("hidden")),
    };
    assert_eq!(check(&env, &term), Ok(false));
}

#[test]
fn constructor_fields_still_require_code_even_when_shared_with_a_parameter() {
    let env = environment();
    for parameter in [number(0), c("hidden")] {
        let term = Typed {
            type_: box_type(parameter.clone()),
            value: construct(parameter, c("hidden")),
        };
        assert_hidden(check(&env, &term));
    }
}

#[test]
fn constructor_erasure_does_not_exempt_the_constructor_itself() {
    let env = crate::noncomputable::register(&environment(), &n("ParamBox.mk")).unwrap();
    let term = Typed {
        type_: box_type(c("hidden")),
        value: construct(c("hidden"), number(9)),
    };
    assert!(matches!(check(&env, &term),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableDependency(name)))
        if name == n("ParamBox.mk")));
}

#[test]
fn a_definition_with_a_constructor_shaped_type_has_no_erased_parameter_prefix() {
    let env = environment();
    let type_ = env.find(&n("ParamBox.mk")).unwrap().constant_val().type_.clone();
    let env = env
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("ordinary.mk"),
                level_params: vec![],
                type_,
            },
            value: c("ParamBox.mk"),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![n("ordinary.mk")],
        }))
        .unwrap();
    let term = Typed {
        type_: box_type(c("hidden")),
        value: Expr::app(Expr::app(c("ordinary.mk"), c("hidden")), number(9)),
    };
    assert_hidden(check(&env, &term));
}

#[test]
fn erased_parameters_do_not_hide_malformed_dependency_metadata() {
    let env = crate::noncomputable::register(&environment(), &n("hidden")).unwrap();
    let env = env
        .push_extension_entry(&crate::noncomputable::journal_name(), b"broken".to_vec())
        .unwrap();
    let term = Typed {
        type_: box_type(c("hidden")),
        value: construct(c("hidden"), number(9)),
    };
    assert!(matches!(check(&env, &term),
        Err(NatDefinitionElabError::Inference(SourceInferenceError::NoncomputableJournal(_)))));
}
