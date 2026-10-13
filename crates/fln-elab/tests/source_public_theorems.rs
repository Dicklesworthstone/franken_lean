//! A split theorem elaboration is an untrusted candidate with a fixed public
//! signature. The engine integration target checks publication through both seats.
#![forbid(unsafe_code)]

use fln_core::{
    expr::{BinderInfo, Expr},
    level::Level,
    name::Name,
    outcome::Outcome,
};
use fln_elab::source::{
    self, TheoremWorlds,
    scope::{SourceScope, simp},
};
use fln_env::{
    constants::{AxiomVal, ConstantInfo, ConstantVal},
    environment::Environment,
};
use fln_kernel::{
    Declaration, check,
    verdict::{Budget, Verdict},
};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn module() -> SourceScope {
    SourceScope {
        namespace: n("API"),
        private_module: Some(n("Main")),
        ..SourceScope::default()
    }
}

fn checked_info(environment: &Environment, declaration: Declaration) -> Environment {
    assert!(matches!(
        check(environment, &declaration, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    let info = match declaration {
        Declaration::Axiom(value) => ConstantInfo::Axiom(value),
        Declaration::Defn(value) => ConstantInfo::Defn(value),
        _ => panic!("fixture must be an axiom or definition"),
    };
    environment.add_decl(info).unwrap()
}

fn axiom(environment: &Environment, name: &str, parameters: Vec<Name>, type_: Expr) -> Environment {
    checked_info(
        environment,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: parameters,
                type_,
            },
            is_unsafe: false,
        }),
    )
}

#[test]
fn theorem_candidate_retains_private_proof_but_exact_public_statement() {
    let public = Environment::new();
    let scope = module();
    let helper = fln_parse::parse_definition(b"def helper (P : Prop) (h : P) : P := h").unwrap();
    let helper =
        source::scope::elaborate_definition(helper.syntax(), &public, budget(), &scope).unwrap();
    let private = checked_info(&public, helper);
    let syntax =
        fln_parse::parse_definition(b"public theorem witness (P : Prop) (h : P) : P := helper P h")
            .unwrap();
    let worlds = TheoremWorlds {
        public: &public,
        private: &private,
        public_scope: &scope,
        private_scope: &scope,
    };
    let theorem = source::elaborate_public_theorem(syntax.syntax(), &worlds, budget()).unwrap();
    let Declaration::Thm(value) = &theorem else {
        panic!("the proof remains a theorem candidate")
    };
    assert_eq!(value.base.name, n("API.witness"));
    assert!(matches!(
        check(&private, &theorem, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    assert!(matches!(
        check(&public, &theorem, budget()),
        Outcome::Complete(Verdict::Rejected { .. })
    ));
    let signature = Declaration::Axiom(AxiomVal {
        base: value.base.clone(),
        is_unsafe: false,
    });
    assert!(matches!(
        check(&public, &signature, budget()),
        Outcome::Complete(Verdict::Accepted { .. })
    ));
    assert!(!private.contains(&n("API.witness")));
    assert!(public.is_empty());
}

#[test]
fn private_header_names_are_refused_before_proof_elaboration() {
    let public = Environment::new();
    let hidden = Name::num(n("_private.Main"), 0).append_core(&n("API.Secret"));
    let private = checked_info(
        &public,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: hidden,
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        }),
    );
    let scope = module();
    let syntax =
        fln_parse::parse_definition(b"public theorem leak (h : Secret) : Secret := h").unwrap();
    assert!(
        source::elaborate_public_theorem(
            syntax.syntax(),
            &TheoremWorlds {
                public: &public,
                private: &private,
                public_scope: &scope,
                private_scope: &scope
            },
            budget()
        )
        .is_err()
    );
    assert!(public.is_empty());
}

#[test]
fn forward_simp_interfaces_classify_propositions_and_reject_data_axioms() {
    let env = axiom(
        &Environment::new(),
        "P",
        Vec::new(),
        Expr::sort(Level::zero()),
    );
    let env = axiom(&env, "proof", Vec::new(), Expr::const_(n("P"), Vec::new()));
    let env = axiom(&env, "Data", Vec::new(), Expr::sort(Level::one()));
    let env = axiom(
        &env,
        "value",
        Vec::new(),
        Expr::const_(n("Data"), Vec::new()),
    );
    let telescope = Expr::forall_e(
        n("Q"),
        Expr::sort(Level::zero()),
        Expr::forall_e(
            n("h"),
            Expr::bvar(0).unwrap(),
            Expr::bvar(1).unwrap(),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = axiom(&env, "identityProof", Vec::new(), telescope);
    let applied_predicate = Expr::forall_e(
        n("Q"),
        Expr::forall_e(
            n("x"),
            Expr::const_(n("Data"), Vec::new()),
            Expr::sort(Level::zero()),
            BinderInfo::Default,
        ),
        Expr::forall_e(
            n("x"),
            Expr::const_(n("Data"), Vec::new()),
            Expr::app(Expr::bvar(1).unwrap(), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let env = axiom(&env, "predicateProof", Vec::new(), applied_predicate);
    for name in ["proof", "identityProof", "predicateProof"] {
        let next = simp::update(&env, &n(name), Some((1000, false))).unwrap();
        assert_eq!(simp::read(&next).unwrap()[0].declaration, n(name));
        assert!(simp::read(&env).unwrap().is_empty());
    }
    for name in ["P", "Data", "value"] {
        assert!(
            matches!(
                simp::update(&env, &n(name), Some((1000, false))),
                Err(simp::SimpSetError::UnsupportedDeclaration(_))
            ),
            "{name}"
        );
    }
    assert!(simp::update(&env, &n("proof"), Some((1000, true))).is_err());
}

#[test]
fn simp_proposition_classifier_instantiates_universes_once() {
    let u = n("u");
    let env = axiom(
        &Environment::new(),
        "Family",
        vec![u.clone()],
        Expr::sort(Level::param(u.clone())),
    );
    let env = axiom(
        &env,
        "proposition",
        Vec::new(),
        Expr::const_(n("Family"), vec![Level::zero()]),
    );
    let env = axiom(
        &env,
        "data",
        Vec::new(),
        Expr::const_(n("Family"), vec![Level::one()]),
    );
    let env = axiom(
        &env,
        "polymorphic",
        vec![u.clone()],
        Expr::const_(n("Family"), vec![Level::param(u)]),
    );
    assert!(simp::update(&env, &n("proposition"), Some((1000, false))).is_ok());
    for name in ["data", "polymorphic"] {
        assert!(matches!(
            simp::update(&env, &n(name), Some((1000, false))),
            Err(simp::SimpSetError::UnsupportedDeclaration(_))
        ));
    }
}
