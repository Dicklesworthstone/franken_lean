use super::*;
use fln_core::level::Level;

fn models(replacement: Option<DefinitionVal>) -> Environment {
    let mut environment = Environment::new();
    for declaration in fln_elab::seed::source_seed_declarations() {
        match declaration {
            Declaration::Defn(mut value)
                if value.base.name == name("ite") || value.base.name == name("dite") =>
            {
                if let Some(replacement) = &replacement
                    && replacement.base.name == value.base.name
                {
                    value = replacement.clone();
                }
                environment = environment.add_decl(ConstantInfo::Defn(value)).unwrap();
            }
            _ => {}
        }
    }
    environment
}

fn arguments() -> Vec<Expr> {
    vec![
        Expr::const_(name("Nat"), vec![]),
        Expr::const_(name("True"), vec![]),
        Expr::const_(name("instDecidableTrue"), vec![]),
        nat::literal(42),
        nat::literal(17),
    ]
}

fn with_strict_work(mut value: Expr, beta: bool) -> Expr {
    let mut binders = Vec::new();
    for _ in 0..5 {
        let ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = value.node()
        else {
            panic!("conditional telescope");
        };
        binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
        value = body.clone();
    }
    let type_ = Expr::const_(name("Nat"), vec![]);
    let work = Expr::app(
        Expr::const_(name("strictWork"), vec![]),
        nat::literal(10000),
    );
    let body = value.lift_loose(0, 1).unwrap();
    value = if beta {
        Expr::app(
            Expr::lam(Name::anonymous(), type_, body, BinderInfo::Default),
            work,
        )
    } else {
        Expr::let_e(Name::anonymous(), type_, work, body, false)
    };
    for (label, domain, info) in binders.into_iter().rev() {
        value = Expr::lam(label, domain, value, info);
    }
    value
}

#[test]
fn conditional_inlining_requires_the_complete_type_body_and_safety_contract() {
    let model = fln_elab::seed::source_seed_declarations()
        .into_iter()
        .find_map(|declaration| {
            if let Declaration::Defn(value) = declaration {
                (value.base.name == name("ite")).then_some(value)
            } else {
                None
            }
        })
        .unwrap();
    for mutation in 0..7 {
        let mut changed = model.clone();
        match mutation {
            0 => changed.safety = DefinitionSafety::Unsafe,
            1 => changed.base.level_params.push(name("other")),
            2 => changed.base.type_ = Expr::const_(name("Nat"), vec![]),
            3 => changed.value = Expr::const_(name("foreignBody"), vec![]),
            4 => changed.all = vec![name("differentGroup")],
            5 => changed.value = with_strict_work(changed.value, false),
            6 => changed.value = with_strict_work(changed.value, true),
            _ => unreachable!(),
        }
        let environment = models(Some(changed));
        let mut preparation = Preparation::new(&environment, IngressLimits::default());
        assert!(
            preparation
                .lazy_conditional(&Expr::const_(name("ite"), vec![Level::one()]), &arguments())
                .unwrap()
                .is_none()
        );
        assert_eq!(preparation.conditional_contracts, [false; 2]);
    }
}

#[test]
fn actual_prelude_conditional_models_include_cases_on_proof_minor_lambdas() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|| {
            std::path::PathBuf::from(std::env::var_os("HOME").unwrap())
                .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
        });
    let path = lib.join("Init/Prelude.olean");
    if !path.exists() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference Prelude unavailable"
        );
        eprintln!("SKIP: actual pinned Prelude unavailable");
        return;
    }
    let read = |path: std::path::PathBuf| std::fs::read(path).unwrap();
    let decoded = crate::decode_olean_module_artifacts(
        &read(path.clone()),
        &read(path.with_extension("olean.server")),
        &read(path.with_extension("olean.private")),
        crate::OleanDecodeLimits::new(256 * 1024 * 1024),
    )
    .unwrap();
    // This is a structural guard test, not an import/admission receipt. Real
    // imported source execution is exercised separately through the council.
    let declarations: Vec<_> = decoded
        .constants
        .into_iter()
        .filter(|info| {
            ["ite", "dite", "Decidable.casesOn"]
                .iter()
                .any(|label| info.name() == &name(label))
        })
        .collect();
    let mut environment = Environment::new();
    for info in &declarations {
        environment = environment.add_decl(info.clone()).unwrap();
    }
    let mut preparation = Preparation::new(&environment, IngressLimits::default());
    for label in ["ite", "dite"] {
        assert!(
            preparation
                .lazy_conditional(&Expr::const_(name(label), vec![Level::one()]), &arguments())
                .unwrap()
                .is_some(),
            "{label}"
        );
    }
    for replaced in ["ite", "Decidable.casesOn"] {
        let mut environment = Environment::new();
        for info in &declarations {
            let mut info = info.clone();
            if let ConstantInfo::Defn(value) = &mut info
                && value.base.name == name(replaced)
            {
                value.value = with_strict_work(value.value.clone(), false);
            }
            environment = environment.add_decl(info).unwrap();
        }
        assert!(
            Preparation::new(&environment, IngressLimits::default())
                .lazy_conditional(&Expr::const_(name("ite"), vec![Level::one()]), &arguments())
                .unwrap()
                .is_none(),
            "strict work in {replaced}"
        );
    }
}
