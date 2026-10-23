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

/// Only a `casesOn` in the admitted auxiliary-recursor journal and a reducible match
/// auxiliary are inlined; look-alike names stay ordinary calls.
#[test]
fn eliminators_inline_only_registered_cases_on_and_reducible_matchers() {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[br#"
inductive Opt where
  | none
  | some (value : Nat)
def Fake.casesOn (n : Nat) : Nat := n
def fake.match_1 (n : Nat) : Nat := n
"#],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let constant = |label: &str| Expr::const_(name(label), vec![]);
    let nat = constant("Nat");
    let mut preparation = Preparation::new(&engine.environment, IngressLimits::default());
    let arguments = [
        Expr::lam(
            Name::anonymous(),
            constant("Opt"),
            nat.clone(),
            BinderInfo::Default,
        ),
        constant("Opt.none"),
        nat::literal(7),
        Expr::lam(
            Name::anonymous(),
            nat,
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
    ];
    let inlined = preparation
        .lazy_eliminator(
            &Expr::const_(name("Opt.casesOn"), vec![Level::one()]),
            &arguments,
        )
        .unwrap()
        .expect("a registered casesOn is inlined");
    let (head, args) = preparation.spine(&inlined).unwrap();
    assert!(
        matches!(head.node(), ExprNode::Const { name: rec, .. } if *rec == name("Opt.rec")),
        "{inlined:?}"
    );
    // The `none` alternative is an argument of the recursor, not evaluated before it.
    assert!(args.iter().any(|argument| *argument == nat::literal(7)));
    for look_alike in ["Fake.casesOn", "fake.match_1"] {
        assert!(
            preparation
                .lazy_eliminator(&constant(look_alike), &[nat::literal(1)])
                .unwrap()
                .is_none(),
            "{look_alike}"
        );
    }
}

/// `second.{u} : {α : Sort u} → α → α → α := fun α x y => y`, tagged `@[macro_inline]` when
/// `tagged`. A bare `Nat` stands in for the literals' type: the unfolding is syntactic.
fn macro_inline_environment(tagged: bool) -> Environment {
    let u = name("u");
    let sort = Expr::sort(Level::param(u.clone()));
    let b = |index| Expr::bvar(index).unwrap();
    let lam = |label: &str, domain, body| Expr::lam(name(label), domain, body, BinderInfo::Default);
    let pi =
        |label: &str, domain, body| Expr::forall_e(name(label), domain, body, BinderInfo::Default);
    let environment = Environment::new()
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: fln_env::constants::ConstantVal {
                name: name("second"),
                level_params: vec![u],
                type_: pi("α", sort.clone(), pi("x", b(0), pi("y", b(1), b(2)))),
            },
            value: lam("α", sort, lam("x", b(0), lam("y", b(1), b(0)))),
            hints: fln_env::constants::ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name("second")],
        }))
        .unwrap();
    if tagged {
        fln_elab::macro_inline::register(&environment, &name("second")).unwrap()
    } else {
        environment
    }
}

/// The pin's `macroInline` (vendored `Lean/Compiler/LCNF/ToDecl.lean:22`): a tagged constant's
/// value at the call's universe levels, beta-reduced against the unevaluated arguments. An untagged
/// constant is untouched, and a malformed journal is refused, never read as "nothing is tagged".
#[test]
fn macro_inline_unfolds_only_tagged_definitions_over_unevaluated_arguments() {
    let head = Expr::const_(name("second"), vec![Level::one()]);
    let nat = Expr::const_(name("Nat"), vec![]);
    let strict = |argument| Expr::app(Expr::const_(name("strictWork"), vec![]), argument);
    let untagged = macro_inline_environment(false);
    assert!(
        Preparation::new(&untagged, IngressLimits::default())
            .macro_inline(
                &head,
                &[nat.clone(), strict(nat::literal(1)), nat::literal(2)]
            )
            .unwrap()
            .is_none()
    );
    let tagged = macro_inline_environment(true);
    let mut preparation = Preparation::new(&tagged, IngressLimits::default());
    // The unselected argument disappears unevaluated; the selected one is the result.
    assert_eq!(
        preparation
            .macro_inline(
                &head,
                &[nat.clone(), strict(nat::literal(1)), nat::literal(2)]
            )
            .unwrap(),
        Some(nat::literal(2))
    );
    // A partial application keeps the remaining lambda; extra arguments apply to the body.
    assert_eq!(
        preparation
            .macro_inline(&head, &[nat.clone(), strict(nat::literal(1))])
            .unwrap(),
        Some(Expr::lam(
            name("y"),
            nat.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default
        ))
    );
    let callee = Expr::const_(name("callee"), vec![]);
    assert_eq!(
        preparation
            .macro_inline(
                &head,
                &[
                    nat.clone(),
                    strict(nat::literal(1)),
                    callee.clone(),
                    nat::literal(3)
                ]
            )
            .unwrap(),
        Some(Expr::app(callee, nat::literal(3)))
    );
    // A bare constant is the value at the call's levels.
    let Some(value) = preparation.macro_inline(&head, &[]).unwrap() else {
        panic!("a bare tagged constant unfolds");
    };
    let ExprNode::Lam { binder_type, .. } = value.node() else {
        panic!("the value's telescope: {value:?}");
    };
    assert_eq!(binder_type, &Expr::sort(Level::one()));
    // The universe arity is the declaration's.
    assert!(
        preparation
            .macro_inline(&Expr::const_(name("second"), vec![]), &[nat::literal(0)])
            .is_err()
    );
    let broken = tagged
        .push_extension_entry(&fln_elab::macro_inline::journal_name(), b"broken".to_vec())
        .unwrap();
    assert!(
        Preparation::new(&broken, IngressLimits::default())
            .macro_inline(&head, &[nat])
            .is_err()
    );
}
