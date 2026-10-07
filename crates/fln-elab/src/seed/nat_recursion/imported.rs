//! Complete pinned logical models for the remaining primitive Nat eliminators.
//!
//! These candidates are data for post-admission recognition. They do not extend
//! the source seed, install declarations, or execute Reference implementation
//! code. In particular the pin's literal dictionaries and matcher helpers are
//! part of the model; recognizing a familiar root body alone is insufficient.
use super::*;
use fln_core::expr::{Literal, NatLit};

fn regular(declaration: Declaration, height: u32) -> Declaration {
    let Declaration::Defn(mut value) = declaration else {
        unreachable!("fixed logical definition")
    };
    value.hints = ReducibilityHints::Regular(height);
    Declaration::Defn(value)
}

fn literal_zero() -> Expr {
    let zero = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
    app(
        constant("OfNat.ofNat", vec![Level::zero()]),
        [
            nat(),
            zero.clone(),
            Expr::app(constant("instOfNatNat", vec![]), zero),
        ],
    )
}

fn unit_declarations() -> [Declaration; 2] {
    let mut terms = Terms::new();
    [
        terms.definition(
            "Unit",
            &[],
            &[],
            Expr::sort(Level::one()),
            constant("PUnit", vec![Level::one()]),
        ),
        terms.definition(
            "Unit.unit",
            &[],
            &[],
            constant("Unit", vec![]),
            constant("PUnit.unit", vec![Level::one()]),
        ),
    ]
}

fn of_nat_declarations() -> [Declaration; 3] {
    let mut terms = Terms::new();
    let universe = level("u");
    let sort = universe.clone().succ().expect("fixed OfNat universe");
    let alpha = terms.local("α", Expr::sort(sort.clone()), BinderInfo::Default);
    let number = terms.local("n", nat(), BinderInfo::Default);
    let field = terms.local("ofNat", fv(&alpha), BinderInfo::Default);
    let family = record_declarations(
        &RecordSpec {
            name: name("OfNat"),
            level_params: vec![name("u")],
            parameters: vec![alpha.clone(), number.clone()],
            fields: vec![field],
            result_level: sort,
            is_class: true,
        },
        RecordBudget::default(),
    )
    .expect("fixed OfNat family")
    .into_iter()
    .next()
    .expect("record family precedes its projections");
    let mut implicit_alpha = alpha.clone();
    implicit_alpha.binder_info = BinderInfo::Implicit;
    let dictionary = terms.local(
        "self",
        app(constant("OfNat", vec![universe]), [fv(&alpha), fv(&number)]),
        BinderInfo::InstImplicit,
    );
    let Declaration::Defn(mut projection) = terms.definition(
        "OfNat.ofNat",
        &["u"],
        &[implicit_alpha, number.clone(), dictionary.clone()],
        fv(&alpha),
        Expr::proj(name("OfNat"), 0, fv(&dictionary)),
    ) else {
        unreachable!("fixed OfNat projection")
    };
    // The pin's projection type infers the carrier, while its implementation
    // lambda binds that same carrier with a Default annotation. Preserve both
    // telescopes exactly; declaration recognition must not erase binder kinds.
    projection.value = terms.lam(
        &[alpha, number.clone(), dictionary.clone()],
        Expr::proj(name("OfNat"), 0, fv(&dictionary)),
    );
    let instance = terms.definition(
        "instOfNatNat",
        &[],
        std::slice::from_ref(&number),
        app(constant("OfNat", vec![Level::zero()]), [nat(), fv(&number)]),
        app(
            constant("OfNat.mk", vec![Level::zero()]),
            [nat(), fv(&number), fv(&number)],
        ),
    );
    [family, Declaration::Defn(projection), regular(instance, 1)]
}

fn unary_match() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u_1");
    let index = terms.local("x", nat(), BinderInfo::Default);
    let motive_type = terms.pi(std::slice::from_ref(&index), Expr::sort(universe.clone()));
    let motive = terms.local("motive", motive_type, BinderInfo::Default);
    let value = terms.local("x", nat(), BinderInfo::Default);
    let first_type = terms.arrow(
        constant("Unit", vec![]),
        Expr::app(fv(&motive), literal_zero()),
    );
    let first = terms.local("h_1", first_type, BinderInfo::Default);
    let predecessor = terms.local("n", nat(), BinderInfo::Default);
    let next_type = terms.pi(
        std::slice::from_ref(&predecessor),
        Expr::app(fv(&motive), succ(fv(&predecessor))),
    );
    let next = terms.local("h_2", next_type, BinderInfo::Default);
    let recursor_motive = terms.lam(
        std::slice::from_ref(&index),
        Expr::app(fv(&motive), fv(&index)),
    );
    let next_body = Expr::app(fv(&next), fv(&predecessor));
    let next_branch = terms.lam(&[predecessor], next_body);
    let body = app(
        constant("Nat.casesOn", vec![universe]),
        [
            recursor_motive,
            fv(&value),
            Expr::app(fv(&first), constant("Unit.unit", vec![])),
            next_branch,
        ],
    );
    let result = Expr::app(fv(&motive), fv(&value));
    terms.definition(
        "Nat.pow.match_1",
        &["u_1"],
        &[motive, value, first, next],
        result,
        body,
    )
}

fn predecessor() -> Declaration {
    let mut terms = Terms::new();
    let value = terms.local("x", nat(), BinderInfo::Default);
    let motive = terms.lam(std::slice::from_ref(&value), nat());
    let dummy = terms.local("_", constant("Unit", vec![]), BinderInfo::Default);
    let first = terms.lam(&[dummy], literal_zero());
    let previous = terms.local("a", nat(), BinderInfo::Default);
    let next = terms.lam(std::slice::from_ref(&previous), fv(&previous));
    let body = app(
        constant("Nat.pow.match_1", vec![Level::one()]),
        [motive, fv(&value), first, next],
    );
    regular(terms.definition("Nat.pred", &[], &[value], nat(), body), 2)
}

fn binary_match() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u_1");
    let a = terms.local("a", nat(), BinderInfo::Default);
    let b = terms.local("b", nat(), BinderInfo::Default);
    let motive_type = terms.pi(&[a.clone(), b.clone()], Expr::sort(universe.clone()));
    let motive = terms.local("motive", motive_type, BinderInfo::Default);
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let first_type = terms.pi(
        std::slice::from_ref(&a),
        app(fv(&motive), [fv(&a), literal_zero()]),
    );
    let first = terms.local("h_1", first_type, BinderInfo::Default);
    let next_type = terms.pi(
        &[a.clone(), b.clone()],
        app(fv(&motive), [fv(&a), succ(fv(&b))]),
    );
    let next = terms.local("h_2", next_type, BinderInfo::Default);
    let recursor_motive = terms.lam(
        std::slice::from_ref(&b),
        app(fv(&motive), [fv(&left), fv(&b)]),
    );
    let next_body = app(fv(&next), [fv(&left), fv(&b)]);
    let next_branch = terms.lam(&[b], next_body);
    let body = app(
        constant("Nat.casesOn", vec![universe]),
        [
            recursor_motive,
            fv(&right),
            Expr::app(fv(&first), fv(&left)),
            next_branch,
        ],
    );
    let result = app(fv(&motive), [fv(&left), fv(&right)]);
    terms.definition(
        "Nat.mul.match_1",
        &["u_1"],
        &[motive, left, right, first, next],
        result,
        body,
    )
}

fn binary_functional(multiply: bool) -> Declaration {
    let mut terms = Terms::new();
    let universe = Level::one();
    let motive = terms.add_motive();
    let value = terms.local("x", nat(), BinderInfo::Default);
    let history = terms.local(
        "f",
        below(&universe, motive.clone(), fv(&value)),
        BinderInfo::Default,
    );
    let left = terms.local("x_1", nat(), BinderInfo::Default);
    let a = terms.local("a", nat(), BinderInfo::Default);
    let b = terms.local("b", nat(), BinderInfo::Default);
    let matcher_result = terms.arrow(below(&universe, motive.clone(), fv(&b)), nat());
    let matcher_motive = terms.lam(&[a.clone(), b.clone()], matcher_result);
    let zero_history = terms.local(
        "x",
        below(&universe, motive.clone(), literal_zero()),
        BinderInfo::Default,
    );
    let first_body = if multiply { literal_zero() } else { fv(&a) };
    let first = terms.lam(&[a.clone(), zero_history], first_body);
    let succ_history = terms.local(
        "x",
        below(&universe, motive, succ(fv(&b))),
        BinderInfo::Default,
    );
    let previous = Expr::app(Expr::proj(name("PProd"), 0, fv(&succ_history)), fv(&a));
    let next_body = if multiply {
        app(constant("Nat.add", vec![]), [previous, fv(&a)])
    } else {
        Expr::app(constant("Nat.pred", vec![]), previous)
    };
    let next = terms.lam(&[a, b, succ_history], next_body);
    let matched = app(
        constant("Nat.mul.match_1", vec![universe]),
        [matcher_motive, fv(&left), fv(&value), first, next],
    );
    let body = Expr::app(matched, fv(&history));
    terms.definition(
        if multiply { "Nat.mul._f" } else { "Nat.sub._f" },
        &[],
        &[value, history, left],
        nat(),
        body,
    )
}

fn binary_root(multiply: bool) -> Declaration {
    let mut terms = Terms::new();
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let motive = terms.add_motive();
    let body = app(
        constant("Nat.brecOn", vec![Level::one()]),
        [
            motive,
            fv(&right),
            constant(if multiply { "Nat.mul._f" } else { "Nat.sub._f" }, vec![]),
            fv(&left),
        ],
    );
    regular(
        terms.definition(
            if multiply { "Nat.mul" } else { "Nat.sub" },
            &[],
            &[left, right],
            nat(),
            body,
        ),
        if multiply { 2 } else { 3 },
    )
}

fn bool_type() -> Expr {
    constant("Bool", vec![])
}

fn equality_motive(terms: &mut Terms) -> Expr {
    let value = terms.local("x", nat(), BinderInfo::Default);
    let function = terms.arrow(nat(), bool_type());
    terms.lam(&[value], function)
}

fn equality_match() -> Declaration {
    let mut terms = Terms::new();
    let universe = level("u_1");
    let n = terms.local("n", nat(), BinderInfo::Default);
    let m = terms.local("m", nat(), BinderInfo::Default);
    let motive_type = terms.pi(&[n.clone(), m.clone()], Expr::sort(universe.clone()));
    let motive = terms.local("motive", motive_type, BinderInfo::Default);
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let first_type = terms.arrow(constant("Unit", vec![]), app(fv(&motive), [zero(), zero()]));
    let first = terms.local("h_1", first_type, BinderInfo::Default);
    let second_type = terms.pi(
        std::slice::from_ref(&n),
        app(fv(&motive), [zero(), succ(fv(&n))]),
    );
    let second = terms.local("h_2", second_type, BinderInfo::Default);
    let third_type = terms.pi(
        std::slice::from_ref(&n),
        app(fv(&motive), [succ(fv(&n)), zero()]),
    );
    let third = terms.local("h_3", third_type, BinderInfo::Default);
    let fourth_type = terms.pi(
        &[n.clone(), m.clone()],
        app(fv(&motive), [succ(fv(&n)), succ(fv(&m))]),
    );
    let fourth = terms.local("h_4", fourth_type, BinderInfo::Default);
    let index = terms.local("x", nat(), BinderInfo::Default);
    let zero_motive = terms.lam(
        std::slice::from_ref(&index),
        app(fv(&motive), [zero(), fv(&index)]),
    );
    let second_body = Expr::app(fv(&second), fv(&n));
    let zero_step = terms.lam(std::slice::from_ref(&n), second_body);
    let zero_branch = app(
        constant("Nat.casesOn", vec![universe.clone()]),
        [
            zero_motive,
            fv(&right),
            Expr::app(fv(&first), constant("Unit.unit", vec![])),
            zero_step,
        ],
    );
    let next_motive = terms.lam(
        std::slice::from_ref(&index),
        app(fv(&motive), [succ(fv(&n)), fv(&index)]),
    );
    let fourth_body = app(fv(&fourth), [fv(&n), fv(&m)]);
    let next_step = terms.lam(&[m], fourth_body);
    let next_body = app(
        constant("Nat.casesOn", vec![universe.clone()]),
        [
            next_motive,
            fv(&right),
            Expr::app(fv(&third), fv(&n)),
            next_step,
        ],
    );
    let next_branch = terms.lam(&[n], next_body);
    let recursor_motive = terms.lam(
        std::slice::from_ref(&index),
        app(fv(&motive), [fv(&index), fv(&right)]),
    );
    let body = app(
        constant("Nat.casesOn", vec![universe]),
        [recursor_motive, fv(&left), zero_branch, next_branch],
    );
    let result = app(fv(&motive), [fv(&left), fv(&right)]);
    terms.definition(
        "Nat.beq.match_1",
        &["u_1"],
        &[motive, left, right, first, second, third, fourth],
        result,
        body,
    )
}

fn equality_functional() -> Declaration {
    let mut terms = Terms::new();
    let universe = Level::one();
    let motive = equality_motive(&mut terms);
    let value = terms.local("x", nat(), BinderInfo::Default);
    let history = terms.local(
        "f",
        below(&universe, motive.clone(), fv(&value)),
        BinderInfo::Default,
    );
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let n = terms.local("n", nat(), BinderInfo::Default);
    let m = terms.local("m", nat(), BinderInfo::Default);
    let matcher_result = terms.arrow(below(&universe, motive.clone(), fv(&n)), bool_type());
    let matcher_motive = terms.lam(&[n.clone(), m.clone()], matcher_result);
    let zero_history = terms.local(
        "x",
        below(&universe, motive.clone(), zero()),
        BinderInfo::Default,
    );
    let dummy = terms.local("_", constant("Unit", vec![]), BinderInfo::Default);
    let first = terms.lam(
        &[dummy, zero_history.clone()],
        constant("Bool.true", vec![]),
    );
    let second = terms.lam(&[n.clone(), zero_history], constant("Bool.false", vec![]));
    let succ_history = terms.local(
        "x",
        below(&universe, motive, succ(fv(&n))),
        BinderInfo::Default,
    );
    let third = terms.lam(
        &[n.clone(), succ_history.clone()],
        constant("Bool.false", vec![]),
    );
    let fourth_body = Expr::app(Expr::proj(name("PProd"), 0, fv(&succ_history)), fv(&m));
    let fourth = terms.lam(&[n, m, succ_history], fourth_body);
    let matched = app(
        constant("Nat.beq.match_1", vec![universe]),
        [
            matcher_motive,
            fv(&value),
            fv(&right),
            first,
            second,
            third,
            fourth,
        ],
    );
    let body = Expr::app(matched, fv(&history));
    terms.definition(
        "Nat.beq._f",
        &[],
        &[value, history, right],
        bool_type(),
        body,
    )
}

fn equality_root() -> Declaration {
    let mut terms = Terms::new();
    let left = terms.local("x", nat(), BinderInfo::Default);
    let right = terms.local("x_1", nat(), BinderInfo::Default);
    let motive = equality_motive(&mut terms);
    let body = app(
        constant("Nat.brecOn", vec![Level::one()]),
        [
            motive,
            fv(&left),
            constant("Nat.beq._f", vec![]),
            fv(&right),
        ],
    );
    regular(
        terms.definition("Nat.beq", &[], &[left, right], bool_type(), body),
        1,
    )
}

/// Complete finite closures, ordered for independent dual-checker admission.
/// No definition is accepted merely because it has one of these names.
pub(super) fn declarations(wanted: &Name) -> Option<Vec<Declaration>> {
    let pred = wanted == &name("Nat.pred");
    let beq = wanted == &name("Nat.beq");
    let mul = wanted == &name("Nat.mul");
    let sub = wanted == &name("Nat.sub");
    if !pred && !beq && !mul && !sub {
        return None;
    }
    let mut declarations = vec![super::super::nat_inductive_seed_declaration()];
    if mul {
        declarations.extend(nat_add_support_seed_declarations());
        declarations.push(nat_add_seed_declaration());
        declarations.extend(of_nat_declarations());
        declarations.extend([binary_match(), binary_functional(true), binary_root(true)]);
        return Some(declarations);
    }
    if beq {
        declarations.push(super::super::bool_seed_declaration());
    }
    declarations.push(punit());
    declarations.extend(unit_declarations());
    if pred || sub {
        declarations.extend(of_nat_declarations());
    }
    declarations.push(nat_cases_on());
    if pred || sub {
        declarations.extend([unary_match(), predecessor()]);
    }
    if beq || sub {
        declarations.extend([pprod(), nat_below(), nat_brec_on_go(), nat_brec_on()]);
    }
    if beq {
        declarations.extend([equality_match(), equality_functional(), equality_root()]);
    } else if sub {
        declarations.extend([binary_match(), binary_functional(false), binary_root(false)]);
    }
    Some(declarations)
}
