//! Complete logical scaffold of the pin's List course-of-values eliminator.
//!
//! These candidates are compared with already admitted declarations. They are
//! not installed into the source seed or used as replacement library bodies.
use super::*;

fn list(alpha: Expr, universe: &Level) -> Expr {
    Expr::app(constant("List", vec![universe.clone()]), alpha)
}

fn nil(alpha: Expr, universe: &Level) -> Expr {
    Expr::app(constant("List.nil", vec![universe.clone()]), alpha)
}

fn cons(alpha: Expr, universe: &Level, head: Expr, tail: Expr) -> Expr {
    app(
        constant("List.cons", vec![universe.clone()]),
        [alpha, head, tail],
    )
}

fn history(universe: &Level, element: &Level, alpha: Expr, motive: Expr, value: Expr) -> Expr {
    app(
        constant("List.below", vec![universe.clone(), element.clone()]),
        [alpha, motive, value],
    )
}

fn parameters(terms: &mut Terms) -> (Level, Level, Level, LocalDecl, LocalDecl, LocalDecl) {
    let universe = level("u_1");
    let element = level("u");
    let element_sort = element.clone().succ().expect("fixed List universe");
    let storage =
        Level::max(element_sort.clone(), universe.clone()).expect("fixed List history universe");
    let alpha = terms.local("α", Expr::sort(element_sort), BinderInfo::Implicit);
    let value = terms.local("t", list(fv(&alpha), &element), BinderInfo::Default);
    let motive_type = terms.pi(std::slice::from_ref(&value), Expr::sort(universe.clone()));
    let motive = terms.local("motive", motive_type, BinderInfo::Implicit);
    (universe, element, storage, alpha, motive, value)
}

fn functional(
    terms: &mut Terms,
    universe: &Level,
    element: &Level,
    alpha: &LocalDecl,
    motive: &LocalDecl,
) -> LocalDecl {
    let value = terms.local("t", list(fv(alpha), element), BinderInfo::Default);
    let previous = terms.local(
        "f",
        history(universe, element, fv(alpha), fv(motive), fv(&value)),
        BinderInfo::Default,
    );
    let type_ = terms.pi(
        &[value.clone(), previous],
        Expr::app(fv(motive), fv(&value)),
    );
    terms.local("F_1", type_, BinderInfo::Default)
}

fn below() -> Declaration {
    let mut terms = Terms::new();
    let (universe, element, storage, alpha, motive, value) = parameters(&mut terms);
    let recursor_motive = terms.lam(std::slice::from_ref(&value), Expr::sort(storage.clone()));
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list(fv(&alpha), &element), BinderInfo::Default);
    let previous = terms.local("tail_ih", Expr::sort(storage.clone()), BinderInfo::Default);
    let step = product(
        &universe,
        &storage,
        Expr::app(fv(&motive), fv(&tail)),
        fv(&previous),
    );
    let step = terms.lam(&[head, tail, previous], step);
    let body = app(
        constant(
            "List.rec",
            vec![
                storage.clone().succ().expect("fixed List sort universe"),
                element,
            ],
        ),
        [
            fv(&alpha),
            recursor_motive,
            constant("PUnit", vec![storage.clone()]),
            step,
            fv(&value),
        ],
    );
    terms.definition(
        "List.below",
        &["u_1", "u"],
        &[alpha, motive, value],
        Expr::sort(storage),
        body,
    )
}

fn go() -> Declaration {
    let mut terms = Terms::new();
    let (universe, element, storage, alpha, motive, value) = parameters(&mut terms);
    let functional = functional(&mut terms, &universe, &element, &alpha, &motive);
    let result = product(
        &universe,
        &storage,
        Expr::app(fv(&motive), fv(&value)),
        history(&universe, &element, fv(&alpha), fv(&motive), fv(&value)),
    );
    let recursor_motive = terms.lam(std::slice::from_ref(&value), result.clone());
    let empty = nil(fv(&alpha), &element);
    let unit = constant("PUnit.unit", vec![storage.clone()]);
    let first = pair(
        &universe,
        &storage,
        Expr::app(fv(&motive), empty.clone()),
        constant("PUnit", vec![storage.clone()]),
        app(fv(&functional), [empty, unit.clone()]),
        unit,
    );
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list(fv(&alpha), &element), BinderInfo::Default);
    let tail_result = product(
        &universe,
        &storage,
        Expr::app(fv(&motive), fv(&tail)),
        history(&universe, &element, fv(&alpha), fv(&motive), fv(&tail)),
    );
    let previous = terms.local("tail_ih", tail_result.clone(), BinderInfo::Default);
    let major = cons(fv(&alpha), &element, fv(&head), fv(&tail));
    // The pin retains this unsimplified second-field universe in its body.
    let nested_storage = Level::max(
        Level::max(Level::one(), universe.clone()).expect("fixed PProd universe"),
        Level::max(
            element.clone().succ().expect("fixed List universe"),
            universe.clone(),
        )
        .expect("fixed List history universe"),
    )
    .expect("fixed nested List history universe");
    let step = pair(
        &universe,
        &nested_storage,
        Expr::app(fv(&motive), major.clone()),
        tail_result,
        app(fv(&functional), [major, fv(&previous)]),
        fv(&previous),
    );
    let step = terms.lam(&[head, tail, previous], step);
    let body = app(
        constant("List.rec", vec![storage, element]),
        [fv(&alpha), recursor_motive, first, step, fv(&value)],
    );
    terms.definition(
        "List.brecOn.go",
        &["u_1", "u"],
        &[alpha, motive, value, functional],
        result,
        body,
    )
}

fn brec_on() -> Declaration {
    let mut terms = Terms::new();
    let (universe, element, _, alpha, motive, value) = parameters(&mut terms);
    let functional = functional(&mut terms, &universe, &element, &alpha, &motive);
    let combined = app(
        constant("List.brecOn.go", vec![universe, element]),
        [fv(&alpha), fv(&motive), fv(&value), fv(&functional)],
    );
    let body = Expr::proj(name("PProd"), 0, combined);
    let result = Expr::app(fv(&motive), fv(&value));
    terms.definition(
        "List.brecOn",
        &["u_1", "u"],
        &[alpha, motive, value, functional],
        result,
        body,
    )
}

pub(super) fn declarations() -> Vec<Declaration> {
    let family = super::super::collections::list_seed_declarations()
        .into_iter()
        .next()
        .expect("List family is first");
    vec![punit(), pprod(), family, below(), go(), brec_on()]
}
