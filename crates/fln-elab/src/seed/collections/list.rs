//! Positive recursive lists and ordinary definitions over the generated recursor.
use super::*;

fn list(alpha: Expr, universe: Level) -> Expr {
    Expr::app(constant("List", vec![universe]), alpha)
}
fn nil(alpha: Expr, universe: Level) -> Expr {
    Expr::app(constant("List.nil", vec![universe]), alpha)
}
fn cons(alpha: Expr, universe: Level, head: Expr, tail: Expr) -> Expr {
    app(constant("List.cons", vec![universe]), [alpha, head, tail])
}

fn family() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.local("α", Expr::sort(type_level("u")), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list(fv(&alpha), level("u")), BinderInfo::Default);
    inductive_declaration(
        &InductiveSpec {
            name: name("List"),
            level_params: vec![name("u")],
            parameters: vec![alpha],
            indices: Vec::new(),
            constructors: vec![
                ConstructorSpec {
                    name: name("nil"),
                    fields: Vec::new(),
                    result_indices: Vec::new(),
                },
                ConstructorSpec {
                    name: name("cons"),
                    fields: vec![head, tail],
                    result_indices: Vec::new(),
                },
            ],
            result_level: type_level("u"),
        },
        RecordBudget::default(),
    )
    .expect("fixed strictly positive uniform List family")
}

fn length() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let list_alpha = list(fv(&alpha), level("u"));
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha, BinderInfo::Default);
    let nat = constant("Nat", Vec::new());
    let ih = terms.local("ih", nat.clone(), BinderInfo::Default);
    let motive = terms.lam(&[major], nat.clone());
    let step = Expr::app(constant("Nat.succ", Vec::new()), fv(&ih));
    let step = terms.lam(&[head, tail, ih], step);
    let body = app(
        constant("List.rec", vec![Level::one(), level("u")]),
        [
            fv(&alpha),
            motive,
            constant("Nat.zero", Vec::new()),
            step,
            fv(&value),
        ],
    );
    terms.definition("List.length", &["u"], &[alpha, value], nat, body)
}

fn append() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let list_alpha = list(fv(&alpha), level("u"));
    let left = terms.local("as", list_alpha.clone(), BinderInfo::Default);
    let right = terms.local("bs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha.clone(), BinderInfo::Default);
    let ih = terms.local("ih", list_alpha.clone(), BinderInfo::Default);
    let motive = terms.lam(&[major], list_alpha.clone());
    let step = cons(fv(&alpha), level("u"), fv(&head), fv(&ih));
    let step = terms.lam(&[head, tail, ih], step);
    let body = app(
        constant("List.rec", vec![type_level("u"), level("u")]),
        [fv(&alpha), motive, fv(&right), step, fv(&left)],
    );
    terms.definition(
        "List.append",
        &["u"],
        &[alpha, left, right],
        list_alpha,
        body,
    )
}

fn map() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let beta = terms.parameter("β", "v");
    let list_alpha = list(fv(&alpha), level("u"));
    let list_beta = list(fv(&beta), level("v"));
    let function_type = terms.arrow(fv(&alpha), fv(&beta));
    let function = terms.local("f", function_type, BinderInfo::Default);
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha, BinderInfo::Default);
    let ih = terms.local("ih", list_beta.clone(), BinderInfo::Default);
    let motive = terms.lam(&[major], list_beta.clone());
    let step = cons(
        fv(&beta),
        level("v"),
        Expr::app(fv(&function), fv(&head)),
        fv(&ih),
    );
    let step = terms.lam(&[head, tail, ih], step);
    let body = app(
        constant("List.rec", vec![type_level("v"), level("u")]),
        [
            fv(&alpha),
            motive,
            nil(fv(&beta), level("v")),
            step,
            fv(&value),
        ],
    );
    terms.definition(
        "List.map",
        &["u", "v"],
        &[alpha, beta, function, value],
        list_beta,
        body,
    )
}

fn foldr() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let beta = terms.parameter("β", "v");
    let list_alpha = list(fv(&alpha), level("u"));
    let accumulator_function = terms.arrow(fv(&beta), fv(&beta));
    let function_type = terms.arrow(fv(&alpha), accumulator_function);
    let function = terms.local("f", function_type, BinderInfo::Default);
    let initial = terms.local("init", fv(&beta), BinderInfo::Default);
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha, BinderInfo::Default);
    let ih = terms.local("ih", fv(&beta), BinderInfo::Default);
    let motive = terms.lam(&[major], fv(&beta));
    let step = app(fv(&function), [fv(&head), fv(&ih)]);
    let step = terms.lam(&[head, tail, ih], step);
    let body = app(
        constant("List.rec", vec![type_level("v"), level("u")]),
        [fv(&alpha), motive, fv(&initial), step, fv(&value)],
    );
    let result = fv(&beta);
    terms.definition(
        "List.foldr",
        &["u", "v"],
        &[alpha, beta, function, initial, value],
        result,
        body,
    )
}

fn foldl() -> Declaration {
    let mut terms = Terms::new();
    // In foldl, α is the accumulator type and β is the element type.
    let alpha = terms.parameter("α", "u");
    let beta = terms.parameter("β", "v");
    let list_beta = list(fv(&beta), level("v"));
    let element_function = terms.arrow(fv(&beta), fv(&alpha));
    let function_type = terms.arrow(fv(&alpha), element_function);
    let function = terms.local("f", function_type, BinderInfo::Default);
    let initial = terms.local("init", fv(&alpha), BinderInfo::Default);
    let value = terms.local("xs", list_beta.clone(), BinderInfo::Default);
    let major = terms.local("t", list_beta.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&beta), BinderInfo::Default);
    let tail = terms.local("tail", list_beta, BinderInfo::Default);
    // Induction produces an accumulator transformer. Applying the final
    // transformer to init preserves left-to-right, not right-fold, semantics.
    let transformer = terms.arrow(fv(&alpha), fv(&alpha));
    let ih = terms.local("ih", transformer.clone(), BinderInfo::Default);
    let accumulator = terms.local("acc", fv(&alpha), BinderInfo::Default);
    let motive = terms.lam(&[major], transformer);
    let base = terms.lam(std::slice::from_ref(&accumulator), fv(&accumulator));
    let updated = app(fv(&function), [fv(&accumulator), fv(&head)]);
    let step = Expr::app(fv(&ih), updated);
    let step = terms.lam(&[head, tail, ih, accumulator], step);
    let transform = app(
        constant("List.rec", vec![type_level("u"), level("v")]),
        [fv(&beta), motive, base, step, fv(&value)],
    );
    let body = Expr::app(transform, fv(&initial));
    let result = fv(&alpha);
    terms.definition(
        "List.foldl",
        &["u", "v"],
        &[alpha, beta, function, initial, value],
        result,
        body,
    )
}

fn reverse() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let list_alpha = list(fv(&alpha), level("u"));
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let accumulator = terms.local("acc", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("a", fv(&alpha), BinderInfo::Default);
    let step = cons(fv(&alpha), level("u"), fv(&head), fv(&accumulator));
    let step = terms.lam(&[accumulator, head], step);
    let body = app(
        constant("List.foldl", vec![level("u"), level("u")]),
        [
            list_alpha.clone(),
            fv(&alpha),
            step,
            nil(fv(&alpha), level("u")),
            fv(&value),
        ],
    );
    terms.definition("List.reverse", &["u"], &[alpha, value], list_alpha, body)
}

fn head_option() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let list_alpha = list(fv(&alpha), level("u"));
    let option_alpha = option(fv(&alpha), level("u"));
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha, BinderInfo::Default);
    let ih = terms.local("ih", option_alpha.clone(), BinderInfo::Default);
    let motive = terms.lam(&[major], option_alpha.clone());
    let step = app(
        constant("Option.some", vec![level("u")]),
        [fv(&alpha), fv(&head)],
    );
    let step = terms.lam(&[head, tail, ih], step);
    let base = Expr::app(constant("Option.none", vec![level("u")]), fv(&alpha));
    let body = app(
        constant("List.rec", vec![type_level("u"), level("u")]),
        [fv(&alpha), motive, base, step, fv(&value)],
    );
    terms.definition("List.head?", &["u"], &[alpha, value], option_alpha, body)
}

fn tail() -> Declaration {
    let mut terms = Terms::new();
    let alpha = terms.parameter("α", "u");
    let list_alpha = list(fv(&alpha), level("u"));
    let value = terms.local("xs", list_alpha.clone(), BinderInfo::Default);
    let major = terms.local("t", list_alpha.clone(), BinderInfo::Default);
    let head = terms.local("head", fv(&alpha), BinderInfo::Default);
    let tail = terms.local("tail", list_alpha.clone(), BinderInfo::Default);
    let ih = terms.local("ih", list_alpha.clone(), BinderInfo::Default);
    let motive = terms.lam(&[major], list_alpha.clone());
    let step = fv(&tail);
    let step = terms.lam(&[head, tail, ih], step);
    let body = app(
        constant("List.rec", vec![type_level("u"), level("u")]),
        [
            fv(&alpha),
            motive,
            nil(fv(&alpha), level("u")),
            step,
            fv(&value),
        ],
    );
    terms.definition("List.tail", &["u"], &[alpha, value], list_alpha, body)
}

pub(super) fn declarations() -> [Declaration; 9] {
    [
        family(),
        length(),
        append(),
        map(),
        foldr(),
        foldl(),
        reverse(),
        head_option(),
        tail(),
    ]
}
