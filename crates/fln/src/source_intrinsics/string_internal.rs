//! Pinned opaque string primitives are ABI contracts, not reducible models.
//!
//! Init.Data.String.Bootstrap at the SUITE.lock pin declares these two safe
//! opaques with Inhabited fallback bodies. The Reference uses their extern
//! entries, never those fallback values. Require the entire opaque and its
//! scalar/class/dictionary contract before selecting the existing generated
//! pure extern row. In particular, an ordinary same-named definition does not
//! acquire an extern, and no opaque body is evaluated to discover authority.

use super::*;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn constant(value: &str) -> Expr {
    Expr::const_(name(value), vec![])
}

fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn bound(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed imported string contract index")
}

fn binder(domain: Expr, body: Expr, style: BinderInfo, lambda: bool) -> Expr {
    if lambda {
        Expr::lam(Name::anonymous(), domain, body, style)
    } else {
        Expr::forall_e(Name::anonymous(), domain, body, style)
    }
}

fn arrow(domain: Expr, body: Expr) -> Expr {
    binder(domain, body, BinderInfo::Default, false)
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    binder(domain, body, BinderInfo::Default, true)
}

fn base(label: &str, levels: Vec<Name>, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: name(label),
        level_params: levels,
        type_,
    }
}

fn pi_inhabited() -> Declaration {
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let result_level = Level::imax(u.clone(), v.clone()).expect("fixed Pi universe");
    let beta = arrow(bound(0), Expr::sort(v.clone()));
    let instances = arrow(
        bound(1),
        Expr::app(
            Expr::const_(name("Inhabited"), vec![v.clone()]),
            Expr::app(bound(1), bound(0)),
        ),
    );
    let function = arrow(bound(2), Expr::app(bound(2), bound(0)));
    let result = Expr::app(
        Expr::const_(name("Inhabited"), vec![result_level.clone()]),
        function.clone(),
    );
    let value = apply(
        Expr::const_(name("Inhabited.mk"), vec![result_level]),
        [
            function,
            lambda(
                bound(2),
                apply(
                    Expr::const_(name("Inhabited.default"), vec![v]),
                    [Expr::app(bound(2), bound(0)), Expr::app(bound(1), bound(0))],
                ),
            ),
        ],
    );
    let wrap = |body, lam| {
        binder(
            Expr::sort(u.clone()),
            binder(
                beta.clone(),
                binder(instances.clone(), body, BinderInfo::InstImplicit, lam),
                BinderInfo::Implicit,
                lam,
            ),
            BinderInfo::Implicit,
            lam,
        )
    };
    Declaration::Defn(DefinitionVal {
        base: base(
            "Pi.instInhabited",
            vec![name("u"), name("v")],
            wrap(result, false),
        ),
        value: wrap(value, true),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![name("Pi.instInhabited")],
    })
}

fn opaque(label: &str) -> OpaqueVal {
    let (arguments, result, instance) = match label {
        "String.Internal.append" => (2, constant("String"), constant("String.instInhabited")),
        "String.Internal.length" => (1, constant("Nat"), constant("instInhabitedNat")),
        _ => unreachable!("fixed imported string primitive"),
    };
    let mut type_ = result;
    let mut dictionary = instance;
    for _ in 0..arguments {
        dictionary = apply(
            Expr::const_(name("Pi.instInhabited"), vec![Level::one(), Level::one()]),
            [
                constant("String"),
                lambda(constant("String"), type_.clone()),
                lambda(constant("String"), dictionary),
            ],
        );
        type_ = arrow(constant("String"), type_);
    }
    OpaqueVal {
        base: base(label, vec![], type_.clone()),
        value: apply(
            Expr::const_(name("Inhabited.default"), vec![Level::one()]),
            [type_, dictionary],
        ),
        is_unsafe: false,
        all: vec![name(label)],
    }
}

fn record_contract(label: &str, constructor: &str, fields: u32, type_: Expr) -> [ConstantInfo; 2] {
    [
        ConstantInfo::Induct(InductiveVal {
            base: base(label, vec![], Expr::sort(Level::one())),
            num_params: 0,
            num_indices: 0,
            all: vec![name(label)],
            ctors: vec![name(constructor)],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        }),
        ConstantInfo::Ctor(ConstructorVal {
            base: base(constructor, vec![], type_),
            induct: name(label),
            cidx: 0,
            num_params: 0,
            num_fields: fields,
            is_unsafe: false,
        }),
    ]
}

fn scalar_records() -> Vec<ConstantInfo> {
    let string = record_contract(
        "String",
        "String.ofByteArray",
        2,
        arrow(
            constant("ByteArray"),
            arrow(
                Expr::app(constant("ByteArray.IsValidUTF8"), bound(0)),
                constant("String"),
            ),
        ),
    );
    let bytes = record_contract(
        "ByteArray",
        "ByteArray.mk",
        1,
        arrow(
            Expr::app(
                Expr::const_(name("Array"), vec![Level::zero()]),
                constant("UInt8"),
            ),
            constant("ByteArray"),
        ),
    );
    string.into_iter().chain(bytes).collect()
}

fn support() -> Vec<Declaration> {
    let mut default = fln_elab::seed::inhabited::default_seed_declaration(true);
    let Declaration::Defn(value) = &mut default else {
        unreachable!("fixed Inhabited projection")
    };
    let ExprNode::Lam {
        binder_type, body, ..
    } = value.value.node()
    else {
        unreachable!("fixed Inhabited projection lambda")
    };
    // The generated projection keeps its type parameter implicit in the type,
    // but its actual value lambda is explicit at the pin.
    value.value = lambda(binder_type.clone(), body.clone());
    let mut natural = fln_elab::seed::inhabited::scalar_inhabited_seed_declaration("Nat");
    let Declaration::Defn(value) = &mut natural else {
        unreachable!("fixed Nat instance")
    };
    // The actual Prelude stores Nat.zero, while the bounded source seed stores
    // the definitionally equal literal. This authority comparison does not
    // normalize the difference away.
    value.value = apply(
        Expr::const_(name("Inhabited.mk"), vec![Level::one()]),
        [constant("Nat"), constant("Nat.zero")],
    );
    vec![
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::inhabited::inhabited_seed_declaration(),
        default,
        pi_inhabited(),
        natural,
        fln_elab::seed::inhabited::scalar_inhabited_seed_declaration("String"),
    ]
}

pub(crate) fn imported_string_internal_matches(
    environment: &Environment,
    requested: &Name,
    cache: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let label = if requested == &name("String.Internal.append") {
        "String.Internal.append"
    } else if requested == &name("String.Internal.length") {
        "String.Internal.length"
    } else {
        return Ok(false);
    };
    if !extern_attribute_matches(environment, requested, true, cache, visited, limits)? {
        return Ok(false);
    }
    let unsupported = || IngressError::UnsupportedNode {
        kind: "imported string extern does not match its complete opaque contract",
    };
    let mut comparison = Comparison { visited, limits };
    if !comparison.constant(environment, ConstantInfo::Opaque(opaque(label)))? {
        return Err(unsupported());
    }
    for expected in scalar_records() {
        if !comparison.constant(environment, expected)? {
            return Err(unsupported());
        }
    }
    for expected in support() {
        if !comparison.declaration(environment, expected)? {
            return Err(unsupported());
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
