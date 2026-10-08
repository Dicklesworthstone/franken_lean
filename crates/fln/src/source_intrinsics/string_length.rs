//! The imported public string length operation uses its explicit native extern.
//!
//! The pin's `String.length` is an ordinary safe definition over `String.toList`.
//! Its extern is a separate execution contract. Recognize the complete root and
//! immediate string view, together with the scalar and container families they
//! name, before selecting the existing generated row. These are compiler-local
//! comparison models; they are never installed as replacement declarations.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}

fn apply(function: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(function, Expr::app)
}

fn arrow(domain: Expr, result: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, result, BinderInfo::Default)
}

fn lambda(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn bound(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed imported string length contract index")
}

fn definition(label: &str, height: u32, result: Expr, body: Expr) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: Vec::new(),
            type_: arrow(constant("String"), result),
        },
        value: lambda(constant("String"), body),
        hints: ReducibilityHints::Regular(height),
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

fn definitions() -> [ConstantInfo; 2] {
    let characters = Expr::app(
        Expr::const_(name("List"), vec![Level::zero()]),
        constant("Char"),
    );
    [
        definition(
            "String.length",
            24,
            constant("Nat"),
            apply(
                Expr::const_(name("List.length"), vec![Level::zero()]),
                [
                    constant("Char"),
                    Expr::app(constant("String.toList"), bound(0)),
                ],
            ),
        ),
        definition(
            "String.toList",
            23,
            characters,
            apply(
                Expr::const_(name("Array.toList"), vec![Level::zero()]),
                [
                    constant("Char"),
                    Expr::app(constant("String.Internal.toArray"), bound(0)),
                ],
            ),
        ),
    ]
}

fn character_records() -> Vec<ConstantInfo> {
    let width = Expr::lit(Literal::Nat(NatLit::from_u64(32)));
    let width = apply(
        Expr::const_(name("OfNat.ofNat"), vec![Level::zero()]),
        [
            constant("Nat"),
            width.clone(),
            Expr::app(constant("instOfNatNat"), width),
        ],
    );
    string_internal::record_contract(
        "Char",
        "Char.mk",
        2,
        arrow(
            constant("UInt32"),
            arrow(
                Expr::app(constant("UInt32.isValidChar"), bound(0)),
                constant("Char"),
            ),
        ),
    )
    .into_iter()
    .chain(string_internal::record_contract(
        "UInt32",
        "UInt32.ofBitVec",
        1,
        arrow(Expr::app(constant("BitVec"), width), constant("UInt32")),
    ))
    .collect()
}

fn list_family() -> Declaration {
    fln_elab::seed::imported_list_recursion_model_declarations()
        .into_iter()
        .find(|declaration| {
            matches!(declaration, Declaration::Inductive(block)
                if block.types.first().is_some_and(|family| family.base.name == name("List")))
        })
        .expect("the existing imported List model includes its family")
}

pub(crate) fn imported_string_length_matches(
    environment: &Environment,
    requested: &Name,
    cache: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if requested != &name("String.length") {
        return Ok(false);
    }
    if !extern_attribute_matches(environment, requested, true, cache, visited, limits)? {
        return Ok(false);
    }
    let unsupported = || IngressError::UnsupportedNode {
        kind: "imported String.length extern does not match its complete supported contract",
    };
    if !extern_attribute_matches(
        environment,
        &name("String.toList"),
        true,
        cache,
        visited,
        limits,
    )? {
        return Err(unsupported());
    }
    let mut comparison = Comparison { visited, limits };
    for expected in definitions()
        .into_iter()
        .chain(string_internal::scalar_records())
        .chain(character_records())
    {
        if !comparison.constant(environment, expected)? {
            return Err(unsupported());
        }
    }
    for expected in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        list_family(),
    ] {
        if !comparison.declaration(environment, expected)? {
            return Err(unsupported());
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
