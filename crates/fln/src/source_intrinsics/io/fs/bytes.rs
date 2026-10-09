//! Exact data layouts and bounded dependency identity for counted file reads.
//!
//! `dependencies.txt` is the complete transitive type/body/recursor-rule and
//! constructor/mutual-membership closure of the seven helpers listed below,
//! decoded from SUITE.lock's actual artifacts. Each cached environment digest
//! binds the complete ConstantInfo, including binder metadata and safety.
//! These are comparison data, never declarations or an admission shortcut.
//! The readable layouts additionally document every logical/native boundary.
use super::*;

const DEPENDENCIES: &str = include_str!("bytes/dependencies.txt");
pub(crate) const HELPERS: [&str; 7] = [
    "ByteArray.data",
    "Array.size",
    "Array.getInternal",
    "UInt8.toNat",
    "USize.ofBitVec",
    "USize.ofNat",
    "USize.toNat",
];

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn c(label: &str) -> Expr {
    Expr::const_(name(label), Vec::new())
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed byte layout binder")
}
fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}
fn pi(domain: Expr, body: Expr, style: BinderInfo) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, style)
}
fn of_nat(value: u64) -> Expr {
    let value = Expr::lit(fln_core::expr::Literal::Nat(
        fln_core::expr::NatLit::from_u64(value),
    ));
    apply(
        Expr::const_(name("OfNat.ofNat"), vec![Level::zero()]),
        [c("Nat"), value.clone(), Expr::app(c("instOfNatNat"), value)],
    )
}

fn layouts() -> Vec<ConstantInfo> {
    let mut output = crate::source_intrinsics::string_internal::scalar_records();
    for (label, constructor, domain) in [
        ("UInt8", "UInt8.ofBitVec", Expr::app(c("BitVec"), of_nat(8))),
        (
            "USize",
            "USize.ofBitVec",
            Expr::app(c("BitVec"), c("System.Platform.numBits")),
        ),
    ] {
        output.extend(crate::source_intrinsics::string_internal::record_contract(
            label,
            constructor,
            1,
            pi(domain, c(label), BinderInfo::Default),
        ));
    }
    let u = Level::param(name("u"));
    let sort = Expr::sort(u.clone().succ().expect("fixed Array universe"));
    output.push(ConstantInfo::Induct(InductiveVal {
        base: ConstantVal {
            name: name("Array"),
            level_params: vec![name("u")],
            type_: pi(sort.clone(), sort.clone(), BinderInfo::Default),
        },
        num_params: 1,
        num_indices: 0,
        all: vec![name("Array")],
        ctors: vec![name("Array.mk")],
        num_nested: 0,
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
    }));
    output.push(ConstantInfo::Ctor(ConstructorVal {
        base: ConstantVal {
            name: name("Array.mk"),
            level_params: vec![name("u")],
            type_: pi(
                sort,
                pi(
                    Expr::app(Expr::const_(name("List"), vec![u.clone()]), b(0)),
                    Expr::app(Expr::const_(name("Array"), vec![u]), b(1)),
                    BinderInfo::Default,
                ),
                BinderInfo::Implicit,
            ),
        },
        induct: name("Array"),
        cidx: 0,
        num_params: 1,
        num_fields: 1,
        is_unsafe: false,
    }));
    output
}

fn dependency_name(
    encoded: &str,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<Name, IngressError> {
    let mut name = Name::anonymous();
    for component in encoded.split('/') {
        charge_catalog_node(visited, limits)?;
        name = if let Some(text) = component.strip_prefix("s:") {
            Name::str(name, text)
        } else if let Some(number) = component.strip_prefix("n:") {
            Name::num(
                name,
                number
                    .parse()
                    .expect("fixed native byte dependency numeric component"),
            )
        } else {
            unreachable!("fixed native byte dependency component encoding")
        };
    }
    Ok(name)
}

pub(crate) fn contract_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<(), IngressError> {
    // The existing complete bound models bind Nat/LT/OfNat/power and the
    // logical Fin/BitVec constructors. Read's outer gate also calls this, but
    // the pure USize.ofNat adapter must establish the same data authority.
    let mut models = stdout::result_models();
    models.extend(stdout::word_bound_models());
    models.extend(layouts());
    let mut comparison = Comparison { visited, limits };
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Err(IngressError::UnsupportedNode {
                kind: "counted file read requires the complete checked byte and word layouts",
            });
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    for line in DEPENDENCIES.lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line.split_once('\t').expect("fixed exact dependency row");
        let requested = dependency_name(encoded, visited, limits)?;
        let Some(entry) = environment.entry(&requested) else {
            return Err(IngressError::UnsupportedNode {
                kind: "counted file read dependency is absent",
            });
        };
        if entry.digest().to_hex() != digest {
            return Err(IngressError::UnsupportedNode {
                kind: "counted file read dependency differs from the exact pinned model",
            });
        }
        // A declaration digest intentionally does not bind extensions. Reject
        // a conflicting explicit extern on every dependency independently.
        check_selected_extern_attribute(environment, &requested, externs, visited, limits)?;
    }
    for helper in HELPERS {
        if !extern_attribute_matches(environment, &name(helper), true, externs, visited, limits)? {
            return Err(IngressError::UnsupportedNode {
                kind: "counted file read requires each native conversion extern",
            });
        }
    }
    Ok(())
}

pub(crate) fn word_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if ![name("USize.ofNat"), name("USize.toNat")].contains(requested) {
        return Ok(false);
    }
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    contract_matches(environment, externs, visited, limits)?;
    Ok(true)
}

#[cfg(test)]
pub(crate) fn assert_pin_layouts(environment: &Environment) {
    for expected in layouts() {
        assert!(
            Comparison {
                visited: &mut 0,
                limits: IngressLimits::default()
            }
            .constant(environment, expected.clone())
            .unwrap(),
            "actual pinned byte layout {}",
            expected.name().to_display_string()
        );
    }
    // Independently reconstruct the whole graph from the actual fixture.
    // Adding or omitting a dependency cannot silently change the authority
    // carried by the fixed production digest inventory.
    let expected: std::collections::BTreeSet<_> = DEPENDENCIES
        .lines()
        .map(|line| {
            dependency_name(
                line.split_once('\t').unwrap().0,
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap()
        })
        .collect();
    assert_eq!(expected.len(), 289);
    let mut pending: Vec<_> = HELPERS.into_iter().map(name).collect();
    let mut actual = std::collections::BTreeSet::new();
    while let Some(label) = pending.pop() {
        if !actual.insert(label.clone()) {
            continue;
        }
        let info = environment
            .find(&label)
            .unwrap_or_else(|| panic!("missing actual dependency {}", label.to_display_string()));
        let mut expressions = vec![&info.constant_val().type_];
        match info {
            ConstantInfo::Defn(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Opaque(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Thm(value) => {
                expressions.push(&value.value);
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Induct(value) => {
                pending.extend(value.ctors.iter().cloned());
                pending.extend(value.all.iter().cloned());
            }
            ConstantInfo::Ctor(value) => pending.push(value.induct.clone()),
            ConstantInfo::Rec(value) => {
                expressions.extend(value.rules.iter().map(|rule| &rule.rhs));
                pending.extend(value.rules.iter().map(|rule| rule.ctor.clone()));
                pending.extend(value.all.iter().cloned());
            }
            _ => {}
        }
        while let Some(expression) = expressions.pop() {
            match expression.node() {
                ExprNode::Const { name, .. } => pending.push(name.clone()),
                ExprNode::App { f, a } => {
                    expressions.push(f);
                    expressions.push(a);
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    expressions.push(binder_type);
                    expressions.push(body);
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    expressions.push(type_);
                    expressions.push(value);
                    expressions.push(body);
                }
                ExprNode::Proj {
                    struct_name, expr, ..
                } => {
                    pending.push(struct_name.clone());
                    expressions.push(expr);
                }
                ExprNode::MData { expr, .. } => expressions.push(expr),
                _ => {}
            }
        }
    }
    assert_eq!(
        actual, expected,
        "complete actual byte-helper dependency closure"
    );
}
