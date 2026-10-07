//! Checked numeric dictionaries and the bounded floating-point source contract.
//!
//! Signatures come from the pinned `Init/Data/Float.lean`, `Float32.lean`,
//! `OfScientific.lean` and `UInt/BasicAux.lean`. The scalar types and opaque
//! operations follow the existing String seed's axiom boundary: this does not
//! import the Reference's FloatSpec or BitVec representations. Every candidate
//! still passes both checking engines, and the compiler must match its complete
//! declaration before binding it to a runtime operation.

use crate::instances::numeric::{NumericSeed, app, c, close, fv, local, n, succ};
use crate::records::RecordError;
use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_kernel::Declaration;

fn signature(name: &str, parameters: &[(&str, &str)], result: Expr) -> Declaration {
    let type_ = parameters
        .iter()
        .rev()
        .fold(result, |body, &(label, type_)| {
            Expr::forall_e(n(label), c(type_, &[]), body, BinderInfo::Default)
        });
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    })
}

fn raw_nat(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn conversion_definition(scalar: &str, alias: bool) -> Declaration {
    let suffix = if scalar == "Float" {
        "toFloat"
    } else {
        "toFloat32"
    };
    let name = n(&if alias {
        format!("Nat.{suffix}")
    } else {
        format!("{scalar}.ofNat")
    });
    let number = Expr::bvar(0).expect("fixed conversion binder");
    let value = if alias {
        Expr::app(c(&format!("{scalar}.ofNat"), &[]), number)
    } else {
        app(
            c("OfScientific.ofScientific", &[Level::zero()]),
            [
                c(scalar, &[]),
                c(&format!("instOfScientific{scalar}"), &[]),
                number,
                c("Bool.false", &[]),
                raw_nat(0),
            ],
        )
    };
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            type_: Expr::forall_e(n("n"), c("Nat", &[]), c(scalar, &[]), BinderInfo::Default),
        },
        value: Expr::lam(n("n"), c("Nat", &[]), value, BinderInfo::Default),
        hints: if alias {
            ReducibilityHints::Abbrev
        } else {
            ReducibilityHints::Regular(1)
        },
        safety: DefinitionSafety::Safe,
        all: vec![name],
    })
}

/// Opaque scalar candidates, ordered with every type before its signatures.
/// These are not a substitute for exporting or importing the real Init modules.
pub fn float_seed_declarations() -> Vec<Declaration> {
    let mut declarations: Vec<_> = ["Float", "Float32", "UInt32", "UInt64"]
        .into_iter()
        .map(|name| signature(name, &[], Expr::sort(Level::one())))
        .collect();
    for scalar in ["Float", "Float32"] {
        for operation in ["add", "sub", "mul", "div"] {
            declarations.push(signature(
                &format!("{scalar}.{operation}"),
                &[("a", scalar), ("b", scalar)],
                c(scalar, &[]),
            ));
        }
        for operation in [
            "neg", "abs", "sqrt", "ceil", "floor", "round", "sin", "cos", "tan", "asin", "acos",
            "atan", "sinh", "cosh", "tanh", "asinh", "acosh", "atanh", "exp", "exp2", "log",
            "log2", "log10", "cbrt",
        ] {
            declarations.push(signature(
                &format!("{scalar}.{operation}"),
                &[("a", scalar)],
                c(scalar, &[]),
            ));
        }
        declarations.push(signature(
            &format!("{scalar}.pow"),
            &[("a", scalar), ("b", scalar)],
            c(scalar, &[]),
        ));
        // The pin declares `atan2 (y x : Float)`: y is the first parameter.
        declarations.push(signature(
            &format!("{scalar}.atan2"),
            &[("y", scalar), ("x", scalar)],
            c(scalar, &[]),
        ));
        declarations.push(signature(
            &format!("{scalar}.beq"),
            &[("a", scalar), ("b", scalar)],
            c("Bool", &[]),
        ));
        for operation in ["isNaN", "isFinite", "isInf"] {
            declarations.push(signature(
                &format!("{scalar}.{operation}"),
                &[("a", scalar)],
                c("Bool", &[]),
            ));
        }
        declarations.push(signature(
            &format!("{scalar}.toString"),
            &[("a", scalar)],
            c("String", &[]),
        ));
        let bits = if scalar == "Float" {
            "UInt64"
        } else {
            "UInt32"
        };
        declarations.push(signature(
            &format!("{scalar}.ofBits"),
            &[("bits", bits)],
            c(scalar, &[]),
        ));
        declarations.push(signature(
            &format!("{scalar}.toBits"),
            &[("a", scalar)],
            c(bits, &[]),
        ));
        for unsigned in ["UInt32", "UInt64"] {
            declarations.push(signature(
                &format!("{scalar}.to{unsigned}"),
                &[("a", scalar)],
                c(unsigned, &[]),
            ));
        }
        declarations.push(signature(
            &format!("{scalar}.ofScientific"),
            &[("m", "Nat"), ("s", "Bool"), ("e", "Nat")],
            c(scalar, &[]),
        ));
        for relation in ["lt", "le"] {
            declarations.push(signature(
                &format!("{scalar}.{relation}"),
                &[("a", scalar), ("b", scalar)],
                Expr::sort(Level::zero()),
            ));
            let proposition = app(
                c(&format!("{scalar}.{relation}"), &[]),
                [
                    Expr::bvar(1).expect("fixed comparison binders"),
                    Expr::bvar(0).expect("fixed comparison binders"),
                ],
            );
            declarations.push(signature(
                &format!("{scalar}.dec{}", if relation == "lt" { "Lt" } else { "Le" }),
                &[("a", scalar), ("b", scalar)],
                Expr::app(c("Decidable", &[]), proposition),
            ));
        }
    }
    for unsigned in ["UInt32", "UInt64"] {
        declarations.push(signature(
            &format!("{unsigned}.ofNat"),
            &[("n", "Nat")],
            c(unsigned, &[]),
        ));
        declarations.push(signature(
            &format!("{unsigned}.toNat"),
            &[("n", unsigned)],
            c("Nat", &[]),
        ));
        for scalar in ["Float", "Float32"] {
            declarations.push(signature(
                &format!("{unsigned}.to{scalar}"),
                &[("n", unsigned)],
                c(scalar, &[]),
            ));
        }
    }
    declarations.push(signature(
        "Float.toFloat32",
        &[("a", "Float")],
        c("Float32", &[]),
    ));
    declarations.push(signature(
        "Float32.toFloat",
        &[("a", "Float32")],
        c("Float", &[]),
    ));
    declarations
}

/// Exact compiler authority for a seeded floating-point operation.
/// A declaration with the same name and a different type or value is not this
/// contract and must remain an ordinary source declaration.
pub fn float_intrinsic_seed_declaration(name: &Name) -> Option<Declaration> {
    for scalar in ["Float", "Float32"] {
        for alias in [false, true] {
            let candidate = conversion_definition(scalar, alias);
            if matches!(&candidate, Declaration::Defn(value) if &value.base.name == name) {
                return Some(candidate);
            }
        }
    }
    float_seed_declarations().into_iter().find(
        |declaration| matches!(declaration, Declaration::Axiom(value) if &value.base.name == name),
    )
}

/// Numeric notation with checked dictionary bodies, including both float widths.
/// Registrations are returned separately so callers can publish them only after
/// every declaration has passed the ordinary admission council.
pub fn float_numeric_seed() -> Result<NumericSeed, RecordError> {
    let mut seed = crate::instances::numeric::declarations()?;
    seed.declarations.extend(float_seed_declarations());
    let u = Level::param(n("u"));
    let carrier = local("α", Expr::sort(succ(&u)?), BinderInfo::Default);
    seed.class(
        "Neg",
        &["u"],
        vec![carrier.clone()],
        "neg",
        close(
            &[local("a", fv(&carrier), BinderInfo::Default)],
            fv(&carrier),
            false,
        )?,
        succ(&u)?,
    )?;
    seed.class(
        "OfScientific",
        &["u"],
        vec![carrier.clone()],
        "ofScientific",
        close(
            &[
                local("mantissa", c("Nat", &[]), BinderInfo::Default),
                local("exponentSign", c("Bool", &[]), BinderInfo::Default),
                local("decimalExponent", c("Nat", &[]), BinderInfo::Default),
            ],
            fv(&carrier),
            false,
        )?,
        succ(&u)?,
    )?;
    for scalar in ["Float", "Float32"] {
        for (class, operation) in [
            ("Add", "add"),
            ("Sub", "sub"),
            ("Mul", "mul"),
            ("Div", "div"),
            ("Neg", "neg"),
            ("BEq", "beq"),
            ("OfScientific", "ofScientific"),
        ] {
            seed.named_instance(
                &format!("inst{class}{scalar}"),
                &[],
                &[],
                Expr::app(c(class, &[Level::zero()]), c(scalar, &[])),
                app(
                    c(&format!("{class}.mk"), &[Level::zero()]),
                    [c(scalar, &[]), c(&format!("{scalar}.{operation}"), &[])],
                ),
                // `mid` is 500 in the pin's Init/Notation.lean. This must
                // follow the homogeneous operator adapters at priority 1000.
                (class == "OfScientific" && scalar == "Float").then_some(501),
            )?;
        }
        seed.declarations.push(conversion_definition(scalar, false));
        seed.declarations.push(conversion_definition(scalar, true));
    }
    for scalar in ["Float", "Float32", "UInt32", "UInt64"] {
        let number = local("n", c("Nat", &[]), BinderInfo::Implicit);
        let name = if scalar.starts_with("UInt") {
            format!("{scalar}.instOfNat")
        } else {
            format!("instOfNat{scalar}")
        };
        seed.named_instance(
            &name,
            &[],
            std::slice::from_ref(&number),
            app(c("OfNat", &[Level::zero()]), [c(scalar, &[]), fv(&number)]),
            app(
                c("OfNat.mk", &[Level::zero()]),
                [
                    c(scalar, &[]),
                    fv(&number),
                    Expr::app(c(&format!("{scalar}.ofNat"), &[]), fv(&number)),
                ],
            ),
            None,
        )?;
    }
    for scalar in ["Float", "Float32"] {
        seed.named_instance(
            &format!("instInhabited{scalar}"),
            &[],
            &[],
            Expr::app(c("Inhabited", &[Level::one()]), c(scalar, &[])),
            app(
                c("Inhabited.mk", &[Level::one()]),
                [
                    c(scalar, &[]),
                    Expr::app(
                        c(&format!("UInt64.to{scalar}"), &[]),
                        Expr::app(c("UInt64.ofNat", &[]), raw_nat(0)),
                    ),
                ],
            ),
            None,
        )?;
    }
    Ok(seed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::outcome::Outcome;
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};
    use fln_kernel::verdict::Budget;

    #[test]
    fn numeric_seed_candidates_have_checked_bodies_before_registration() {
        let seed = float_numeric_seed().expect("fixed numeric candidate construction");
        let mut environment = Environment::new();
        for candidate in super::super::source_seed_declarations()
            .into_iter()
            .chain(seed.declarations)
        {
            let name = match &candidate {
                Declaration::Axiom(value) => &value.base.name,
                Declaration::Defn(value) => &value.base.name,
                Declaration::Thm(value) => &value.base.name,
                Declaration::Opaque(value) => &value.base.name,
                Declaration::Inductive(block) => &block.types[0].base.name,
                Declaration::Quotient(values) => &values[0].base.name,
                Declaration::Mutual(values) => &values[0].base.name,
            }
            .to_display_string();
            let Outcome::Complete(admitted) = admit(&environment, candidate, Budget::DEFAULT)
            else {
                panic!("candidate {name} must produce an admission answer");
            };
            let checked = match convene(&Council::nobody_was_asked(), admitted) {
                CouncilOutcome::Agreed(checked) => checked,
                CouncilOutcome::KernelRejected { class, message, .. } => {
                    panic!("candidate {name} failed admission ({class:?}): {message}");
                }
                CouncilOutcome::Halted(halt) => {
                    panic!("candidate {name} halted admission: {}", halt.summary());
                }
            };
            environment = match checked.publish(
                DeclarationBudget::default(),
                CollisionBudget::default(),
                None,
            ) {
                Outcome::Complete(Published::Committed(DeclarationCommitted::Published(
                    result,
                ))) => result.environment,
                Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
                other => panic!("candidate {name} failed publication: {other:?}"),
            };
        }
        for class in ["Inhabited", "Decidable"] {
            environment = crate::instances::register_class(&environment, &n(class))
                .expect("base classes are checked");
        }
        for class in seed.classes {
            environment = crate::instances::register_class(&environment, &class)
                .expect("numeric classes are checked");
        }
        for instance in seed.instances {
            environment = crate::instances::register_instance(&environment, &instance, 1000)
                .expect("numeric dictionaries are checked");
        }
        for (instance, priority) in seed.defaults {
            environment = crate::instances::defaults::register(&environment, &instance, priority)
                .expect("defaults refer to admitted dictionaries");
        }
        assert!(environment.contains(&n("instOfScientificFloat")));
        assert!(environment.contains(&n("instOfNatFloat32")));
        assert!(environment.contains(&n("instBEqOfDecidableEq")));
    }
}
