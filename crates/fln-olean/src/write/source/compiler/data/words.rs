//! Structural authority for unsigned scalars in computed-field artifacts.
//! A declaration named UIntN is insufficient: the actual checked chain must
//! be UIntN -> BitVec N -> Fin (HPow.hPow 2 N), with Fin's numeric proof
//! field. The caller separately reduces that actual bound before publication;
//! dictionary names alone never prove the power operation's value.
//! This is a data-layout projection, not an executable word-conversion adapter.
use super::*;
use fln_core::expr::{Literal, NatLit};
use fln_env::constants::{ConstructorVal, DefinitionSafety};

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn c(value: &str) -> Expr {
    Expr::const_(name(value), Vec::new())
}

fn cp(value: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(name(value), levels)
}

fn b(index: u32) -> Expr {
    Expr::bvar(index).expect("fixed word model binder")
}

fn app(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}

fn literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn numeral(value: u64) -> Expr {
    let value = literal(value);
    app(
        cp("OfNat.ofNat", vec![Level::zero()]),
        [c("Nat"), value.clone(), Expr::app(c("instOfNatNat"), value)],
    )
}

// Alpha comparison is bounded independently of expression sharing. Binder
// names/info and source metadata do not change the constructor's data shape.
fn same<E>(
    actual: &Expr,
    expected: &Expr,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let mut pending = vec![(actual, expected)];
    while let Some((actual, expected)) = pending.pop() {
        charge(1)?;
        let actual = without_metadata(actual, charge)?;
        let expected = without_metadata(expected, charge)?;
        match (actual.node(), expected.node()) {
            (ExprNode::BVar { idx: actual }, ExprNode::BVar { idx: expected })
                if actual == expected => {}
            (ExprNode::Sort { level: actual }, ExprNode::Sort { level: expected })
                if actual == expected => {}
            (
                ExprNode::Const {
                    name: a,
                    levels: al,
                },
                ExprNode::Const {
                    name: e,
                    levels: el,
                },
            ) if a == e && al == el => {}
            (ExprNode::Lit { literal: actual }, ExprNode::Lit { literal: expected })
                if actual == expected => {}
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: ef, a: ea }) => {
                pending.push((af, ef));
                pending.push((aa, ea));
            }
            (
                ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: et,
                    body: eb,
                    ..
                },
            )
            | (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::Lam {
                    binder_type: et,
                    body: eb,
                    ..
                },
            ) => {
                pending.push((at, et));
                pending.push((ab, eb));
            }
            (
                ExprNode::Proj {
                    struct_name: an,
                    idx: ai,
                    expr: ae,
                },
                ExprNode::Proj {
                    struct_name: en,
                    idx: ei,
                    expr: ee,
                },
            ) if an == en && ai == ei => pending.push((ae, ee)),
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn family<'a, E>(
    family: &str,
    constructor: &str,
    parameters: u32,
    fields: u32,
    find: &mut impl FnMut(&Name) -> Option<&'a ConstantInfo>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<Option<(&'a InductiveVal, &'a ConstructorVal)>, E> {
    charge(1)?;
    let family_name = name(family);
    let constructor_name = name(constructor);
    let Some(ConstantInfo::Induct(family)) = find(&family_name) else {
        return Ok(None);
    };
    let Some(ConstantInfo::Ctor(constructor)) = find(&constructor_name) else {
        return Ok(None);
    };
    if family.base.name != family_name
        || family.is_unsafe
        || family.is_rec
        || family.num_params != parameters
        || family.num_indices != 0
        || family.num_nested != 0
        || family.all.as_slice() != std::slice::from_ref(&family_name)
        || family.ctors.as_slice() != std::slice::from_ref(&constructor_name)
        || constructor.base.name != constructor_name
        || constructor.is_unsafe
        || constructor.induct != family_name
        || constructor.cidx != 0
        || constructor.num_params != parameters
        || constructor.num_fields != fields
        || constructor.base.level_params != family.base.level_params
    {
        return Ok(None);
    }
    Ok(Some((family, constructor)))
}

fn natural_numerals<'a, E>(
    find: &mut impl FnMut(&Name) -> Option<&'a ConstantInfo>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let Some((family, constructor)) = family("OfNat", "OfNat.mk", 2, 1, find, charge)? else {
        return Ok(false);
    };
    let [universe] = family.base.level_params.as_slice() else {
        return Ok(false);
    };
    let level = Level::param(universe.clone());
    let type_ =
        Expr::sort(Level::succ(level.clone()).expect("one successor of a word-model parameter"));
    if !same(
        &family.base.type_,
        &pi(type_.clone(), pi(c("Nat"), type_.clone())),
        charge,
    )? || !same(
        &constructor.base.type_,
        &pi(
            type_.clone(),
            pi(
                c("Nat"),
                pi(b(1), app(cp("OfNat", vec![level]), [b(2), b(1)])),
            ),
        ),
        charge,
    )? {
        return Ok(false);
    }
    let Some(ConstantInfo::Defn(dictionary)) = find(&name("instOfNatNat")) else {
        return Ok(false);
    };
    let Some(ConstantInfo::Defn(projection)) = find(&name("OfNat.ofNat")) else {
        return Ok(false);
    };
    if dictionary.safety != DefinitionSafety::Safe
        || !dictionary.base.level_params.is_empty()
        || projection.safety != DefinitionSafety::Safe
        || projection.base.level_params.len() != 1
    {
        return Ok(false);
    }
    let level = Level::param(projection.base.level_params[0].clone());
    let type_ =
        Expr::sort(Level::succ(level.clone()).expect("one successor of a word-model parameter"));
    let dictionary_type = app(cp("OfNat", vec![level]), [b(1), b(0)]);
    Ok(same(
        &dictionary.base.type_,
        &pi(
            c("Nat"),
            app(cp("OfNat", vec![Level::zero()]), [c("Nat"), b(0)]),
        ),
        charge,
    )? && same(
        &dictionary.value,
        &lam(
            c("Nat"),
            app(cp("OfNat.mk", vec![Level::zero()]), [c("Nat"), b(0), b(0)]),
        ),
        charge,
    )? && same(
        &projection.base.type_,
        &pi(
            type_.clone(),
            pi(c("Nat"), pi(dictionary_type.clone(), b(2))),
        ),
        charge,
    )? && same(
        &projection.value,
        &lam(
            type_,
            lam(
                c("Nat"),
                lam(dictionary_type, Expr::proj(name("OfNat"), 0, b(0))),
            ),
        ),
        charge,
    )?)
}

fn natural_order<'a, E>(
    find: &mut impl FnMut(&Name) -> Option<&'a ConstantInfo>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    charge(1)?;
    let family_name = name("Nat.le");
    let constructors = [name("Nat.le.refl"), name("Nat.le.step")];
    let Some(ConstantInfo::Induct(family)) = find(&family_name) else {
        return Ok(false);
    };
    if family.base.name != family_name
        || !family.base.level_params.is_empty()
        || family.is_unsafe
        || !family.is_rec
        || family.num_params != 1
        || family.num_indices != 1
        || family.num_nested != 0
        || family.all.as_slice() != std::slice::from_ref(&family_name)
        || family.ctors.as_slice() != constructors
        || !same(
            &family.base.type_,
            &pi(c("Nat"), pi(c("Nat"), Expr::sort(Level::zero()))),
            charge,
        )?
    {
        return Ok(false);
    }
    let expected = [
        pi(c("Nat"), app(c("Nat.le"), [b(0), b(0)])),
        pi(
            c("Nat"),
            pi(
                c("Nat"),
                pi(
                    app(c("Nat.le"), [b(1), b(0)]),
                    app(c("Nat.le"), [b(2), Expr::app(c("Nat.succ"), b(1))]),
                ),
            ),
        ),
    ];
    for (index, constructor_name) in constructors.iter().enumerate() {
        charge(1)?;
        let Some(ConstantInfo::Ctor(constructor)) = find(constructor_name) else {
            return Ok(false);
        };
        if constructor.base.name != *constructor_name
            || !constructor.base.level_params.is_empty()
            || constructor.is_unsafe
            || constructor.induct != family_name
            || constructor.cidx as usize != index
            || constructor.num_params != 1
            || constructor.num_fields != if index == 0 { 0 } else { 2 }
            || !same(&constructor.base.type_, &expected[index], charge)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn unsigned_word_matches<'a, E>(
    width: u32,
    find: &mut impl FnMut(&Name) -> Option<&'a ConstantInfo>,
    charge: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    charge(1)?;
    let word_name = match width {
        8 => "UInt8",
        16 => "UInt16",
        32 => "UInt32",
        64 => "UInt64",
        _ => return Ok(false),
    };
    let Some((word, word_ctor)) = family(
        word_name,
        &format!("{word_name}.ofBitVec"),
        0,
        1,
        find,
        charge,
    )?
    else {
        return Ok(false);
    };
    let Some((bits, bits_ctor)) = family("BitVec", "BitVec.ofFin", 1, 1, find, charge)? else {
        return Ok(false);
    };
    let Some((finite, finite_ctor)) = family("Fin", "Fin.mk", 1, 2, find, charge)? else {
        return Ok(false);
    };
    if [word, bits, finite]
        .iter()
        .any(|family| !family.base.level_params.is_empty())
    {
        return Ok(false);
    }
    let type_ = Expr::sort(Level::one());
    let pow = app(
        cp("HPow.hPow", vec![Level::zero(); 3]),
        [
            c("Nat"),
            c("Nat"),
            c("Nat"),
            app(
                cp("instHPow", vec![Level::zero(); 2]),
                [
                    c("Nat"),
                    c("Nat"),
                    app(
                        cp("instPowNat", vec![Level::zero()]),
                        [c("Nat"), c("instNatPowNat")],
                    ),
                ],
            ),
            numeral(2),
            b(0),
        ],
    );
    let proof = app(
        cp("LT.lt", vec![Level::zero()]),
        [c("Nat"), c("instLTNat"), b(0), b(1)],
    );
    Ok(same(&word.base.type_, &type_, charge)?
        && same(&bits.base.type_, &pi(c("Nat"), type_.clone()), charge)?
        && same(&finite.base.type_, &pi(c("Nat"), type_), charge)?
        && same(
            &word_ctor.base.type_,
            &pi(
                Expr::app(c("BitVec"), numeral(u64::from(width))),
                c(word_name),
            ),
            charge,
        )?
        && same(
            &bits_ctor.base.type_,
            &pi(
                c("Nat"),
                pi(Expr::app(c("Fin"), pow), Expr::app(c("BitVec"), b(1))),
            ),
            charge,
        )?
        && same(
            &finite_ctor.base.type_,
            &pi(c("Nat"), pi(c("Nat"), pi(proof, Expr::app(c("Fin"), b(2))))),
            charge,
        )?
        && natural_numerals(find, charge)?
        && natural_order(find, charge)?)
}
