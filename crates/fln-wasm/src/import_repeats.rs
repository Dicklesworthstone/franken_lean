//! Import compatibility for independently read theorem and erased-axiom rows.
//!
//! Compatibility never checks a replacement proof. Every nonidentical theorem
//! repeat is separately admitted under a fresh name after the module's new
//! declarations, against that module's actual checked import closure.

use std::collections::BTreeSet;

use fln_checker::environment::{
    ConstantDeclaration, ConstantEntry, ConstantEnvironment, ConstantKind, ConstantSafety,
};
use fln_checker::wire::{
    DecodeBudget, DecodeOutcome, ExprId, ExprNode, LevelId, LevelNode, WireExpr, WireName,
    decode_name,
};
use fln_core::name::Name;
use fln_hash::canon::Canonical;

type RepeatResult<T> = Result<T, &'static str>;

struct Work<'a> {
    remaining: &'a mut u64,
}

impl Work<'_> {
    fn charge(&mut self, count: usize) -> RepeatResult<()> {
        *self.remaining = self
            .remaining
            .checked_sub(u64::try_from(count).unwrap_or(u64::MAX))
            .ok_or("import repeat comparison budget exhausted")?;
        Ok(())
    }
}

enum Pair {
    Expression(ExprId, ExprId),
    Level(LevelId, LevelId),
}

fn theorem_members(declaration: &ConstantDeclaration) -> Option<&[WireName]> {
    declaration.body_value().and(declaration.body_mutual())
}

fn push(pending: &mut Vec<Pair>, pair: Pair) -> RepeatResult<()> {
    pending
        .try_reserve(1)
        .map_err(|_| "import repeat comparison allocation failed")?;
    pending.push(pair);
    Ok(())
}

/// The import rule's structural expression equivalence: binder names/styles
/// and let names are irrelevant; metadata and let non-dependence are not.
/// Both expression and universe pairs are memoized, never expanded as trees.
fn statements_equivalent(
    left: &WireExpr,
    right: &WireExpr,
    work: &mut Work<'_>,
) -> RepeatResult<bool> {
    let mut pending = Vec::new();
    push(&mut pending, Pair::Expression(left.root(), right.root()))?;
    let mut expressions = BTreeSet::new();
    let mut levels = BTreeSet::new();
    while let Some(pair) = pending.pop() {
        work.charge(1)?;
        match pair {
            Pair::Level(a, b) => {
                if !levels.insert((a, b)) {
                    continue;
                }
                let (Some(a), Some(b)) = (left.level(a), right.level(b)) else {
                    return Err("internal fault: import repeat universe node is absent");
                };
                match (a, b) {
                    (LevelNode::Zero, LevelNode::Zero) => {}
                    (LevelNode::Succ(a), LevelNode::Succ(b)) => {
                        push(&mut pending, Pair::Level(*a, *b))?;
                    }
                    (LevelNode::Max(a1, a2), LevelNode::Max(b1, b2))
                    | (LevelNode::IMax(a1, a2), LevelNode::IMax(b1, b2)) => {
                        push(&mut pending, Pair::Level(*a1, *b1))?;
                        push(&mut pending, Pair::Level(*a2, *b2))?;
                    }
                    (LevelNode::Parameter(a), LevelNode::Parameter(b))
                    | (LevelNode::Meta(a), LevelNode::Meta(b))
                        if a == b => {}
                    _ => return Ok(false),
                }
            }
            Pair::Expression(a, b) => {
                if !expressions.insert((a, b)) {
                    continue;
                }
                let (Some(a), Some(b)) = (left.node(a), right.node(b)) else {
                    return Err("internal fault: import repeat expression node is absent");
                };
                match (a, b) {
                    (ExprNode::Bound { index: a }, ExprNode::Bound { index: b }) if a == b => {}
                    (ExprNode::Free { name: a }, ExprNode::Free { name: b })
                    | (ExprNode::Meta { name: a }, ExprNode::Meta { name: b })
                        if a == b => {}
                    (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                        push(&mut pending, Pair::Level(*a, *b))?;
                    }
                    (
                        ExprNode::Constant {
                            name: a,
                            levels: au,
                        },
                        ExprNode::Constant {
                            name: b,
                            levels: bu,
                        },
                    ) if a == b && au.len() == bu.len() => {
                        work.charge(au.len())?;
                        for (a, b) in au.iter().zip(bu) {
                            push(&mut pending, Pair::Level(*a, *b))?;
                        }
                    }
                    (
                        ExprNode::Apply {
                            function: af,
                            argument: aa,
                        },
                        ExprNode::Apply {
                            function: bf,
                            argument: ba,
                        },
                    ) => {
                        push(&mut pending, Pair::Expression(*af, *bf))?;
                        push(&mut pending, Pair::Expression(*aa, *ba))?;
                    }
                    (
                        ExprNode::Lambda {
                            binder_type: at,
                            body: ab,
                            ..
                        },
                        ExprNode::Lambda {
                            binder_type: bt,
                            body: bb,
                            ..
                        },
                    )
                    | (
                        ExprNode::Forall {
                            binder_type: at,
                            body: ab,
                            ..
                        },
                        ExprNode::Forall {
                            binder_type: bt,
                            body: bb,
                            ..
                        },
                    ) => {
                        push(&mut pending, Pair::Expression(*at, *bt))?;
                        push(&mut pending, Pair::Expression(*ab, *bb))?;
                    }
                    (
                        ExprNode::Let {
                            type_: at,
                            value: av,
                            body: ab,
                            non_dependent: an,
                            ..
                        },
                        ExprNode::Let {
                            type_: bt,
                            value: bv,
                            body: bb,
                            non_dependent: bn,
                            ..
                        },
                    ) if an == bn => {
                        push(&mut pending, Pair::Expression(*at, *bt))?;
                        push(&mut pending, Pair::Expression(*av, *bv))?;
                        push(&mut pending, Pair::Expression(*ab, *bb))?;
                    }
                    (
                        ExprNode::NatLiteral { limbs_le: a },
                        ExprNode::NatLiteral { limbs_le: b },
                    ) => {
                        work.charge(a.len())?;
                        if a != b {
                            return Ok(false);
                        }
                    }
                    (ExprNode::StringLiteral(a), ExprNode::StringLiteral(b)) => {
                        work.charge(a.len())?;
                        if a != b {
                            return Ok(false);
                        }
                    }
                    (
                        ExprNode::Metadata {
                            entries: a,
                            expression: ae,
                        },
                        ExprNode::Metadata {
                            entries: b,
                            expression: be,
                        },
                    ) => {
                        work.charge(a.len())?;
                        if a != b {
                            return Ok(false);
                        }
                        push(&mut pending, Pair::Expression(*ae, *be))?;
                    }
                    (
                        ExprNode::Projection {
                            structure_name: a,
                            index: ai,
                            expression: ae,
                        },
                        ExprNode::Projection {
                            structure_name: b,
                            index: bi,
                            expression: be,
                        },
                    ) if a == b && ai == bi => {
                        push(&mut pending, Pair::Expression(*ae, *be))?;
                    }
                    _ => return Ok(false),
                }
            }
        }
    }
    Ok(true)
}

/// A narrow independent counterpart of native import `subsumesInfo`.
/// Nonidentical axiom/axiom subsumption and other declaration kinds remain
/// unsupported. Successful compatibility does not authorize a theorem body.
pub(super) fn compatible(
    left: &ConstantEntry,
    right: &ConstantEntry,
    remaining: &mut u64,
) -> RepeatResult<bool> {
    let mut work = Work { remaining };
    work.charge(1)?;
    if left.name() != right.name() {
        return Ok(false);
    }
    let (a, b) = (left.declaration(), right.declaration());
    if a.safety() != ConstantSafety::Safe || b.safety() != ConstantSafety::Safe {
        return Ok(false);
    }
    work.charge(a.level_parameters().len())?;
    if a.level_parameters() != b.level_parameters() {
        return Ok(false);
    }
    let metadata_matches = match (a.kind(), b.kind()) {
        (ConstantKind::Theorem, ConstantKind::Theorem) => {
            match (theorem_members(a), theorem_members(b)) {
                (Some(am), Some(bm)) => {
                    work.charge(am.len())?;
                    am == bm
                }
                _ => false,
            }
        }
        (ConstantKind::Theorem, ConstantKind::Axiom) => {
            theorem_members(a) == Some(std::slice::from_ref(left.name()))
        }
        (ConstantKind::Axiom, ConstantKind::Theorem) => {
            theorem_members(b) == Some(std::slice::from_ref(right.name()))
        }
        _ => false,
    };
    if !metadata_matches {
        return Ok(false);
    }
    statements_equivalent(a.type_(), b.type_(), &mut work)
}

/// Native repeat checking renames the declaration and its `all` entries only.
/// References in the statement and proof continue to name the checked import.
pub(super) fn fresh_theorem(
    entry: &ConstantEntry,
    environment: &ConstantEnvironment,
    maximum_work: u64,
) -> RepeatResult<ConstantEntry> {
    let declaration = entry.declaration();
    if declaration.kind() != ConstantKind::Theorem || declaration.safety() != ConstantSafety::Safe {
        return Err("internal fault: import repeat is not a safe theorem");
    }
    let Some(value) = declaration.body_value() else {
        return Err("internal fault: repeated theorem has no proof");
    };
    let Some(mutual) = declaration.body_mutual() else {
        return Err("internal fault: repeated theorem has no mutual metadata");
    };
    let mut remaining = maximum_work;
    let mut work = Work {
        remaining: &mut remaining,
    };
    work.charge(entry.name().parts().len())?;
    let base = Name::str(
        super::wire_name_to_core(entry.name()),
        "_fln_subsumed_repeat",
    );
    let mut suffix = 0u64;
    let fresh = loop {
        work.charge(1)?;
        let candidate = if suffix == 0 {
            base.clone()
        } else {
            Name::num(base.clone(), suffix)
        };
        let bytes = candidate
            .to_canonical_bytes_within(usize::try_from(*work.remaining).unwrap_or(usize::MAX))
            .ok_or("import repeat comparison budget exhausted")?;
        work.charge(bytes.len())?;
        let candidate =
            match decode_name(&bytes, DecodeBudget::new(bytes.len() as u64, maximum_work)) {
                DecodeOutcome::Complete(Ok(candidate)) => candidate,
                DecodeOutcome::Inconclusive(_) => {
                    return Err("import repeat name decoding budget exhausted");
                }
                DecodeOutcome::Complete(Err(_)) => {
                    return Err("internal fault: generated import repeat name is malformed");
                }
            };
        if environment.find(&candidate).is_none() {
            break candidate;
        }
        suffix = suffix
            .checked_add(1)
            .ok_or("import repeat name space exhausted")?;
    };
    work.charge(mutual.len())?;
    work.charge(declaration.level_parameters().len())?;
    let mut renamed = Vec::new();
    renamed
        .try_reserve_exact(mutual.len())
        .map_err(|_| "import repeat metadata allocation failed")?;
    renamed.extend(mutual.iter().map(|name| {
        if name == entry.name() {
            fresh.clone()
        } else {
            name.clone()
        }
    }));
    let mut parameters = Vec::new();
    parameters
        .try_reserve_exact(declaration.level_parameters().len())
        .map_err(|_| "import repeat parameter allocation failed")?;
    parameters.extend(declaration.level_parameters().iter().cloned());
    Ok(ConstantEntry::new(
        fresh,
        ConstantDeclaration::theorem(
            parameters,
            declaration.type_().clone(),
            value.clone(),
            renamed,
        ),
    ))
}
