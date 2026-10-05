//! The identity of one reading of a declaration, independent of how its terms
//! share subterms (bead `franken_lean-z8j.1.14`).
//!
//! The council compares two readings of every `.olean` declaration: the one K1
//! judges (decoded by `fln-olean`) and the checker's own ([`crate::olean`]). Two
//! decoders legitimately share subterms differently, so arena positions cannot be
//! compared. Each node is hashed from its own fields and its children's digests
//! instead, once per node, so the cost is linear in the shared size of the term,
//! never in its tree size.
use crate::wire::{BinderStyle, ExprNode, LevelNode, MetadataValue, NamePart, WireExpr, WireName};
use fln_hash::domain::{Digest, Domain, DomainHasher};

fn hasher(kind: &[u8]) -> DomainHasher {
    let mut hasher = DomainHasher::new(Domain::CacheKey);
    hasher.update(b"fln.checker-reading/1\0");
    field(&mut hasher, kind);
    hasher
}

fn field(hasher: &mut DomainHasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

pub(crate) fn name(hasher: &mut DomainHasher, name: &WireName) {
    hasher.update(&(name.parts().len() as u64).to_le_bytes());
    for part in name.parts() {
        match part {
            NamePart::Text(text) => {
                hasher.update(&[0]);
                field(hasher, text.as_bytes());
            }
            NamePart::Numeric { value, overflowed } => {
                hasher.update(&[1, u8::from(*overflowed)]);
                hasher.update(&value.to_le_bytes());
            }
        }
    }
}

pub(crate) fn names(hasher: &mut DomainHasher, list: &[WireName]) {
    hasher.update(&(list.len() as u64).to_le_bytes());
    for item in list {
        name(hasher, item);
    }
}

fn level_digests(levels: &[LevelNode]) -> Vec<Digest> {
    let mut digests: Vec<Digest> = Vec::with_capacity(levels.len());
    for node in levels {
        let child = |id: crate::wire::LevelId| digests[id.index()].0;
        let mut h = hasher(b"level");
        match node {
            LevelNode::Zero => h.update(&[0]),
            LevelNode::Succ(of) => h.update(&[1]).update(&child(*of)),
            LevelNode::Max(left, right) => {
                h.update(&[2]).update(&child(*left)).update(&child(*right))
            }
            LevelNode::IMax(left, right) => {
                h.update(&[3]).update(&child(*left)).update(&child(*right))
            }
            LevelNode::Parameter(n) => {
                h.update(&[4]);
                name(&mut h, n);
                &mut h
            }
            LevelNode::Meta(n) => {
                h.update(&[5]);
                name(&mut h, n);
                &mut h
            }
        };
        digests.push(h.finalize());
    }
    digests
}

fn style(style: BinderStyle) -> u8 {
    match style {
        BinderStyle::Default => 0,
        BinderStyle::Implicit => 1,
        BinderStyle::StrictImplicit => 2,
        BinderStyle::InstanceImplicit => 3,
    }
}

/// The digest of a term, from its root, modulo sharing. Arenas place children
/// before parents, so one forward pass sees every child before its parent.
pub fn expr_digest(expr: &WireExpr) -> Digest {
    let levels = level_digests(expr.levels());
    let mut digests: Vec<Digest> = Vec::with_capacity(expr.nodes().len());
    for node in expr.nodes() {
        let child = |id: crate::wire::ExprId| digests[id.index()].0;
        let mut h = hasher(b"expr");
        match node {
            ExprNode::Bound { index } => {
                h.update(&[0]).update(&index.to_le_bytes());
            }
            ExprNode::Free { name: n } => {
                h.update(&[1]);
                name(&mut h, n);
            }
            ExprNode::Meta { name: n } => {
                h.update(&[2]);
                name(&mut h, n);
            }
            ExprNode::Sort { level } => {
                h.update(&[3]).update(&levels[level.index()].0);
            }
            ExprNode::Constant {
                name: n,
                levels: us,
            } => {
                h.update(&[4]);
                name(&mut h, n);
                h.update(&(us.len() as u64).to_le_bytes());
                for u in us {
                    h.update(&levels[u.index()].0);
                }
            }
            ExprNode::Apply { function, argument } => {
                h.update(&[5])
                    .update(&child(*function))
                    .update(&child(*argument));
            }
            ExprNode::Lambda {
                binder_name,
                binder_type,
                body,
                style: s,
            }
            | ExprNode::Forall {
                binder_name,
                binder_type,
                body,
                style: s,
            } => {
                h.update(&[if matches!(node, ExprNode::Lambda { .. }) {
                    6
                } else {
                    7
                }]);
                name(&mut h, binder_name);
                h.update(&child(*binder_type))
                    .update(&child(*body))
                    .update(&[style(*s)]);
            }
            ExprNode::Let {
                declaration_name,
                type_,
                value,
                body,
                non_dependent,
            } => {
                h.update(&[8]);
                name(&mut h, declaration_name);
                h.update(&child(*type_))
                    .update(&child(*value))
                    .update(&child(*body))
                    .update(&[u8::from(*non_dependent)]);
            }
            ExprNode::NatLiteral { limbs_le } => {
                h.update(&[9])
                    .update(&(limbs_le.len() as u64).to_le_bytes());
                for limb in limbs_le {
                    h.update(&limb.to_le_bytes());
                }
            }
            ExprNode::StringLiteral(text) => {
                h.update(&[10]);
                field(&mut h, text.as_bytes());
            }
            ExprNode::Metadata {
                entries,
                expression,
            } => {
                h.update(&[11])
                    .update(&(entries.len() as u64).to_le_bytes());
                for (key, value) in entries {
                    name(&mut h, key);
                    match value {
                        MetadataValue::Text(text) => {
                            h.update(&[0]);
                            field(&mut h, text.as_bytes());
                        }
                        MetadataValue::Bool(value) => {
                            h.update(&[1, u8::from(*value)]);
                        }
                        MetadataValue::Name(value) => {
                            h.update(&[2]);
                            name(&mut h, value);
                        }
                        MetadataValue::Nat(value) => {
                            h.update(&[3]).update(&value.to_le_bytes());
                        }
                        MetadataValue::Int(value) => {
                            h.update(&[4]).update(&value.to_le_bytes());
                        }
                        MetadataValue::Syntax(value) => {
                            h.update(&[5]).update(&value.to_le_bytes());
                        }
                    }
                }
                h.update(&child(*expression));
            }
            ExprNode::Projection {
                structure_name,
                index,
                expression,
            } => {
                h.update(&[12]);
                name(&mut h, structure_name);
                h.update(&index.to_le_bytes()).update(&child(*expression));
            }
        }
        digests.push(h.finalize());
    }
    digests
        .get(expr.root().index())
        .copied()
        .unwrap_or(Digest([0; 32]))
}

pub(crate) fn start(kind: &[u8]) -> DomainHasher {
    hasher(kind)
}
