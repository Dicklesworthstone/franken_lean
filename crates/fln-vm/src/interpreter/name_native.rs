//! Native `Lean.Name.beq` (Init/Prelude.lean:4782), including arbitrary Nat
//! components. Names are compared structurally, never by cached hash alone.
//! Validate both complete borrowed carriers before comparing: even an alias
//! cannot make a malformed cached field or an exhausted walk succeed.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity};
use fln_core::lean_hash::{mix_hash, string_hash};
use std::collections::HashSet;

// Match the other native Name operations' bounded membrane. One allowance
// covers both operands, including copied strings and the complete mpz limbs.
const MAX_NAME_NODES: u64 = 1_000_000;
const MAX_NAME_BYTES: u64 = 16 * 1024 * 1024;
const HEADER_BYTES: usize = std::mem::size_of::<fln_rt::obj::Header>();
const WORD_BYTES: usize = std::mem::size_of::<usize>();

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Beq,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        (row == "extern:Lean.Name.beq").then_some(Self::Beq)
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, 2)?;
        let equal = equal(&args[0], &args[1], &mut Budget::default())?;
        // lean_name_eq returns a uint8_t in the generated ABI contract.
        Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(equal))))
    }
}

#[derive(PartialEq, Eq)]
enum Component {
    Str(String),
    Num(Vec<u64>),
}

impl Component {
    fn hash(&self) -> u64 {
        match self {
            Self::Str(value) => string_hash(value),
            Self::Num(value) => match value.as_slice() {
                [] => 0,
                [value] => *value,
                // Name.hash uses 17 for every Nat >= UInt64.size
                // (Init/Prelude.lean:4717). Equality still uses every limb.
                _ => 17,
            },
        }
    }
}

struct Part {
    component: Component,
    stored_hash: Option<u64>,
}

struct Budget {
    nodes: u64,
    bytes: u64,
    max_nodes: u64,
    max_bytes: u64,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            nodes: 0,
            bytes: 0,
            max_nodes: MAX_NAME_NODES,
            max_bytes: MAX_NAME_BYTES,
        }
    }
}

impl Budget {
    fn node(&mut self) -> Result<(), IntrinsicFailure> {
        self.nodes = self.nodes.saturating_add(1);
        limit("name equality nodes", self.max_nodes, self.nodes)
    }

    fn bytes(&mut self, size: usize) -> Result<(), IntrinsicFailure> {
        self.bytes = self.bytes.saturating_add(size as u64);
        limit("name equality bytes", self.max_bytes, self.bytes)
    }

    fn object(&mut self, value: &Obj) -> Result<(), IntrinsicFailure> {
        if !value.is_scalar() {
            self.bytes(value.byte_size())?;
        }
        Ok(())
    }
}

fn limit(resource: &'static str, allowed: u64, observed: u64) -> Result<(), IntrinsicFailure> {
    if observed > allowed {
        return Err(IntrinsicFailure::MirrorResource {
            resource,
            allowed,
            observed,
        });
    }
    Ok(())
}

fn equal(left: &Obj, right: &Obj, budget: &mut Budget) -> Result<bool, IntrinsicFailure> {
    let left = checked_name(left, budget)?;
    let right = checked_name(right, budget)?;
    Ok(left
        .iter()
        .map(|part| &part.component)
        .eq(right.iter().map(|part| &part.component)))
}

fn checked_name(value: &Obj, budget: &mut Budget) -> Result<Vec<Part>, IntrinsicFailure> {
    let mut cursor = value.clone_ref();
    let mut seen = HashSet::new();
    let mut parts = Vec::new();
    loop {
        budget.node()?;
        if cursor.is_scalar() {
            if cursor.unbox() != 0 {
                return Err(VmRefusal::InvalidCtorObject.into());
            }
            break;
        }
        budget.object(&cursor)?;
        if !seen.insert(cursor.identity_token()) {
            return Err(VmRefusal::InvalidCtorObject.into());
        }
        let header = cursor.header();
        let size = cursor.byte_size();
        // The pin declares anonymous | str (Name) (String) | num (Name) (Nat).
        // Also accept the converter's children-only and inline-u64 carriers.
        if header.tag == 0 && header.other == 0 && size == HEADER_BYTES {
            break;
        }
        let inline_num =
            header.tag == 2 && header.other == 1 && size == HEADER_BYTES + WORD_BYTES + 8;
        let ordinary = matches!(header.tag, 1 | 2)
            && header.other == 2
            && matches!(size.checked_sub(HEADER_BYTES + 2 * WORD_BYTES), Some(0 | 8));
        if !inline_num && !ordinary {
            return Err(VmRefusal::InvalidCtorObject.into());
        }
        let parent = cursor
            .try_ctor_child(0)
            .ok_or(VmRefusal::InvalidCtorObject)?;
        let component = if inline_num {
            let value = cursor
                .try_ctor_scalar_u64(WORD_BYTES)
                .ok_or(VmRefusal::InvalidCtorObject)?;
            Component::Num(if value == 0 { Vec::new() } else { vec![value] })
        } else {
            let value = cursor
                .try_ctor_child(1)
                .ok_or(VmRefusal::InvalidCtorObject)?;
            budget.object(&value)?;
            if header.tag == 1 {
                let (_, _, chars, bytes) = value
                    .try_borrow_string_view()
                    .ok_or(VmRefusal::InvalidCtorObject)?;
                let text = bytes
                    .strip_suffix(&[0])
                    .and_then(|bytes| std::str::from_utf8(bytes).ok())
                    .ok_or(VmRefusal::InvalidCtorObject)?;
                if text.chars().count() != chars {
                    return Err(VmRefusal::InvalidCtorObject.into());
                }
                Component::Str(text.to_owned())
            } else {
                Component::Num(natural(&value, budget)?)
            }
        };
        parts.push(Part {
            component,
            stored_hash: (!inline_num)
                .then(|| cursor.try_ctor_scalar_u64(2 * WORD_BYTES))
                .flatten(),
        });
        cursor = parent;
    }
    let mut hash = 1723; // Name.anonymous.hash, Init/Prelude.lean:4715.
    for part in parts.iter().rev() {
        hash = mix_hash(hash, part.component.hash());
        if part.stored_hash.is_some_and(|stored| stored != hash) {
            return Err(VmRefusal::InvalidCtorObject.into());
        }
    }
    Ok(parts)
}

fn natural(value: &Obj, budget: &mut Budget) -> Result<Vec<u64>, IntrinsicFailure> {
    if value.is_scalar() {
        return Ok(if value.unbox() == 0 {
            Vec::new()
        } else {
            vec![value.unbox() as u64]
        });
    }
    let (_, size, limbs) = value.try_mpz_view().ok_or(VmRefusal::InvalidCtorObject)?;
    natural_limbs(size, limbs, budget)
}

fn natural_limbs(
    size: i32,
    limbs: &[u64],
    budget: &mut Budget,
) -> Result<Vec<u64>, IntrinsicFailure> {
    if size < 0 || limbs.last() == Some(&0) {
        return Err(VmRefusal::InvalidCtorObject.into());
    }
    budget.bytes(limbs.len().saturating_mul(8))?;
    Ok(limbs.to_vec())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::name::Name;
    use fln_rt::convert::inject_name;

    #[test]
    fn noncanonical_and_negative_magnitudes_are_not_names() {
        // The safe Obj constructor normalizes mpz limbs, so exercise the
        // borrowed-view validator directly for foreign noncanonical carriers.
        for (size, limbs) in [(2, &[1, 0][..]), (1, &[0][..]), (-1, &[1][..])] {
            assert!(matches!(
                natural_limbs(size, limbs, &mut Budget::default()),
                Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
            ));
        }
        assert!(matches!(
            natural_limbs(2, &[7, 1], &mut Budget::default()),
            Ok(value) if value == [7, 1]
        ));
    }

    #[test]
    fn one_budget_covers_both_operands_even_when_they_alias() {
        let value = inject_name(&Name::str(Name::anonymous(), "x"));
        assert!(matches!(
            equal(
                &value,
                &value,
                &mut Budget {
                    max_nodes: 3,
                    ..Budget::default()
                },
            ),
            Err(IntrinsicFailure::MirrorResource {
                resource: "name equality nodes",
                allowed: 3,
                observed: 4,
            })
        ));
        let bytes = value.byte_size() + value.try_ctor_child(1).unwrap().byte_size();
        assert!(matches!(
            equal(
                &value,
                &value,
                &mut Budget {
                    max_bytes: bytes as u64,
                    ..Budget::default()
                },
            ),
            Err(IntrinsicFailure::MirrorResource {
                resource: "name equality bytes",
                ..
            })
        ));
        assert!(matches!(
            equal(&value, &value, &mut Budget::default()),
            Ok(true)
        ));
    }
}
