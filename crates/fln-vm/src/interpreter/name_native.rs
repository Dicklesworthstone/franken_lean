//! Native Name equality and numeric construction, including arbitrary Nat
//! components. Names are compared structurally, never by cached hash alone.
//! Validate complete carriers before comparing or using their hashes. Numeric
//! construction retains the original Compat operands and every numeral limb.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity};
use fln_core::lean_hash::{mix_hash, string_hash};
use fln_rt::syntax_abi_generated as layout;
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
    Num,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        match row {
            "extern:Lean.Name.beq" => Some(Self::Beq),
            "mirror:Lean.Name.num._override" => Some(Self::Num),
            _ => None,
        }
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(row, args, 2)?;
        match self {
            Self::Beq => {
                let equal = equal(&args[0], &args[1], &mut Budget::default())?;
                // lean_name_eq returns a uint8_t in the generated ABI contract.
                Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(equal))))
            }
            Self::Num => numeric(&args[0], &args[1], &mut Budget::constructor())
                .map(IntrinsicResult::raw_object),
        }
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

struct CheckedName {
    parts: Vec<Part>,
    hash: u64,
}

struct Budget {
    nodes: u64,
    bytes: u64,
    max_nodes: u64,
    max_bytes: u64,
    node_resource: &'static str,
    byte_resource: &'static str,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            nodes: 0,
            bytes: 0,
            max_nodes: MAX_NAME_NODES,
            max_bytes: MAX_NAME_BYTES,
            node_resource: "name equality nodes",
            byte_resource: "name equality bytes",
        }
    }
}

impl Budget {
    fn constructor() -> Self {
        Self {
            node_resource: "name constructor nodes",
            byte_resource: "name constructor bytes",
            ..Self::default()
        }
    }

    fn node(&mut self) -> Result<(), IntrinsicFailure> {
        self.nodes = self.nodes.saturating_add(1);
        limit(self.node_resource, self.max_nodes, self.nodes)
    }

    fn bytes(&mut self, size: usize) -> Result<(), IntrinsicFailure> {
        self.bytes = self.bytes.saturating_add(size as u64);
        limit(self.byte_resource, self.max_bytes, self.bytes)
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
        .parts
        .iter()
        .map(|part| &part.component)
        .eq(right.parts.iter().map(|part| &part.component)))
}

fn numeric(parent: &Obj, value: &Obj, budget: &mut Budget) -> Result<Obj, IntrinsicFailure> {
    // Charge the new node before inspecting its inputs, and charge every
    // retained input and copied magnitude before allocating the result.
    budget.node()?;
    let parent_hash = checked_name(parent, budget)?.hash;
    budget.object(value)?;
    let component = Component::Num(natural(value, budget)?);
    let hash = mix_hash(parent_hash, component.hash());
    budget.bytes(HEADER_BYTES + 2 * WORD_BYTES + 8)?;
    Ok(Obj::mk_ctor(
        layout::NAME_NUM_CTOR.tag,
        vec![parent.clone_ref(), value.clone_ref()],
        &hash.to_ne_bytes(),
    ))
}

fn checked_name(value: &Obj, budget: &mut Budget) -> Result<CheckedName, IntrinsicFailure> {
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
    Ok(CheckedName { parts, hash })
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

    #[test]
    fn numeric_construction_retains_arbitrary_naturals_and_parent_identity() {
        let parent = inject_name(&Name::str(Name::anonymous(), "λ\0root"));
        for limbs in [vec![], vec![u64::MAX], vec![7, 1], vec![8, 1, 3]] {
            let number = Obj::mk_mpz(&limbs, false);
            let Ok(name) = numeric(&parent, &number, &mut Budget::constructor()) else {
                panic!("valid numeric Name construction must succeed");
            };
            assert_eq!(
                name.try_ctor_child(0).unwrap().identity_token(),
                parent.identity_token()
            );
            assert_eq!(
                name.try_ctor_child(1).unwrap().identity_token(),
                number.identity_token()
            );
            let component_hash = match limbs.as_slice() {
                [] => 0,
                [value] => *value,
                _ => 17,
            };
            let expected = mix_hash(
                Name::str(Name::anonymous(), "λ\0root").hash(),
                component_hash,
            );
            assert_eq!(name.try_ctor_scalar_u64(2 * WORD_BYTES), Some(expected));
            let Ok(checked) = checked_name(&name, &mut Budget::default()) else {
                panic!("constructed numeric Name must validate");
            };
            assert_eq!(checked.hash, expected);
            let Ok(child) = numeric(&name, &Obj::mk_nat(9), &mut Budget::constructor()) else {
                panic!("a valid arbitrary-size numeric prefix must be accepted");
            };
            assert_eq!(
                child.try_ctor_scalar_u64(2 * WORD_BYTES),
                Some(mix_hash(expected, 9))
            );
        }
    }

    #[test]
    fn numeric_construction_refuses_malformed_inputs_and_charges_before_allocation() {
        let zero = Obj::mk_nat(0);
        for parent in [
            Obj::mk_nat(1),
            Obj::mk_string("not a name"),
            Obj::mk_ctor(2, vec![Obj::mk_nat(0), Obj::mk_nat(1)], &0u64.to_ne_bytes()),
        ] {
            assert!(matches!(
                numeric(&parent, &zero, &mut Budget::constructor()),
                Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
            ));
        }
        for number in [Obj::mk_mpz(&[1], true), Obj::mk_string("not a natural")] {
            assert!(matches!(
                numeric(&zero, &number, &mut Budget::constructor()),
                Err(IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject))
            ));
        }
        assert!(matches!(
            numeric(
                &zero,
                &zero,
                &mut Budget {
                    max_nodes: 1,
                    ..Budget::constructor()
                }
            ),
            Err(IntrinsicFailure::MirrorResource {
                resource: "name constructor nodes",
                allowed: 1,
                observed: 2,
            })
        ));
        assert!(matches!(
            numeric(
                &zero,
                &zero,
                &mut Budget {
                    max_bytes: 0,
                    ..Budget::constructor()
                }
            ),
            Err(IntrinsicFailure::MirrorResource {
                resource: "name constructor bytes",
                allowed: 0,
                ..
            })
        ));
    }
}
