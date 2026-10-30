//! Native definitions from Init.Prelude's Syntax API. All reads use checked
//! safe object observers; Reference toolchain bodies are never dispatched.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity, nat_as_usize};
use fln_core::name::Name;
use fln_rt::convert::{Conversion, ConvertError, inject_name};
use fln_rt::syntax_abi_generated as layout;

const MAX_NAME_NODES: u64 = 1_000_000;
const MAX_NAME_BYTES: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    MkStr1,
    IsOfKind,
    GetArg,
    GetNumArgs,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "mirror:Lean.Name.mkStr1" => Self::MkStr1,
            "mirror:Lean.Syntax.isOfKind" => Self::IsOfKind,
            "mirror:Lean.Syntax.getArg" => Self::GetArg,
            "mirror:Lean.Syntax.getNumArgs" => Self::GetNumArgs,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(
            row,
            args,
            if matches!(self, Self::IsOfKind | Self::GetArg) {
                2
            } else {
                1
            },
        )?;
        match self {
            Self::MkStr1 => {
                let text = string(&args[0])?;
                limit("name bytes", MAX_NAME_BYTES, text.len() as u64)?;
                Ok(IntrinsicResult::raw_object(inject_name(&Name::str(
                    Name::anonymous(),
                    text,
                ))))
            }
            Self::IsOfKind => {
                let kind = match syntax_kind(&args[0])? {
                    SyntaxKind::Missing => Name::str(Name::anonymous(), "missing"),
                    SyntaxKind::Ident => Name::str(Name::anonymous(), "ident"),
                    SyntaxKind::Atom => {
                        let value = child(&args[0], 1)?;
                        let text = string(&value)?;
                        limit("name bytes", MAX_NAME_BYTES, text.len() as u64)?;
                        Name::str(Name::anonymous(), text)
                    }
                    SyntaxKind::Node => name(&child(&args[0], 1)?)?,
                };
                Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                    kind == name(&args[1])?,
                ))))
            }
            Self::GetArg => {
                let index = nat_as_usize(&args[1], "Lean.Syntax.getArg", 1)?;
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    let array = child(&args[0], 2)?;
                    let (size, _) = array
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    if let Some(index) = index.filter(|index| *index < size) {
                        array.array_child(index)
                    } else {
                        Obj::mk_nat(layout::SYNTAX_MISSING_TAG)
                    }
                } else {
                    Obj::mk_nat(layout::SYNTAX_MISSING_TAG)
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::GetNumArgs => {
                let size = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    child(&args[0], 2)?
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?
                        .0
                } else {
                    0
                };
                Ok(IntrinsicResult::raw_object(Obj::mk_nat(size)))
            }
        }
    }
}

enum SyntaxKind {
    Missing,
    Node,
    Atom,
    Ident,
}

fn syntax_kind(value: &Obj) -> Result<SyntaxKind, VmRefusal> {
    if value.is_scalar() {
        return if value.unbox() == layout::SYNTAX_MISSING_TAG {
            Ok(SyntaxKind::Missing)
        } else {
            Err(VmRefusal::InvalidCtorObject)
        };
    }
    let (expected, kind) = if value.obj_tag() == usize::from(layout::SYNTAX_NODE.tag) {
        (layout::SYNTAX_NODE, SyntaxKind::Node)
    } else if value.obj_tag() == usize::from(layout::SYNTAX_ATOM.tag) {
        (layout::SYNTAX_ATOM, SyntaxKind::Atom)
    } else if value.obj_tag() == usize::from(layout::SYNTAX_IDENT.tag) {
        (layout::SYNTAX_IDENT, SyntaxKind::Ident)
    } else {
        return Err(VmRefusal::InvalidCtorObject);
    };
    let word = std::mem::size_of::<usize>();
    let bytes =
        (word + expected.object_fields * word + expected.scalar_bytes).div_ceil(word) * word;
    if usize::from(value.header().other) != expected.object_fields || value.byte_size() != bytes {
        return Err(VmRefusal::InvalidCtorObject);
    }
    Ok(kind)
}

fn child(value: &Obj, index: usize) -> Result<Obj, VmRefusal> {
    value
        .try_ctor_child(index)
        .ok_or(VmRefusal::InvalidCtorObject)
}

fn string(value: &Obj) -> Result<&str, VmRefusal> {
    let (_, _, chars, bytes) = value
        .try_borrow_string_view()
        .ok_or(VmRefusal::InvalidStringObject)?;
    let text = bytes
        .strip_suffix(&[0])
        .and_then(|bytes| std::str::from_utf8(bytes).ok())
        .ok_or(VmRefusal::InvalidStringObject)?;
    if text.chars().count() != chars {
        return Err(VmRefusal::InvalidStringObject);
    }
    Ok(text)
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

fn name(value: &Obj) -> Result<Name, IntrinsicFailure> {
    // Bound the complete borrowed carrier before the converter allocates its
    // Native Name. Its own checker also validates component shapes and hashes.
    let mut cursor = value.clone_ref();
    let mut nodes = 0u64;
    let mut bytes = 0u64;
    loop {
        nodes = nodes.saturating_add(1);
        limit("name nodes", MAX_NAME_NODES, nodes)?;
        if cursor.is_scalar() {
            break;
        }
        bytes = bytes.saturating_add(cursor.byte_size() as u64);
        limit("name bytes", MAX_NAME_BYTES, bytes)?;
        if cursor.obj_tag() == 0 {
            break;
        }
        let component = child(&cursor, 1)?;
        if !component.is_scalar() {
            bytes = bytes.saturating_add(component.byte_size() as u64);
        }
        limit("name bytes", MAX_NAME_BYTES, bytes)?;
        cursor = child(&cursor, 0)?;
    }
    Conversion::new()
        .project_name(value)
        .map_err(|error| match error {
            ConvertError::NodeBudgetExhausted {
                visited, budget, ..
            } => IntrinsicFailure::MirrorResource {
                resource: "name nodes",
                allowed: budget as u64,
                observed: visited as u64,
            },
            _ => VmRefusal::InvalidCtorObject.into(),
        })
}

#[cfg(test)]
mod tests;
