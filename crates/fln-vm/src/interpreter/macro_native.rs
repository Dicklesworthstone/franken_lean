//! Native definitions from Init.Prelude's Syntax API. All reads use checked
//! safe object observers; Reference toolchain bodies are never dispatched.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity, nat_as_usize};
use crate::macro_native::{MacroLookup, MacroLookupError};
use fln_core::name::{LeafView, Name};
use fln_rt::convert::{Conversion, ConvertError, inject_name};
use fln_rt::syntax_abi_generated as layout;

const MAX_NAME_NODES: u64 = 1_000_000;
const MAX_NAME_BYTES: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    MkStr1,
    AddMacroScope,
    MacroAddMacroScope,
    IsOfKind,
    GetArg,
    GetNumArgs,
    GetKind,
    SetKind,
    GetArgs,
    IsMissing,
    IsIdent,
    GetId,
    GetCurrNamespace,
    HasDecl,
    ResolveNamespace,
    ResolveGlobalName,
    ExpandMacro,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "mirror:Lean.Name.mkStr1" => Self::MkStr1,
            "mirror:Lean.addMacroScope" => Self::AddMacroScope,
            "mirror:Lean.Macro.addMacroScope" => Self::MacroAddMacroScope,
            "mirror:Lean.Syntax.isOfKind" => Self::IsOfKind,
            "mirror:Lean.Syntax.getArg" => Self::GetArg,
            "mirror:Lean.Syntax.getNumArgs" => Self::GetNumArgs,
            "mirror:Lean.Syntax.getKind" => Self::GetKind,
            "mirror:Lean.Syntax.setKind" => Self::SetKind,
            "mirror:Lean.Syntax.getArgs" => Self::GetArgs,
            "mirror:Lean.Syntax.isMissing" => Self::IsMissing,
            "mirror:Lean.Syntax.isIdent" => Self::IsIdent,
            "mirror:Lean.Syntax.getId" => Self::GetId,
            "mirror:Lean.Macro.getCurrNamespace" => Self::GetCurrNamespace,
            "mirror:Lean.Macro.hasDecl" => Self::HasDecl,
            "mirror:Lean.Macro.resolveNamespace" => Self::ResolveNamespace,
            "mirror:Lean.Macro.resolveGlobalName" => Self::ResolveGlobalName,
            "mirror:Lean.Macro.expandMacro?" => Self::ExpandMacro,
            _ => return None,
        })
    }

    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        self.invoke_with_lookup(row, args, None)
    }

    pub(super) fn invoke_with_lookup(
        self,
        row: &str,
        args: &[Obj],
        lookup: Option<&dyn MacroLookup>,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        expect_arity(
            row,
            args,
            match self {
                Self::IsOfKind | Self::GetArg | Self::SetKind | Self::GetCurrNamespace => 2,
                Self::AddMacroScope
                | Self::MacroAddMacroScope
                | Self::HasDecl
                | Self::ResolveNamespace
                | Self::ResolveGlobalName
                | Self::ExpandMacro => 3,
                _ => 1,
            },
        )?;
        match self {
            Self::ExpandMacro => Err(IntrinsicFailure::Refused(
                VmRefusal::MacroExpansionUnavailable,
            )),
            Self::MkStr1 => {
                let text = string(&args[0])?;
                limit("name bytes", MAX_NAME_BYTES, text.len() as u64)?;
                Ok(IntrinsicResult::raw_object(inject_name(&Name::str(
                    Name::anonymous(),
                    text,
                ))))
            }
            Self::AddMacroScope => Ok(IntrinsicResult::raw_object(attach_scope(
                &args[0], &args[1], &args[2],
            )?)),
            Self::MacroAddMacroScope => {
                check_layout(&args[1], layout::MACRO_CONTEXT)?;
                check_layout(&args[2], layout::MACRO_STATE)?;
                // Pure quotation data only: never inspect MethodsRef or derive
                // a host capability from the opaque context field.
                let value = attach_scope(
                    &child(&args[1], layout::MACRO_CONTEXT_QUOTATION_FIELD)?,
                    &args[0],
                    &child(&args[1], layout::MACRO_CONTEXT_SCOPE_FIELD)?,
                )?;
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::RESULT_OK.tag,
                    vec![value, args[2].clone_ref()],
                    &[],
                )))
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
            Self::GetKind => {
                let kind = match syntax_kind(&args[0])? {
                    SyntaxKind::Missing => inject_name(&Name::str(Name::anonymous(), "missing")),
                    SyntaxKind::Ident => inject_name(&Name::str(Name::anonymous(), "ident")),
                    SyntaxKind::Atom => {
                        let value = child(&args[0], 1)?;
                        let text = string(&value)?;
                        limit("name bytes", MAX_NAME_BYTES, text.len() as u64)?;
                        inject_name(&Name::str(Name::anonymous(), text))
                    }
                    SyntaxKind::Node => {
                        let kind = child(&args[0], 1)?;
                        name(&kind)?;
                        kind
                    }
                };
                Ok(IntrinsicResult::raw_object(kind))
            }
            Self::SetKind => {
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    name(&args[1])?;
                    let children = child(&args[0], 2)?;
                    children
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    // Preserve the original source information and exact child
                    // handles. Rebuilding just the node cannot mutate an alias.
                    Obj::mk_ctor(
                        layout::SYNTAX_NODE.tag,
                        vec![child(&args[0], 0)?, args[1].clone_ref(), children],
                        &[],
                    )
                } else {
                    args[0].clone_ref()
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::GetArgs => {
                let children = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    let children = child(&args[0], 2)?;
                    children
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    children
                } else {
                    Obj::mk_array(Vec::new())
                };
                Ok(IntrinsicResult::raw_object(children))
            }
            Self::IsMissing | Self::IsIdent => {
                let kind = syntax_kind(&args[0])?;
                let matches = matches!(
                    (self, kind),
                    (Self::IsMissing, SyntaxKind::Missing) | (Self::IsIdent, SyntaxKind::Ident)
                );
                Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(matches))))
            }
            Self::GetId => {
                let id = if matches!(syntax_kind(&args[0])?, SyntaxKind::Ident) {
                    let id = child(&args[0], 2)?;
                    name(&id)?;
                    id
                } else {
                    inject_name(&Name::anonymous())
                };
                Ok(IntrinsicResult::raw_object(id))
            }
            Self::GetCurrNamespace
            | Self::HasDecl
            | Self::ResolveNamespace
            | Self::ResolveGlobalName => {
                let context_index = usize::from(self != Self::GetCurrNamespace);
                check_layout(&args[context_index], layout::MACRO_CONTEXT)?;
                let state = &args[context_index + 1];
                check_layout(state, layout::MACRO_STATE)?;
                let operation = if self == Self::HasDecl {
                    "Lean.Macro.hasDecl"
                } else if self == Self::ResolveNamespace {
                    "Lean.Macro.resolveNamespace"
                } else if self == Self::ResolveGlobalName {
                    "Lean.Macro.resolveGlobalName"
                } else {
                    "Lean.Macro.getCurrNamespace"
                };
                let lookup = lookup.ok_or(VmRefusal::MacroLookupUnavailable { operation })?;
                let value = if self == Self::HasDecl {
                    let declaration = name(&args[0])?;
                    Obj::mk_nat(usize::from(lookup.has_decl(&declaration)))
                } else if self == Self::ResolveNamespace {
                    let requested = name(&args[0])?;
                    let names = lookup
                        .resolve_namespace(&requested)
                        .map_err(|error| lookup_error(operation, error))?;
                    namespace_candidates(&names)?
                } else if self == Self::ResolveGlobalName {
                    let requested = name(&args[0])?;
                    let names = lookup
                        .resolve_global_name(&requested)
                        .map_err(|error| lookup_error(operation, error))?;
                    global_candidates(&names)?
                } else {
                    bounded_native_name(lookup.current_namespace())?
                };
                // All methods are MacroM actions. Preserve the complete state
                // handle and return the exact generated EStateM.ok carrier.
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::RESULT_OK.tag,
                    vec![value, state.clone_ref()],
                    &[],
                )))
            }
        }
    }
}

fn attach_scope(context: &Obj, value: &Obj, scope: &Obj) -> Result<Obj, IntrinsicFailure> {
    let context = name(context)?;
    let value = name(value)?;
    let (bits, scope) = super::with_nat_view(scope, "Lean.addMacroScope", 2, |view| {
        (view.bit_length(), view.to_u64())
    })?;
    limit("macro scope bits", 64, bits)?;
    let scope = scope.ok_or(VmRefusal::InvalidCtorObject)?;
    // Bound the whole result before copying components or allocating ABI Names.
    // Two individually valid inputs can exceed the combined allowance.
    let mut budget = NameBudget::new("macro scope nodes", "macro scope bytes");
    budget.name(&context)?;
    budget.name(&value)?;
    budget.nodes(3)?; // separator, marker and the new numeric scope
    budget.text("_@_hyg")?;
    let result = fln_core::name::hygiene::add_macro_scope(&context, &value, scope)
        .map_err(|_| VmRefusal::InvalidCtorObject)?;
    Ok(inject_name(&result))
}

fn lookup_error(operation: &'static str, error: MacroLookupError) -> IntrinsicFailure {
    match error {
        MacroLookupError::Unavailable => VmRefusal::MacroLookupUnavailable { operation }.into(),
        MacroLookupError::Invalid(detail) => {
            VmRefusal::MacroLookupInvalid { operation, detail }.into()
        }
        MacroLookupError::Exhausted(resource) => IntrinsicFailure::MacroLookupExhausted {
            operation,
            resource,
        },
        MacroLookupError::Limit {
            resource,
            limit,
            observed,
        } => IntrinsicFailure::MirrorResource {
            resource,
            allowed: limit,
            observed,
        },
    }
}

/// Bound the whole overload list before allocating any ABI objects. Individual
/// name limits alone permit unbounded lists of small names or projections.
struct NameBudget {
    nodes: u64,
    bytes: u64,
    node_resource: &'static str,
    byte_resource: &'static str,
}

impl NameBudget {
    fn new(node_resource: &'static str, byte_resource: &'static str) -> Self {
        Self {
            nodes: 0,
            bytes: 0,
            node_resource,
            byte_resource,
        }
    }

    fn nodes(&mut self, count: u64) -> Result<(), IntrinsicFailure> {
        self.nodes = self.nodes.saturating_add(count);
        limit(self.node_resource, MAX_NAME_NODES, self.nodes)
    }

    fn text(&mut self, text: &str) -> Result<(), IntrinsicFailure> {
        self.bytes = self.bytes.saturating_add(text.len() as u64);
        limit(self.byte_resource, MAX_NAME_BYTES, self.bytes)
    }

    fn name(&mut self, name: &Name) -> Result<(), IntrinsicFailure> {
        let mut cursor = name.clone();
        loop {
            self.nodes(1)?;
            if cursor.component_overflowed() {
                return Err(VmRefusal::InvalidCtorObject.into());
            }
            if let LeafView::Str(text) = cursor.leaf_view() {
                self.text(text)?;
            }
            if cursor.is_anonymous() {
                return Ok(());
            }
            cursor = cursor.parent();
        }
    }
}

fn cons(head: Obj, tail: Obj) -> Obj {
    Obj::mk_ctor(layout::LIST_CONS.tag, vec![head, tail], &[])
}

fn namespace_candidates(names: &[Name]) -> Result<Obj, IntrinsicFailure> {
    let mut budget = NameBudget::new("macro lookup nodes", "macro lookup bytes");
    budget.nodes(names.len() as u64)?;
    for name in names {
        budget.name(name)?;
    }
    // Namespace resolution deliberately preserves duplicates and host order.
    let mut result = Obj::mk_nat(layout::LIST_NIL_TAG);
    for name in names.iter().rev() {
        result = cons(inject_name(name), result);
    }
    Ok(result)
}

fn global_candidates(names: &[(Name, Vec<String>)]) -> Result<Obj, IntrinsicFailure> {
    let mut budget = NameBudget::new("macro lookup nodes", "macro lookup bytes");
    budget.nodes((names.len() as u64).saturating_mul(2))?;
    for (name, projections) in names {
        budget.name(name)?;
        budget.nodes((projections.len() as u64).saturating_mul(2))?;
        for projection in projections {
            budget.text(projection)?;
        }
    }
    let mut result = Obj::mk_nat(layout::LIST_NIL_TAG);
    for (name, projections) in names.iter().rev() {
        let mut fields = Obj::mk_nat(layout::LIST_NIL_TAG);
        for projection in projections.iter().rev() {
            fields = cons(Obj::mk_string(projection), fields);
        }
        let candidate = Obj::mk_ctor(layout::PROD.tag, vec![inject_name(name), fields], &[]);
        result = cons(candidate, result);
    }
    Ok(result)
}

enum SyntaxKind {
    Missing,
    Node,
    Atom,
    Ident,
}

fn check_layout(value: &Obj, expected: layout::CtorLayout) -> Result<(), VmRefusal> {
    if value.is_scalar() || value.obj_tag() != usize::from(expected.tag) {
        return Err(VmRefusal::InvalidCtorObject);
    }
    let word = std::mem::size_of::<usize>();
    let bytes =
        (word + expected.object_fields * word + expected.scalar_bytes).div_ceil(word) * word;
    if usize::from(value.header().other) != expected.object_fields || value.byte_size() != bytes {
        return Err(VmRefusal::InvalidCtorObject);
    }
    Ok(())
}

fn bounded_native_name(value: &Name) -> Result<Obj, IntrinsicFailure> {
    let mut cursor = value.clone();
    let mut nodes = 0u64;
    let mut bytes = 0u64;
    loop {
        nodes = nodes.saturating_add(1);
        if let LeafView::Str(text) = cursor.leaf_view() {
            bytes = bytes.saturating_add(text.len() as u64);
        }
        limit("name nodes", MAX_NAME_NODES, nodes)?;
        limit("name bytes", MAX_NAME_BYTES, bytes)?;
        if cursor.is_anonymous() {
            return Ok(inject_name(value));
        }
        cursor = cursor.parent();
    }
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
