//! Native definitions from Init.Prelude's Syntax API. All reads use checked
//! safe object observers; Reference toolchain bodies are never dispatched.

use super::{IntrinsicFailure, IntrinsicResult, Obj, VmRefusal, expect_arity, nat_as_usize};
use crate::macro_native::{MacroLookup, MacroLookupError};
use fln_core::name::identifier::{NameRenderError, to_identifier_string};
use fln_core::name::{LeafView, Name};
use fln_rt::convert::{Conversion, ConvertError, inject_name};
use fln_rt::macro_expansion_abi_generated as expansion_layout;
use fln_rt::syntax_abi_generated as layout;

const MAX_NAME_NODES: u64 = 1_000_000;
const MAX_NAME_BYTES: u64 = 16 * 1024 * 1024;
const MAX_SYNTAX_NODES: u64 = 1_000_000;

mod literals;
mod numbers;
mod patterns;
mod sequences;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    NameStr,
    MkStr1,
    NameHasMacroScopes,
    NameEraseMacroScopes,
    AddMacroScope,
    MacroAddMacroScope,
    IsOfKind,
    GetArg,
    GetNumArgs,
    IsNodeOf,
    MatchesNull,
    MatchesIdent,
    MatchesLit,
    GetOptional,
    GetKind,
    SetKind,
    GetArgs,
    GetSepArgs,
    MkSepArray,
    MkSep,
    SepArrayGetElems,
    TSepArrayGetElems,
    SepArrayOfElems,
    TSepArrayPush,
    SetArgs,
    SetArg,
    IsAtom,
    GetAtomVal,
    SetAtomVal,
    GetHeadInfo,
    SourceInfoGetPos,
    SourceInfoGetTailPos,
    GetPos,
    GetTailPos,
    SourceInfoFromRef,
    MkAtom,
    MkAtomFrom,
    MkIdent,
    MkIdentFrom,
    MkCIdent,
    MkCIdentFrom,
    MkLit,
    MkStrLit,
    IsLit,
    IsStrLit,
    GetString,
    MkNumLit,
    MkNatLit,
    IsNatLit,
    GetNat,
    NatReprFast,
    ReplaceRef,
    ThrowError,
    ThrowErrorAt,
    ThrowUnsupported,
    SetInfo,
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
            "mirror:Lean.Name.str._override" => Self::NameStr,
            "mirror:Lean.Name.mkStr1" => Self::MkStr1,
            "mirror:Lean.Name.hasMacroScopes" => Self::NameHasMacroScopes,
            "mirror:Lean.Name.eraseMacroScopes" => Self::NameEraseMacroScopes,
            "mirror:Lean.addMacroScope" => Self::AddMacroScope,
            "mirror:Lean.Macro.addMacroScope" => Self::MacroAddMacroScope,
            "mirror:Lean.Syntax.isOfKind" => Self::IsOfKind,
            "mirror:Lean.Syntax.getArg" => Self::GetArg,
            "mirror:Lean.Syntax.getNumArgs" => Self::GetNumArgs,
            "mirror:Lean.Syntax.isNodeOf" => Self::IsNodeOf,
            "mirror:Lean.Syntax.matchesNull" => Self::MatchesNull,
            "mirror:Lean.Syntax.matchesIdent" => Self::MatchesIdent,
            "mirror:Lean.Syntax.matchesLit" => Self::MatchesLit,
            "mirror:Lean.Syntax.getOptional?" => Self::GetOptional,
            "mirror:Lean.Syntax.getKind" => Self::GetKind,
            "mirror:Lean.Syntax.setKind" => Self::SetKind,
            "mirror:Lean.Syntax.getArgs" => Self::GetArgs,
            "mirror:Lean.Syntax.getSepArgs" => Self::GetSepArgs,
            "mirror:Lean.mkSepArray" => Self::MkSepArray,
            "mirror:Lean.Syntax.mkSep" => Self::MkSep,
            "mirror:Lean.Syntax.SepArray.getElems._redArg" => Self::SepArrayGetElems,
            "mirror:Lean.Syntax.TSepArray.getElems._redArg" => Self::TSepArrayGetElems,
            "mirror:Lean.Syntax.SepArray.ofElems" => Self::SepArrayOfElems,
            "mirror:Lean.Syntax.TSepArray.push._redArg" => Self::TSepArrayPush,
            "mirror:Lean.Syntax.setArgs" => Self::SetArgs,
            "mirror:Lean.Syntax.setArg" => Self::SetArg,
            "mirror:Lean.Syntax.isAtom" => Self::IsAtom,
            "mirror:Lean.Syntax.getAtomVal" => Self::GetAtomVal,
            "mirror:Lean.Syntax.setAtomVal" => Self::SetAtomVal,
            "mirror:Lean.Syntax.getHeadInfo" => Self::GetHeadInfo,
            "mirror:Lean.SourceInfo.getPos?" => Self::SourceInfoGetPos,
            "mirror:Lean.SourceInfo.getTailPos?" => Self::SourceInfoGetTailPos,
            "mirror:Lean.Syntax.getPos?" => Self::GetPos,
            "mirror:Lean.Syntax.getTailPos?" => Self::GetTailPos,
            "mirror:Lean.SourceInfo.fromRef" => Self::SourceInfoFromRef,
            "mirror:Lean.mkAtom" => Self::MkAtom,
            "mirror:Lean.mkAtomFrom" => Self::MkAtomFrom,
            "mirror:Lean.mkIdent" => Self::MkIdent,
            "mirror:Lean.mkIdentFrom" => Self::MkIdentFrom,
            "mirror:Lean.mkCIdent" => Self::MkCIdent,
            "mirror:Lean.mkCIdentFrom" => Self::MkCIdentFrom,
            "mirror:Lean.Syntax.mkLit" => Self::MkLit,
            "mirror:Lean.Syntax.mkStrLit" => Self::MkStrLit,
            "mirror:Lean.Syntax.isLit?" => Self::IsLit,
            "mirror:Lean.Syntax.isStrLit?" => Self::IsStrLit,
            "mirror:Lean.TSyntax.getString" => Self::GetString,
            "mirror:Lean.Syntax.mkNumLit" => Self::MkNumLit,
            "mirror:Lean.Syntax.mkNatLit" => Self::MkNatLit,
            "mirror:Lean.Syntax.isNatLit?" => Self::IsNatLit,
            "mirror:Lean.TSyntax.getNat" => Self::GetNat,
            "mirror:Nat.reprFast" => Self::NatReprFast,
            "mirror:Lean.replaceRef" => Self::ReplaceRef,
            "mirror:Lean.Macro.throwError._redArg" => Self::ThrowError,
            "mirror:Lean.Macro.throwErrorAt._redArg" => Self::ThrowErrorAt,
            "mirror:Lean.Macro.throwUnsupported._redArg" => Self::ThrowUnsupported,
            "mirror:Lean.Syntax.setInfo" => Self::SetInfo,
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

    #[cfg(test)]
    pub(super) fn invoke(
        self,
        row: &str,
        args: &[Obj],
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        self.invoke_with_lookup(
            row,
            args,
            None,
            super::ExecutionLimits::default().max_nat_magnitude_bytes,
        )
    }

    pub(super) fn invoke_owned_with_lookup(
        self,
        row: &str,
        args: Vec<Obj>,
        lookup: Option<&dyn MacroLookup>,
        max_nat_magnitude_bytes: u64,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        if self == Self::TSepArrayPush {
            let [separator, array, element] = super::exact_owned_args(row, args)?;
            return sequences::push(separator, array, element).map(IntrinsicResult::raw_object);
        }
        self.invoke_with_lookup(row, &args, lookup, max_nat_magnitude_bytes)
    }

    pub(super) fn invoke_with_lookup(
        self,
        row: &str,
        args: &[Obj],
        lookup: Option<&dyn MacroLookup>,
        max_nat_magnitude_bytes: u64,
    ) -> Result<IntrinsicResult, IntrinsicFailure> {
        let max_nat_magnitude_bytes =
            max_nat_magnitude_bytes.min((fln_bignum::nat::MAX_LIMBS as u64).saturating_mul(8));
        expect_arity(
            row,
            args,
            match self {
                Self::NameStr
                | Self::IsOfKind
                | Self::MatchesNull
                | Self::MatchesIdent
                | Self::GetArg
                | Self::SetKind
                | Self::SetArgs
                | Self::MkSepArray
                | Self::MkSep
                | Self::SepArrayOfElems
                | Self::SetAtomVal
                | Self::SetInfo
                | Self::SourceInfoGetPos
                | Self::SourceInfoGetTailPos
                | Self::GetPos
                | Self::GetTailPos
                | Self::SourceInfoFromRef
                | Self::ReplaceRef
                | Self::MkStrLit
                | Self::MkNumLit
                | Self::MkNatLit
                | Self::IsLit
                | Self::GetCurrNamespace => 2,
                Self::AddMacroScope
                | Self::MacroAddMacroScope
                | Self::HasDecl
                | Self::ResolveNamespace
                | Self::ResolveGlobalName
                | Self::IsNodeOf
                | Self::MatchesLit
                | Self::SetArg
                | Self::TSepArrayPush
                | Self::MkAtomFrom
                | Self::MkIdentFrom
                | Self::MkCIdentFrom
                | Self::MkLit
                | Self::ThrowError
                | Self::ExpandMacro => 3,
                Self::ThrowErrorAt => 4,
                _ => 1,
            },
        )?;
        match self {
            Self::ExpandMacro => Err(IntrinsicFailure::Refused(
                VmRefusal::MacroExpansionUnavailable,
            )),
            Self::NameStr => {
                let parent = name(&args[0])?;
                let text = string(&args[1])?;
                // Bound the whole result, including the new component, before
                // allocating its native Name and computed-hash ABI carrier.
                let mut budget =
                    NameBudget::new("name constructor nodes", "name constructor bytes");
                budget.name(&parent)?;
                budget.nodes(1)?;
                budget.text(text)?;
                Ok(IntrinsicResult::raw_object(inject_name(&Name::str(
                    parent, text,
                ))))
            }
            Self::MkStr1 => {
                let text = string(&args[0])?;
                limit("name bytes", MAX_NAME_BYTES, text.len() as u64)?;
                Ok(IntrinsicResult::raw_object(inject_name(&Name::str(
                    Name::anonymous(),
                    text,
                ))))
            }
            Self::NameHasMacroScopes => Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                name(&args[0])?.has_macro_scopes(),
            )))),
            Self::NameEraseMacroScopes => {
                let value = name(&args[0])?;
                let erased = if value.has_macro_scopes() {
                    inject_name(&value.erase_macro_scopes())
                } else {
                    args[0].clone_ref()
                };
                Ok(IntrinsicResult::raw_object(erased))
            }
            Self::IsNodeOf => Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                patterns::is_node_of(
                    &args[0],
                    &name(&args[1])?,
                    &args[2],
                    "Lean.Syntax.isNodeOf",
                    2,
                )?,
            )))),
            Self::MatchesNull => Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                patterns::is_node_of(
                    &args[0],
                    &Name::str(Name::anonymous(), "null"),
                    &args[1],
                    "Lean.Syntax.matchesNull",
                    1,
                )?,
            )))),
            Self::MatchesIdent => Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                patterns::matches_ident(&args[0], &args[1])?,
            )))),
            Self::MatchesLit => Ok(IntrinsicResult::scalar(Obj::mk_nat(usize::from(
                patterns::matches_lit(&args[0], &args[1], &args[2])?,
            )))),
            Self::GetOptional => Ok(IntrinsicResult::raw_object(patterns::get_optional(
                &args[0],
            )?)),
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
            Self::GetSepArgs => {
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    patterns::sep_elems(&child(&args[0], 2)?)?
                } else {
                    Obj::mk_array(Vec::new())
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::SepArrayGetElems | Self::TSepArrayGetElems => {
                Ok(IntrinsicResult::raw_object(patterns::sep_elems(&args[0])?))
            }
            Self::MkSepArray => Ok(IntrinsicResult::raw_object(patterns::mk_sep_array(
                &args[0], &args[1],
            )?)),
            Self::MkSep => Ok(IntrinsicResult::raw_object(sequences::null_node(
                patterns::mk_sep_array(&args[0], &args[1])?,
            ))),
            Self::SepArrayOfElems => Ok(IntrinsicResult::raw_object(sequences::from_elements(
                &args[0], &args[1],
            )?)),
            Self::TSepArrayPush => Ok(IntrinsicResult::raw_object(sequences::push(
                args[0].clone_ref(),
                args[1].clone_ref(),
                args[2].clone_ref(),
            )?)),
            Self::SetArgs => {
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    args[1]
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    Obj::mk_ctor(
                        layout::SYNTAX_NODE.tag,
                        vec![
                            child(&args[0], 0)?,
                            child(&args[0], 1)?,
                            args[1].clone_ref(),
                        ],
                        &[],
                    )
                } else {
                    args[0].clone_ref()
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::SetArg => {
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Node) {
                    let index = nat_as_usize(&args[1], "Lean.Syntax.setArg", 1)?;
                    let children = child(&args[0], 2)?;
                    let (size, _) = children
                        .try_array_view()
                        .ok_or(VmRefusal::InvalidArrayObject)?;
                    if let Some(index) = index.filter(|index| *index < size) {
                        syntax_kind(&args[2])?;
                        limit("syntax argument count", MAX_SYNTAX_NODES, size as u64)?;
                        // The original syntax retains its reference, so the
                        // safe array membrane copies before replacing a child.
                        let children = children
                            .try_array_set(index, args[2].clone_ref())
                            .ok_or(VmRefusal::InvalidArrayObject)?;
                        Obj::mk_ctor(
                            layout::SYNTAX_NODE.tag,
                            vec![child(&args[0], 0)?, child(&args[0], 1)?, children],
                            &[],
                        )
                    } else {
                        args[0].clone_ref()
                    }
                } else {
                    args[0].clone_ref()
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::GetAtomVal => {
                let text = if matches!(syntax_kind(&args[0])?, SyntaxKind::Atom) {
                    let text = child(&args[0], 1)?;
                    string(&text)?;
                    text
                } else {
                    Obj::mk_string("")
                };
                Ok(IntrinsicResult::raw_object(text))
            }
            Self::SetAtomVal => {
                let value = if matches!(syntax_kind(&args[0])?, SyntaxKind::Atom) {
                    string(&args[1])?;
                    Obj::mk_ctor(
                        layout::SYNTAX_ATOM.tag,
                        vec![child(&args[0], 0)?, args[1].clone_ref()],
                        &[],
                    )
                } else {
                    args[0].clone_ref()
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::GetHeadInfo => Ok(IntrinsicResult::raw_object(get_head_info(&args[0])?)),
            Self::SourceInfoGetPos
            | Self::SourceInfoGetTailPos
            | Self::GetPos
            | Self::GetTailPos => {
                let operation = match self {
                    Self::SourceInfoGetPos => "Lean.SourceInfo.getPos?",
                    Self::SourceInfoGetTailPos => "Lean.SourceInfo.getTailPos?",
                    Self::GetPos => "Lean.Syntax.getPos?",
                    Self::GetTailPos => "Lean.Syntax.getTailPos?",
                    _ => unreachable!(),
                };
                let canonical_only = super::bool_value(&args[1], operation, 1)?;
                let position = if self == Self::GetTailPos {
                    get_tail_pos(&args[0], canonical_only)?
                } else {
                    let info = if self == Self::GetPos {
                        get_head_info(&args[0])?
                    } else {
                        args[0].clone_ref()
                    };
                    source_position(
                        &info,
                        canonical_only,
                        self == Self::SourceInfoGetTailPos,
                        operation,
                    )?
                };
                let value = match position {
                    Some(position) => {
                        Obj::mk_ctor(expansion_layout::OPTION_SOME.tag, vec![position], &[])
                    }
                    None => Obj::mk_nat(expansion_layout::OPTION_NONE_TAG),
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::SourceInfoFromRef => {
                let canonical = super::bool_value(&args[1], "Lean.SourceInfo.fromRef", 1)?;
                Ok(IntrinsicResult::raw_object(source_info_from_ref(
                    &args[0], canonical,
                )?))
            }
            Self::MkAtom | Self::MkAtomFrom => {
                let (info, text) = if self == Self::MkAtomFrom {
                    string(&args[1])?;
                    let canonical = super::bool_value(&args[2], "Lean.mkAtomFrom", 2)?;
                    (source_info_from_ref(&args[0], canonical)?, &args[1])
                } else {
                    string(&args[0])?;
                    (Obj::mk_nat(layout::SOURCE_NONE_TAG), &args[0])
                };
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::SYNTAX_ATOM.tag,
                    vec![info, text.clone_ref()],
                    &[],
                )))
            }
            Self::MkIdent | Self::MkIdentFrom | Self::MkCIdent | Self::MkCIdentFrom => {
                let from_ref = matches!(self, Self::MkIdentFrom | Self::MkCIdentFrom);
                let constant = matches!(self, Self::MkCIdent | Self::MkCIdentFrom);
                let original = &args[usize::from(from_ref)];
                let info = if from_ref {
                    let operation = if constant {
                        "Lean.mkCIdentFrom"
                    } else {
                        "Lean.mkIdentFrom"
                    };
                    let canonical = super::bool_value(&args[2], operation, 2)?;
                    source_info_from_ref(&args[0], canonical)?
                } else {
                    Obj::mk_nat(layout::SOURCE_NONE_TAG)
                };
                let value = if constant {
                    // The reserved scope prevents a source local from capturing
                    // a constant. It is independent of the caller's fresh scope.
                    attach_scope(
                        &inject_name(&Name::from_components(["_internal"])),
                        original,
                        &Obj::mk_nat(fln_core::name::hygiene::RESERVED_MACRO_SCOPE as usize),
                    )?
                } else {
                    original.clone_ref()
                };
                let text = to_identifier_string(&name(&value)?, MAX_NAME_BYTES as usize).map_err(
                    |error| match error {
                        NameRenderError::OverflowedComponent => {
                            IntrinsicFailure::Refused(VmRefusal::InvalidCtorObject)
                        }
                        NameRenderError::ByteBudgetExceeded { limit, observed } => {
                            IntrinsicFailure::MirrorResource {
                                resource: "identifier spelling bytes",
                                allowed: limit as u64,
                                observed: observed as u64,
                            }
                        }
                    },
                )?;
                let raw = Obj::mk_ctor(
                    layout::SUBSTRING_RAW.tag,
                    vec![
                        Obj::mk_string(&text),
                        Obj::mk_nat(0),
                        Obj::mk_nat(text.len()),
                    ],
                    &[],
                );
                let preresolved = if constant {
                    cons(
                        Obj::mk_ctor(
                            layout::PRERESOLVED_DECL.tag,
                            vec![original.clone_ref(), Obj::mk_nat(layout::LIST_NIL_TAG)],
                            &[],
                        ),
                        Obj::mk_nat(layout::LIST_NIL_TAG),
                    )
                } else {
                    Obj::mk_nat(layout::LIST_NIL_TAG)
                };
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::SYNTAX_IDENT.tag,
                    vec![info, raw, value, preresolved],
                    &[],
                )))
            }
            Self::ReplaceRef => Ok(IntrinsicResult::raw_object(replace_ref(
                &args[0], &args[1],
            )?)),
            Self::MkLit => {
                literals::mk_lit(&args[0], &args[1], &args[2]).map(IntrinsicResult::raw_object)
            }
            Self::MkStrLit => {
                literals::mk_str_lit(&args[0], &args[1]).map(IntrinsicResult::raw_object)
            }
            Self::IsLit => literals::is_lit(&args[0], &args[1]).map(IntrinsicResult::raw_object),
            Self::IsStrLit => literals::is_str_lit(&args[0]).map(IntrinsicResult::raw_object),
            Self::GetString => literals::get_string(&args[0]).map(IntrinsicResult::raw_object),
            Self::MkNumLit => {
                numbers::mk_num_lit(&args[0], &args[1]).map(IntrinsicResult::raw_object)
            }
            Self::MkNatLit => numbers::mk_nat_lit(&args[0], &args[1], max_nat_magnitude_bytes)
                .map(IntrinsicResult::raw_object),
            Self::IsNatLit => numbers::is_nat_lit(&args[0], max_nat_magnitude_bytes)
                .map(IntrinsicResult::raw_object),
            Self::GetNat => {
                numbers::get_nat(&args[0], max_nat_magnitude_bytes).map(IntrinsicResult::raw_object)
            }
            Self::NatReprFast => numbers::nat_repr_fast(&args[0], max_nat_magnitude_bytes)
                .map(IntrinsicResult::raw_object),
            Self::ThrowUnsupported => {
                check_layout(&args[0], layout::MACRO_STATE)?;
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::RESULT_ERROR.tag,
                    vec![
                        Obj::mk_nat(layout::EXCEPTION_UNSUPPORTED_TAG),
                        args[0].clone_ref(),
                    ],
                    &[],
                )))
            }
            Self::ThrowError | Self::ThrowErrorAt => {
                let offset = usize::from(self == Self::ThrowErrorAt);
                let message = &args[offset];
                let context = &args[offset + 1];
                let state = &args[offset + 2];
                string(message)?;
                check_layout(context, layout::MACRO_CONTEXT)?;
                check_layout(state, layout::MACRO_STATE)?;
                // The current reference is ordinary reader data. MethodsRef
                // neither supplies nor grants a capability to report errors.
                let old = child(context, expansion_layout::MACRO_CONTEXT_REF_FIELD)?;
                syntax_kind(&old)?;
                let reference = if self == Self::ThrowErrorAt {
                    replace_ref(&args[0], &old)?
                } else {
                    old
                };
                let exception = Obj::mk_ctor(
                    layout::EXCEPTION_ERROR.tag,
                    vec![reference, message.clone_ref()],
                    &[],
                );
                Ok(IntrinsicResult::raw_object(Obj::mk_ctor(
                    layout::RESULT_ERROR.tag,
                    vec![exception, state.clone_ref()],
                    &[],
                )))
            }
            Self::SetInfo => {
                // The pin's telescope takes SourceInfo before Syntax.
                let kind = syntax_kind(&args[1])?;
                let value = if let SyntaxKind::Missing = kind {
                    args[1].clone_ref()
                } else {
                    source_info(&args[0])?;
                    let expected = match kind {
                        SyntaxKind::Node => layout::SYNTAX_NODE,
                        SyntaxKind::Atom => layout::SYNTAX_ATOM,
                        SyntaxKind::Ident => layout::SYNTAX_IDENT,
                        SyntaxKind::Missing => unreachable!(),
                    };
                    let mut fields = Vec::with_capacity(expected.object_fields);
                    fields.push(args[0].clone_ref());
                    for index in 1..expected.object_fields {
                        fields.push(child(&args[1], index)?);
                    }
                    Obj::mk_ctor(expected.tag, fields, &[])
                };
                Ok(IntrinsicResult::raw_object(value))
            }
            Self::IsMissing | Self::IsIdent | Self::IsAtom => {
                let kind = syntax_kind(&args[0])?;
                let matches = matches!(
                    (self, kind),
                    (Self::IsMissing, SyntaxKind::Missing)
                        | (Self::IsIdent, SyntaxKind::Ident)
                        | (Self::IsAtom, SyntaxKind::Atom)
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

/// Validate the discriminator and extracted layout without decoding source
/// positions against a particular file. The syntax conversion boundary owns
/// that check; these operations preserve the exact SourceInfo object.
fn source_info(value: &Obj) -> Result<bool, VmRefusal> {
    if value.is_scalar() {
        return if value.unbox() == layout::SOURCE_NONE_TAG {
            Ok(true)
        } else {
            Err(VmRefusal::InvalidCtorObject)
        };
    }
    if value.obj_tag() == usize::from(layout::SOURCE_ORIGINAL.tag) {
        check_layout(value, layout::SOURCE_ORIGINAL)?;
    } else if value.obj_tag() == usize::from(layout::SOURCE_SYNTHETIC.tag) {
        check_layout(value, layout::SOURCE_SYNTHETIC)?;
    } else {
        return Err(VmRefusal::InvalidCtorObject);
    }
    Ok(false)
}

fn get_head_info(value: &Obj) -> Result<Obj, IntrinsicFailure> {
    get_head_info_bounded(value, &mut 0, "syntax head-info nodes")
}

fn get_head_info_bounded(
    value: &Obj,
    visited: &mut u64,
    resource: &'static str,
) -> Result<Obj, IntrinsicFailure> {
    let mut current = value.clone_ref();
    let mut pending = Vec::new();
    loop {
        *visited += 1;
        limit(resource, MAX_SYNTAX_NODES, *visited)?;
        match syntax_kind(&current)? {
            SyntaxKind::Missing => {}
            SyntaxKind::Atom | SyntaxKind::Ident => {
                let info = child(&current, 0)?;
                source_info(&info)?;
                // A token with SourceInfo.none is still the first token.
                // getHeadInfo? returns `some none`, never searches past it.
                return Ok(info);
            }
            SyntaxKind::Node => {
                let info = child(&current, 0)?;
                if !source_info(&info)? {
                    return Ok(info);
                }
                let children = child(&current, 2)?;
                let (size, _) = children
                    .try_array_view()
                    .ok_or(VmRefusal::InvalidArrayObject)?;
                if size != 0 {
                    current = children.array_child(0);
                    if size > 1 {
                        pending.push((children, 1, size));
                    }
                    continue;
                }
            }
        }
        // Keep only each ancestor's next sibling, rather than recursing on
        // the host stack or materializing every child of a wide syntax node.
        let Some((children, index, size)) = pending.pop() else {
            return Ok(Obj::mk_nat(layout::SOURCE_NONE_TAG));
        };
        current = children.array_child(index);
        if index + 1 < size {
            pending.push((children, index + 1, size));
        }
    }
}

/// Project the selected Nat without truncating it to a host byte offset. These
/// pure Mirror methods can inspect positions outside the caller's source file;
/// conversion of a returned Syntax tree owns the source-boundary checks.
fn source_position(
    info: &Obj,
    canonical_only: bool,
    tail: bool,
    operation: &'static str,
) -> Result<Option<Obj>, IntrinsicFailure> {
    if source_info(info)? {
        return Ok(None);
    }
    let field = if info.obj_tag() == usize::from(layout::SOURCE_ORIGINAL.tag) {
        if tail {
            layout::SOURCE_ORIGINAL_TAIL_POS_FIELD
        } else {
            layout::SOURCE_ORIGINAL_POS_FIELD
        }
    } else {
        let offset = layout::SOURCE_SYNTHETIC_CANONICAL_OBJECT_FIELDS
            * std::mem::size_of::<usize>()
            + layout::SOURCE_SYNTHETIC_CANONICAL_BYTE_OFFSET;
        let flag = info
            .try_ctor_scalar_u32(offset)
            .ok_or(VmRefusal::InvalidCtorObject)?
            .to_ne_bytes()[0];
        let canonical = match flag {
            0 => false,
            1 => true,
            _ => return Err(VmRefusal::InvalidCtorObject.into()),
        };
        if canonical_only && !canonical {
            return Ok(None);
        }
        if tail {
            layout::SOURCE_SYNTHETIC_TAIL_POS_FIELD
        } else {
            layout::SOURCE_SYNTHETIC_POS_FIELD
        }
    };
    let position = child(info, field)?;
    super::with_nat_view(&position, operation, 0, |_| ())?;
    Ok(Some(position))
}

fn get_tail_pos(value: &Obj, canonical_only: bool) -> Result<Option<Obj>, IntrinsicFailure> {
    get_tail_pos_bounded(value, canonical_only, &mut 0, "syntax tail-position nodes")
}

fn get_tail_pos_bounded(
    value: &Obj,
    canonical_only: bool,
    visited: &mut u64,
    resource: &'static str,
) -> Result<Option<Obj>, IntrinsicFailure> {
    let mut current = value.clone_ref();
    let mut pending = Vec::new();
    loop {
        *visited += 1;
        limit(resource, MAX_SYNTAX_NODES, *visited)?;
        let kind = syntax_kind(&current)?;
        if !matches!(kind, SyntaxKind::Missing) {
            let info = child(&current, 0)?;
            if let Some(position) =
                source_position(&info, canonical_only, true, "Lean.Syntax.getTailPos?")?
            {
                return Ok(Some(position));
            }
            if matches!(kind, SyntaxKind::Node) {
                let children = child(&current, 2)?;
                let (size, _) = children
                    .try_array_view()
                    .ok_or(VmRefusal::InvalidArrayObject)?;
                if size != 0 {
                    current = children.array_child(size - 1);
                    if size > 1 {
                        pending.push((children, size - 1));
                    }
                    continue;
                }
            }
        }
        // Unlike getPos?, this scans past unpositioned tokens and filtered
        // synthetic nodes. Keep one sibling cursor per ancestor, in reverse
        // order, to avoid host recursion and copying wide child arrays.
        let Some((children, remaining)) = pending.pop() else {
            return Ok(None);
        };
        current = children.array_child(remaining - 1);
        if remaining > 1 {
            pending.push((children, remaining - 1));
        }
    }
}

fn source_info_from_ref(value: &Obj, canonical: bool) -> Result<Obj, IntrinsicFailure> {
    let mut visited = 0;
    let mut positions = |canonical_only| {
        let info = get_head_info_bounded(value, &mut visited, "syntax source-info nodes")?;
        let pos = source_position(&info, canonical_only, false, "Lean.SourceInfo.fromRef")?;
        // The pin evaluates both endpoints even when the head has no position.
        let tail = get_tail_pos_bounded(
            value,
            canonical_only,
            &mut visited,
            "syntax source-info nodes",
        )?;
        Ok::<_, IntrinsicFailure>(pos.zip(tail))
    };
    if canonical && let Some((pos, tail)) = positions(true)? {
        return Ok(synthetic_info(pos, tail, true));
    }
    // Canonical construction falls back to the complete noncanonical range,
    // not a mixture of one canonical and one noncanonical endpoint. All walks
    // share one node budget, including this retry.
    Ok(match positions(false)? {
        Some((pos, tail)) => synthetic_info(pos, tail, false),
        None => Obj::mk_nat(layout::SOURCE_NONE_TAG),
    })
}

fn replace_ref(value: &Obj, old: &Obj) -> Result<Obj, IntrinsicFailure> {
    syntax_kind(old)?;
    let info = get_head_info(value)?;
    // withRef accepts a noncanonical position, including zero and large Nat.
    // It asks only for the head position, never for a tail or complete range.
    let selected = if source_position(&info, false, false, "Lean.replaceRef")?.is_some() {
        value
    } else {
        old
    };
    Ok(selected.clone_ref())
}

fn synthetic_info(pos: Obj, tail: Obj, canonical: bool) -> Obj {
    let mut fields: Vec<_> = (0..layout::SOURCE_SYNTHETIC.object_fields)
        .map(|_| Obj::mk_nat(0))
        .collect();
    fields[layout::SOURCE_SYNTHETIC_POS_FIELD] = pos;
    fields[layout::SOURCE_SYNTHETIC_TAIL_POS_FIELD] = tail;
    let mut scalars = vec![0; layout::SOURCE_SYNTHETIC.scalar_bytes];
    scalars[layout::SOURCE_SYNTHETIC_CANONICAL_BYTE_OFFSET] = u8::from(canonical);
    Obj::mk_ctor(layout::SOURCE_SYNTHETIC.tag, fields, &scalars)
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
