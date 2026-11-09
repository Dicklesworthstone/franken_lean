//! Exact native Mirror rows used by imported MacroM functions.
//!
//! These are Lean definitions, not extern declarations. Their runtime
//! telescopes are mechanically extracted from the pinned compiler alongside
//! the Syntax ABI contract. Keeping a distinct `mirror:` identity avoids
//! fabricating rows in the generated extern census.

use crate::interpreter::{CancellationProbe, ExecutionLimits, ExecutionUsage, VmRefusal};
use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_rt::obj::Obj;
use fln_rt::syntax_abi_generated as generated;

/// Invocation-local authority to expand one root using the active macro table.
/// The opaque MethodsRef never grants this capability. The arguments and result
/// use the extracted MacroM ABI; the host must validate them before use.
pub trait MacroExpansion {
    fn expand_macro(
        &self,
        syntax: &Obj,
        context: &Obj,
        state: &Obj,
        limits: ExecutionLimits,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> MacroExpansionResult;
}

/// A callback's EStateM result and the completed VM work it performed.
/// Resource stops and internal faults remain outside the Lean exception value.
pub struct MacroExpansionResult {
    pub outcome: Outcome<Result<Obj, VmRefusal>>,
    pub usage: ExecutionUsage,
}

/// Independent capabilities borrowed for one VM invocation, never cached.
#[derive(Clone, Copy, Default)]
pub struct MacroMethods<'a> {
    pub lookup: Option<&'a dyn MacroLookup>,
    pub expansion: Option<&'a dyn MacroExpansion>,
}

/// Read-only host lookups explicitly supplied for one macro invocation.
///
/// The VM never reconstructs this authority from an opaque MethodsRef value.
/// Callers bind it to their native environment and current source namespace.
pub trait MacroLookup {
    fn current_namespace(&self) -> &Name;
    fn has_decl(&self, declaration: &Name) -> bool;

    /// Namespace candidates in the pin's lookup order, including repetitions.
    /// A provider that cannot answer must refuse, never return an empty answer.
    fn resolve_namespace(&self, _name: &Name) -> Result<Vec<Name>, MacroLookupError> {
        Err(MacroLookupError::Unavailable)
    }

    /// Global candidates with their projection suffixes, in lookup order.
    /// Resolving a reserved name does not execute its declaration action.
    fn resolve_global_name(&self, _name: &Name) -> Result<ResolvedGlobals, MacroLookupError> {
        Err(MacroLookupError::Unavailable)
    }
}

/// Ordered overload candidates and their projection suffixes.
pub type ResolvedGlobals = Vec<(Name, Vec<String>)>;

/// A name query's host-side stop, kept distinct from a successful empty result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MacroLookupError {
    Unavailable,
    Invalid(&'static str),
    /// A dependency exhausted its resources without numerical usage details.
    Exhausted(&'static str),
    Limit {
        resource: &'static str,
        limit: u64,
        observed: u64,
    },
}

impl std::fmt::Display for MacroLookupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unavailable => f.write_str("macro lookup capability is unavailable"),
            Self::Invalid(detail) => write!(f, "invalid macro lookup: {detail}"),
            Self::Exhausted(resource) => {
                write!(f, "native macro lookup exhausted {resource}")
            }
            Self::Limit {
                resource,
                limit,
                observed,
            } => {
                write!(
                    f,
                    "macro lookup {resource} limit {limit}, observed {observed}"
                )
            }
        }
    }
}

impl std::error::Error for MacroLookupError {}

#[derive(Clone, Copy, Debug)]
pub struct MirrorRow {
    pub id: &'static str,
    pub name: &'static str,
    pub borrowed: &'static [bool],
    pub parameters: &'static [&'static str],
    pub result_type: &'static str,
}

impl MirrorRow {
    pub fn argument_ownership(&self) -> Vec<ArgumentOwnership> {
        self.borrowed
            .iter()
            .zip(self.parameters)
            .map(|(borrowed, parameter)| {
                if *parameter == "u8" {
                    ArgumentOwnership::Scalar
                } else if *borrowed {
                    ArgumentOwnership::Borrowed
                } else {
                    ArgumentOwnership::Owned
                }
            })
            .collect()
    }

    pub fn result_ownership(&self) -> ResultOwnership {
        // Every non-scalar result is a fresh owned handle, including Syntax
        // missing and small Nat. RawObject records that erased representation.
        if self.result_type == "u8" {
            ResultOwnership::Scalar
        } else {
            ResultOwnership::RawObject
        }
    }
}

pub const ROWS: &[MirrorRow] = &[
    MirrorRow {
        id: "mirror:Lean.Name.str._override",
        name: "Lean.Name.str._override",
        borrowed: generated::NAME_STR_BORROWED,
        parameters: generated::NAME_STR_PARAMETERS,
        result_type: generated::NAME_STR_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Name.mkStr1",
        name: "Lean.Name.mkStr1",
        borrowed: generated::NAME_MK_STR1_BORROWED,
        parameters: generated::NAME_MK_STR1_PARAMETERS,
        result_type: generated::NAME_MK_STR1_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.addMacroScope",
        name: "Lean.addMacroScope",
        borrowed: generated::ADD_MACRO_SCOPE_BORROWED,
        parameters: generated::ADD_MACRO_SCOPE_PARAMETERS,
        result_type: generated::ADD_MACRO_SCOPE_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.addMacroScope",
        name: "Lean.Macro.addMacroScope",
        borrowed: generated::MACRO_ADD_MACRO_SCOPE_BORROWED,
        parameters: generated::MACRO_ADD_MACRO_SCOPE_PARAMETERS,
        result_type: generated::MACRO_ADD_MACRO_SCOPE_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getArg",
        name: "Lean.Syntax.getArg",
        borrowed: generated::SYNTAX_GET_ARG_BORROWED,
        parameters: generated::SYNTAX_GET_ARG_PARAMETERS,
        result_type: generated::SYNTAX_GET_ARG_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getNumArgs",
        name: "Lean.Syntax.getNumArgs",
        borrowed: generated::SYNTAX_GET_NUM_ARGS_BORROWED,
        parameters: generated::SYNTAX_GET_NUM_ARGS_PARAMETERS,
        result_type: generated::SYNTAX_GET_NUM_ARGS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.isOfKind",
        name: "Lean.Syntax.isOfKind",
        borrowed: generated::SYNTAX_IS_OF_KIND_BORROWED,
        parameters: generated::SYNTAX_IS_OF_KIND_PARAMETERS,
        result_type: generated::SYNTAX_IS_OF_KIND_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getKind",
        name: "Lean.Syntax.getKind",
        borrowed: generated::SYNTAX_GET_KIND_BORROWED,
        parameters: generated::SYNTAX_GET_KIND_PARAMETERS,
        result_type: generated::SYNTAX_GET_KIND_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.setKind",
        name: "Lean.Syntax.setKind",
        borrowed: generated::SYNTAX_SET_KIND_BORROWED,
        parameters: generated::SYNTAX_SET_KIND_PARAMETERS,
        result_type: generated::SYNTAX_SET_KIND_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getArgs",
        name: "Lean.Syntax.getArgs",
        borrowed: generated::SYNTAX_GET_ARGS_BORROWED,
        parameters: generated::SYNTAX_GET_ARGS_PARAMETERS,
        result_type: generated::SYNTAX_GET_ARGS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.setArgs",
        name: "Lean.Syntax.setArgs",
        borrowed: generated::SYNTAX_SET_ARGS_BORROWED,
        parameters: generated::SYNTAX_SET_ARGS_PARAMETERS,
        result_type: generated::SYNTAX_SET_ARGS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.setArg",
        name: "Lean.Syntax.setArg",
        borrowed: generated::SYNTAX_SET_ARG_BORROWED,
        parameters: generated::SYNTAX_SET_ARG_PARAMETERS,
        result_type: generated::SYNTAX_SET_ARG_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.isAtom",
        name: "Lean.Syntax.isAtom",
        borrowed: generated::SYNTAX_IS_ATOM_BORROWED,
        parameters: generated::SYNTAX_IS_ATOM_PARAMETERS,
        result_type: generated::SYNTAX_IS_ATOM_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getAtomVal",
        name: "Lean.Syntax.getAtomVal",
        borrowed: generated::SYNTAX_GET_ATOM_VAL_BORROWED,
        parameters: generated::SYNTAX_GET_ATOM_VAL_PARAMETERS,
        result_type: generated::SYNTAX_GET_ATOM_VAL_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.setAtomVal",
        name: "Lean.Syntax.setAtomVal",
        borrowed: generated::SYNTAX_SET_ATOM_VAL_BORROWED,
        parameters: generated::SYNTAX_SET_ATOM_VAL_PARAMETERS,
        result_type: generated::SYNTAX_SET_ATOM_VAL_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getHeadInfo",
        name: "Lean.Syntax.getHeadInfo",
        borrowed: generated::SYNTAX_GET_HEAD_INFO_BORROWED,
        parameters: generated::SYNTAX_GET_HEAD_INFO_PARAMETERS,
        result_type: generated::SYNTAX_GET_HEAD_INFO_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.SourceInfo.getPos?",
        name: "Lean.SourceInfo.getPos?",
        borrowed: generated::SOURCE_INFO_GET_POS_BORROWED,
        parameters: generated::SOURCE_INFO_GET_POS_PARAMETERS,
        result_type: generated::SOURCE_INFO_GET_POS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.SourceInfo.getTailPos?",
        name: "Lean.SourceInfo.getTailPos?",
        borrowed: generated::SOURCE_INFO_GET_TAIL_POS_BORROWED,
        parameters: generated::SOURCE_INFO_GET_TAIL_POS_PARAMETERS,
        result_type: generated::SOURCE_INFO_GET_TAIL_POS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getPos?",
        name: "Lean.Syntax.getPos?",
        borrowed: generated::SYNTAX_GET_POS_BORROWED,
        parameters: generated::SYNTAX_GET_POS_PARAMETERS,
        result_type: generated::SYNTAX_GET_POS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getTailPos?",
        name: "Lean.Syntax.getTailPos?",
        borrowed: generated::SYNTAX_GET_TAIL_POS_BORROWED,
        parameters: generated::SYNTAX_GET_TAIL_POS_PARAMETERS,
        result_type: generated::SYNTAX_GET_TAIL_POS_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.setInfo",
        name: "Lean.Syntax.setInfo",
        borrowed: generated::SYNTAX_SET_INFO_BORROWED,
        parameters: generated::SYNTAX_SET_INFO_PARAMETERS,
        result_type: generated::SYNTAX_SET_INFO_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.isMissing",
        name: "Lean.Syntax.isMissing",
        borrowed: generated::SYNTAX_IS_MISSING_BORROWED,
        parameters: generated::SYNTAX_IS_MISSING_PARAMETERS,
        result_type: generated::SYNTAX_IS_MISSING_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.isIdent",
        name: "Lean.Syntax.isIdent",
        borrowed: generated::SYNTAX_IS_IDENT_BORROWED,
        parameters: generated::SYNTAX_IS_IDENT_PARAMETERS,
        result_type: generated::SYNTAX_IS_IDENT_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Syntax.getId",
        name: "Lean.Syntax.getId",
        borrowed: generated::SYNTAX_GET_ID_BORROWED,
        parameters: generated::SYNTAX_GET_ID_PARAMETERS,
        result_type: generated::SYNTAX_GET_ID_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.getCurrNamespace",
        name: "Lean.Macro.getCurrNamespace",
        borrowed: generated::MACRO_GET_CURR_NAMESPACE_BORROWED,
        parameters: generated::MACRO_GET_CURR_NAMESPACE_PARAMETERS,
        result_type: generated::MACRO_GET_CURR_NAMESPACE_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.hasDecl",
        name: "Lean.Macro.hasDecl",
        borrowed: generated::MACRO_HAS_DECL_BORROWED,
        parameters: generated::MACRO_HAS_DECL_PARAMETERS,
        result_type: generated::MACRO_HAS_DECL_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.resolveNamespace",
        name: "Lean.Macro.resolveNamespace",
        borrowed: generated::MACRO_RESOLVE_NAMESPACE_BORROWED,
        parameters: generated::MACRO_RESOLVE_NAMESPACE_PARAMETERS,
        result_type: generated::MACRO_RESOLVE_NAMESPACE_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.resolveGlobalName",
        name: "Lean.Macro.resolveGlobalName",
        borrowed: generated::MACRO_RESOLVE_GLOBAL_NAME_BORROWED,
        parameters: generated::MACRO_RESOLVE_GLOBAL_NAME_PARAMETERS,
        result_type: generated::MACRO_RESOLVE_GLOBAL_NAME_RESULT,
    },
    MirrorRow {
        id: "mirror:Lean.Macro.expandMacro?",
        name: "Lean.Macro.expandMacro?",
        borrowed: fln_rt::macro_expansion_abi_generated::MACRO_EXPAND_MACRO_BORROWED,
        parameters: fln_rt::macro_expansion_abi_generated::MACRO_EXPAND_MACRO_PARAMETERS,
        result_type: fln_rt::macro_expansion_abi_generated::MACRO_EXPAND_MACRO_RESULT,
    },
];

pub fn row_for_name(name: &Name) -> Option<&'static MirrorRow> {
    ROWS.iter()
        .find(|row| Name::from_components(row.name.split('.')) == *name)
}

pub fn row_for_id(id: &str) -> Option<&'static MirrorRow> {
    ROWS.iter().find(|row| row.id == id)
}

/// Included in inline-cache context identity alongside the extern contract.
pub const CONTRACT: &str = concat!(
    include_str!("../../fln-rt/src/syntax_abi_generated.rs"),
    include_str!("../../fln-rt/src/macro_expansion_abi_generated.rs"),
);
