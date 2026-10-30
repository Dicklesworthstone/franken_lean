//! Exact native Mirror rows used by imported MacroM functions.
//!
//! These are Lean definitions, not extern declarations. Their runtime
//! telescopes are mechanically extracted from the pinned compiler alongside
//! the Syntax ABI contract. Keeping a distinct `mirror:` identity avoids
//! fabricating rows in the generated extern census.

use fln_comp::flbc::{ArgumentOwnership, ResultOwnership};
use fln_core::name::Name;
use fln_rt::syntax_abi_generated as generated;

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
            .map(|borrowed| {
                if *borrowed {
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
        id: "mirror:Lean.Name.mkStr1",
        name: "Lean.Name.mkStr1",
        borrowed: generated::NAME_MK_STR1_BORROWED,
        parameters: generated::NAME_MK_STR1_PARAMETERS,
        result_type: generated::NAME_MK_STR1_RESULT,
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
];

pub fn row_for_name(name: &Name) -> Option<&'static MirrorRow> {
    ROWS.iter()
        .find(|row| Name::from_components(row.name.split('.')) == *name)
}

pub fn row_for_id(id: &str) -> Option<&'static MirrorRow> {
    ROWS.iter().find(|row| row.id == id)
}

/// Included in inline-cache context identity alongside the extern contract.
pub const CONTRACT: &str = include_str!("../../fln-rt/src/syntax_abi_generated.rs");
