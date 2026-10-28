//! Exact post-admission authority for the pin's `lean_string_mk` declarations.
//!
//! The logical model encodes List Char into a proof-carrying ByteArray before
//! constructing String. Its genuine native extern instead traverses the
//! character list. The pin attaches that extern to Prelude's `String.ofList`
//! and to Bootstrap's deprecated alias `String.mk`. The alias shares the
//! extern symbol and its native traversal but is a separate declaration: it
//! has its own generated census row, extern check and fixed inventory, never
//! its target's, and a Prelude-only `String.ofList` call stays independent of
//! the Bootstrap module. Each inventory binds the complete transitive type,
//! value, proof, constructor membership and recursor-rule closure of its root
//! from the pin. These comparison data never admit or install declarations.
//! Every selected extern journal is checked independently of declaration
//! digests.

use super::*;

const DEPENDENCIES: &str = include_str!("string_from_list/dependencies.txt");
const MK_DEPENDENCIES: &str = include_str!("string_from_list/mk_dependencies.txt");

/// A pinned declaration whose `@[extern]` is `lean_string_mk`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Root {
    /// `String.ofList` (Prelude.lean:3525).
    OfList,
    /// `String.mk` (Bootstrap.lean:142), deprecated in favour of `String.ofList`.
    Mk,
}

impl Root {
    pub(crate) const ALL: [Self; 2] = [Self::OfList, Self::Mk];

    pub(crate) fn index(self) -> usize {
        self as usize
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::OfList => "String.ofList",
            Self::Mk => "String.mk",
        }
    }

    pub(crate) fn source_name(self) -> Name {
        Name::from_components(self.label().split('.'))
    }

    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|root| requested == &root.source_name())
    }

    /// The generated census row's defining module.
    fn module(self) -> &'static str {
        match self {
            Self::OfList => "Init.Prelude",
            Self::Mk => "Init.Data.String.Bootstrap",
        }
    }

    pub(crate) fn dependency_inventory(self) -> &'static str {
        match self {
            Self::OfList => DEPENDENCIES,
            Self::Mk => MK_DEPENDENCIES,
        }
    }
}

fn dependency_name(
    encoded: &str,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<Name, IngressError> {
    let mut result = Name::anonymous();
    for component in encoded.split('/') {
        charge_catalog_node(visited, limits)?;
        result = if let Some(text) = component.strip_prefix("s:") {
            Name::str(result, text)
        } else if let Some(number) = component.strip_prefix("n:") {
            Name::num(
                result,
                number
                    .parse()
                    .expect("fixed lean_string_mk dependency numeric component"),
            )
        } else {
            unreachable!("fixed lean_string_mk dependency component encoding")
        };
    }
    Ok(result)
}

pub(crate) fn contract_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let Some(root) = Root::from_name(requested) else {
        return Ok(false);
    };
    let refusal = |of_list: &'static str, mk: &'static str| IngressError::UnsupportedNode {
        kind: match root {
            Root::OfList => of_list,
            Root::Mk => mk,
        },
    };
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let Some(row) = fln_vm::extern_table_generated::EXTERN_ROWS
        .iter()
        .find(|row| row.name == root.label())
    else {
        return Err(refusal(
            "String.ofList requires its generated native row",
            "String.mk requires its generated native row",
        ));
    };
    if row.id.strip_prefix("extern:") != Some(root.label())
        || row.kind != "defn"
        || row.module != root.module()
        || row.levels != 0
        || row.arity != 1
        || row.effect != "pure"
        || row.safety != "safe"
        || row.symbol != "lean_string_mk"
        || row.ownership != "abi((cs: owned_arg) -> owned_res)"
    {
        return Err(refusal(
            "String.ofList generated native contract differs from the pin",
            "String.mk generated native contract differs from the pin",
        ));
    }
    let mut root_seen = false;
    for line in root.dependency_inventory().lines() {
        charge_catalog_node(visited, limits)?;
        let (encoded, digest) = line
            .split_once('\t')
            .expect("fixed lean_string_mk dependency row");
        let dependency = dependency_name(encoded, visited, limits)?;
        root_seen |= dependency == *requested;
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(refusal(
                "String.ofList dependency differs from its exact pinned contract",
                "String.mk dependency differs from its exact pinned contract",
            ));
        }
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
    }
    if !root_seen {
        return Err(refusal(
            "String.ofList requires its complete dependency inventory",
            "String.mk requires its complete dependency inventory",
        ));
    }
    Ok(true)
}
