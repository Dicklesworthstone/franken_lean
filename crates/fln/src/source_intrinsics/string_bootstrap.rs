//! Native ABI contracts for the pin's String traversal and position helpers.
//!
//! Bootstrap's safe opaques contain Inhabited fallbacks, not executable
//! implementations. Prelude's utf8ByteSize instead exposes the logical byte
//! array representation. The native operations require their explicit extern
//! and their complete pinned declaration closure before crossing either boundary.
//! The fixed inventory binds every ConstantInfo, including proof dependencies,
//! dictionaries, recursor rules, metadata and safety. Membership bits keep a
//! Prelude-only byte-size call independent of the Bootstrap module.
//! These comparison data never install declarations or confer admission.

use super::*;

const DEPENDENCIES: &str = include_str!("string_bootstrap/dependencies.txt");
const DEPENDENCY_COUNT: usize = 343;

/// Successful dependency checks shared only within one immutable Preparation.
/// Membership and each selected root's extern still belong to its operation.
pub(crate) struct VerifiedDependencies([bool; DEPENDENCY_COUNT]);

impl Default for VerifiedDependencies {
    fn default() -> Self {
        Self([false; DEPENDENCY_COUNT])
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub(crate) enum Operation {
    ByteSize,
    PosOf,
    OffsetOfPos,
    Extract,
    Next,
    Pushn,
    Foldl,
    IsEmpty,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Domain {
    String,
    Char,
    Position,
    Nat,
    Bool,
    StringCallback,
}

impl Domain {
    pub(crate) fn source_type(self) -> Expr {
        let c = |label| Expr::const_(name(label), Vec::new());
        match self {
            Self::String => c("String"),
            Self::Char => c("Char"),
            Self::Position => c("String.Pos.Raw"),
            Self::Nat => c("Nat"),
            Self::Bool => c("Bool"),
            Self::StringCallback => Expr::forall_e(
                Name::anonymous(),
                c("String"),
                Expr::forall_e(
                    Name::anonymous(),
                    c("Char"),
                    c("String"),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
        }
    }
}

impl Operation {
    pub(crate) const ALL: [Self; 8] = [
        Self::ByteSize,
        Self::PosOf,
        Self::OffsetOfPos,
        Self::Extract,
        Self::Next,
        Self::Pushn,
        Self::Foldl,
        Self::IsEmpty,
    ];

    pub(crate) fn index(self) -> usize {
        self as usize
    }

    fn mask(self) -> u8 {
        1 << self.index()
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::ByteSize => "String.utf8ByteSize",
            Self::PosOf => "String.Internal.posOf",
            Self::OffsetOfPos => "String.Internal.offsetOfPos",
            Self::Extract => "String.Internal.extract",
            Self::Next => "String.Internal.next",
            Self::Pushn => "String.Internal.pushn",
            Self::Foldl => "String.Internal.foldl",
            Self::IsEmpty => "String.Internal.isEmpty",
        }
    }

    pub(crate) fn source_name(self) -> Name {
        name(self.label())
    }

    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        Self::ALL
            .into_iter()
            .find(|operation| requested == &operation.source_name())
    }

    pub(crate) fn domains(self) -> &'static [Domain] {
        use Domain::{Char, Nat, Position, String, StringCallback};
        match self {
            Self::ByteSize | Self::IsEmpty => &[String],
            Self::PosOf => &[String, Char],
            Self::OffsetOfPos | Self::Next => &[String, Position],
            Self::Extract => &[String, Position, Position],
            Self::Pushn => &[String, Char, Nat],
            Self::Foldl => &[StringCallback, String, String],
        }
    }

    #[cfg(test)]
    pub(crate) fn uses_character(self) -> bool {
        matches!(self, Self::PosOf | Self::Pushn | Self::Foldl)
    }

    pub(crate) fn result(self) -> Domain {
        match self {
            Self::ByteSize | Self::OffsetOfPos => Domain::Nat,
            Self::PosOf | Self::Next => Domain::Position,
            Self::Extract | Self::Pushn | Self::Foldl => Domain::String,
            Self::IsEmpty => Domain::Bool,
        }
    }

    pub(crate) fn primitive(self) -> Name {
        Name::num(name("_fln_runtime_string_bootstrap_abi"), self as u64)
    }
}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
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
                    .expect("fixed String bootstrap dependency number"),
            )
        } else {
            unreachable!("fixed String bootstrap dependency encoding")
        };
    }
    Ok(result)
}

fn inventory_row(line: &str) -> (u8, &str, &str) {
    let (mask, rest) = line
        .split_once('\t')
        .expect("fixed String bootstrap membership");
    let (encoded, digest) = rest
        .split_once('\t')
        .expect("fixed String bootstrap dependency");
    (
        u8::from_str_radix(mask, 16).expect("fixed String bootstrap membership bits"),
        encoded,
        digest,
    )
}

pub(crate) fn contract_matches(
    environment: &Environment,
    operation: Operation,
    verified: &mut VerifiedDependencies,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let requested = operation.source_name();
    if !extern_attribute_matches(environment, &requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let mut root_seen = false;
    for (index, line) in DEPENDENCIES.lines().enumerate() {
        charge_catalog_node(visited, limits)?;
        let (mask, encoded, digest) = inventory_row(line);
        if mask & operation.mask() == 0 {
            continue;
        }
        let dependency = dependency_name(encoded, visited, limits)?;
        root_seen |= dependency == requested;
        let checked = verified
            .0
            .get_mut(index)
            .ok_or(IngressError::UnsupportedNode {
                kind: "String bootstrap dependency inventory length",
            })?;
        if *checked {
            continue;
        }
        if environment
            .entry(&dependency)
            .is_none_or(|entry| entry.digest().to_hex() != digest)
        {
            return Err(IngressError::UnsupportedNode {
                kind: "String bootstrap dependency differs from its exact pinned contract",
            });
        }
        // Declaration identity does not bind extensions. Never let an altered
        // selected helper extern inherit a native implementation from its body.
        check_selected_extern_attribute(environment, &dependency, externs, visited, limits)?;
        *checked = true;
    }
    if !root_seen {
        return Err(IngressError::UnsupportedNode {
            kind: "String bootstrap operation requires its complete dependency inventory",
        });
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
