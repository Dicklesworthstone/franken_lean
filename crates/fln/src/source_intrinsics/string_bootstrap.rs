//! Native ABI contracts for the pin's String traversal and position helpers.
//!
//! Bootstrap's safe opaques contain Inhabited fallbacks, not executable
//! implementations. Prelude's utf8ByteSize and the position-indexed Basic,
//! PosRaw and Modify definitions instead expose the logical byte array
//! representation, which a native String does not have. The native operations
//! require their explicit extern and their complete pinned declaration closure
//! before crossing either boundary. The fixed inventory binds every
//! ConstantInfo, including proof dependencies, dictionaries, recursor rules,
//! metadata and safety. Membership bits keep a Prelude-only byte-size call
//! independent of the Bootstrap module, and a Bootstrap call independent of
//! the larger Basic and Modify closures. A deprecated alias (`String.get`,
//! `set`, `data`, ...) shares its target's extern symbol but is a separate
//! declaration: it has its own row, extern check and closure, never its
//! target's.
//! These comparison data never install declarations or confer admission.

use super::*;

const DEPENDENCIES: &str = include_str!("string_bootstrap/dependencies.txt");
const DEPENDENCY_COUNT: usize = 4089;

/// Successful dependency checks shared only within one immutable Preparation.
/// Membership and each selected root's extern still belong to its operation.
/// One flag per inventory row, kept on the heap: every Preparation carries
/// this table, and Preparations live on small host stacks.
pub(crate) struct VerifiedDependencies(Box<[bool]>);

impl Default for VerifiedDependencies {
    fn default() -> Self {
        Self(vec![false; DEPENDENCY_COUNT].into_boxed_slice())
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
    InternalGet,
    RawGet,
    RawSet,
    DecodeChar,
    GetUtf8Byte,
    RawNextFast,
    RawExtract,
    PosSet,
    PosExtract,
    ToList,
    Get,
    GetFast,
    RawGetFast,
    NextFast,
    PosNext,
    Set,
    GetUtf8ByteAlias,
    InternalGetUtf8Byte,
    Data,
}

/// One bit per operation in the inventory's membership column.
type Membership = u32;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Domain {
    String,
    Char,
    Position,
    Nat,
    Bool,
    StringCallback,
    /// `String.Pos s`, the checked `Pos.Raw` record over the earlier String.
    /// As a result it is rebuilt over the same String.
    StringPosition,
    /// A checked proof argument, which the native ABI never receives.
    Proof,
    /// `UInt8`, as a result only.
    Byte,
    /// `List Char`, as a result only.
    CharList,
}

impl Domain {
    /// The closed source type of a non-dependent domain. Dependent positions
    /// and proofs take their binder types from the checked telescope instead.
    pub(crate) fn source_type(self) -> Expr {
        let c = |label| Expr::const_(name(label), Vec::new());
        match self {
            Self::String => c("String"),
            Self::Char => c("Char"),
            Self::Position => c("String.Pos.Raw"),
            Self::Nat => c("Nat"),
            Self::Bool => c("Bool"),
            Self::Byte => c("UInt8"),
            Self::CharList => Expr::app(Expr::const_(name("List"), vec![Level::zero()]), c("Char")),
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
            Self::StringPosition | Self::Proof => {
                unreachable!("dependent String domains use the checked telescope")
            }
        }
    }
}

impl Operation {
    pub(crate) const ALL: [Self; 27] = [
        Self::ByteSize,
        Self::PosOf,
        Self::OffsetOfPos,
        Self::Extract,
        Self::Next,
        Self::Pushn,
        Self::Foldl,
        Self::IsEmpty,
        Self::InternalGet,
        Self::RawGet,
        Self::RawSet,
        Self::DecodeChar,
        Self::GetUtf8Byte,
        Self::RawNextFast,
        Self::RawExtract,
        Self::PosSet,
        Self::PosExtract,
        Self::ToList,
        Self::Get,
        Self::GetFast,
        Self::RawGetFast,
        Self::NextFast,
        Self::PosNext,
        Self::Set,
        Self::GetUtf8ByteAlias,
        Self::InternalGetUtf8Byte,
        Self::Data,
    ];

    pub(crate) fn index(self) -> usize {
        self as usize
    }

    fn mask(self) -> Membership {
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
            Self::InternalGet => "String.Internal.get",
            Self::RawGet => "String.Pos.Raw.get",
            Self::RawSet => "String.Pos.Raw.set",
            Self::DecodeChar => "String.decodeChar",
            Self::GetUtf8Byte => "String.getUTF8Byte",
            Self::RawNextFast => "String.Pos.Raw.next'",
            Self::RawExtract => "String.Pos.Raw.extract",
            Self::PosSet => "String.Pos.set",
            Self::PosExtract => "String.extract",
            Self::ToList => "String.toList",
            Self::Get => "String.get",
            Self::GetFast => "String.get'",
            Self::RawGetFast => "String.Pos.Raw.get'",
            Self::NextFast => "String.next'",
            Self::PosNext => "String.Pos.next",
            Self::Set => "String.set",
            Self::GetUtf8ByteAlias => "String.getUtf8Byte",
            Self::InternalGetUtf8Byte => "String.Internal.getUTF8Byte",
            Self::Data => "String.data",
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

    /// The generated census row's declaration kind and defining module.
    pub(crate) fn declaration(self) -> (&'static str, &'static str) {
        match self {
            Self::ByteSize => ("defn", "Init.Prelude"),
            Self::PosOf
            | Self::OffsetOfPos
            | Self::Extract
            | Self::Next
            | Self::Pushn
            | Self::Foldl
            | Self::IsEmpty
            | Self::InternalGet
            | Self::InternalGetUtf8Byte => ("opaque", "Init.Data.String.Bootstrap"),
            Self::RawGet
            | Self::DecodeChar
            | Self::RawNextFast
            | Self::RawExtract
            | Self::PosExtract
            | Self::ToList
            | Self::Get
            | Self::GetFast
            | Self::RawGetFast
            | Self::NextFast
            | Self::PosNext
            | Self::Data => ("defn", "Init.Data.String.Basic"),
            Self::GetUtf8Byte | Self::GetUtf8ByteAlias => ("defn", "Init.Data.String.PosRaw"),
            Self::RawSet | Self::PosSet | Self::Set => ("defn", "Init.Data.String.Modify"),
        }
    }

    /// The checked telescope, in source order. Proofs are logical arguments
    /// that the native row does not receive.
    pub(crate) fn domains(self) -> &'static [Domain] {
        use Domain::{Char, Nat, Position, Proof, String, StringCallback, StringPosition};
        match self {
            Self::ByteSize | Self::IsEmpty | Self::ToList | Self::Data => &[String],
            Self::PosOf => &[String, Char],
            Self::OffsetOfPos | Self::Next | Self::InternalGet | Self::RawGet | Self::Get => {
                &[String, Position]
            }
            Self::Extract | Self::RawExtract => &[String, Position, Position],
            Self::Pushn => &[String, Char, Nat],
            Self::Foldl => &[StringCallback, String, String],
            Self::RawSet | Self::Set => &[String, Position, Char],
            Self::DecodeChar | Self::InternalGetUtf8Byte => &[String, Nat, Proof],
            Self::GetUtf8Byte
            | Self::RawNextFast
            | Self::GetFast
            | Self::RawGetFast
            | Self::NextFast
            | Self::GetUtf8ByteAlias => &[String, Position, Proof],
            Self::PosNext => &[String, StringPosition, Proof],
            Self::PosSet => &[String, StringPosition, Char, Proof],
            Self::PosExtract => &[String, StringPosition, StringPosition],
        }
    }

    /// Whether the adapter's binders follow the declaration's own dependent
    /// telescope. The original rows keep their closed source types.
    pub(crate) fn dependent(self) -> bool {
        self.domains()
            .iter()
            .any(|domain| matches!(domain, Domain::StringPosition | Domain::Proof))
    }

    /// Whether the adapter reads or rebuilds a record whose proof field it
    /// erases to the checked `Bool` placeholder: `Char`, `UInt8`, `String.Pos`.
    #[cfg(test)]
    pub(crate) fn uses_character(self) -> bool {
        matches!(self, Self::PosOf | Self::Pushn | Self::Foldl) || self >= Self::InternalGet
    }

    pub(crate) fn result(self) -> Domain {
        match self {
            Self::ByteSize | Self::OffsetOfPos => Domain::Nat,
            Self::PosOf | Self::Next | Self::RawNextFast | Self::NextFast => Domain::Position,
            Self::PosNext => Domain::StringPosition,
            Self::Extract
            | Self::Pushn
            | Self::Foldl
            | Self::RawSet
            | Self::RawExtract
            | Self::PosSet
            | Self::PosExtract
            | Self::Set => Domain::String,
            Self::IsEmpty => Domain::Bool,
            Self::InternalGet
            | Self::RawGet
            | Self::DecodeChar
            | Self::Get
            | Self::GetFast
            | Self::RawGetFast => Domain::Char,
            Self::GetUtf8Byte | Self::GetUtf8ByteAlias | Self::InternalGetUtf8Byte => Domain::Byte,
            Self::ToList | Self::Data => Domain::CharList,
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

fn inventory_row(line: &str) -> (Membership, &str, &str) {
    let (mask, rest) = line
        .split_once('\t')
        .expect("fixed String bootstrap membership");
    let (encoded, digest) = rest
        .split_once('\t')
        .expect("fixed String bootstrap dependency");
    (
        Membership::from_str_radix(mask, 16).expect("fixed String bootstrap membership bits"),
        encoded,
        digest,
    )
}

/// The inventory's spelling of a name, for comparing a row without decoding it.
fn encoded_name(label: &Name) -> String {
    use fln_core::name::LeafView;
    let mut components = Vec::new();
    let mut current = label.clone();
    loop {
        match current.leaf_view() {
            LeafView::Anonymous => break,
            LeafView::Str(text) => components.push(format!("s:{text}")),
            LeafView::Num(number) => components.push(format!("n:{number}")),
        }
        current = current.parent();
    }
    components.reverse();
    components.join("/")
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
    let root = encoded_name(&requested);
    let mut root_seen = false;
    for (index, line) in DEPENDENCIES.lines().enumerate() {
        charge_catalog_node(visited, limits)?;
        let (mask, encoded, digest) = inventory_row(line);
        if mask & operation.mask() == 0 {
            continue;
        }
        root_seen |= encoded == root;
        let checked = verified
            .0
            .get_mut(index)
            .ok_or(IngressError::UnsupportedNode {
                kind: "String bootstrap dependency inventory length",
            })?;
        // A row another operation already proved is charged, not re-decoded:
        // a Basic-level closure shares thousands of rows with its siblings.
        if *checked {
            continue;
        }
        let dependency = dependency_name(encoded, visited, limits)?;
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
