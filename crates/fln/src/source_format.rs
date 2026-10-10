//! Bounded presentation of a checked, logical `Std.Format` returned by Golem.
//!
//! This is a value projection, not an admission or runtime replacement. The
//! caller retains the environment, checked type and VM exit which produced the
//! value. Constructor identities and fields are checked against the admitted
//! logical families before they acquire native formatting meaning. In
//! particular, logical `Int` constructors are not the runtime's packed Int ABI.

use crate::pretty::format::{Behavior, Format, FormatRenderError, FormatRenderLimits};
use crate::{DefinitionExecution, Environment, Expr, Name, VmExit, VmValueKind, vm_value_kind};
use fln_core::expr::{BinderInfo, ExprNode};
use fln_core::level::Level;
use fln_env::constants::ConstantInfo;
use fln_rt::obj::{Header, Obj};
use std::fmt;

const FORMAT: &str = "Std.Format";
const BEHAVIOR: &str = "Std.Format.FlattenBehavior";

/// The owned native format uses boxes; bounding its depth also bounds its
/// destruction stack. Larger requested depth limits are capped at this value.
pub const MAX_DEPTH: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Format nodes and scalar payloads visited, including ignored tag labels.
    pub max_nodes: usize,
    /// Maximum number of format edges below the root. Zero permits a leaf.
    pub max_depth: usize,
    /// Total UTF-8 text copied out of the VM, before layout or indentation.
    pub max_text_bytes: usize,
    pub rendering: FormatRenderLimits,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_nodes: 100_000,
            max_depth: MAX_DEPTH,
            max_text_bytes: 16 * 1024 * 1024,
            rendering: FormatRenderLimits {
                max_work: 1_000_000,
                max_output_bytes: 16 * 1024 * 1024,
            },
        }
    }
}

/// A failed projection or render never returns partial text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedType,
    UnsupportedContract {
        family: &'static str,
    },
    NonReturningExit,
    Representation {
        expected: &'static str,
    },
    Limit {
        resource: &'static str,
        limit: usize,
        observed: usize,
    },
    IntegerRange,
    AllocationFailure,
    Render(FormatRenderError),
}

impl Error {
    /// Diagnostic class, completion flag and process exit code. Resource
    /// exhaustion and malformed VM values cannot be presented as user answers.
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::UnexpectedType | Self::UnsupportedContract { .. } => ("capability", false, 5),
            Self::NonReturningExit | Self::Representation { .. } => ("internal-fault", false, 4),
            Self::Limit { .. } | Self::IntegerRange | Self::AllocationFailure | Self::Render(_) => {
                ("resource", false, 3)
            }
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedType => f.write_str("format presentation requires checked Std.Format"),
            Self::UnsupportedContract { family } => {
                write!(
                    f,
                    "format presentation requires the supported {family} declaration layout"
                )
            }
            Self::NonReturningExit => {
                f.write_str("format presentation requires a returned VM value")
            }
            Self::Representation { expected } => {
                write!(f, "malformed runtime representation for {expected}")
            }
            Self::Limit {
                resource,
                limit,
                observed,
            } => write!(f, "format {resource} limit {limit} exceeded by {observed}"),
            Self::IntegerRange => f.write_str("format indentation exceeds the native signed range"),
            Self::AllocationFailure => f.write_str("format projection allocation failed"),
            Self::Render(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

/// Render a completed checked execution. The source adapter, rather than the
/// value's tag, decides whether the result should be displayed this way.
pub fn render(
    execution: &DefinitionExecution,
    width: usize,
    limits: Limits,
) -> Result<String, Error> {
    render_vm(
        execution.engine.environment(),
        &execution.runtime_type,
        &execution.exit,
        width,
        limits,
    )
}

/// Project an original or replayed VM exit under its retained checked type and
/// environment. This function grants no admission authority to supplied data.
pub fn render_vm(
    environment: &Environment,
    runtime_type: &Expr,
    exit: &VmExit,
    width: usize,
    limits: Limits,
) -> Result<String, Error> {
    if !is_constant(runtime_type, FORMAT) {
        return Err(Error::UnexpectedType);
    }
    let contract = Contract::read(environment)?;
    let VmExit::Returned(returned) = exit else {
        return Err(Error::NonReturningExit);
    };
    Decoder::new(contract, limits)
        .decode(&returned.value)?
        .try_pretty(width, limits.rendering)
        .map_err(Error::Render)
}

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn is_constant(expr: &Expr, label: &str) -> bool {
    matches!(expr.node(), ExprNode::Const { name: actual, levels }
        if actual == &name(label) && levels.is_empty())
}

#[derive(Clone, Copy)]
enum Domain {
    Constant(&'static str),
    BehaviorDefault,
    ValidUtf8,
}

impl Domain {
    fn matches(self, expr: &Expr) -> bool {
        match self {
            Self::Constant(label) => is_constant(expr, label),
            Self::BehaviorDefault => {
                let ExprNode::App { f, a } = expr.node() else {
                    return false;
                };
                let ExprNode::App { f: head, a: type_ } = f.node() else {
                    return false;
                };
                matches!(head.node(), ExprNode::Const { name: actual, levels }
                    if actual == &name("optParam") && levels.as_slice() == [Level::one()])
                    && is_constant(type_, BEHAVIOR)
                    && is_constant(a, "Std.Format.FlattenBehavior.allOrNone")
            }
            Self::ValidUtf8 => matches!(expr.node(), ExprNode::App { f, a }
                if is_constant(f, "ByteArray.IsValidUTF8")
                    && matches!(a.node(), ExprNode::BVar { idx: 0 })),
        }
    }
}

struct CtorSpec {
    label: &'static str,
    domains: &'static [Domain],
}

const FORMAT_CTORS: [CtorSpec; 8] = [
    CtorSpec {
        label: "Std.Format.nil",
        domains: &[],
    },
    CtorSpec {
        label: "Std.Format.line",
        domains: &[],
    },
    CtorSpec {
        label: "Std.Format.align",
        domains: &[Domain::Constant("Bool")],
    },
    CtorSpec {
        label: "Std.Format.text",
        domains: &[Domain::Constant("String")],
    },
    CtorSpec {
        label: "Std.Format.nest",
        domains: &[Domain::Constant("Int"), Domain::Constant(FORMAT)],
    },
    CtorSpec {
        label: "Std.Format.append",
        domains: &[Domain::Constant(FORMAT), Domain::Constant(FORMAT)],
    },
    CtorSpec {
        label: "Std.Format.group",
        domains: &[Domain::Constant(FORMAT), Domain::BehaviorDefault],
    },
    CtorSpec {
        label: "Std.Format.tag",
        domains: &[Domain::Constant("Nat"), Domain::Constant(FORMAT)],
    },
];
const BEHAVIOR_CTORS: [CtorSpec; 2] = [
    CtorSpec {
        label: "Std.Format.FlattenBehavior.allOrNone",
        domains: &[],
    },
    CtorSpec {
        label: "Std.Format.FlattenBehavior.fill",
        domains: &[],
    },
];
const INT_CTORS: [CtorSpec; 2] = [
    CtorSpec {
        label: "Int.ofNat",
        domains: &[Domain::Constant("Nat")],
    },
    CtorSpec {
        label: "Int.negSucc",
        domains: &[Domain::Constant("Nat")],
    },
];
const BOOL_CTORS: [CtorSpec; 2] = [
    CtorSpec {
        label: "Bool.false",
        domains: &[],
    },
    CtorSpec {
        label: "Bool.true",
        domains: &[],
    },
];
const NAT_CTORS: [CtorSpec; 2] = [
    CtorSpec {
        label: "Nat.zero",
        domains: &[],
    },
    CtorSpec {
        label: "Nat.succ",
        domains: &[Domain::Constant("Nat")],
    },
];
const STRING_CTORS: [CtorSpec; 1] = [CtorSpec {
    label: "String.ofByteArray",
    domains: &[Domain::Constant("ByteArray"), Domain::ValidUtf8],
}];

/// Read source constructor indices only after validating their complete small
/// logical signatures. These indices are not upstream packed ABI constants.
fn family<const N: usize>(
    environment: &Environment,
    label: &'static str,
    recursive: bool,
    specs: &[CtorSpec; N],
) -> Result<[u8; N], Error> {
    let invalid = Error::UnsupportedContract { family: label };
    let family_name = name(label);
    let Some(ConstantInfo::Induct(induct)) = environment.find(&family_name) else {
        return Err(invalid);
    };
    if induct.base.name != family_name
        || !induct.base.level_params.is_empty()
        || !matches!(induct.base.type_.node(), ExprNode::Sort { level } if level == &Level::one())
        || induct.num_params != 0
        || induct.num_indices != 0
        || induct.num_nested != 0
        || induct.all.as_slice() != [family_name.clone()]
        || induct.ctors.len() != N
        || induct.is_rec != recursive
        || induct.is_unsafe
        || induct.is_reflexive
    {
        return Err(invalid);
    }
    let mut tags = [0; N];
    for (index, spec) in specs.iter().enumerate() {
        let ctor_name = name(spec.label);
        let Some(ConstantInfo::Ctor(ctor)) = environment.find(&ctor_name) else {
            return Err(invalid);
        };
        if induct.ctors[index] != ctor_name
            || ctor.base.name != ctor_name
            || !ctor.base.level_params.is_empty()
            || ctor.induct != family_name
            || usize::try_from(ctor.cidx).ok() != Some(index)
            || ctor.num_params != 0
            || usize::try_from(ctor.num_fields).ok() != Some(spec.domains.len())
            || ctor.is_unsafe
        {
            return Err(invalid);
        }
        let mut type_ = &ctor.base.type_;
        for domain in spec.domains {
            let ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } = type_.node()
            else {
                return Err(invalid);
            };
            if *binder_info != BinderInfo::Default || !domain.matches(binder_type) {
                return Err(invalid);
            }
            type_ = body;
        }
        if !is_constant(type_, label) {
            return Err(invalid);
        }
        tags[index] = u8::try_from(ctor.cidx).map_err(|_| invalid)?;
    }
    Ok(tags)
}

struct Contract {
    format: [u8; 8],
    behavior: [u8; 2],
    int: [u8; 2],
}

impl Contract {
    fn read(environment: &Environment) -> Result<Self, Error> {
        let format = family(environment, FORMAT, true, &FORMAT_CTORS)?;
        let behavior = family(environment, BEHAVIOR, false, &BEHAVIOR_CTORS)?;
        let int = family(environment, "Int", false, &INT_CTORS)?;
        family(environment, "Bool", false, &BOOL_CTORS)?;
        family(environment, "Nat", true, &NAT_CTORS)?;
        family(environment, "String", false, &STRING_CTORS)?;
        string_payload_sorts(environment)?;
        Ok(Self {
            format,
            behavior,
            int,
        })
    }
}

fn string_payload_sorts(environment: &Environment) -> Result<(), Error> {
    // These fields are never projected as ByteArray or proof objects. Their
    // sorts still matter: a same-name predicate returning Type would change
    // which String constructor fields the compiler erases.
    for label in ["ByteArray", "ByteArray.IsValidUTF8"] {
        let invalid = Error::UnsupportedContract { family: label };
        let Some(ConstantInfo::Induct(row)) = environment.find(&name(label)) else {
            return Err(invalid);
        };
        if row.base.name != name(label) || !row.base.level_params.is_empty() || row.is_unsafe {
            return Err(invalid);
        }
        let valid_type = if label == "ByteArray" {
            matches!(row.base.type_.node(), ExprNode::Sort { level } if level == &Level::one())
        } else {
            matches!(row.base.type_.node(), ExprNode::ForallE { binder_type, body, binder_info, .. }
                if *binder_info == BinderInfo::Default
                    && is_constant(binder_type, "ByteArray")
                    && matches!(body.node(), ExprNode::Sort { level } if level.is_zero()))
        };
        if !valid_type {
            return Err(invalid);
        }
    }
    Ok(())
}

fn invalid(expected: &'static str) -> Error {
    Error::Representation { expected }
}

fn constructor(value: &Obj, fields: usize, expected: &'static str) -> Result<u8, Error> {
    let VmValueKind::Ctor(tag) = vm_value_kind(value) else {
        return Err(invalid(expected));
    };
    if usize::from(value.header().other) != fields
        || value.byte_size() != size_of::<Header>() + fields * size_of::<usize>()
    {
        return Err(invalid(expected));
    }
    Ok(tag)
}

fn child(value: &Obj, index: usize, expected: &'static str) -> Result<Obj, Error> {
    value.try_ctor_child(index).ok_or_else(|| invalid(expected))
}

fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), Error> {
    values
        .try_reserve(1)
        .map_err(|_| Error::AllocationFailure)?;
    values.push(value);
    Ok(())
}

fn boxed(value: Format) -> Result<Box<Format>, Error> {
    Box::try_new(value).map_err(|_| Error::AllocationFailure)
}

enum Task {
    Read(Obj, usize),
    Nest(i64),
    Append,
    Group(Behavior),
}

struct Decoder {
    contract: Contract,
    limits: Limits,
    nodes: usize,
    text_bytes: usize,
}

impl Decoder {
    fn new(contract: Contract, limits: Limits) -> Self {
        Self {
            contract,
            limits,
            nodes: 0,
            text_bytes: 0,
        }
    }

    fn node(&mut self) -> Result<(), Error> {
        let observed = self.nodes.saturating_add(1);
        if observed > self.limits.max_nodes || self.nodes == usize::MAX {
            return Err(Error::Limit {
                resource: "nodes",
                limit: self.limits.max_nodes,
                observed,
            });
        }
        self.nodes = observed;
        Ok(())
    }

    fn nat(&mut self, value: &Obj) -> Result<(), Error> {
        self.node()?;
        if value.is_scalar() {
            return Ok(());
        }
        let Some((_, size, limbs)) = value.try_mpz_view() else {
            return Err(invalid("Nat"));
        };
        if size < 0 || limbs.last() == Some(&0) {
            return Err(invalid("Nat"));
        }
        Ok(())
    }

    fn int(&mut self, value: &Obj) -> Result<i64, Error> {
        self.node()?;
        let tag = constructor(value, 1, "Int")?;
        let magnitude = child(value, 0, "Int")?;
        self.nat(&magnitude)?;
        let unsigned = if magnitude.is_scalar() {
            u64::try_from(magnitude.unbox()).map_err(|_| Error::IntegerRange)?
        } else {
            match magnitude.try_mpz_view().ok_or_else(|| invalid("Nat"))?.2 {
                [] => 0,
                [limb] => *limb,
                _ => return Err(Error::IntegerRange),
            }
        };
        let signed = i64::try_from(unsigned).map_err(|_| Error::IntegerRange)?;
        if tag == self.contract.int[0] {
            Ok(signed)
        } else if tag == self.contract.int[1] {
            Ok(-signed - 1)
        } else {
            Err(invalid("Int"))
        }
    }

    fn boolean(&mut self, value: &Obj) -> Result<bool, Error> {
        self.node()?;
        if value.is_scalar() && value.unbox() <= 1 {
            Ok(value.unbox() == 1)
        } else {
            Err(invalid("Bool"))
        }
    }

    fn behavior(&mut self, value: &Obj) -> Result<Behavior, Error> {
        self.node()?;
        let tag = constructor(value, 0, BEHAVIOR)?;
        if tag == self.contract.behavior[0] {
            Ok(Behavior::AllOrNone)
        } else if tag == self.contract.behavior[1] {
            Ok(Behavior::Fill)
        } else {
            Err(invalid(BEHAVIOR))
        }
    }

    fn text(&mut self, value: &Obj) -> Result<String, Error> {
        self.node()?;
        // The borrowed safe membrane view performs no allocation. Check the
        // aggregate byte budget before either a UTF-8 scan or a text copy.
        let Some((size, _, length, bytes)) = value.try_borrow_string_view() else {
            return Err(invalid("String"));
        };
        let content = bytes.get(..size - 1).ok_or_else(|| invalid("String"))?;
        let observed = self.text_bytes.saturating_add(content.len());
        if observed > self.limits.max_text_bytes
            || self.text_bytes.checked_add(content.len()).is_none()
        {
            return Err(Error::Limit {
                resource: "text bytes",
                limit: self.limits.max_text_bytes,
                observed,
            });
        }
        let text = std::str::from_utf8(content).map_err(|_| invalid("String"))?;
        if text.chars().count() != length {
            return Err(invalid("String"));
        }
        let mut owned = String::new();
        owned
            .try_reserve_exact(text.len())
            .map_err(|_| Error::AllocationFailure)?;
        owned.push_str(text);
        self.text_bytes = observed;
        Ok(owned)
    }

    fn decode(mut self, root: &Obj) -> Result<Format, Error> {
        let mut tasks = Vec::new();
        let mut values = Vec::new();
        push(&mut tasks, Task::Read(root.clone_ref(), 0))?;
        while let Some(task) = tasks.pop() {
            match task {
                Task::Read(value, depth) => {
                    self.node()?;
                    let depth_limit = self.limits.max_depth.min(MAX_DEPTH);
                    if depth > depth_limit {
                        return Err(Error::Limit {
                            resource: "depth",
                            limit: depth_limit,
                            observed: depth,
                        });
                    }
                    let VmValueKind::Ctor(tag) = vm_value_kind(&value) else {
                        return Err(invalid(FORMAT));
                    };
                    let Some(index) = self
                        .contract
                        .format
                        .iter()
                        .position(|candidate| *candidate == tag)
                    else {
                        return Err(invalid(FORMAT));
                    };
                    constructor(&value, FORMAT_CTORS[index].domains.len(), FORMAT)?;
                    match index {
                        0 => push(&mut values, Format::Nil)?,
                        1 => push(&mut values, Format::Line)?,
                        2 => {
                            let force = self.boolean(&child(&value, 0, FORMAT)?)?;
                            push(&mut values, Format::Align(force))?;
                        }
                        3 => {
                            let text = self.text(&child(&value, 0, FORMAT)?)?;
                            push(&mut values, Format::Text(text))?;
                        }
                        4 => {
                            let indent = self.int(&child(&value, 0, FORMAT)?)?;
                            push(&mut tasks, Task::Nest(indent))?;
                            push(&mut tasks, Task::Read(child(&value, 1, FORMAT)?, depth + 1))?;
                        }
                        5 => {
                            push(&mut tasks, Task::Append)?;
                            push(&mut tasks, Task::Read(child(&value, 1, FORMAT)?, depth + 1))?;
                            push(&mut tasks, Task::Read(child(&value, 0, FORMAT)?, depth + 1))?;
                        }
                        6 => {
                            let behavior = self.behavior(&child(&value, 1, FORMAT)?)?;
                            push(&mut tasks, Task::Group(behavior))?;
                            push(&mut tasks, Task::Read(child(&value, 0, FORMAT)?, depth + 1))?;
                        }
                        7 => {
                            self.nat(&child(&value, 0, FORMAT)?)?;
                            push(&mut tasks, Task::Read(child(&value, 1, FORMAT)?, depth + 1))?;
                        }
                        _ => return Err(invalid(FORMAT)),
                    }
                }
                Task::Nest(indent) => {
                    let inner = values.pop().ok_or_else(|| invalid(FORMAT))?;
                    push(&mut values, Format::Nest(indent, boxed(inner)?))?;
                }
                Task::Append => {
                    let right = values.pop().ok_or_else(|| invalid(FORMAT))?;
                    let left = values.pop().ok_or_else(|| invalid(FORMAT))?;
                    push(&mut values, Format::Append(boxed(left)?, boxed(right)?))?;
                }
                Task::Group(behavior) => {
                    let inner = values.pop().ok_or_else(|| invalid(FORMAT))?;
                    push(&mut values, Format::Group(boxed(inner)?, behavior))?;
                }
            }
        }
        if values.len() != 1 {
            return Err(invalid(FORMAT));
        }
        values.pop().ok_or_else(|| invalid(FORMAT))
    }
}

#[cfg(test)]
mod tests;
