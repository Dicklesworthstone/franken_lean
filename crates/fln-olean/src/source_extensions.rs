//! Data-only decoding of pinned class, instance, default-instance, simp, export-alias
//! and protected-declaration journals.
//!
//! Field offsets and enum tags are extracted from the Reference declarations.
//! This grants no proof authority: declarations must pass the ordinary council
//! before a source consumer activates their metadata. Scoped instances remain
//! explicitly scoped. Other extension schemas are not interpreted here.
use crate::region::OpaqueExtensionBlock;
use crate::source_extension_format as format;
use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::name::Name;
use fln_rt::convert::{Conversion, ConvertError};
use fln_rt::native_heap::NativeHeap;
use fln_rt::obj::Obj;
use fln_rt::region::{RegionFault, audit, materialize};
use std::collections::BTreeSet;

pub use format::{
    ALIAS_EXTENSION, CLASS_EXTENSION, DEFAULT_EXTENSION, INSTANCE_EXTENSION, PROTECTED_EXTENSION,
    REDUCIBILITY_EXTENSION, SIMP_EXTENSION,
};
mod simp;
pub use simp::{SimpEntry, SimpKind, SimpTheorem};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassEntry {
    pub name: Name,
    pub out_params: Vec<u32>,
    pub out_level_params: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceEntry {
    pub declaration: Name,
    pub value: Expr,
    pub priority: u32,
    /// Absolute positions in the declaration telescope, not just instance binders.
    pub synth_order: Vec<u32>,
    /// `Some` is inactive until that namespace is explicitly activated.
    pub scope: Option<Name>,
    /// The pin's discrimination-tree path for the instance's type, computed when
    /// the instance was registered (`mkInstanceKey`, vendored
    /// `src/Lean/Meta/Instances.lean`) and stored with it. The pin never stores
    /// an empty path. FrankenLean's own artifacts may, and an empty path leaves
    /// the instance out of the index, so it is never filtered.
    pub keys: Vec<InstanceKey>,
}

/// One edge of a pin `DiscrTree` path (`DiscrTree.Key`, vendored
/// `src/Lean/Meta/DiscrTree/Types.lean`), in constructor order. Arities and
/// projection indices are the pin's `Nat`s, bounded here to `u32`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceKey {
    Star,
    Other,
    Lit(Literal),
    /// The free variable's `FVarId`, whose only field is this `Name`.
    FVar(Name, u32),
    Const(Name, u32),
    Arrow,
    /// Structure name, field index, argument count.
    Proj(Name, u32, u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefaultEntry {
    pub class: Name,
    pub declaration: Name,
    pub priority: u32,
}

/// An `export` alias: `alias` names `declaration`. The pin's `export A (x)` in
/// namespace `B` records `B.x ~> A.x` as `addAlias env a e`, the pair `(a, e)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AliasEntry {
    pub alias: Name,
    pub declaration: Name,
}

/// The pin's `ReducibilityStatus` (vendored `src/Lean/ReducibilityAttrs.lean`):
/// which transparency modes may unfold a definition. `ImplicitReducible`
/// unfolds at `instances` transparency and above; instances carry it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReducibilityStatus {
    Reducible,
    Semireducible,
    Irreducible,
    ImplicitReducible,
}

/// One `reducibilityCore` entry: a module's own declaration and its status.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReducibilityEntry {
    pub declaration: Name,
    pub status: ReducibilityStatus,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceExtensions {
    pub classes: Vec<ClassEntry>,
    pub instances: Vec<InstanceEntry>,
    pub defaults: Vec<DefaultEntry>,
    pub simps: Vec<SimpEntry>,
    pub aliases: Vec<AliasEntry>,
    /// `protected` declarations (the pin's `protectedExt`): each entry names one
    /// declaration its own module tagged. A name tagged twice is refused.
    pub protected: Vec<Name>,
    /// Reducibility statuses (the pin's `reducibilityCore`), in journal order.
    pub reducibility: Vec<ReducibilityEntry>,
    /// Nonempty foreign extensions whose semantics this decoder does not serve.
    pub uninterpreted: Vec<Name>,
}

#[derive(Debug, Clone, Copy)]
pub struct DecodeLimits {
    pub max_bytes: usize,
    pub max_objects: u64,
    pub max_entries: usize,
    pub max_indices: usize,
    /// Cumulative instance `DiscrTree` keys across the batch.
    pub max_keys: usize,
}
impl Default for DecodeLimits {
    fn default() -> Self {
        Self {
            max_bytes: 64 * 1024 * 1024,
            max_objects: 1_000_000,
            max_entries: 65_536,
            max_indices: 65_536,
            max_keys: 1 << 20,
        }
    }
}

#[derive(Debug)]
pub enum DecodeError {
    Limit { resource: &'static str },
    Shape { detail: &'static str },
    Region(RegionFault),
    Conversion(ConvertError),
}
impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "source extension decode: {self:?}")
    }
}
impl std::error::Error for DecodeError {}
impl DecodeError {
    pub fn is_resource(&self) -> bool {
        matches!(
            self,
            Self::Limit { .. }
                | Self::Conversion(ConvertError::NodeBudgetExhausted { .. })
                | Self::Conversion(ConvertError::NativeOverflow { .. })
        )
    }
}
fn shape(detail: &'static str) -> DecodeError {
    DecodeError::Shape { detail }
}
fn limit(resource: &'static str) -> DecodeError {
    DecodeError::Limit { resource }
}
fn constructor(obj: &Obj, tag: u8, pointers: usize) -> Result<(), DecodeError> {
    if obj.is_scalar()
        || obj.obj_tag() != usize::from(tag)
        || usize::from(obj.header().other) != pointers
    {
        return Err(shape("unexpected constructor or object-field count"));
    }
    Ok(())
}
fn field(obj: &Obj, index: usize) -> Result<Obj, DecodeError> {
    obj.try_ctor_child(index)
        .ok_or_else(|| shape("missing constructor field"))
}
fn natural(obj: &Obj) -> Result<u32, DecodeError> {
    if obj.is_scalar() {
        return u32::try_from(obj.unbox()).map_err(|_| limit("natural number exceeds u32"));
    }
    let Some((_, sign, limbs)) = obj.try_mpz_view() else {
        return Err(shape("expected a Nat payload"));
    };
    if sign < 0 {
        return Err(shape("negative Nat payload"));
    }
    match limbs {
        [] => Ok(0),
        [value] => u32::try_from(*value).map_err(|_| limit("natural number exceeds u32")),
        _ => Err(limit("natural number exceeds u32")),
    }
}
fn array_length(obj: &Obj) -> Result<usize, DecodeError> {
    obj.try_array_view()
        .map(|(size, _)| size)
        .ok_or_else(|| shape("expected an Array"))
}

struct Reader {
    conversion: Conversion,
    indices_left: usize,
    keys_left: usize,
}
impl Reader {
    fn name(&mut self, obj: &Obj) -> Result<Name, DecodeError> {
        let name = self
            .conversion
            .project_name(obj)
            .map_err(DecodeError::Conversion)?;
        if name.is_anonymous() {
            return Err(shape("anonymous class, instance or scope name"));
        }
        Ok(name)
    }
    fn indices(&mut self, obj: &Obj) -> Result<Vec<u32>, DecodeError> {
        let size = array_length(obj)?;
        self.indices_left = self
            .indices_left
            .checked_sub(size)
            .ok_or_else(|| limit("index cells"))?;
        let mut seen = BTreeSet::new();
        let mut out = Vec::with_capacity(size);
        for index in 0..size {
            let value = natural(&obj.array_child(index))?;
            if !seen.insert(value) {
                return Err(shape("duplicate parameter or synthesis-order index"));
            }
            out.push(value);
        }
        Ok(out)
    }
    /// `InstanceEntry.keys`. A field-less key is a boxed scalar carrying its
    /// constructor index; every other key is a constructor object with that tag.
    fn keys(&mut self, obj: &Obj) -> Result<Vec<InstanceKey>, DecodeError> {
        let size = array_length(obj)?;
        self.keys_left = self
            .keys_left
            .checked_sub(size)
            .ok_or_else(|| limit("instance keys"))?;
        let mut out = Vec::with_capacity(size);
        for index in 0..size {
            out.push(self.key(&obj.array_child(index))?);
        }
        Ok(out)
    }
    fn key(&mut self, obj: &Obj) -> Result<InstanceKey, DecodeError> {
        if obj.is_scalar() {
            return match u8::try_from(obj.unbox()) {
                Ok(format::KEY_STAR) => Ok(InstanceKey::Star),
                Ok(format::KEY_OTHER) => Ok(InstanceKey::Other),
                Ok(format::KEY_ARROW) => Ok(InstanceKey::Arrow),
                _ => Err(shape("unknown field-less DiscrTree key")),
            };
        }
        let tag = u8::try_from(obj.obj_tag()).map_err(|_| shape("unknown DiscrTree key"))?;
        match tag {
            format::KEY_LIT => {
                constructor(obj, tag, format::KEY_LIT_POINTERS)?;
                let literal = self
                    .conversion
                    .project_literal(&field(obj, 0)?)
                    .map_err(DecodeError::Conversion)?;
                Ok(InstanceKey::Lit(literal))
            }
            format::KEY_FVAR => {
                constructor(obj, tag, format::KEY_FVAR_POINTERS)?;
                Ok(InstanceKey::FVar(
                    self.name(&field(obj, 0)?)?,
                    natural(&field(obj, 1)?)?,
                ))
            }
            format::KEY_CONST => {
                constructor(obj, tag, format::KEY_CONST_POINTERS)?;
                Ok(InstanceKey::Const(
                    self.name(&field(obj, 0)?)?,
                    natural(&field(obj, 1)?)?,
                ))
            }
            format::KEY_PROJ => {
                constructor(obj, tag, format::KEY_PROJ_POINTERS)?;
                Ok(InstanceKey::Proj(
                    self.name(&field(obj, 0)?)?,
                    natural(&field(obj, 1)?)?,
                    natural(&field(obj, 2)?)?,
                ))
            }
            _ => Err(shape("unknown DiscrTree key")),
        }
    }
    fn class(&mut self, obj: &Obj) -> Result<ClassEntry, DecodeError> {
        constructor(obj, 0, format::CLASS_POINTERS)?;
        Ok(ClassEntry {
            name: self.name(&field(obj, format::CLASS_NAME)?)?,
            out_params: self.indices(&field(obj, format::CLASS_OUT_PARAMS)?)?,
            out_level_params: self.indices(&field(obj, format::CLASS_OUT_LEVEL_PARAMS)?)?,
        })
    }
    fn instance(&mut self, obj: &Obj) -> Result<InstanceEntry, DecodeError> {
        if obj.is_scalar() {
            return Err(shape("instance entry lacks its scope wrapper"));
        }
        let (scope, entry) = match obj.obj_tag() as u8 {
            format::SCOPE_GLOBAL => {
                constructor(obj, format::SCOPE_GLOBAL, 1)?;
                (None, field(obj, 0)?)
            }
            format::SCOPE_SCOPED => {
                constructor(obj, format::SCOPE_SCOPED, 2)?;
                (Some(self.name(&field(obj, 0)?)?), field(obj, 1)?)
            }
            _ => return Err(shape("unknown instance scope tag")),
        };
        constructor(&entry, 0, format::INSTANCE_POINTERS)?;
        let attribute = entry
            .try_ctor_scalar_u64(format::INSTANCE_POINTERS * 8 + format::INSTANCE_ATTR_KIND_SCALAR)
            .ok_or_else(|| shape("missing instance attribute kind"))? as u8;
        let expected = if scope.is_some() {
            format::ATTRIBUTE_SCOPED
        } else {
            format::ATTRIBUTE_GLOBAL
        };
        if attribute != expected {
            return Err(shape(
                "persistent instance scope and attribute kind disagree",
            ));
        }
        let global = field(&entry, format::INSTANCE_GLOBAL_NAME_OPTION)?;
        constructor(&global, 1, 1)?;
        let declaration = self.name(&field(&global, 0)?)?;
        let mut heap = NativeHeap::new();
        let value = self
            .conversion
            .project_expr(&mut heap, &field(&entry, format::INSTANCE_VAL)?)
            .map_err(DecodeError::Conversion)?;
        let value = heap
            .get(value)
            .map_err(|_| shape("projected instance expression is missing"))?
            .clone();
        if !matches!(value.node(), ExprNode::Const { name, .. } if name == &declaration)
            || value.has_level_mvar()
        {
            return Err(shape("global instance value does not name its declaration"));
        }
        Ok(InstanceEntry {
            declaration,
            value,
            priority: natural(&field(&entry, format::INSTANCE_PRIORITY)?)?,
            synth_order: self.indices(&field(&entry, format::INSTANCE_SYNTH_ORDER)?)?,
            scope,
            keys: self.keys(&field(&entry, format::INSTANCE_KEYS)?)?,
        })
    }
    fn reducibility(&mut self, obj: &Obj) -> Result<ReducibilityEntry, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        let status = field(obj, format::PROD_SND)?;
        if !status.is_scalar() {
            return Err(shape("reducibility status is not an enumeration value"));
        }
        let status = match status.unbox() {
            format::REDUCIBILITY_REDUCIBLE => ReducibilityStatus::Reducible,
            format::REDUCIBILITY_SEMIREDUCIBLE => ReducibilityStatus::Semireducible,
            format::REDUCIBILITY_IRREDUCIBLE => ReducibilityStatus::Irreducible,
            format::REDUCIBILITY_IMPLICIT_REDUCIBLE => ReducibilityStatus::ImplicitReducible,
            _ => return Err(shape("unknown reducibility status")),
        };
        Ok(ReducibilityEntry {
            declaration: self.name(&field(obj, format::PROD_FST)?)?,
            status,
        })
    }
    fn alias(&mut self, obj: &Obj) -> Result<AliasEntry, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        Ok(AliasEntry {
            alias: self.name(&field(obj, format::PROD_FST)?)?,
            declaration: self.name(&field(obj, format::PROD_SND)?)?,
        })
    }
    fn default_instance(&mut self, obj: &Obj) -> Result<DefaultEntry, DecodeError> {
        constructor(obj, 0, format::DEFAULT_POINTERS)?;
        Ok(DefaultEntry {
            class: self.name(&field(obj, format::DEFAULT_CLASS_NAME)?)?,
            declaration: self.name(&field(obj, format::DEFAULT_INSTANCE_NAME)?)?,
            priority: natural(&field(obj, format::DEFAULT_PRIORITY)?)?,
        })
    }
}

/// Decode a complete batch, keeping journal order. Cumulative bounds are
/// checked before materialization; a malformed selected entry exposes no prefix.
/// Unknown nonempty extension names are reported, never guessed to be understood.
pub fn decode(
    blocks: &[OpaqueExtensionBlock],
    limits: DecodeLimits,
) -> Result<SourceExtensions, DecodeError> {
    let name = |s: &str| Name::from_components(s.split('.'));
    let selected = [
        name(format::CLASS_EXTENSION),
        name(format::INSTANCE_EXTENSION),
        name(format::DEFAULT_EXTENSION),
        name(format::SIMP_EXTENSION),
        name(format::ALIAS_EXTENSION),
        name(format::PROTECTED_EXTENSION),
        name(format::REDUCIBILITY_EXTENSION),
    ];
    let mut seen = BTreeSet::new();
    let mut bytes_left = limits.max_bytes;
    let mut entries_left = limits.max_entries;
    let mut objects_left = limits.max_objects;
    let mut reader = Reader {
        conversion: Conversion::new(),
        indices_left: limits.max_indices,
        keys_left: limits.max_keys,
    };
    let mut out = SourceExtensions::default();
    let mut protected = BTreeSet::new();
    for block in blocks {
        if !seen.insert(block.name.clone()) {
            return Err(shape("duplicate extension block"));
        }
        let Some(kind) = selected.iter().position(|name| name == &block.name) else {
            if !block.entries.is_empty() {
                out.uninterpreted.push(block.name.clone());
            }
            continue;
        };
        entries_left = entries_left
            .checked_sub(block.entries.len())
            .ok_or_else(|| limit("entries"))?;
        for payload in &block.entries {
            bytes_left = bytes_left
                .checked_sub(payload.len())
                .ok_or_else(|| limit("payload bytes"))?;
            let report = audit(payload, 0).map_err(DecodeError::Region)?;
            objects_left = objects_left
                .checked_sub(report.objects)
                .ok_or_else(|| limit("objects"))?;
            let obj = materialize(payload, 0).map_err(DecodeError::Region)?;
            match kind {
                0 => out.classes.push(reader.class(&obj)?),
                1 => out.instances.push(reader.instance(&obj)?),
                2 => out.defaults.push(reader.default_instance(&obj)?),
                3 => out.simps.push(reader.simp(&obj)?),
                4 => out.aliases.push(reader.alias(&obj)?),
                5 => {
                    // The pin tags a declaration only in the module that declares
                    // it (`TagDeclarationExtension.tag`), so a repeat is malformed.
                    let declaration = reader.name(&obj)?;
                    if !protected.insert(declaration.clone()) {
                        return Err(shape("protected declaration tagged twice"));
                    }
                    out.protected.push(declaration);
                }
                6 => out.reducibility.push(reader.reducibility(&obj)?),
                _ => unreachable!("seven selected extension families"),
            }
        }
    }
    Ok(out)
}
