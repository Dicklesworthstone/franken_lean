//! Data-only decoding of pinned class, instance, default-instance, simp, export-alias
//! protected-declaration, auxiliary-recursor, structure, extern, implemented_by, inlining
//! and initialization journals.
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
    ALIAS_EXTENSION, APP_UNEXPANDER_EXTENSION, AUX_RECURSOR_EXTENSION, BACKWARD_DEFEQ_EXTENSION,
    CLASS_EXTENSION, DEFAULT_EXTENSION, DEFEQ_EXTENSION, EXTERN_EXTENSION,
    IMPLEMENTED_BY_EXTENSION, INLINE_EXTENSION, INSTANCE_EXTENSION, NONCOMPUTABLE_EXTENSION,
    PP_ANONYMOUS_CONSTRUCTOR_EXTENSION, PP_NODOT_EXTENSION, PROTECTED_EXTENSION,
    REDUCIBILITY_EXTENSION, SIMP_EXTENSION, STRUCTURE_EXTENSION,
};
mod externs;
pub use externs::{ExternAttribute, ExternEntry};
mod simp;
pub use simp::{SimpEntry, SimpKind, SimpTheorem};
mod structures;
pub use structures::{StructureEntry, StructureField, StructureParent};

/// The private extension name contains a numeric component. Parsing its display
/// spelling as a dot-separated string would produce a different Lean Name.
pub fn structure_extension_name() -> Name {
    let module = Name::from_components(format::STRUCTURE_EXTENSION_MODULE.split('.'));
    let prefix = Name::from_components([format::STRUCTURE_PRIVATE_HEADER]).append_core(&module);
    Name::num(prefix, format::STRUCTURE_EXTENSION_PRIVATE_INDEX).append_core(
        &Name::from_components(format::STRUCTURE_EXTENSION_DECLARATION.split('.')),
    )
}

/// Pin-extracted private identity; the numeric component is a Lean `Name.num`.
pub fn namespace_extension_name() -> Name {
    let module = Name::from_components(format::NAMESPACE_EXTENSION_MODULE.split('.'));
    let prefix = Name::from_components([format::STRUCTURE_PRIVATE_HEADER]).append_core(&module);
    Name::num(prefix, format::NAMESPACE_EXTENSION_PRIVATE_INDEX).append_core(
        &Name::from_components(format::NAMESPACE_EXTENSION_DECLARATION.split('.')),
    )
}

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

/// An `@[app_unexpander key] declaration` registration (the pin's
/// `appUnexpanderAttribute`): applications of `key` print through `declaration`, compiled
/// code this door does not run. `scope` names the namespace of a `scoped` registration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppUnexpanderEntry {
    pub key: Name,
    pub declaration: Name,
    pub scope: Option<Name>,
}

/// The pin's `implementedByAttr`: an explicit executable replacement. Both
/// names still need checked ownership/type validation before source activation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplementedByEntry {
    pub declaration: Name,
    pub implementation: Name,
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

/// The pin's `InlineAttributeKind` (vendored `src/Lean/Compiler/InlineAttrs.lean`), in
/// constructor order. Only `MacroInline` changes what a program computes: the pin's compiler
/// inlines such a definition before any argument is evaluated (`macroInline`, vendored
/// `src/Lean/Compiler/LCNF/ToDecl.lean`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InlineKind {
    Inline,
    NoInline,
    MacroInline,
    InlineIfReduce,
    AlwaysInline,
}

/// One `Lean.Compiler.inlineAttrs` entry: a module's own declaration and its kind. The pin's
/// enumeration attribute keeps one kind per declaration and exports it once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlineEntry {
    pub declaration: Name,
    pub kind: InlineKind,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SourceExtensions {
    /// Actual namespace registrations, including empty and re-export-only ones.
    /// These are independent of alias names and grant no declaration authority.
    pub namespaces: Vec<Name>,
    pub classes: Vec<ClassEntry>,
    pub instances: Vec<InstanceEntry>,
    pub defaults: Vec<DefaultEntry>,
    pub simps: Vec<SimpEntry>,
    pub aliases: Vec<AliasEntry>,
    /// `protected` declarations (the pin's `protectedExt`): each entry names one
    /// declaration its own module tagged. A name tagged twice is refused.
    pub protected: Vec<Name>,
    /// Generated auxiliary recursors (the pin's `auxRecExt`), recorded only by
    /// their owning module. A suffix alone never supplies this metadata.
    pub aux_recursors: Vec<Name>,
    /// Noncomputable tags, interpreted only after checking their owning module.
    pub noncomputable: Vec<Name>,
    /// The pin's defeq attribute tags, not evidence that an equation is true.
    /// Source activation must bind names to their checked owning module; each
    /// use still requires conversion and ordinary proof checking.
    pub defeq: Vec<Name>,
    /// Legacy-only tags remain distinct: default dsimp must not activate them.
    pub backward_defeq: Vec<Name>,
    /// Structure fields and extends-clause metadata, still awaiting checked
    /// constructor/projection validation by the source importer.
    pub structures: Vec<StructureEntry>,
    /// Reducibility statuses (the pin's `reducibilityCore`), in journal order.
    pub reducibility: Vec<ReducibilityEntry>,
    /// Explicit extern bindings. Consumers must validate their declarations and
    /// selected backend/symbol before granting executable authority.
    pub externs: Vec<ExternAttribute>,
    /// Executable replacements, separate from the declarations' logical bodies.
    pub implemented_by: Vec<ImplementedByEntry>,
    /// Inlining attributes (the pin's `inlineAttrs`), in journal order. A name appears once.
    pub inline: Vec<InlineEntry>,
    /// Ordered initialization journals. A named initializer replaces a stored
    /// body at runtime; an anonymous parameter denotes a standalone IO action.
    pub initializers: crate::initializers::InitJournals,
    /// Structures tagged `@[pp_using_anonymous_constructor]`, which print as `⟨…⟩`.
    pub pp_anonymous_constructor: Vec<Name>,
    /// Functions tagged `@[pp_nodot]`, never printed with field notation.
    pub pp_nodot: Vec<Name>,
    /// `@[app_unexpander]` registrations, in journal order.
    pub app_unexpanders: Vec<AppUnexpanderEntry>,
    /// Nonempty foreign extensions whose semantics this decoder does not serve.
    pub uninterpreted: Vec<Name>,
}

#[derive(Debug, Clone, Copy)]
pub struct DecodeLimits {
    pub max_bytes: usize,
    pub max_objects: u64,
    /// Cumulative journal rows, extern list cells, and structure array cells.
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
    /// `Name × InlineAttributeKind`, the same Prod as a reducibility entry.
    fn inline(&mut self, obj: &Obj) -> Result<InlineEntry, DecodeError> {
        constructor(obj, 0, format::PROD_POINTERS)?;
        let kind = field(obj, format::PROD_SND)?;
        if !kind.is_scalar() {
            return Err(shape("inline attribute kind is not an enumeration value"));
        }
        let kind = match kind.unbox() {
            format::INLINE_INLINE => InlineKind::Inline,
            format::INLINE_NOINLINE => InlineKind::NoInline,
            format::INLINE_MACRO_INLINE => InlineKind::MacroInline,
            format::INLINE_INLINE_IF_REDUCE => InlineKind::InlineIfReduce,
            format::INLINE_ALWAYS_INLINE => InlineKind::AlwaysInline,
            _ => return Err(shape("unknown inline attribute kind")),
        };
        Ok(InlineEntry {
            declaration: self.name(&field(obj, format::PROD_FST)?)?,
            kind,
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
    /// A scope-wrapped `KeyedDeclsAttribute.OLeanEntry` (the same `ScopedEnvExtension.Entry`
    /// wrapper as an instance's).
    fn app_unexpander(&mut self, obj: &Obj) -> Result<AppUnexpanderEntry, DecodeError> {
        if obj.is_scalar() {
            return Err(shape("unexpander entry lacks its scope wrapper"));
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
            _ => return Err(shape("unknown unexpander scope tag")),
        };
        constructor(&entry, 0, format::KEYED_ENTRY_POINTERS)?;
        let key = self.name(&field(&entry, format::KEYED_ENTRY_KEY)?)?;
        let declaration = self.name(&field(&entry, format::KEYED_ENTRY_DECL_NAME)?)?;
        if key.is_anonymous() || declaration.is_anonymous() {
            return Err(shape("anonymous unexpander key or declaration"));
        }
        Ok(AppUnexpanderEntry {
            key,
            declaration,
            scope,
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
        name(format::EXTERN_EXTENSION),
        name(format::IMPLEMENTED_BY_EXTENSION),
        name(format::AUX_RECURSOR_EXTENSION),
        name(crate::initializers::REGULAR_INIT_EXTENSION),
        name(crate::initializers::BUILTIN_INIT_EXTENSION),
        structure_extension_name(),
        name(format::NONCOMPUTABLE_EXTENSION),
        name(format::DEFEQ_EXTENSION),
        name(format::BACKWARD_DEFEQ_EXTENSION),
        name(format::PP_ANONYMOUS_CONSTRUCTOR_EXTENSION),
        name(format::PP_NODOT_EXTENSION),
        name(format::APP_UNEXPANDER_EXTENSION),
        name(format::INLINE_EXTENSION),
        namespace_extension_name(),
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
    let mut aux_recursors = BTreeSet::new();
    let mut noncomputable = BTreeSet::new();
    let mut defeq = BTreeSet::new();
    let mut backward_defeq = BTreeSet::new();
    let mut pp_anonymous_constructor = BTreeSet::new();
    let mut pp_nodot = BTreeSet::new();
    let mut structures = BTreeSet::new();
    let mut inline = BTreeSet::new();
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
                7 => out
                    .externs
                    .push(reader.extern_attribute(&obj, &mut entries_left)?),
                8 => {
                    // ParametricAttribute Name exports Name × Name, the same
                    // extracted Prod shape as aliases, in declaration/target order.
                    let pair = reader.alias(&obj)?;
                    out.implemented_by.push(ImplementedByEntry {
                        declaration: pair.alias,
                        implementation: pair.declaration,
                    });
                }
                9 => {
                    let declaration = reader.name(&obj)?;
                    if !aux_recursors.insert(declaration.clone()) {
                        return Err(shape("auxiliary recursor tagged twice"));
                    }
                    out.aux_recursors.push(declaration);
                }
                10 => out
                    .initializers
                    .regular
                    .push(crate::initializers::project_entry(
                        &mut reader.conversion,
                        &obj,
                    )?),
                11 => out
                    .initializers
                    .builtin
                    .push(crate::initializers::project_entry(
                        &mut reader.conversion,
                        &obj,
                    )?),
                12 => {
                    let row = reader.structure(&obj, &mut entries_left)?;
                    if !structures.insert(row.name.clone()) {
                        return Err(shape("structure metadata registered twice"));
                    }
                    out.structures.push(row);
                }
                13 => {
                    let declaration = reader.name(&obj)?;
                    if declaration.is_anonymous() || !noncomputable.insert(declaration.clone()) {
                        return Err(shape("anonymous or repeated noncomputable declaration"));
                    }
                    out.noncomputable.push(declaration);
                }
                14 | 15 => {
                    let declaration = reader.name(&obj)?;
                    let (seen, names) = if kind == 14 {
                        (&mut defeq, &mut out.defeq)
                    } else {
                        (&mut backward_defeq, &mut out.backward_defeq)
                    };
                    if declaration.is_anonymous() || !seen.insert(declaration.clone()) {
                        return Err(shape("anonymous or repeated definitional-equality tag"));
                    }
                    names.push(declaration);
                }
                16 | 17 => {
                    let declaration = reader.name(&obj)?;
                    let (seen, names) = if kind == 16 {
                        (
                            &mut pp_anonymous_constructor,
                            &mut out.pp_anonymous_constructor,
                        )
                    } else {
                        (&mut pp_nodot, &mut out.pp_nodot)
                    };
                    if declaration.is_anonymous() || !seen.insert(declaration.clone()) {
                        return Err(shape("anonymous or repeated delaborator tag"));
                    }
                    names.push(declaration);
                }
                18 => out.app_unexpanders.push(reader.app_unexpander(&obj)?),
                19 => {
                    // An enumeration attribute's NameMap exports each declaration once.
                    let row = reader.inline(&obj)?;
                    if !inline.insert(row.declaration.clone()) {
                        return Err(shape("inline attribute recorded twice"));
                    }
                    out.inline.push(row);
                }
                20 => {
                    // Unlike declaration names, Name.anonymous is a valid
                    // namespace: the pin registers the root namespace too.
                    let namespace = reader
                        .conversion
                        .project_name(&obj)
                        .map_err(DecodeError::Conversion)?;
                    // Several modules may register the same namespace. Keep
                    // module windows intact; activation performs set lookup.
                    out.namespaces.push(namespace);
                }
                _ => unreachable!("twenty-one selected extension families"),
            }
        }
    }
    Ok(out)
}
