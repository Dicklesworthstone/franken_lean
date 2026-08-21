//! Fresh expression-region construction for the faithful `.olean` writer
//! (bead `franken_lean-0nz`, plan §7.3).
//!
//! This is the first write-side semantic path: a FrankenLean [`Expr`] DAG is
//! converted to the pinned Lean runtime object inventory, then serialized by
//! [`fln_rt::region::compact`], the same compactor used by the runtime region
//! engine. Expression allocation identity is retained exactly: shared input
//! nodes become one wire object, while independently allocated equal nodes
//! remain distinct. Traversal is iterative and all heap-object and output-byte
//! costs are charged before construction.
//!
//! The same substrate also constructs complete basic `ModuleData` images for
//! imports and every `ConstantInfo` variant. Serialized environment-extension
//! payloads, closure-bearing v3 regions, `.ilean`, and transactional artifact
//! publication remain later slices of the same bead.

use std::collections::HashMap;

use fln_core::expr::{Expr, ExprNode, Literal, NatLit};
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, QuotKind, RecursorRule, ReducibilityHints,
};
use fln_rt::obj::Obj;

use crate::format;
use crate::region::ModuleImport;

type WResult<T> = Result<T, WriteError>;

/// Fresh writer formats implemented by this module.
///
/// The safe object graph emitted here cannot contain closures, so v3 writes a
/// real length-prefixed data section followed by empty closure and library
/// relocation tables. Closure-bearing v3 regions remain typed-unsupported in
/// the shared compactor.
const OLEAN_WRITER_VERSIONS: &[u8] = &[2, 3];

/// The resource whose writer limit was reached.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteResource {
    Objects,
    Bytes,
}

/// A bounded, typed refusal from fresh region construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WriteError {
    Budget {
        resource: WriteResource,
        limit: u64,
        attempted: u64,
    },
    Unsupported {
        what: &'static str,
    },
    Contract {
        what: &'static str,
    },
    Region(fln_rt::region::RegionFault),
}

impl From<fln_rt::region::RegionFault> for WriteError {
    fn from(value: fln_rt::region::RegionFault) -> Self {
        Self::Region(value)
    }
}

impl std::fmt::Display for WriteError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Budget {
                resource,
                limit,
                attempted,
            } => write!(
                formatter,
                "expression-region {resource:?} budget {limit} exceeded by attempt {attempted}"
            ),
            Self::Unsupported { what } => write!(formatter, "unsupported writer value: {what}"),
            Self::Contract { what } => write!(formatter, "writer contract: {what}"),
            Self::Region(error) => write!(formatter, "region compactor: {error}"),
        }
    }
}

impl std::error::Error for WriteError {}

/// Limits for one expression-rooted artifact. Both include supporting
/// Name/Level/list/literal/metadata objects, not only Expr constructors.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WriteBudget {
    pub max_objects: u64,
    /// Complete file bytes, including the generated-contract header and root
    /// slot.
    pub max_bytes: u64,
}

impl Default for WriteBudget {
    fn default() -> Self {
        Self {
            max_objects: 20_000_000,
            max_bytes: 4 * 1024 * 1024 * 1024,
        }
    }
}

/// Caller-supplied epoch/header identity.
///
/// `base_addr` is explicit because fresh faithful emission has not yet
/// ratified a universal base-address choice. It must obey the generated
/// alignment contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OleanWriteHeader<'a> {
    pub version: u8,
    pub flags: u8,
    pub lean_version: &'a str,
    pub githash: &'a str,
    pub base_addr: u64,
}

/// Exact accounting for one successful expression-region write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprWriteReport {
    /// Distinct input Expr allocation identities.
    pub expr_nodes: u64,
    /// Expr presentations, including repeated references to a shared node.
    pub expr_presentations: u64,
    pub shared_expr_presentations: u64,
    /// All emitted heap objects, including supporting runtime objects.
    pub runtime_objects: u64,
    pub file_bytes: u64,
}

/// A complete olean envelope whose root is an Expr object rather than
/// `ModuleData`. [`crate::decl::DeclDecoder::decode_expr`] accepts `root`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodedExprRegion {
    pub bytes: Vec<u8>,
    pub root: u64,
    pub report: ExprWriteReport,
}

/// Semantic input for one complete basic `ModuleData` image.
///
/// Environment-extension payloads are intentionally absent from this first
/// complete-root slice. The emitted `entries` array is empty; a later API will
/// require typed extension payloads rather than accepting opaque handles it
/// cannot reconstruct.
#[derive(Debug, Clone, Copy)]
pub struct ModuleWriteInput<'a> {
    /// Whether this is one part of a module-system artifact.
    ///
    /// When true, the caller must also emit the `.server`, `.private`, and
    /// `.ir` siblings required by the pinned loader. This function encodes
    /// one `ModuleData` region; it does not claim cross-artifact publication.
    pub is_module: bool,
    pub imports: &'a [ModuleImport],
    pub constants: &'a [ConstantInfo],
    pub extra_const_names: &'a [Name],
}

/// Exact accounting for one complete basic module image.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleWriteReport {
    pub imports: u64,
    pub constants: u64,
    pub extra_const_names: u64,
    pub expr_nodes: u64,
    pub expr_presentations: u64,
    pub shared_expr_presentations: u64,
    pub runtime_objects: u64,
    pub file_bytes: u64,
}

/// A complete olean envelope rooted at `ModuleData`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodedModule {
    pub bytes: Vec<u8>,
    pub root: u64,
    pub report: ModuleWriteReport,
}

fn align8(value: u64) -> WResult<u64> {
    value
        .checked_add(7)
        .map(|sum| sum / 8 * 8)
        .ok_or(WriteError::Contract {
            what: "serialized object size overflows",
        })
}

fn header_field(name: &str) -> WResult<(usize, usize)> {
    format::OLEAN_HEADER_FIELDS
        .iter()
        .find(|field| field.name == name)
        .map(|field| (field.offset, field.size))
        .ok_or(WriteError::Contract {
            what: "generated header field is absent",
        })
}

fn build_header(spec: OleanWriteHeader<'_>) -> WResult<Vec<u8>> {
    if !format::OLEAN_ACCEPTED_VERSIONS.contains(&spec.version) {
        return Err(WriteError::Contract {
            what: "header version is outside the generated accepted set",
        });
    }
    if !OLEAN_WRITER_VERSIONS.contains(&spec.version) {
        return Err(WriteError::Unsupported {
            what: "accepted olean version is not implemented by the fresh writer",
        });
    }
    if !spec.base_addr.is_multiple_of(format::REGION_ALIGN as u64) {
        return Err(WriteError::Contract {
            what: "base address violates generated region alignment",
        });
    }
    if spec.lean_version.as_bytes().contains(&0) || spec.githash.as_bytes().contains(&0) {
        return Err(WriteError::Contract {
            what: "header text contains an interior NUL",
        });
    }

    let mut output = vec![0u8; format::OLEAN_HEADER_SIZE];
    let (magic_offset, magic_size) = header_field("marker")?;
    if magic_size != format::OLEAN_MAGIC.len() {
        return Err(WriteError::Contract {
            what: "generated marker field has the wrong width",
        });
    }
    output[magic_offset..magic_offset + magic_size].copy_from_slice(&format::OLEAN_MAGIC);

    let (version_offset, version_size) = header_field("version")?;
    let (flags_offset, flags_size) = header_field("flags")?;
    if version_size != 1 || flags_size != 1 {
        return Err(WriteError::Contract {
            what: "generated scalar header field has the wrong width",
        });
    }
    output[version_offset] = spec.version;
    output[flags_offset] = spec.flags;

    for (name, value) in [
        ("lean_version", spec.lean_version),
        ("githash", spec.githash),
    ] {
        let (offset, size) = header_field(name)?;
        if value.len() > size {
            return Err(WriteError::Contract {
                what: "header text exceeds its generated field",
            });
        }
        output[offset..offset + value.len()].copy_from_slice(value.as_bytes());
    }

    let (base_offset, base_size) = header_field("base_addr")?;
    if base_size != size_of::<u64>() {
        return Err(WriteError::Contract {
            what: "generated base-address field is not one word",
        });
    }
    output[base_offset..base_offset + base_size].copy_from_slice(&spec.base_addr.to_le_bytes());
    Ok(output)
}

fn require_object_fields(
    fields: &[format::LeanField],
    expected: &[&str],
    structure: &'static str,
) -> WResult<()> {
    let actual: Vec<&str> = fields
        .iter()
        .filter(|field| field.lean_type != "Bool")
        .map(|field| field.name)
        .collect();
    if actual != expected {
        return Err(WriteError::Contract { what: structure });
    }
    Ok(())
}

fn bool_scalars(
    fields: &[format::LeanField],
    values: &[(&str, bool)],
    structure: &'static str,
) -> WResult<Vec<u8>> {
    let mut output = Vec::new();
    for field in fields.iter().filter(|field| field.lean_type == "Bool") {
        let mut matches = values.iter().filter(|(name, _)| *name == field.name);
        let Some((_, value)) = matches.next() else {
            return Err(WriteError::Contract { what: structure });
        };
        if matches.next().is_some() {
            return Err(WriteError::Contract { what: structure });
        }
        output.push(u8::from(*value));
    }
    if output.len() != values.len() {
        return Err(WriteError::Contract { what: structure });
    }
    Ok(output)
}

struct Encoder {
    budget: WriteBudget,
    objects: u64,
    bytes: u64,
    names: HashMap<Name, Obj>,
    levels: HashMap<Level, Obj>,
    strings: HashMap<String, Obj>,
    exprs: HashMap<*const ExprNode, Obj>,
    expr_presentations: u64,
}

impl Encoder {
    fn new(budget: WriteBudget, version: u8) -> WResult<Self> {
        let framing = match version {
            2 => 0,
            3 => size_of::<u64>() + 2 * size_of::<u32>(),
            _ => {
                return Err(WriteError::Contract {
                    what: "writer accounting received an unsupported version",
                });
            }
        };
        let initial = u64::try_from(format::OLEAN_HEADER_SIZE)
            .ok()
            .and_then(|size| size.checked_add(framing as u64))
            .and_then(|size| size.checked_add(8))
            .ok_or(WriteError::Contract {
                what: "framing and root size overflow",
            })?;
        if initial > budget.max_bytes {
            return Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                limit: budget.max_bytes,
                attempted: initial,
            });
        }
        Ok(Self {
            budget,
            objects: 0,
            bytes: initial,
            names: HashMap::new(),
            levels: HashMap::new(),
            strings: HashMap::new(),
            exprs: HashMap::new(),
            expr_presentations: 0,
        })
    }

    fn charge_object(&mut self, serialized_bytes: u64) -> WResult<()> {
        let attempted_objects = self.objects.checked_add(1).ok_or(WriteError::Contract {
            what: "object accounting overflows",
        })?;
        if attempted_objects > self.budget.max_objects {
            return Err(WriteError::Budget {
                resource: WriteResource::Objects,
                limit: self.budget.max_objects,
                attempted: attempted_objects,
            });
        }
        let attempted_bytes =
            self.bytes
                .checked_add(serialized_bytes)
                .ok_or(WriteError::Contract {
                    what: "byte accounting overflows",
                })?;
        if attempted_bytes > self.budget.max_bytes {
            return Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                limit: self.budget.max_bytes,
                attempted: attempted_bytes,
            });
        }
        self.objects = attempted_objects;
        self.bytes = attempted_bytes;
        Ok(())
    }

    fn ctor(&mut self, tag: u8, children: Vec<Obj>, scalars: &[u8]) -> WResult<Obj> {
        if tag > fln_rt::abi::TAG_MAX_CTOR_TAG
            || children.len() >= fln_rt::abi::MAX_CTOR_FIELDS
            || scalars.len() >= fln_rt::abi::MAX_CTOR_SCALARS_SIZE
        {
            return Err(WriteError::Contract {
                what: "constructor exceeds the generated ABI shape",
            });
        }
        let children_bytes = u64::try_from(children.len())
            .ok()
            .and_then(|count| count.checked_mul(8))
            .ok_or(WriteError::Contract {
                what: "constructor child size overflows",
            })?;
        let scalar_bytes = u64::try_from(scalars.len()).map_err(|_| WriteError::Contract {
            what: "constructor scalar size overflows",
        })?;
        self.charge_object(align8(
            8u64.checked_add(children_bytes)
                .and_then(|size| size.checked_add(scalar_bytes))
                .ok_or(WriteError::Contract {
                    what: "constructor size overflows",
                })?,
        )?)?;
        Ok(Obj::mk_ctor(tag, children, scalars))
    }

    fn string(&mut self, value: &str) -> WResult<Obj> {
        if let Some(found) = self.strings.get(value) {
            return Ok(found.clone_ref());
        }
        let payload = u64::try_from(value.len())
            .ok()
            .and_then(|size| size.checked_add(1))
            .ok_or(WriteError::Contract {
                what: "string size overflows",
            })?;
        self.charge_object(align8(32u64.checked_add(payload).ok_or(
            WriteError::Contract {
                what: "string object size overflows",
            },
        )?)?)?;
        let object = Obj::mk_string(value);
        self.strings.insert(value.to_owned(), object.clone_ref());
        Ok(object)
    }

    fn nat(&mut self, value: &NatLit) -> WResult<Obj> {
        if let Some(small) = value.to_u64().and_then(|word| usize::try_from(word).ok())
            && small <= usize::MAX >> 1
        {
            return Ok(Obj::mk_nat(small));
        }
        let limbs = value.limbs_le();
        if limbs.is_empty() {
            return Ok(Obj::mk_nat(0));
        }
        let limb_bytes = u64::try_from(limbs.len())
            .ok()
            .and_then(|count| count.checked_mul(8))
            .ok_or(WriteError::Contract {
                what: "mpz limb size overflows",
            })?;
        self.charge_object(24u64.checked_add(limb_bytes).ok_or(WriteError::Contract {
            what: "mpz object size overflows",
        })?)?;
        Ok(Obj::mk_mpz(limbs, false))
    }

    fn nat_u64(&mut self, value: u64) -> WResult<Obj> {
        self.nat(&NatLit::from_u64(value))
    }

    fn int(&mut self, value: i64) -> WResult<Obj> {
        let small = if cfg!(target_pointer_width = "64") {
            (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&value)
        } else {
            (i64::from(i32::MIN / 2)..=i64::from(i32::MAX / 2)).contains(&value)
        };
        if !small {
            self.charge_object(32)?;
        }
        Ok(Obj::mk_int(value))
    }

    fn name(&mut self, root: &Name) -> WResult<Obj> {
        if root.is_anonymous() {
            return Ok(Obj::mk_nat(0));
        }
        if let Some(found) = self.names.get(root) {
            return Ok(found.clone_ref());
        }

        let mut chain = Vec::new();
        let mut cursor = root.clone();
        let mut current = loop {
            if cursor.is_anonymous() {
                break Obj::mk_nat(0);
            }
            if let Some(found) = self.names.get(&cursor) {
                break found.clone_ref();
            }
            chain.push(cursor.clone());
            cursor = cursor.parent();
        };

        for component in chain.into_iter().rev() {
            let (tag, payload) = match component.leaf_view() {
                LeafView::Anonymous => {
                    return Err(WriteError::Contract {
                        what: "anonymous Name entered the component chain",
                    });
                }
                LeafView::Str(value) => (1, self.string(value)?),
                LeafView::Num(value) => {
                    if component.component_overflowed() {
                        return Err(WriteError::Unsupported {
                            what: "Name.num component wider than u64",
                        });
                    }
                    (2, self.nat_u64(value)?)
                }
            };
            let object = self.ctor(tag, vec![current, payload], &component.hash().to_le_bytes())?;
            self.names.insert(component, object.clone_ref());
            current = object;
        }
        Ok(current)
    }

    fn level(&mut self, root: &Level) -> WResult<Obj> {
        if let Some(found) = self.levels.get(root) {
            return Ok(found.clone_ref());
        }
        let mut stack = vec![(root.clone(), false)];
        while let Some((level, exit)) = stack.pop() {
            if self.levels.contains_key(&level) {
                continue;
            }
            if !exit {
                stack.push((level.clone(), true));
                match level.view() {
                    LevelView::Zero | LevelView::Param(_) | LevelView::MVar(_) => {}
                    LevelView::Succ(child) => stack.push((child.clone(), false)),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        stack.push((right.clone(), false));
                        stack.push((left.clone(), false));
                    }
                }
                continue;
            }

            let object = match level.view() {
                LevelView::Zero => Obj::mk_nat(0),
                LevelView::Succ(child) => self.ctor(
                    1,
                    vec![self.level_object(child)?],
                    &level.data().0.to_le_bytes(),
                )?,
                LevelView::Max(left, right) => self.ctor(
                    2,
                    vec![self.level_object(left)?, self.level_object(right)?],
                    &level.data().0.to_le_bytes(),
                )?,
                LevelView::IMax(left, right) => self.ctor(
                    3,
                    vec![self.level_object(left)?, self.level_object(right)?],
                    &level.data().0.to_le_bytes(),
                )?,
                LevelView::Param(name) => {
                    let name = self.name(name)?;
                    self.ctor(4, vec![name], &level.data().0.to_le_bytes())?
                }
                LevelView::MVar(id) => {
                    let name = self.name(&id.0)?;
                    self.ctor(5, vec![name], &level.data().0.to_le_bytes())?
                }
            };
            self.levels.insert(level, object);
        }
        self.level_object(root)
    }

    fn level_object(&self, level: &Level) -> WResult<Obj> {
        self.levels
            .get(level)
            .map(Obj::clone_ref)
            .ok_or(WriteError::Contract {
                what: "level child was not encoded before its parent",
            })
    }

    fn list(&mut self, values: Vec<Obj>) -> WResult<Obj> {
        let mut list = Obj::mk_nat(0);
        for value in values.into_iter().rev() {
            list = self.ctor(1, vec![value, list], &[])?;
        }
        Ok(list)
    }

    fn array(&mut self, values: Vec<Obj>) -> WResult<Obj> {
        let element_bytes = u64::try_from(values.len())
            .ok()
            .and_then(|count| count.checked_mul(8))
            .ok_or(WriteError::Contract {
                what: "array element size overflows",
            })?;
        self.charge_object(
            24u64
                .checked_add(element_bytes)
                .ok_or(WriteError::Contract {
                    what: "array object size overflows",
                })?,
        )?;
        Ok(Obj::mk_array(values))
    }

    fn name_list(&mut self, values: &[Name]) -> WResult<Obj> {
        let mut encoded = Vec::with_capacity(values.len());
        for value in values {
            encoded.push(self.name(value)?);
        }
        self.list(encoded)
    }

    fn level_list(&mut self, values: &[Level]) -> WResult<Obj> {
        let mut encoded = Vec::with_capacity(values.len());
        for value in values {
            encoded.push(self.level(value)?);
        }
        self.list(encoded)
    }

    fn literal(&mut self, value: &Literal) -> WResult<Obj> {
        match value {
            Literal::Nat(value) => {
                let child = self.nat(value)?;
                self.ctor(0, vec![child], &[])
            }
            Literal::Str(value) => {
                let child = self.string(value)?;
                self.ctor(1, vec![child], &[])
            }
        }
    }

    fn data_value(&mut self, value: &DataValue) -> WResult<Obj> {
        match value {
            DataValue::OfString(value) => {
                let child = self.string(value)?;
                self.ctor(0, vec![child], &[])
            }
            DataValue::OfBool(value) => self.ctor(1, Vec::new(), &[u8::from(*value)]),
            DataValue::OfName(value) => {
                let child = self.name(value)?;
                self.ctor(2, vec![child], &[])
            }
            DataValue::OfNat(value) => {
                let child = self.nat_u64(*value)?;
                self.ctor(3, vec![child], &[])
            }
            DataValue::OfInt(value) => {
                let child = self.int(*value)?;
                self.ctor(4, vec![child], &[])
            }
            DataValue::OfSyntax(_) => Err(WriteError::Unsupported {
                what: "opaque SyntaxHandle has no serializable arena payload",
            }),
        }
    }

    fn kvmap(&mut self, map: &KVMap) -> WResult<Obj> {
        let mut pairs = Vec::with_capacity(map.len());
        for (key, value) in map.entries() {
            let key = self.name(key)?;
            let value = self.data_value(value)?;
            pairs.push(self.ctor(0, vec![key, value], &[])?);
        }
        self.list(pairs)
    }

    fn constant_val(&mut self, value: &ConstantVal) -> WResult<Obj> {
        let name = self.name(&value.name)?;
        let level_params = self.name_list(&value.level_params)?;
        let type_ = self.expression(&value.type_)?;
        self.ctor(0, vec![name, level_params, type_], &[])
    }

    fn reducibility_hints(&mut self, hints: ReducibilityHints) -> WResult<Obj> {
        match hints {
            ReducibilityHints::Opaque => Ok(Obj::mk_nat(0)),
            ReducibilityHints::Abbrev => Ok(Obj::mk_nat(1)),
            ReducibilityHints::Regular(height) => self.ctor(2, Vec::new(), &height.to_le_bytes()),
        }
    }

    fn recursor_rule(&mut self, rule: &RecursorRule) -> WResult<Obj> {
        let ctor = self.name(&rule.ctor)?;
        let nfields = self.nat_u64(u64::from(rule.nfields))?;
        let rhs = self.expression(&rule.rhs)?;
        self.ctor(0, vec![ctor, nfields, rhs], &[])
    }

    fn constant_info(&mut self, info: &ConstantInfo) -> WResult<Obj> {
        let (tag, value) = match info {
            ConstantInfo::Axiom(value) => {
                let base = self.constant_val(&value.base)?;
                let scalars = [u8::from(value.is_unsafe)];
                (0, self.ctor(0, vec![base], &scalars)?)
            }
            ConstantInfo::Defn(value) => {
                let base = self.constant_val(&value.base)?;
                let body = self.expression(&value.value)?;
                let hints = self.reducibility_hints(value.hints)?;
                let all = self.name_list(&value.all)?;
                let safety = match value.safety {
                    DefinitionSafety::Unsafe => 0,
                    DefinitionSafety::Safe => 1,
                    DefinitionSafety::Partial => 2,
                };
                (1, self.ctor(0, vec![base, body, hints, all], &[safety])?)
            }
            ConstantInfo::Thm(value) => {
                let base = self.constant_val(&value.base)?;
                let body = self.expression(&value.value)?;
                let all = self.name_list(&value.all)?;
                (2, self.ctor(0, vec![base, body, all], &[])?)
            }
            ConstantInfo::Opaque(value) => {
                let base = self.constant_val(&value.base)?;
                let body = self.expression(&value.value)?;
                let all = self.name_list(&value.all)?;
                let scalars = [u8::from(value.is_unsafe)];
                (3, self.ctor(0, vec![base, body, all], &scalars)?)
            }
            ConstantInfo::Quot(value) => {
                let base = self.constant_val(&value.base)?;
                let kind = match value.kind {
                    QuotKind::Type => 0,
                    QuotKind::Ctor => 1,
                    QuotKind::Lift => 2,
                    QuotKind::Ind => 3,
                };
                (4, self.ctor(0, vec![base], &[kind])?)
            }
            ConstantInfo::Induct(value) => {
                let base = self.constant_val(&value.base)?;
                let num_params = self.nat_u64(u64::from(value.num_params))?;
                let num_indices = self.nat_u64(u64::from(value.num_indices))?;
                let all = self.name_list(&value.all)?;
                let ctors = self.name_list(&value.ctors)?;
                let num_nested = self.nat_u64(u64::from(value.num_nested))?;
                let scalars = [
                    u8::from(value.is_rec),
                    u8::from(value.is_unsafe),
                    u8::from(value.is_reflexive),
                ];
                (
                    5,
                    self.ctor(
                        0,
                        vec![base, num_params, num_indices, all, ctors, num_nested],
                        &scalars,
                    )?,
                )
            }
            ConstantInfo::Ctor(value) => {
                let base = self.constant_val(&value.base)?;
                let induct = self.name(&value.induct)?;
                let cidx = self.nat_u64(u64::from(value.cidx))?;
                let num_params = self.nat_u64(u64::from(value.num_params))?;
                let num_fields = self.nat_u64(u64::from(value.num_fields))?;
                let scalars = [u8::from(value.is_unsafe)];
                (
                    6,
                    self.ctor(
                        0,
                        vec![base, induct, cidx, num_params, num_fields],
                        &scalars,
                    )?,
                )
            }
            ConstantInfo::Rec(value) => {
                let base = self.constant_val(&value.base)?;
                let all = self.name_list(&value.all)?;
                let num_params = self.nat_u64(u64::from(value.num_params))?;
                let num_indices = self.nat_u64(u64::from(value.num_indices))?;
                let num_motives = self.nat_u64(u64::from(value.num_motives))?;
                let num_minors = self.nat_u64(u64::from(value.num_minors))?;
                let mut rules = Vec::with_capacity(value.rules.len());
                for rule in &value.rules {
                    rules.push(self.recursor_rule(rule)?);
                }
                let rules = self.list(rules)?;
                let scalars = [u8::from(value.k), u8::from(value.is_unsafe)];
                (
                    7,
                    self.ctor(
                        0,
                        vec![
                            base,
                            all,
                            num_params,
                            num_indices,
                            num_motives,
                            num_minors,
                            rules,
                        ],
                        &scalars,
                    )?,
                )
            }
        };
        self.ctor(tag, vec![value], &[])
    }

    fn module_root(&mut self, input: ModuleWriteInput<'_>) -> WResult<Obj> {
        require_object_fields(
            format::IMPORT_FIELDS,
            &["module"],
            "generated Import object-field inventory differs from the writer",
        )?;
        let mut imports = Vec::with_capacity(input.imports.len());
        for import in input.imports {
            let module = self.name(&import.module)?;
            let scalars = bool_scalars(
                format::IMPORT_FIELDS,
                &[
                    ("importAll", import.import_all),
                    ("isExported", import.is_exported),
                    ("isMeta", import.is_meta),
                ],
                "generated Import Bool inventory differs from the writer",
            )?;
            imports.push(self.ctor(0, vec![module], &scalars)?);
        }
        let imports = self.array(imports)?;

        let mut const_names = Vec::with_capacity(input.constants.len());
        let mut constants = Vec::with_capacity(input.constants.len());
        for constant in input.constants {
            const_names.push(self.name(constant.name())?);
            constants.push(self.constant_info(constant)?);
        }
        let const_names = self.array(const_names)?;
        let constants = self.array(constants)?;

        let mut extra_const_names = Vec::with_capacity(input.extra_const_names.len());
        for name in input.extra_const_names {
            extra_const_names.push(self.name(name)?);
        }
        let extra_const_names = self.array(extra_const_names)?;
        let entries = self.array(Vec::new())?;

        require_object_fields(
            format::MODULE_DATA_FIELDS,
            &[
                "imports",
                "constNames",
                "constants",
                "extraConstNames",
                "entries",
            ],
            "generated ModuleData object-field inventory differs from the writer",
        )?;
        let scalars = bool_scalars(
            format::MODULE_DATA_FIELDS,
            &[("isModule", input.is_module)],
            "generated ModuleData Bool inventory differs from the writer",
        )?;
        self.ctor(
            0,
            vec![imports, const_names, constants, extra_const_names, entries],
            &scalars,
        )
    }

    fn expression(&mut self, root: &Expr) -> WResult<Obj> {
        let mut stack = vec![(root, false)];
        while let Some((expr, exit)) = stack.pop() {
            if !exit {
                self.expr_presentations =
                    self.expr_presentations
                        .checked_add(1)
                        .ok_or(WriteError::Contract {
                            what: "expression presentation count overflows",
                        })?;
            }
            let key = std::ptr::from_ref(expr.node());
            if self.exprs.contains_key(&key) {
                continue;
            }
            if !exit {
                stack.push((expr, true));
                match expr.node() {
                    ExprNode::BVar { .. }
                    | ExprNode::FVar { .. }
                    | ExprNode::MVar { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Const { .. }
                    | ExprNode::Lit { .. } => {}
                    ExprNode::App { f, a } => {
                        stack.push((a, false));
                        stack.push((f, false));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push((body, false));
                        stack.push((binder_type, false));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push((body, false));
                        stack.push((value, false));
                        stack.push((type_, false));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        stack.push((expr, false));
                    }
                }
                continue;
            }

            let mut scalars = expr.data().0.to_le_bytes().to_vec();
            let (tag, children) = match expr.node() {
                ExprNode::BVar { idx } => (0, vec![self.nat_u64(u64::from(*idx))?]),
                ExprNode::FVar { id } => (1, vec![self.name(&id.0)?]),
                ExprNode::MVar { id } => (2, vec![self.name(&id.0)?]),
                ExprNode::Sort { level } => (3, vec![self.level(level)?]),
                ExprNode::Const { name, levels } => {
                    (4, vec![self.name(name)?, self.level_list(levels)?])
                }
                ExprNode::App { f, a } => (
                    5,
                    vec![self.expression_object(f)?, self.expression_object(a)?],
                ),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    scalars.push(binder_info.to_u64() as u8);
                    (
                        6,
                        vec![
                            self.name(binder_name)?,
                            self.expression_object(binder_type)?,
                            self.expression_object(body)?,
                        ],
                    )
                }
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => {
                    scalars.push(binder_info.to_u64() as u8);
                    (
                        7,
                        vec![
                            self.name(binder_name)?,
                            self.expression_object(binder_type)?,
                            self.expression_object(body)?,
                        ],
                    )
                }
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value,
                    body,
                    non_dep,
                } => {
                    scalars.push(u8::from(*non_dep));
                    (
                        8,
                        vec![
                            self.name(decl_name)?,
                            self.expression_object(type_)?,
                            self.expression_object(value)?,
                            self.expression_object(body)?,
                        ],
                    )
                }
                ExprNode::Lit { literal } => (9, vec![self.literal(literal)?]),
                ExprNode::MData { data, expr } => {
                    (10, vec![self.kvmap(data)?, self.expression_object(expr)?])
                }
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => (
                    11,
                    vec![
                        self.name(struct_name)?,
                        self.nat_u64(*idx)?,
                        self.expression_object(expr)?,
                    ],
                ),
            };
            let object = self.ctor(tag, children, &scalars)?;
            self.exprs.insert(key, object);
        }
        self.expression_object(root)
    }

    fn expression_object(&self, expr: &Expr) -> WResult<Obj> {
        self.exprs
            .get(&std::ptr::from_ref(expr.node()))
            .map(Obj::clone_ref)
            .ok_or(WriteError::Contract {
                what: "expression child was not encoded before its parent",
            })
    }
}

struct FinishedRegion {
    bytes: Vec<u8>,
    root: u64,
    region: fln_rt::region::RegionReport,
    encoder: Encoder,
}

fn finish_region(
    encoder: Encoder,
    root_object: Obj,
    header: Vec<u8>,
    version: u8,
    base_addr: u64,
) -> WResult<FinishedRegion> {
    let mut file = header;
    let data_prefix = match version {
        2 => 0,
        3 => size_of::<u64>(),
        _ => {
            return Err(WriteError::Contract {
                what: "region finalization received an unsupported version",
            });
        }
    };
    let payload_base = base_addr
        .checked_add(format::OLEAN_HEADER_SIZE as u64)
        .and_then(|base| base.checked_add(data_prefix as u64))
        .ok_or(WriteError::Contract {
            what: "payload base overflows",
        })?;
    let payload = fln_rt::region::compact(&root_object, payload_base)?;
    let region = fln_rt::region::audit(&payload, payload_base)?;
    if region.objects != encoder.objects || region.bytes != payload.len() {
        return Err(WriteError::Contract {
            what: "writer accounting differs from the shared region audit",
        });
    }
    let payload_bytes = u64::try_from(region.bytes).map_err(|_| WriteError::Contract {
        what: "payload byte count overflows",
    })?;
    let trailer_bytes = if version == 3 {
        2 * size_of::<u32>()
    } else {
        0
    };
    let file_bytes = u64::try_from(file.len())
        .ok()
        .and_then(|size| size.checked_add(data_prefix as u64))
        .and_then(|size| size.checked_add(payload_bytes))
        .and_then(|size| size.checked_add(trailer_bytes as u64))
        .ok_or(WriteError::Contract {
            what: "final file size overflows",
        })?;
    if file_bytes != encoder.bytes {
        return Err(WriteError::Contract {
            what: "pre-construction byte charge differs from compacted bytes",
        });
    }
    base_addr
        .checked_add(file_bytes)
        .ok_or(WriteError::Contract {
            what: "final mapped address range overflows",
        })?;
    let root = region.root;
    if version == 3 {
        file.extend_from_slice(&payload_bytes.to_le_bytes());
    }
    file.extend_from_slice(&payload);
    if version == 3 {
        file.extend_from_slice(&0u32.to_le_bytes());
        file.extend_from_slice(&0u32.to_le_bytes());
    }
    Ok(FinishedRegion {
        bytes: file,
        root,
        region,
        encoder,
    })
}

/// Encode one expression DAG into an olean envelope through the shared region
/// compactor.
pub fn encode_expr_region(
    expression: &Expr,
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> WResult<EncodedExprRegion> {
    let header_bytes = build_header(header)?;
    let mut encoder = Encoder::new(budget, header.version)?;
    let root_object = encoder.expression(expression)?;
    let finished = finish_region(
        encoder,
        root_object,
        header_bytes,
        header.version,
        header.base_addr,
    )?;
    let expr_nodes =
        u64::try_from(finished.encoder.exprs.len()).map_err(|_| WriteError::Contract {
            what: "expression node count overflows",
        })?;
    let file_bytes = u64::try_from(finished.bytes.len()).map_err(|_| WriteError::Contract {
        what: "final file size overflows",
    })?;
    Ok(EncodedExprRegion {
        bytes: finished.bytes,
        root: finished.root,
        report: ExprWriteReport {
            expr_nodes,
            expr_presentations: finished.encoder.expr_presentations,
            shared_expr_presentations: finished
                .encoder
                .expr_presentations
                .saturating_sub(expr_nodes),
            runtime_objects: finished.region.objects,
            file_bytes,
        },
    })
}

/// Encode one complete basic `ModuleData` image. Imports, all eight
/// `ConstantInfo` variants, extra constant names, and the empty extension
/// array are emitted in generated-contract field order.
///
/// An image with `input.is_module == false` is directly loadable as a
/// standalone `.olean`. A true value denotes one physical part of the
/// module-system artifact set; the caller remains responsible for the
/// companion parts documented on [`ModuleWriteInput::is_module`].
pub fn encode_module(
    input: ModuleWriteInput<'_>,
    header: OleanWriteHeader<'_>,
    budget: WriteBudget,
) -> WResult<EncodedModule> {
    let header_bytes = build_header(header)?;
    let mut encoder = Encoder::new(budget, header.version)?;
    let root_object = encoder.module_root(input)?;
    let finished = finish_region(
        encoder,
        root_object,
        header_bytes,
        header.version,
        header.base_addr,
    )?;
    let expr_nodes =
        u64::try_from(finished.encoder.exprs.len()).map_err(|_| WriteError::Contract {
            what: "expression node count overflows",
        })?;
    let imports = u64::try_from(input.imports.len()).map_err(|_| WriteError::Contract {
        what: "import count overflows",
    })?;
    let constants = u64::try_from(input.constants.len()).map_err(|_| WriteError::Contract {
        what: "constant count overflows",
    })?;
    let extra_const_names =
        u64::try_from(input.extra_const_names.len()).map_err(|_| WriteError::Contract {
            what: "extra constant-name count overflows",
        })?;
    let file_bytes = u64::try_from(finished.bytes.len()).map_err(|_| WriteError::Contract {
        what: "final file size overflows",
    })?;
    Ok(EncodedModule {
        bytes: finished.bytes,
        root: finished.root,
        report: ModuleWriteReport {
            imports,
            constants,
            extra_const_names,
            expr_nodes,
            expr_presentations: finished.encoder.expr_presentations,
            shared_expr_presentations: finished
                .encoder
                .expr_presentations
                .saturating_sub(expr_nodes),
            runtime_objects: finished.region.objects,
            file_bytes,
        },
    })
}

#[cfg(test)]
mod tests {
    use fln_core::expr::{BinderInfo, FVarId, MVarId};
    use fln_core::level::LMVarId;
    use fln_env::constants::{
        AxiomVal, ConstructorVal, DefinitionVal, InductiveVal, OpaqueVal, QuotVal, RecursorVal,
        TheoremVal,
    };

    use super::*;
    use crate::decl::DeclDecoder;
    use crate::region::{OleanView, WalkBudget};

    const HASH: &str = "0123456789abcdef0123456789abcdef01234567";

    fn header() -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version: 2,
            flags: 1,
            lean_version: "4.32.0",
            githash: HASH,
            base_addr: 0x20_000,
        }
    }

    fn v3_header() -> OleanWriteHeader<'static> {
        OleanWriteHeader {
            version: 3,
            ..header()
        }
    }

    fn name(value: &str) -> Name {
        Name::str(Name::anonymous(), value)
    }

    fn roundtrip(expression: &Expr) -> EncodedExprRegion {
        let encoded =
            encode_expr_region(expression, header(), WriteBudget::default()).expect("encode");
        assert_eq!(encoded.bytes.len() as u64, encoded.report.file_bytes);
        let view = OleanView::parse(&encoded.bytes).expect("header");
        let audit = view.shared_audit().expect("shared audit");
        assert_eq!(audit.objects, encoded.report.runtime_objects);
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let decoded = decoder.decode_expr(encoded.root).expect("decode");
        assert_eq!(&decoded, expression);
        encoded
    }

    fn base(local_name: &str, type_: &Expr) -> ConstantVal {
        ConstantVal {
            name: name(local_name),
            level_params: vec![name("u")],
            type_: type_.clone(),
        }
    }

    #[test]
    fn complete_module_roundtrips_every_constant_variant_and_import_flag() {
        let type_ = Expr::sort(Level::param(name("u")));
        let value = Expr::bvar(0).expect("value");
        let constants = vec![
            ConstantInfo::Axiom(AxiomVal {
                base: base("Demo.ax", &type_),
                is_unsafe: true,
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: base("Demo.def.opaque", &type_),
                value: value.clone(),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Unsafe,
                all: vec![name("Demo.def.opaque")],
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: base("Demo.def.abbrev", &type_),
                value: value.clone(),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name("Demo.def.abbrev")],
            }),
            ConstantInfo::Defn(DefinitionVal {
                base: base("Demo.def.regular", &type_),
                value: value.clone(),
                hints: ReducibilityHints::Regular(u32::MAX),
                safety: DefinitionSafety::Partial,
                all: vec![name("Demo.def.regular")],
            }),
            ConstantInfo::Thm(TheoremVal {
                base: base("Demo.thm", &type_),
                value: value.clone(),
                all: vec![name("Demo.thm")],
            }),
            ConstantInfo::Opaque(OpaqueVal {
                base: base("Demo.opaque", &type_),
                value: value.clone(),
                is_unsafe: true,
                all: vec![name("Demo.opaque")],
            }),
            ConstantInfo::Quot(QuotVal {
                base: base("Demo.quot.type", &type_),
                kind: QuotKind::Type,
            }),
            ConstantInfo::Quot(QuotVal {
                base: base("Demo.quot.ctor", &type_),
                kind: QuotKind::Ctor,
            }),
            ConstantInfo::Quot(QuotVal {
                base: base("Demo.quot.lift", &type_),
                kind: QuotKind::Lift,
            }),
            ConstantInfo::Quot(QuotVal {
                base: base("Demo.quot.ind", &type_),
                kind: QuotKind::Ind,
            }),
            ConstantInfo::Induct(InductiveVal {
                base: base("Demo.ind", &type_),
                num_params: u32::MAX,
                num_indices: 2,
                // TWO distinct names in each list. A single-element list
                // proves the cons loop is reachable but has no ORDER to get
                // wrong, and `all` and `ctors` are adjacent List Name slots
                // (3 and 4), so a codec that crossed them would round-trip
                // clean. See
                // `the_inductive_name_lists_keep_their_arity_and_order_on_the_wire`.
                all: vec![name("Demo.ind"), name("Demo.ind.mutual")],
                ctors: vec![name("Demo.ind.mk"), name("Demo.ind.mk2")],
                num_nested: 3,
                is_rec: true,
                is_unsafe: true,
                is_reflexive: true,
            }),
            ConstantInfo::Ctor(ConstructorVal {
                base: base("Demo.ind.mk", &type_),
                induct: name("Demo.ind"),
                cidx: u32::MAX,
                num_params: 1,
                num_fields: u32::MAX,
                is_unsafe: true,
            }),
            ConstantInfo::Rec(RecursorVal {
                base: base("Demo.ind.rec", &type_),
                all: vec![name("Demo.ind")],
                num_params: u32::MAX,
                num_indices: 2,
                num_motives: 3,
                num_minors: 4,
                rules: vec![RecursorRule {
                    ctor: name("Demo.ind.mk"),
                    nfields: u32::MAX,
                    rhs: value,
                }],
                k: true,
                is_unsafe: true,
            }),
        ];
        let imports: Vec<ModuleImport> = (0u64..8)
            .map(|bits| ModuleImport {
                module: Name::num(name("Import"), bits),
                import_all: bits & 1 != 0,
                is_exported: bits & 2 != 0,
                is_meta: bits & 4 != 0,
            })
            .collect();
        let extras = vec![name("Demo.extra"), Name::num(name("Demo.extra"), u64::MAX)];

        let encoded = encode_module(
            ModuleWriteInput {
                is_module: true,
                imports: &imports,
                constants: &constants,
                extra_const_names: &extras,
            },
            header(),
            WriteBudget::default(),
        )
        .expect("encode module");
        assert_eq!(encoded.bytes.len() as u64, encoded.report.file_bytes);
        assert_eq!(encoded.report.imports, imports.len() as u64);
        assert_eq!(encoded.report.constants, constants.len() as u64);
        assert!(encoded.report.shared_expr_presentations > 0);

        let view = OleanView::parse(&encoded.bytes).expect("header");
        let audit = view.shared_audit().expect("shared audit");
        assert_eq!(audit.objects, encoded.report.runtime_objects);
        view.walk(WalkBudget::default()).expect("reachable walk");
        let module = view.module_data(WalkBudget::default()).expect("ModuleData");
        assert!(module.is_module);
        assert_eq!(module.imports, imports);
        assert_eq!(module.constants, constants.len() as u64);
        assert_eq!(module.extra_const_names, extras.len() as u64);
        assert!(module.extensions.is_empty());
        assert_eq!(
            module.const_names,
            constants
                .iter()
                .map(|constant| constant.name().to_display_string())
                .collect::<Vec<_>>()
        );

        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        assert_eq!(
            decoder.decode_module_constants().expect("constants"),
            constants
        );
    }

    /// An inductive's `all` and `ctors` keep their ARITY and their ORDER, and
    /// the claim is made against the WIRE rather than against the round trip.
    ///
    /// `complete_module_roundtrips_every_constant_variant_and_import_flag`
    /// compares decoded constants to the values that were encoded, which is
    /// symmetric-blind: an encoder that reverses a name list and a decoder that
    /// reverses it back agree with each other, and the equality holds while
    /// both are wrong. Nothing in that test reads a byte the codec did not also
    /// write, so the only way to separate the two is to walk the cons chain
    /// directly.
    ///
    /// The fixture also could not have shown it. Both lists held a single name
    /// until this commit, and a list of one has no order to get wrong - the
    /// same insufficiency that made the recursor's rule list unpinnable before
    /// `191a5783`, arriving here for a second pair of fields.
    ///
    /// `all` and `ctors` are the sharper case, because they are BOTH
    /// `List Name` and they are ADJACENT - slots 3 and 4 of the payload. A
    /// codec that read one for the other produces two well-formed name lists
    /// and no arity, size or constructor rule can object, so this cell asserts
    /// the two are not equal to each other as well as walking each.
    #[test]
    fn the_inductive_name_lists_keep_their_arity_and_order_on_the_wire() {
        let type_ = Expr::sort(Level::param(name("u")));
        let all = vec![name("Demo.ind"), name("Demo.ind.mutual")];
        let ctors = vec![name("Demo.ind.mk"), name("Demo.ind.mk2")];

        // The guard: with one member, or two equal ones, a reversal would be
        // invisible; with `all == ctors` the slot confusion would be too.
        assert_eq!(all.len(), 2, "two members, or there is no order");
        assert_eq!(ctors.len(), 2, "two members, or there is no order");
        assert_ne!(all[0], all[1], "the members must be distinguishable");
        assert_ne!(ctors[0], ctors[1], "the members must be distinguishable");
        assert_ne!(
            all, ctors,
            "the two lists must differ, or reading slot 4 for slot 3 would \
             produce the right answer by accident"
        );

        // One constant, so the constants array's element 0 is unambiguous.
        let constants = vec![ConstantInfo::Induct(InductiveVal {
            base: base("Demo.ind", &type_),
            num_params: 1,
            num_indices: 2,
            all: all.clone(),
            ctors: ctors.clone(),
            num_nested: 3,
            is_rec: true,
            is_unsafe: false,
            is_reflexive: true,
        })];

        let encoded = encode_module(
            ModuleWriteInput {
                is_module: true,
                imports: &[],
                constants: &constants,
                extra_const_names: &[],
            },
            header(),
            WriteBudget::default(),
        )
        .expect("encode module");

        let view = OleanView::parse(&encoded.bytes).expect("header");
        let arrays = view.module_arrays().expect("constant array");
        let info_off = view
            .deref(
                view.read_u64(arrays.constants.0 + 24)
                    .expect("ConstantInfo"),
            )
            .expect("ConstantInfo object");
        assert_eq!(
            view.obj_header(info_off).expect("ConstantInfo header").0,
            5,
            "ConstantInfo.inductInfo"
        );
        let val_off = view
            .deref(view.read_u64(info_off + 8).expect("InductiveVal pointer"))
            .expect("InductiveVal object");

        // Walk one `List Name` from a payload slot, on the wire.
        let walk = |slot: u64| -> Vec<String> {
            let mut cursor = view.read_u64(val_off + 8 + 8 * slot).expect("list slot");
            let mut names = Vec::new();
            while cursor & 1 == 0 {
                let cell = view.deref(cursor).expect("cons cell");
                assert_eq!(
                    view.obj_header(cell).expect("cons header").0,
                    1,
                    "List.cons"
                );
                let head = view.read_u64(cell + 8).expect("head pointer");
                names.push(
                    DeclDecoder::new(&view, WalkBudget::default())
                        .decode_name(head)
                        .expect("member name")
                        .to_display_string(),
                );
                cursor = view.read_u64(cell + 16).expect("tail pointer");
            }
            assert_eq!(cursor >> 1, 0, "the list ends in boxed nil");
            names
        };

        let all_on_the_wire = walk(3);
        let ctors_on_the_wire = walk(4);
        assert_eq!(
            all_on_the_wire,
            vec!["Demo.ind".to_owned(), "Demo.ind.mutual".to_owned()],
            "the mutual block, in the order it was given"
        );
        assert_eq!(
            ctors_on_the_wire,
            vec!["Demo.ind.mk".to_owned(), "Demo.ind.mk2".to_owned()],
            "the constructors, in the order they were given; constructor i is \
             identified by its POSITION, so a reversal renames every one"
        );

        // And the decoder agrees with the bytes rather than with the encoder.
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let decoded = decoder.decode_module_constants().expect("constants");
        let ConstantInfo::Induct(inductive) = &decoded[0] else {
            panic!("the fixture declares one inductive")
        };
        let display =
            |names: &[Name]| -> Vec<String> { names.iter().map(Name::to_display_string).collect() };
        assert_eq!(display(&inductive.all), all_on_the_wire, "`all` as chained");
        assert_eq!(
            display(&inductive.ctors),
            ctors_on_the_wire,
            "`ctors` as chained"
        );
    }

    #[test]
    fn empty_complete_module_is_a_valid_nonmodule_image() {
        let encoded = encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            header(),
            WriteBudget::default(),
        )
        .expect("encode empty module");
        let view = OleanView::parse(&encoded.bytes).expect("header");
        let module = view.module_data(WalkBudget::default()).expect("ModuleData");
        assert!(!module.is_module);
        assert!(module.imports.is_empty());
        assert_eq!(module.constants, 0);
        assert_eq!(module.extra_const_names, 0);
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        assert!(
            decoder
                .decode_module_constants()
                .expect("constants")
                .is_empty()
        );
    }

    #[test]
    fn v3_framing_roundtrips_real_data_and_rejects_legacy_or_corrupt_bodies() {
        let expression = Expr::app(
            Expr::const_(name("Demo.f"), vec![Level::zero()]),
            Expr::lit(Literal::Str("v3".to_owned())),
        );
        let encoded = encode_expr_region(&expression, v3_header(), WriteBudget::default())
            .expect("encode v3 expression");
        let envelope = fln_rt::region::parse_olean_envelope(&encoded.bytes).expect("v3 envelope");
        assert_eq!(envelope.version, 3);
        assert_eq!(
            envelope.payload_offset,
            format::OLEAN_HEADER_SIZE + size_of::<u64>()
        );
        assert_eq!(
            u64::from_le_bytes(
                encoded.bytes[format::OLEAN_HEADER_SIZE..envelope.payload_offset]
                    .try_into()
                    .expect("data-size prefix"),
            ),
            envelope.payload_len as u64
        );
        let trailer = envelope.payload_offset + envelope.payload_len;
        assert_eq!(
            &encoded.bytes[trailer..],
            &[0; 2 * size_of::<u32>()],
            "closure and library relocation tables are explicitly empty"
        );
        let view = OleanView::parse(&encoded.bytes).expect("v3 view");
        view.shared_audit().expect("v3 shared audit");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        assert_eq!(
            decoder.decode_expr(encoded.root).expect("v3 decode"),
            expression
        );
        let exact_budget = WriteBudget {
            max_objects: WriteBudget::default().max_objects,
            max_bytes: encoded.report.file_bytes,
        };
        encode_expr_region(&expression, v3_header(), exact_budget)
            .expect("v3 framing is fully charged at the exact byte boundary");
        assert!(matches!(
            encode_expr_region(
                &expression,
                v3_header(),
                WriteBudget {
                    max_bytes: encoded.report.file_bytes - 1,
                    ..exact_budget
                },
            ),
            Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                ..
            })
        ));

        let module = encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[],
                extra_const_names: &[name("Demo.extra")],
            },
            v3_header(),
            WriteBudget::default(),
        )
        .expect("encode v3 ModuleData");
        let view = OleanView::parse(&module.bytes).expect("v3 module view");
        assert_eq!(
            view.module_data(WalkBudget::default())
                .expect("v3 ModuleData")
                .extra_const_names,
            1
        );

        let mut legacy_body = roundtrip(&expression).bytes;
        legacy_body[5] = 3;
        assert!(OleanView::parse(&legacy_body).is_err());

        let mut corrupt_size = encoded.bytes.clone();
        let oversized = (envelope.payload_len as u64 + 8).to_le_bytes();
        corrupt_size[format::OLEAN_HEADER_SIZE..envelope.payload_offset]
            .copy_from_slice(&oversized);
        assert!(OleanView::parse(&corrupt_size).is_err());

        let mut truncated_trailer = encoded.bytes.clone();
        truncated_trailer.pop();
        assert!(OleanView::parse(&truncated_trailer).is_err());

        let mut overflowing_closure_table = encoded.bytes.clone();
        overflowing_closure_table[trailer..trailer + size_of::<u32>()]
            .copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(OleanView::parse(&overflowing_closure_table).is_err());

        let mut truncated_library_table = encoded.bytes.clone();
        truncated_library_table[trailer + size_of::<u32>()..trailer + 2 * size_of::<u32>()]
            .copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(OleanView::parse(&truncated_library_table).is_err());

        let mut invalid_closure_offset = encoded.bytes.clone();
        invalid_closure_offset[trailer..trailer + size_of::<u32>()]
            .copy_from_slice(&1u32.to_le_bytes());
        invalid_closure_offset.splice(
            trailer + size_of::<u32>()..trailer + size_of::<u32>(),
            (envelope.payload_len as u64 - 4).to_le_bytes(),
        );
        assert!(OleanView::parse(&invalid_closure_offset).is_err());
    }

    #[test]
    fn every_expression_constructor_roundtrips_with_computed_fields_checked() {
        let zero = Level::zero();
        let successor = zero.clone().succ().expect("successor");
        let universe = Level::param(name("u"));
        let level_mvar = Level::mvar(LMVarId(name("um")));
        let max_level = Level::max(universe.clone(), level_mvar.clone()).expect("max");
        let imax_level = Level::imax(level_mvar, successor.clone()).expect("imax");
        let type_ = Expr::sort(max_level.clone());
        let body = Expr::bvar(0).expect("bvar");
        let fvar = Expr::fvar(FVarId(name("x")));
        let mvar = Expr::mvar(MVarId(name("m")));
        let numeric_name = Name::num(name("Demo"), u64::MAX);
        let constant = Expr::const_(
            numeric_name.clone(),
            vec![zero, successor, universe, max_level, imax_level],
        );
        let app = Expr::app(constant.clone(), fvar.clone());

        let metadata = KVMap::from_entries(vec![
            (name("s"), DataValue::OfString("text".to_owned())),
            (name("b"), DataValue::OfBool(true)),
            (name("n"), DataValue::OfName(numeric_name)),
            (name("u"), DataValue::OfNat(u64::MAX)),
            (name("i.small"), DataValue::OfInt(-7)),
            (name("i.large"), DataValue::OfInt(i64::MIN)),
            (name("i.positive"), DataValue::OfInt(i64::MAX)),
        ]);

        let cases = vec![
            body.clone(),
            fvar,
            mvar,
            type_.clone(),
            constant,
            app,
            Expr::lam(name("x"), type_.clone(), body.clone(), BinderInfo::Implicit),
            Expr::forall_e(
                name("x"),
                type_.clone(),
                body.clone(),
                BinderInfo::StrictImplicit,
            ),
            Expr::let_e(
                name("x"),
                type_,
                Expr::lit(Literal::Nat(NatLit::from_u64(42))),
                body.clone(),
                true,
            ),
            Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![0, 1]))),
            Expr::lit(Literal::Str("writer".to_owned())),
            Expr::mdata(metadata, body.clone()),
            Expr::mdata(
                KVMap::from_entries(vec![
                    (name("dup"), DataValue::OfNat(1)),
                    (name("other"), DataValue::OfBool(false)),
                    (name("dup"), DataValue::OfNat(2)),
                ]),
                body.clone(),
            ),
            Expr::proj(name("Demo.Pair"), u64::MAX, body),
        ];

        for case in cases {
            roundtrip(&case);
        }
    }

    #[test]
    fn mdata_duplicate_keys_survive_decode_as_the_entry_list() {
        // Pin `KVMap.mk`: duplicate keys are representable. `insert` would
        // replace the first `dup` and the stored Expr.Data word would then
        // fail the decoder's cross-check — or, with the check off, silently
        // shrink the map. The codec must keep both rows.
        let metadata = KVMap::from_entries(vec![
            (name("dup"), DataValue::OfNat(1)),
            (name("other"), DataValue::OfString("keep".to_owned())),
            (name("dup"), DataValue::OfNat(2)),
        ]);
        let expression = Expr::mdata(metadata, Expr::bvar(0).expect("body"));
        roundtrip(&expression);
        let encoded =
            encode_expr_region(&expression, header(), WriteBudget::default()).expect("encode");
        let view = OleanView::parse(&encoded.bytes).expect("header");
        let decoded = DeclDecoder::new(&view, WalkBudget::default())
            .decode_expr(encoded.root)
            .expect("decode");
        assert!(
            matches!(decoded.node(), ExprNode::MData { data, .. } if data.entries()
                == [
                    (name("dup"), DataValue::OfNat(1)),
                    (name("other"), DataValue::OfString("keep".to_owned())),
                    (name("dup"), DataValue::OfNat(2)),
                ]
                && data.find(&name("dup")) == Some(&DataValue::OfNat(1))
                && data.len() == 3)
        );
    }

    #[test]
    fn expression_allocation_sharing_is_preserved_exactly() {
        let shared = Expr::bvar(0).expect("bvar");
        let shared_root = Expr::app(shared.clone(), shared);
        let encoded = roundtrip(&shared_root);
        assert_eq!(encoded.report.expr_nodes, 2);
        assert_eq!(encoded.report.expr_presentations, 3);
        assert_eq!(encoded.report.shared_expr_presentations, 1);

        let view = OleanView::parse(&encoded.bytes).expect("header");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let decoded = decoder.decode_expr(encoded.root).expect("decode");
        assert!(matches!(decoded.node(), ExprNode::App { .. }));
        if let ExprNode::App { f, a } = decoded.node() {
            assert!(std::ptr::eq(f.node(), a.node()));
        }

        let distinct_root = Expr::app(Expr::bvar(0).expect("left"), Expr::bvar(0).expect("right"));
        let distinct = roundtrip(&distinct_root);
        let view = OleanView::parse(&distinct.bytes).expect("header");
        let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
        let decoded = decoder.decode_expr(distinct.root).expect("decode");
        assert!(matches!(decoded.node(), ExprNode::App { .. }));
        if let ExprNode::App { f, a } = decoded.node() {
            assert!(!std::ptr::eq(f.node(), a.node()));
        }
    }

    #[test]
    fn budgets_and_opaque_syntax_refuse_before_artifact_publication() {
        let expression = Expr::app(Expr::bvar(0).expect("left"), Expr::bvar(1).expect("right"));
        assert!(matches!(
            encode_expr_region(
                &expression,
                header(),
                WriteBudget {
                    max_objects: 1,
                    max_bytes: u64::MAX,
                },
            ),
            Err(WriteError::Budget {
                resource: WriteResource::Objects,
                ..
            })
        ));
        assert!(matches!(
            encode_expr_region(
                &expression,
                header(),
                WriteBudget {
                    max_objects: u64::MAX,
                    max_bytes: format::OLEAN_HEADER_SIZE as u64 + 8,
                },
            ),
            Err(WriteError::Budget {
                resource: WriteResource::Bytes,
                ..
            })
        ));

        let metadata = KVMap::from_entries(vec![(
            name("syntax"),
            DataValue::OfSyntax(fln_core::options::SyntaxHandle(7)),
        )]);
        let expression = Expr::mdata(metadata, Expr::bvar(0).expect("body"));
        assert!(matches!(
            encode_expr_region(&expression, header(), WriteBudget::default()),
            Err(WriteError::Unsupported {
                what: "opaque SyntaxHandle has no serializable arena payload"
            })
        ));
    }

    #[test]
    fn deep_expression_encoding_and_decoding_fit_a_small_thread_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                let leaf = Expr::bvar(0).expect("leaf");
                let mut expression = leaf.clone();
                for _ in 0..12_000 {
                    expression = Expr::app(expression, leaf.clone());
                }
                let encoded = encode_expr_region(
                    &expression,
                    header(),
                    WriteBudget {
                        max_objects: 20_000,
                        max_bytes: 2 * 1024 * 1024,
                    },
                )
                .expect("encode");
                let view = OleanView::parse(&encoded.bytes).expect("header");
                let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
                assert_eq!(
                    decoder.decode_expr(encoded.root).expect("decode"),
                    expression
                );
            })
            .expect("spawn")
            .join()
            .expect("small-stack writer");
    }

    #[test]
    fn header_contract_rejects_unratified_or_ambiguous_values() {
        let expression = Expr::bvar(0).expect("expression");
        let mut invalid = header();
        invalid.version = 255;
        assert!(matches!(
            encode_expr_region(&expression, invalid, WriteBudget::default()),
            Err(WriteError::Contract {
                what: "header version is outside the generated accepted set"
            })
        ));
        invalid = header();
        invalid.base_addr += 8;
        assert!(matches!(
            encode_expr_region(&expression, invalid, WriteBudget::default()),
            Err(WriteError::Contract {
                what: "base address violates generated region alignment"
            })
        ));
    }
}
