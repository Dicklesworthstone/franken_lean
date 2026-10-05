//! The independent checker's own reading of `.olean` artifacts (bead
//! `franken_lean-z8j.1.14`).
//!
//! K1 judges declarations decoded by `fln-olean`. Until this module, the checker
//! judged the same decoded values, re-encoded into its wire format, so a decode
//! defect (a misread binder, level, literal or projection index) reached both
//! seats identically and the council could not see it. This reader goes from the
//! artifact's bytes straight to the checker's own term representation. It is
//! written from the pinned Reference only, never from `fln-olean`:
//! - the compacted region: `vendor/lean4-src/src/runtime/compact.cpp`, whose v2
//!   payload is a root word followed by objects whose pointers are absolute
//!   against the header's `base_addr`;
//! - the object layout: `vendor/lean4-src/src/include/lean/lean.h`, an 8-byte
//!   header (`m_rc`, `m_cs_sz`, `m_other`, `m_tag`), object fields, then scalars;
//! - the declarations: `Lean/Environment.lean` (`ModuleData`),
//!   `Lean/Declaration.lean`, `Lean/Expr.lean`, `Lean/Level.lean` and
//!   `Lean/Data/KVMap.lean`.
//!
//! Lean erases a structure with a single relevant field to that field, so `FVarId`,
//! `MVarId`, `LMVarId` and `KVMap` are read as their one field. A constructor with
//! no fields is a boxed scalar (`lean_box(tag)`). Cached `Expr.Data`, `Level.Data`
//! and `Name.hash` words are not read: they derive from the term, and the term is
//! what this reading compares.
//!
//! Both framings the pinned loader accepts are read (module.cpp:130-140, 492). In
//! v2 the compacted data follows the header directly; v3 puts a `size_t data_size`
//! there, the data at offset 96, and a closure-relocation trailer after the data.
//! Every pointer must land inside some part's data. Closures only occur in v3
//! trailers' referents, never in the declarations read here.
use crate::environment::{
    ConstantDeclaration, ConstantEntry, ConstantKind, ConstantSafety, ConstructorDeclaration,
    DefinitionBody, DefinitionSafety, InductiveDeclaration, QuotientKind, RecursorDeclaration,
    RecursorRule, ReducibilityHint,
};
use crate::wire::{
    BinderStyle, ExprId, ExprNode, LevelId, LevelNode, MAX_BVAR_INDEX, MAX_LEVEL_DEPTH,
    MetadataValue, NamePart, WireExpr, WireName,
};
use std::collections::HashMap;

const MAGIC: &[u8; 5] = b"olean";
/// `sizeof(olean_header)` on LP64: marker, version, flags, version string, githash,
/// base address (module.cpp:107-141).
const HEADER_BYTES: usize = 5 + 1 + 1 + 33 + 40 + 8;
const BASE_ADDR_AT: usize = 5 + 1 + 1 + 33 + 40;
const OBJECT_HEADER: usize = 8;

// lean.h object categories.
const TAG_ARRAY: u8 = 246;
const TAG_STRING: u8 = 249;
const TAG_MPZ: u8 = 250;

/// Why the checker could not read an artifact. None of these is a verdict about
/// the declarations; the council treats an unread artifact as no independent answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OleanReadError {
    /// The fixed header or framing is malformed.
    Header(&'static str),
    /// A framing version the pinned loader does not accept: refused, not guessed at.
    UnsupportedVersion(u8),
    /// A pointer that lands in no part's payload, or not on a word boundary.
    Pointer(u64),
    /// An object whose shape is not the structure being read.
    Shape { address: u64, what: &'static str },
    /// A number that does not fit the checker's field for it.
    Overflow { address: u64, what: &'static str },
    /// The object budget ran out.
    Budget { visited: u64 },
}

impl std::fmt::Display for OleanReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Header(what) => write!(f, "artifact header: {what}"),
            Self::UnsupportedVersion(version) => {
                write!(f, "artifact framing version {version} is not read")
            }
            Self::Pointer(pointer) => write!(f, "pointer {pointer:#x} lands in no payload"),
            Self::Shape { address, what } => write!(f, "object at {address:#x}: {what}"),
            Self::Overflow { address, what } => {
                write!(f, "object at {address:#x}: {what} does not fit")
            }
            Self::Budget { visited } => write!(f, "object budget exhausted after {visited}"),
        }
    }
}

impl std::error::Error for OleanReadError {}

type Read<T> = Result<T, OleanReadError>;

/// One part of a module chain: its bytes, base address, and the file offsets that
/// bound its compacted data, whose first word is the root pointer.
struct Part<'a> {
    bytes: &'a [u8],
    base: u64,
    data_start: usize,
    data_end: usize,
}

/// Where a part's compacted data lies, by framing version.
fn data_extent(bytes: &[u8]) -> Read<(usize, usize)> {
    match bytes[5] {
        2 => Ok((HEADER_BYTES, bytes.len())),
        3 => {
            let size = bytes
                .get(HEADER_BYTES..HEADER_BYTES + 8)
                .and_then(|word| word.try_into().ok())
                .map(u64::from_le_bytes)
                .ok_or(OleanReadError::Header("v3 data size is missing"))?;
            let start = HEADER_BYTES + 8;
            let end = usize::try_from(size)
                .ok()
                .and_then(|size| start.checked_add(size))
                .filter(|end| *end <= bytes.len())
                .ok_or(OleanReadError::Header("v3 data runs past the file"))?;
            Ok((start, end))
        }
        version => Err(OleanReadError::UnsupportedVersion(version)),
    }
}

/// Where a pointer lands: the part and the byte offset within it.
#[derive(Clone, Copy)]
struct At {
    part: usize,
    offset: usize,
}

/// A bounded reader over a chain of compacted regions. The last part is the one
/// whose `ModuleData` is read; earlier parts are the regions its pointers may reach.
///
/// The budget is per declaration. A checker term is its own arena, so a subterm
/// two declarations share is read once for each, exactly as the checker holds it;
/// a module-wide count would refuse a module for sharing well. Names are immutable
/// and shared module-wide.
pub struct OleanReader<'a> {
    parts: Vec<Part<'a>>,
    max_objects: u64,
    visited: u64,
    names: HashMap<u64, WireName>,
    expr_memo: HashMap<u64, ExprId>,
    level_memo: HashMap<u64, LevelId>,
}

/// The constants one artifact chain declares, as the checker reads them.
#[derive(Debug, Clone)]
pub struct OleanReading {
    pub constants: Vec<ConstantEntry>,
}

impl<'a> OleanReader<'a> {
    /// `parts` in load order: `[X.olean]`, or `[X.olean, X.olean.server,
    /// X.olean.private]` for a module-system chain.
    pub fn new(parts: &[&'a [u8]], max_objects: u64) -> Read<Self> {
        if parts.is_empty() {
            return Err(OleanReadError::Header("no artifact part"));
        }
        let mut read = Vec::with_capacity(parts.len());
        for bytes in parts {
            if bytes.len() < HEADER_BYTES + 8 {
                return Err(OleanReadError::Header("shorter than its fixed header"));
            }
            if &bytes[..5] != MAGIC {
                return Err(OleanReadError::Header("marker is not `olean`"));
            }
            let (data_start, data_end) = data_extent(bytes)?;
            if data_end < data_start + 8 {
                return Err(OleanReadError::Header("no root word"));
            }
            let base = u64::from_le_bytes(
                bytes[BASE_ADDR_AT..BASE_ADDR_AT + 8]
                    .try_into()
                    .map_err(|_| OleanReadError::Header("base address"))?,
            );
            if base.checked_add(bytes.len() as u64).is_none() {
                return Err(OleanReadError::Header("base address wraps"));
            }
            read.push(Part {
                bytes,
                base,
                data_start,
                data_end,
            });
        }
        Ok(Self {
            parts: read,
            max_objects,
            visited: 0,
            names: HashMap::new(),
            expr_memo: HashMap::new(),
            level_memo: HashMap::new(),
        })
    }

    fn charge(&mut self) -> Read<()> {
        self.visited = self.visited.saturating_add(1);
        if self.visited > self.max_objects {
            return Err(OleanReadError::Budget {
                visited: self.visited,
            });
        }
        Ok(())
    }

    fn is_scalar(pointer: u64) -> bool {
        pointer & 1 == 1
    }

    fn unbox(pointer: u64) -> u64 {
        pointer >> 1
    }

    /// Resolve an absolute pointer into some part's payload.
    fn locate(&self, pointer: u64) -> Read<At> {
        if !pointer.is_multiple_of(8) {
            return Err(OleanReadError::Pointer(pointer));
        }
        for (part, region) in self.parts.iter().enumerate() {
            let Some(offset) = pointer.checked_sub(region.base) else {
                continue;
            };
            let Ok(offset) = usize::try_from(offset) else {
                continue;
            };
            if offset >= region.data_start + 8 && offset + OBJECT_HEADER <= region.data_end {
                return Ok(At { part, offset });
            }
        }
        Err(OleanReadError::Pointer(pointer))
    }

    /// Bytes of the object at `at`, which must lie inside its part's data.
    fn bytes(&self, at: At, start: usize, len: usize) -> Read<&'a [u8]> {
        let part = &self.parts[at.part];
        let region = &part.bytes[..part.data_end];
        let begin = at
            .offset
            .checked_add(start)
            .ok_or(OleanReadError::Header("offset overflow"))?;
        let end = begin
            .checked_add(len)
            .ok_or(OleanReadError::Header("offset overflow"))?;
        region.get(begin..end).ok_or(OleanReadError::Shape {
            address: self.address(at),
            what: "object runs past its part",
        })
    }

    fn word(&self, at: At, start: usize) -> Read<u64> {
        let (words, _) = self.bytes(at, start, 8)?.as_chunks::<8>();
        words
            .first()
            .map(|word| u64::from_le_bytes(*word))
            .ok_or(OleanReadError::Shape {
                address: self.address(at),
                what: "a word field",
            })
    }

    fn address(&self, at: At) -> u64 {
        self.parts[at.part].base + at.offset as u64
    }

    /// `(tag, number of object fields, stored size)` of the object at `pointer`, charged
    /// to the budget.
    fn object(&mut self, pointer: u64) -> Read<(At, u8, u8, u16)> {
        self.charge()?;
        self.revisit(pointer)
    }

    /// [`Self::object`] for an object this traversal already charged: a term's second
    /// visit, which builds the node its first visit expanded.
    fn revisit(&self, pointer: u64) -> Read<(At, u8, u8, u16)> {
        if Self::is_scalar(pointer) {
            return Err(OleanReadError::Shape {
                address: pointer,
                what: "a boxed scalar where an object belongs",
            });
        }
        let at = self.locate(pointer)?;
        let header = self.bytes(at, 0, OBJECT_HEADER)?;
        let size = u16::from_le_bytes([header[4], header[5]]);
        Ok((at, header[7], header[6], size))
    }

    /// A constructor object with exactly `fields` object fields and tag `tag`.
    fn constructor(&mut self, pointer: u64, tag: u8, fields: u8, what: &'static str) -> Read<At> {
        let (at, found_tag, found_fields, _) = self.object(pointer)?;
        if found_tag != tag || found_fields != fields {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what,
            });
        }
        Ok(at)
    }

    fn field(&self, at: At, index: usize) -> Read<u64> {
        self.word(at, OBJECT_HEADER + 8 * index)
    }

    /// The scalar byte `index` after `fields` object fields.
    fn scalar_u8(&self, at: At, fields: usize, index: usize) -> Read<u8> {
        Ok(self.bytes(at, OBJECT_HEADER + 8 * fields + index, 1)?[0])
    }

    fn bool(&self, at: At, fields: usize, index: usize, what: &'static str) -> Read<bool> {
        match self.scalar_u8(at, fields, index)? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(OleanReadError::Shape {
                address: self.address(at),
                what,
            }),
        }
    }

    /// A `String` object: `m_size` counts the bytes with the NUL (lean.h).
    fn string(&mut self, pointer: u64) -> Read<String> {
        let (at, tag, _, _) = self.object(pointer)?;
        if tag != TAG_STRING {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "not a String",
            });
        }
        let size = usize::try_from(self.word(at, 8)?).map_err(|_| OleanReadError::Overflow {
            address: self.address(at),
            what: "string size",
        })?;
        if size == 0 {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "string without its NUL",
            });
        }
        let content = self.bytes(at, 32, size)?;
        if content[size - 1] != 0 {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "string without its NUL",
            });
        }
        std::str::from_utf8(&content[..size - 1])
            .map(str::to_owned)
            .map_err(|_| OleanReadError::Shape {
                address: self.address(at),
                what: "string is not UTF-8",
            })
    }

    /// An `Array` object's element words.
    fn array(&mut self, pointer: u64) -> Read<Vec<u64>> {
        let (at, tag, _, _) = self.object(pointer)?;
        if tag != TAG_ARRAY {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "not an Array",
            });
        }
        let size = usize::try_from(self.word(at, 8)?).map_err(|_| OleanReadError::Overflow {
            address: self.address(at),
            what: "array size",
        })?;
        let bytes = self.bytes(
            at,
            24,
            size.checked_mul(8).ok_or(OleanReadError::Overflow {
                address: self.address(at),
                what: "array size",
            })?,
        )?;
        Ok(bytes
            .as_chunks::<8>()
            .0
            .iter()
            .map(|word| u64::from_le_bytes(*word))
            .collect())
    }

    /// A `List`'s element words: `nil` is `box(0)`, `cons` is tag 1 with two fields.
    fn list(&mut self, mut pointer: u64) -> Read<Vec<u64>> {
        let mut elements = Vec::new();
        loop {
            if Self::is_scalar(pointer) {
                if Self::unbox(pointer) != 0 {
                    return Err(OleanReadError::Shape {
                        address: pointer,
                        what: "a scalar List other than nil",
                    });
                }
                return Ok(elements);
            }
            let at = self.constructor(pointer, 1, 2, "List.cons")?;
            elements.push(self.field(at, 0)?);
            pointer = self.field(at, 1)?;
        }
    }

    /// A `Nat`: a boxed scalar, or an mpz object whose limbs follow its
    /// `__mpz_struct` (compact.cpp `insert_mpz`, GMP build). Limbs little-endian,
    /// trailing zeros stripped, so zero is no limbs.
    fn nat(&mut self, pointer: u64) -> Read<Vec<u64>> {
        if Self::is_scalar(pointer) {
            let value = Self::unbox(pointer);
            return Ok(if value == 0 { Vec::new() } else { vec![value] });
        }
        let (negative, mut limbs) = self.mpz(pointer)?;
        if negative {
            return Err(OleanReadError::Shape {
                address: pointer,
                what: "a negative Nat",
            });
        }
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
        Ok(limbs)
    }

    fn mpz(&mut self, pointer: u64) -> Read<(bool, Vec<u64>)> {
        let (at, tag, _, _) = self.object(pointer)?;
        if tag != TAG_MPZ {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "neither a boxed number nor an mpz",
            });
        }
        let header = self.bytes(at, 8, 8)?;
        let size = i32::from_le_bytes([header[4], header[5], header[6], header[7]]);
        let count = size.unsigned_abs() as usize;
        let data = self.word(at, 16)?;
        // The compactor points `_mp_d` at the limbs it wrote right after the struct.
        if data != self.address(at) + 24 {
            return Err(OleanReadError::Shape {
                address: self.address(at),
                what: "mpz limbs are not inline",
            });
        }
        let bytes = self.bytes(
            at,
            24,
            count.checked_mul(8).ok_or(OleanReadError::Overflow {
                address: self.address(at),
                what: "mpz limb count",
            })?,
        )?;
        let limbs = bytes
            .as_chunks::<8>()
            .0
            .iter()
            .map(|word| u64::from_le_bytes(*word))
            .collect();
        Ok((size < 0, limbs))
    }

    fn nat_u64(&mut self, pointer: u64, what: &'static str) -> Read<u64> {
        match self.nat(pointer)?.as_slice() {
            [] => Ok(0),
            [value] => Ok(*value),
            _ => Err(OleanReadError::Overflow {
                address: pointer,
                what,
            }),
        }
    }

    fn nat_u32(&mut self, pointer: u64, what: &'static str) -> Read<u32> {
        u32::try_from(self.nat_u64(pointer, what)?).map_err(|_| OleanReadError::Overflow {
            address: pointer,
            what,
        })
    }

    /// An `Int`: small values are boxed as a 32-bit signed number, larger ones are
    /// an mpz (lean.h `lean_int64_to_int`, `lean_scalar_to_int`).
    fn int(&mut self, pointer: u64) -> Read<i64> {
        if Self::is_scalar(pointer) {
            return Ok(i64::from((pointer >> 1) as u32 as i32));
        }
        let (negative, limbs) = self.mpz(pointer)?;
        let magnitude = match limbs.as_slice() {
            [] => 0,
            [limb] => *limb,
            _ => {
                return Err(OleanReadError::Overflow {
                    address: pointer,
                    what: "Int",
                });
            }
        };
        if negative {
            0i64.checked_sub_unsigned(magnitude)
                .ok_or(OleanReadError::Overflow {
                    address: pointer,
                    what: "Int",
                })
        } else {
            i64::try_from(magnitude).map_err(|_| OleanReadError::Overflow {
                address: pointer,
                what: "Int",
            })
        }
    }

    /// A `Name`: `anonymous` is `box(0)`; `str` (tag 1) and `num` (tag 2) carry the
    /// prefix and the component, then the cached hash, which is not read.
    pub(crate) fn name(&mut self, pointer: u64) -> Read<WireName> {
        let mut links = Vec::new();
        let mut cursor = pointer;
        let base = loop {
            if Self::is_scalar(cursor) {
                if Self::unbox(cursor) != 0 {
                    return Err(OleanReadError::Shape {
                        address: cursor,
                        what: "a scalar Name other than anonymous",
                    });
                }
                break Vec::new();
            }
            if let Some(known) = self.names.get(&cursor) {
                break known.parts().to_vec();
            }
            let (at, tag, fields, _) = self.object(cursor)?;
            if !(tag == 1 || tag == 2) || fields != 2 {
                return Err(OleanReadError::Shape {
                    address: self.address(at),
                    what: "Name.str or Name.num",
                });
            }
            links.push((cursor, at, tag));
            cursor = self.field(at, 0)?;
        };
        let mut parts = base;
        for (pointer, at, tag) in links.into_iter().rev() {
            let component = self.field(at, 1)?;
            parts.push(if tag == 1 {
                NamePart::Text(self.string(component)?)
            } else {
                NamePart::Numeric {
                    value: self.nat_u64(component, "Name.num component")?,
                    overflowed: false,
                }
            });
            self.names
                .insert(pointer, WireName::from_parts(parts.clone()));
        }
        Ok(WireName::from_parts(parts))
    }

    fn names(&mut self, pointer: u64) -> Read<Vec<WireName>> {
        let elements = self.list(pointer)?;
        elements.into_iter().map(|p| self.name(p)).collect()
    }

    /// The constants of the chain's last part, in the order its `ModuleData`
    /// stores them.
    pub fn constants(mut self) -> Read<OleanReading> {
        let primary = self.parts.len() - 1;
        let root = {
            let region = &self.parts[primary];
            u64::from_le_bytes(
                region.bytes[region.data_start..region.data_start + 8]
                    .try_into()
                    .map_err(|_| OleanReadError::Header("root word"))?,
            )
        };
        // ModuleData: imports, constNames, constants, extraConstNames, entries;
        // then the isModule byte (Environment.lean:109).
        let module = self.constructor(root, 0, 5, "ModuleData")?;
        let constants = self.field(module, 2)?;
        let mut entries = Vec::new();
        for info in self.array(constants)? {
            self.visited = 0;
            entries.push(self.constant(info)?);
        }
        Ok(OleanReading { constants: entries })
    }

    /// One `ConstantInfo`: a tag-per-kind wrapper around its value structure
    /// (Declaration.lean). Each value begins with its `ConstantVal` (name,
    /// universe parameters, type).
    fn constant(&mut self, pointer: u64) -> Read<ConstantEntry> {
        let (wrapper, kind, fields, _) = self.object(pointer)?;
        if fields != 1 || kind > 7 {
            return Err(OleanReadError::Shape {
                address: self.address(wrapper),
                what: "ConstantInfo",
            });
        }
        // Object fields of each value structure; its scalars follow them.
        let object_fields: u8 = match kind {
            0 | 4 => 1,
            1 => 4,
            2 | 3 => 3,
            5 => 6,
            6 => 5,
            _ => 7,
        };
        let value = self.field(wrapper, 0)?;
        let at = self.constructor(value, 0, object_fields, "a declaration value structure")?;
        let header = self.constructor(self.field(at, 0)?, 0, 3, "ConstantVal")?;
        let name = self.name(self.field(header, 0)?)?;
        let level_parameters = self.names(self.field(header, 1)?)?;
        let type_ = self.expr(self.field(header, 2)?)?;
        let n = usize::from(object_fields);
        let safety = |unsafe_: bool| {
            if unsafe_ {
                ConstantSafety::Unsafe
            } else {
                ConstantSafety::Safe
            }
        };
        let declaration = match kind {
            0 => ConstantDeclaration::header(
                level_parameters,
                type_,
                ConstantKind::Axiom,
                safety(self.bool(at, n, 0, "AxiomVal.isUnsafe")?),
            ),
            1 => {
                let body = self.expr(self.field(at, 1)?)?;
                let hint = self.hints(self.field(at, 2)?)?;
                let all = self.names(self.field(at, 3)?)?;
                let definition_safety = match self.scalar_u8(at, n, 0)? {
                    0 => DefinitionSafety::Unsafe,
                    1 => DefinitionSafety::Safe,
                    2 => DefinitionSafety::Partial,
                    _ => {
                        return Err(OleanReadError::Shape {
                            address: self.address(at),
                            what: "DefinitionSafety",
                        });
                    }
                };
                ConstantDeclaration::definition(
                    level_parameters,
                    type_,
                    safety(definition_safety == DefinitionSafety::Unsafe),
                    DefinitionBody::new(body, hint, definition_safety, all),
                )
            }
            2 => {
                let body = self.expr(self.field(at, 1)?)?;
                let all = self.names(self.field(at, 2)?)?;
                ConstantDeclaration::theorem(level_parameters, type_, body, all)
            }
            3 => {
                let body = self.expr(self.field(at, 1)?)?;
                let all = self.names(self.field(at, 2)?)?;
                let unsafe_ = self.bool(at, n, 0, "OpaqueVal.isUnsafe")?;
                ConstantDeclaration::opaque(level_parameters, type_, safety(unsafe_), body, all)
            }
            4 => {
                let kind = match self.scalar_u8(at, n, 0)? {
                    0 => QuotientKind::Type,
                    1 => QuotientKind::Constructor,
                    2 => QuotientKind::Lift,
                    3 => QuotientKind::Induction,
                    _ => {
                        return Err(OleanReadError::Shape {
                            address: self.address(at),
                            what: "QuotKind",
                        });
                    }
                };
                ConstantDeclaration::quotient(level_parameters, type_, kind)
            }
            5 => {
                let num_parameters = self.nat_u32(self.field(at, 1)?, "numParams")?;
                let num_indices = self.nat_u32(self.field(at, 2)?, "numIndices")?;
                let all = self.names(self.field(at, 3)?)?;
                let constructors = self.names(self.field(at, 4)?)?;
                let num_nested = self.nat_u32(self.field(at, 5)?, "numNested")?;
                let recursive = self.bool(at, n, 0, "InductiveVal.isRec")?;
                let unsafe_ = self.bool(at, n, 1, "InductiveVal.isUnsafe")?;
                let reflexive = self.bool(at, n, 2, "InductiveVal.isReflexive")?;
                ConstantDeclaration::inductive(
                    level_parameters,
                    type_,
                    safety(unsafe_),
                    InductiveDeclaration::new(
                        num_parameters,
                        num_indices,
                        all,
                        constructors,
                        num_nested,
                        recursive,
                        reflexive,
                    ),
                )
            }
            6 => {
                let inductive = self.name(self.field(at, 1)?)?;
                let index = self.nat_u32(self.field(at, 2)?, "cidx")?;
                let num_parameters = self.nat_u32(self.field(at, 3)?, "numParams")?;
                let num_fields = self.nat_u32(self.field(at, 4)?, "numFields")?;
                let unsafe_ = self.bool(at, n, 0, "ConstructorVal.isUnsafe")?;
                ConstantDeclaration::constructor(
                    level_parameters,
                    type_,
                    safety(unsafe_),
                    ConstructorDeclaration::new(inductive, index, num_parameters, num_fields),
                )
            }
            _ => {
                let all = self.names(self.field(at, 1)?)?;
                let num_parameters = self.nat_u32(self.field(at, 2)?, "numParams")?;
                let num_indices = self.nat_u32(self.field(at, 3)?, "numIndices")?;
                let num_motives = self.nat_u32(self.field(at, 4)?, "numMotives")?;
                let num_minors = self.nat_u32(self.field(at, 5)?, "numMinors")?;
                let mut rules = Vec::new();
                for rule in self.list(self.field(at, 6)?)? {
                    let rule = self.constructor(rule, 0, 3, "RecursorRule")?;
                    let constructor = self.name(self.field(rule, 0)?)?;
                    let num_fields = self.nat_u32(self.field(rule, 1)?, "nfields")?;
                    let rhs = self.expr(self.field(rule, 2)?)?;
                    rules.push(RecursorRule::new(constructor, num_fields, rhs));
                }
                let k = self.bool(at, n, 0, "RecursorVal.k")?;
                let unsafe_ = self.bool(at, n, 1, "RecursorVal.isUnsafe")?;
                ConstantDeclaration::recursor(
                    level_parameters,
                    type_,
                    safety(unsafe_),
                    RecursorDeclaration::new(
                        all,
                        num_parameters,
                        num_indices,
                        num_motives,
                        num_minors,
                        rules,
                        k,
                    ),
                )
            }
        };
        Ok(ConstantEntry::new(name, declaration))
    }

    /// `ReducibilityHints`: `opaque` and `abbrev` are boxed; `regular` (tag 2) has
    /// no object fields and a `UInt32` height.
    fn hints(&mut self, pointer: u64) -> Read<ReducibilityHint> {
        if Self::is_scalar(pointer) {
            return match Self::unbox(pointer) {
                0 => Ok(ReducibilityHint::Opaque),
                1 => Ok(ReducibilityHint::Abbrev),
                _ => Err(OleanReadError::Shape {
                    address: pointer,
                    what: "ReducibilityHints",
                }),
            };
        }
        let at = self.constructor(pointer, 2, 0, "ReducibilityHints.regular")?;
        let (height, _) = self.bytes(at, OBJECT_HEADER, 4)?.as_chunks::<4>();
        height
            .first()
            .map(|height| ReducibilityHint::Regular(u32::from_le_bytes(*height)))
            .ok_or(OleanReadError::Shape {
                address: self.address(at),
                what: "ReducibilityHints.regular height",
            })
    }

    /// One `Level` into `arena`, shared by address within the term being read.
    fn level(
        &mut self,
        root: u64,
        arena: &mut Vec<LevelNode>,
        depths: &mut Vec<u32>,
        memo: &mut HashMap<u64, LevelId>,
    ) -> Read<LevelId> {
        let mut stack = vec![(root, false)];
        while let Some((pointer, expanded)) = stack.pop() {
            if memo.contains_key(&pointer) {
                continue;
            }
            if Self::is_scalar(pointer) {
                if Self::unbox(pointer) != 0 {
                    return Err(OleanReadError::Shape {
                        address: pointer,
                        what: "a scalar Level other than zero",
                    });
                }
                let id = push_level(arena, depths, LevelNode::Zero, 0, pointer)?;
                memo.insert(pointer, id);
                continue;
            }
            let (at, tag, fields, _) = if expanded {
                self.revisit(pointer)?
            } else {
                self.object(pointer)?
            };
            let children: &[usize] = match (tag, fields) {
                (1, 1) => &[0],
                (2, 2) | (3, 2) => &[0, 1],
                (4, 1) | (5, 1) => &[],
                _ => {
                    return Err(OleanReadError::Shape {
                        address: self.address(at),
                        what: "Level",
                    });
                }
            };
            let child_pointers = self.children(at, children)?;
            let child_pointers = &child_pointers[..children.len()];
            if !expanded {
                stack.push((pointer, true));
                for child in child_pointers.iter().rev() {
                    if !memo.contains_key(child) {
                        stack.push((*child, false));
                    }
                }
                continue;
            }
            let get = |p: &u64| memo.get(p).copied().ok_or(OleanReadError::Pointer(*p));
            let depth_of = |id: LevelId| depths.get(id.index()).copied().unwrap_or(0);
            let (node, depth) = match tag {
                1 => {
                    let child = get(&child_pointers[0])?;
                    (LevelNode::Succ(child), depth_of(child).saturating_add(1))
                }
                2 | 3 => {
                    let left = get(&child_pointers[0])?;
                    let right = get(&child_pointers[1])?;
                    let depth = depth_of(left).max(depth_of(right)).saturating_add(1);
                    if tag == 2 {
                        (LevelNode::Max(left, right), depth)
                    } else {
                        (LevelNode::IMax(left, right), depth)
                    }
                }
                4 => (LevelNode::Parameter(self.name(self.field(at, 0)?)?), 0),
                _ => (LevelNode::Meta(self.name(self.field(at, 0)?)?), 0),
            };
            let id = push_level(arena, depths, node, depth, pointer)?;
            memo.insert(pointer, id);
        }
        memo.get(&root)
            .copied()
            .ok_or(OleanReadError::Pointer(root))
    }

    /// One `Expr` as a checker term, shared by address: children are pushed
    /// before their parents and every node but the root feeds a later one.
    pub(crate) fn expr(&mut self, root: u64) -> Read<WireExpr> {
        let mut nodes: Vec<ExprNode> = Vec::new();
        let mut levels: Vec<LevelNode> = Vec::new();
        let mut depths: Vec<u32> = Vec::new();
        // The memos are per term, so they are emptied here; keeping their capacity
        // across terms spares an allocation per term.
        let mut memo = std::mem::take(&mut self.expr_memo);
        memo.clear();
        let mut level_memo = std::mem::take(&mut self.level_memo);
        level_memo.clear();
        let mut stack = vec![(root, false)];
        while let Some((pointer, expanded)) = stack.pop() {
            if memo.contains_key(&pointer) {
                continue;
            }
            let (at, tag, fields, _) = if expanded {
                self.revisit(pointer)?
            } else {
                self.object(pointer)?
            };
            // Object fields per constructor (Expr.lean), and which are terms.
            let (expected, children): (u8, &[usize]) = match tag {
                0..=3 => (1, &[]),
                4 => (2, &[]),
                5 => (2, &[0, 1]),
                6 | 7 => (3, &[1, 2]),
                8 => (4, &[1, 2, 3]),
                9 => (1, &[]),
                10 => (2, &[1]),
                11 => (3, &[2]),
                _ => {
                    return Err(OleanReadError::Shape {
                        address: self.address(at),
                        what: "Expr constructor",
                    });
                }
            };
            if fields != expected {
                return Err(OleanReadError::Shape {
                    address: self.address(at),
                    what: "Expr field count",
                });
            }
            let child_pointers = self.children(at, children)?;
            let child_pointers = &child_pointers[..children.len()];
            if !expanded {
                stack.push((pointer, true));
                for child in child_pointers.iter().rev() {
                    if !memo.contains_key(child) {
                        stack.push((*child, false));
                    }
                }
                continue;
            }
            let child = |i: usize| -> Read<ExprId> {
                memo.get(&child_pointers[i])
                    .copied()
                    .ok_or(OleanReadError::Pointer(child_pointers[i]))
            };
            let n = usize::from(fields);
            let node = match tag {
                0 => {
                    let index = self.nat_u32(self.field(at, 0)?, "bvar index")?;
                    if index > MAX_BVAR_INDEX {
                        return Err(OleanReadError::Overflow {
                            address: self.address(at),
                            what: "bvar index",
                        });
                    }
                    ExprNode::Bound { index }
                }
                1 => ExprNode::Free {
                    name: self.name(self.field(at, 0)?)?,
                },
                2 => ExprNode::Meta {
                    name: self.name(self.field(at, 0)?)?,
                },
                3 => ExprNode::Sort {
                    level: self.level(
                        self.field(at, 0)?,
                        &mut levels,
                        &mut depths,
                        &mut level_memo,
                    )?,
                },
                4 => {
                    let name = self.name(self.field(at, 0)?)?;
                    let mut ids = Vec::new();
                    for level in self.list(self.field(at, 1)?)? {
                        ids.push(self.level(level, &mut levels, &mut depths, &mut level_memo)?);
                    }
                    ExprNode::Constant { name, levels: ids }
                }
                5 => ExprNode::Apply {
                    function: child(0)?,
                    argument: child(1)?,
                },
                6 | 7 => {
                    let binder_name = self.name(self.field(at, 0)?)?;
                    // Scalars: the `Data` word, then the binder info byte.
                    let style = match self.scalar_u8(at, n, 8)? {
                        0 => BinderStyle::Default,
                        1 => BinderStyle::Implicit,
                        2 => BinderStyle::StrictImplicit,
                        3 => BinderStyle::InstanceImplicit,
                        _ => {
                            return Err(OleanReadError::Shape {
                                address: self.address(at),
                                what: "BinderInfo",
                            });
                        }
                    };
                    let (binder_type, body) = (child(0)?, child(1)?);
                    if tag == 6 {
                        ExprNode::Lambda {
                            binder_name,
                            binder_type,
                            body,
                            style,
                        }
                    } else {
                        ExprNode::Forall {
                            binder_name,
                            binder_type,
                            body,
                            style,
                        }
                    }
                }
                8 => ExprNode::Let {
                    declaration_name: self.name(self.field(at, 0)?)?,
                    type_: child(0)?,
                    value: child(1)?,
                    body: child(2)?,
                    non_dependent: self.bool(at, n, 8, "letE nonDep")?,
                },
                9 => {
                    let literal = self.field(at, 0)?;
                    let (literal_at, literal_tag, literal_fields, _) = self.object(literal)?;
                    if literal_fields != 1 {
                        return Err(OleanReadError::Shape {
                            address: self.address(literal_at),
                            what: "Literal",
                        });
                    }
                    let payload = self.field(literal_at, 0)?;
                    match literal_tag {
                        0 => ExprNode::NatLiteral {
                            limbs_le: self.nat(payload)?,
                        },
                        1 => ExprNode::StringLiteral(self.string(payload)?),
                        _ => {
                            return Err(OleanReadError::Shape {
                                address: self.address(literal_at),
                                what: "Literal",
                            });
                        }
                    }
                }
                10 => ExprNode::Metadata {
                    entries: self.metadata(self.field(at, 0)?)?,
                    expression: child(0)?,
                },
                _ => ExprNode::Projection {
                    structure_name: self.name(self.field(at, 0)?)?,
                    index: self.nat_u64(self.field(at, 1)?, "projection index")?,
                    expression: child(0)?,
                },
            };
            if nodes.len() >= u32::MAX as usize {
                return Err(OleanReadError::Budget {
                    visited: self.visited,
                });
            }
            let id = ExprId::from_index(nodes.len()).ok_or(OleanReadError::Budget {
                visited: self.visited,
            })?;
            nodes.push(node);
            memo.insert(pointer, id);
        }
        let root = memo
            .get(&root)
            .copied()
            .ok_or(OleanReadError::Pointer(root))?;
        self.expr_memo = memo;
        self.level_memo = level_memo;
        Ok(WireExpr::from_parts(nodes, levels, root))
    }

    /// The object fields at `indices` (at most three), without allocating.
    fn children(&self, at: At, indices: &[usize]) -> Read<[u64; 3]> {
        let mut pointers = [0; 3];
        for (slot, &index) in pointers.iter_mut().zip(indices) {
            *slot = self.field(at, index)?;
        }
        Ok(pointers)
    }

    /// `MData` is a `KVMap`, erased to its `List (Name × DataValue)`.
    fn metadata(&mut self, pointer: u64) -> Read<Vec<(WireName, MetadataValue)>> {
        let mut entries = Vec::new();
        for pair in self.list(pointer)? {
            let pair = self.constructor(pair, 0, 2, "KVMap entry")?;
            let key = self.name(self.field(pair, 0)?)?;
            let value = self.field(pair, 1)?;
            let (at, tag, fields, _) = self.object(value)?;
            let value = match (tag, fields) {
                (0, 1) => MetadataValue::Text(self.string(self.field(at, 0)?)?),
                (1, 0) => MetadataValue::Bool(self.bool(at, 0, 0, "DataValue.ofBool")?),
                (2, 1) => MetadataValue::Name(self.name(self.field(at, 0)?)?),
                (3, 1) => MetadataValue::Nat(self.nat_u64(self.field(at, 0)?, "DataValue.ofNat")?),
                (4, 1) => MetadataValue::Int(self.int(self.field(at, 0)?)?),
                (5, 1) => {
                    // Syntax is not interpreted by either seat; it crosses as the
                    // location of its object: a boxed value's payload, the offset
                    // within the part being read, or the absolute address of an
                    // object in an earlier part.
                    let syntax = self.field(at, 0)?;
                    MetadataValue::Syntax(if Self::is_scalar(syntax) {
                        Self::unbox(syntax)
                    } else {
                        let found = self.locate(syntax)?;
                        if found.part == self.parts.len() - 1 {
                            found.offset as u64
                        } else {
                            syntax
                        }
                    })
                }
                _ => {
                    return Err(OleanReadError::Shape {
                        address: self.address(at),
                        what: "DataValue",
                    });
                }
            };
            entries.push((key, value));
        }
        Ok(entries)
    }
}

fn push_level(
    arena: &mut Vec<LevelNode>,
    depths: &mut Vec<u32>,
    node: LevelNode,
    depth: u32,
    at: u64,
) -> Read<LevelId> {
    if depth > MAX_LEVEL_DEPTH {
        return Err(OleanReadError::Overflow {
            address: at,
            what: "universe depth",
        });
    }
    let id = LevelId::from_index(arena.len()).ok_or(OleanReadError::Overflow {
        address: at,
        what: "universe arena",
    })?;
    arena.push(node);
    depths.push(depth);
    Ok(id)
}

/// Read the constants of one artifact chain (`[X.olean]` or `[X.olean,
/// X.olean.server, X.olean.private]`) with the checker's own decoder.
pub fn read_constants(parts: &[&[u8]], max_objects: u64) -> Read<OleanReading> {
    OleanReader::new(parts, max_objects)?.constants()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::{ExprId, LevelId};

    const BASE: u64 = 0x1000_0000;

    /// A compacted region assembled by hand from compact.cpp's v2 layout, so these tests
    /// hold the reader to the format itself rather than to any other decoder or writer.
    struct Region {
        bytes: Vec<u8>,
        data_start: usize,
    }

    impl Region {
        fn new() -> Self {
            Self::framed(2)
        }

        /// v3 framing: a `data_size` word after the header, the data at 96, and a
        /// (here empty) closure trailer after the data.
        fn v3() -> Self {
            Self::framed(3)
        }

        fn framed(version: u8) -> Self {
            let mut bytes = Vec::new();
            bytes.extend_from_slice(MAGIC);
            bytes.push(version);
            bytes.push(1);
            bytes.resize(BASE_ADDR_AT, 0);
            bytes.extend_from_slice(&BASE.to_le_bytes());
            if version == 3 {
                bytes.extend_from_slice(&0_u64.to_le_bytes());
            }
            let data_start = bytes.len();
            bytes.extend_from_slice(&0_u64.to_le_bytes());
            Region { bytes, data_start }
        }

        fn address(&self) -> u64 {
            BASE + self.bytes.len() as u64
        }

        fn header(&mut self, other: u8, tag: u8) {
            self.bytes.extend_from_slice(&0_i32.to_le_bytes());
            self.bytes.extend_from_slice(&1_u16.to_le_bytes());
            self.bytes.push(other);
            self.bytes.push(tag);
        }

        fn word(&mut self, word: u64) {
            self.bytes.extend_from_slice(&word.to_le_bytes());
        }

        fn pad(&mut self) {
            while !self.bytes.len().is_multiple_of(8) {
                self.bytes.push(0);
            }
        }

        /// A constructor object: its object fields, then its scalar bytes.
        fn ctor(&mut self, tag: u8, fields: &[u64], scalars: &[u8]) -> u64 {
            let at = self.address();
            self.header(u8::try_from(fields.len()).expect("few fields"), tag);
            for field in fields {
                self.word(*field);
            }
            self.bytes.extend_from_slice(scalars);
            self.pad();
            at
        }

        fn array(&mut self, elements: &[u64]) -> u64 {
            let at = self.address();
            self.header(0, TAG_ARRAY);
            self.word(elements.len() as u64);
            self.word(elements.len() as u64);
            for element in elements {
                self.word(*element);
            }
            at
        }

        fn string(&mut self, text: &str) -> u64 {
            let at = self.address();
            self.header(0, TAG_STRING);
            self.word(text.len() as u64 + 1);
            self.word(text.len() as u64 + 1);
            self.word(text.chars().count() as u64);
            self.bytes.extend_from_slice(text.as_bytes());
            self.bytes.push(0);
            self.pad();
            at
        }

        fn finish(mut self, root: u64) -> Vec<u8> {
            let start = self.data_start;
            self.bytes[start..start + 8].copy_from_slice(&root.to_le_bytes());
            if start != HEADER_BYTES {
                let size = (self.bytes.len() - start) as u64;
                self.bytes[HEADER_BYTES..start].copy_from_slice(&size.to_le_bytes());
                // num_closure_offsets = 0, num_libs = 0.
                self.bytes.extend_from_slice(&[0; 8]);
            }
            self.bytes
        }
    }

    fn boxed(value: u64) -> u64 {
        (value << 1) | 1
    }

    /// `axiom <name> : Prop` for each name, with `is_unsafe` as its scalar byte.
    fn axioms(names: &[&str], is_unsafe: u8) -> Vec<u8> {
        axioms_in(Region::new(), names, is_unsafe)
    }

    fn axioms_in(mut region: Region, names: &[&str], is_unsafe: u8) -> Vec<u8> {
        let mut infos = Vec::new();
        for name in names {
            let text = region.string(name);
            // Name.str [prefix, string] + cached hash; Expr.sort [Level.zero] + Data.
            let name = region.ctor(1, &[boxed(0), text], &0_u64.to_le_bytes());
            let prop = region.ctor(3, &[boxed(0)], &0_u64.to_le_bytes());
            let header = region.ctor(0, &[name, boxed(0), prop], &[]);
            let value = region.ctor(0, &[header], &[is_unsafe]);
            infos.push(region.ctor(0, &[value], &[]));
        }
        let constants = region.array(&infos);
        let empty = region.array(&[]);
        let module = region.ctor(0, &[empty, empty, constants, empty, empty], &[0]);
        region.finish(module)
    }

    fn expected_axiom(name: &str, safety: ConstantSafety) -> ConstantEntry {
        let prop = WireExpr::from_parts(
            vec![ExprNode::Sort {
                level: LevelId::from_index(0).expect("first level"),
            }],
            vec![LevelNode::Zero],
            ExprId::from_index(0).expect("first node"),
        );
        ConstantEntry::new(
            WireName::from_parts(vec![NamePart::Text(name.to_owned())]),
            ConstantDeclaration::header(Vec::new(), prop, ConstantKind::Axiom, safety),
        )
    }

    #[test]
    fn an_axiom_in_a_hand_assembled_region_reads_as_the_format_says() {
        let reading = read_constants(&[&axioms(&["A"], 0)], 1_000).expect("the region reads");
        assert_eq!(reading.constants.len(), 1);
        assert_eq!(
            reading.constants[0].reading_digest(),
            expected_axiom("A", ConstantSafety::Safe).reading_digest()
        );
    }

    #[test]
    fn a_flipped_scalar_changes_the_reading_and_an_impossible_one_is_refused() {
        let reading = read_constants(&[&axioms(&["A"], 1)], 1_000).expect("the region reads");
        let digest = reading.constants[0].reading_digest();
        assert_eq!(
            digest,
            expected_axiom("A", ConstantSafety::Unsafe).reading_digest()
        );
        assert_ne!(
            digest,
            expected_axiom("A", ConstantSafety::Safe).reading_digest()
        );
        assert!(matches!(
            read_constants(&[&axioms(&["A"], 2)], 1_000),
            Err(OleanReadError::Shape {
                what: "AxiomVal.isUnsafe",
                ..
            })
        ));
    }

    #[test]
    fn both_framings_the_pinned_loader_accepts_read_alike() {
        let v2 = read_constants(&[&axioms(&["A"], 0)], 1_000).expect("v2 reads");
        let v3 = read_constants(&[&axioms_in(Region::v3(), &["A"], 0)], 1_000).expect("v3 reads");
        assert_eq!(
            v2.constants[0].reading_digest(),
            v3.constants[0].reading_digest()
        );
        // A v3 data size reaching past the file is refused, and so is a pointer into
        // the trailer, which is not data.
        let mut long = axioms_in(Region::v3(), &["A"], 0);
        long[HEADER_BYTES..HEADER_BYTES + 8].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(matches!(
            read_constants(&[&long], 1_000),
            Err(OleanReadError::Header(_))
        ));
        let trailer = Region::v3();
        let past_data = BASE + trailer.bytes.len() as u64 + 8;
        assert_eq!(
            read_constants(&[&trailer.finish(past_data)], 1_000).err(),
            Some(OleanReadError::Pointer(past_data))
        );
    }

    #[test]
    fn framing_the_reader_does_not_implement_is_refused() {
        let good = axioms(&["A"], 0);
        let mut v4 = good.clone();
        v4[5] = 4;
        assert_eq!(
            read_constants(&[&v4], 1_000).err(),
            Some(OleanReadError::UnsupportedVersion(4))
        );
        let mut marker = good.clone();
        marker[0] = b'x';
        assert!(matches!(
            read_constants(&[&marker], 1_000),
            Err(OleanReadError::Header(_))
        ));
        assert!(matches!(
            read_constants(&[&good[..HEADER_BYTES]], 1_000),
            Err(OleanReadError::Header(_))
        ));
        assert!(matches!(
            read_constants(&[], 1_000),
            Err(OleanReadError::Header(_))
        ));
    }

    #[test]
    fn pointers_outside_every_part_and_scalars_in_object_slots_are_refused() {
        let outside = BASE + 1_000_000;
        assert_eq!(
            read_constants(&[&Region::new().finish(outside)], 1_000).err(),
            Some(OleanReadError::Pointer(outside))
        );
        let mut region = Region::new();
        let misaligned = region.address() + 4;
        assert_eq!(
            read_constants(&[&Region::new().finish(misaligned)], 1_000).err(),
            Some(OleanReadError::Pointer(misaligned))
        );
        let empty = region.array(&[]);
        let constants = region.array(&[boxed(7)]);
        let root = region.ctor(0, &[empty, empty, constants, empty, empty], &[0]);
        assert!(matches!(
            read_constants(&[&region.finish(root)], 1_000),
            Err(OleanReadError::Shape { .. })
        ));
        assert!(matches!(
            read_constants(&[&Region::new().finish(boxed(0))], 1_000),
            Err(OleanReadError::Shape { .. })
        ));
    }

    #[test]
    fn the_object_budget_binds_each_declaration_separately() {
        // Each axiom is six objects: the wrapper, its value, its ConstantVal, the Name,
        // the Name's string and the Sort. A module-wide count would refuse the pair.
        let two = axioms(&["A", "B"], 0);
        let reading = read_constants(&[&two], 6).expect("each declaration fits");
        assert_eq!(reading.constants.len(), 2);
        assert!(matches!(
            read_constants(&[&two], 5),
            Err(OleanReadError::Budget { .. })
        ));
    }
}
