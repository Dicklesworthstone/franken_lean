//! Grimoire's prototype region reader — the G0-1 ABI-resurrection spike (bead
//! franken_lean-y24, plan §22.1-1, feeds §6/§7.2).
//!
//! Parses a real `.olean` produced by the pinned Reference: fixed header,
//! compacted-region object graph, `ModuleData` traversal. Every decoded field
//! is driven by the GENERATED contract tables (`crate::format` for the header
//! and file laws, `fln_rt::abi` for the object model) — never hand-written
//! constants (Rule D5/D9).
//!
//! This is a pure by-value reader: stored pointers are interpreted as
//! `base_addr`-relative file offsets and every dereference is bounds- and
//! alignment-checked, so the reader needs no `unsafe` and no mmap-at-address.
//! Malformed input yields a typed [`RegionError`], never a panic and never a
//! silently-partial success (FL-INV-07 discipline), and traversal is
//! budgeted and iterative (no recursion), so hostile inputs cannot exhaust
//! the stack or run away.
//!
//! Unknown environment-extension payloads are preserved losslessly and
//! reported opaquely — walked for object-graph integrity, never interpreted.

use std::collections::HashSet;
use std::fmt;
use std::path::Path;

use fln_core::name::Name;
use fln_rt::abi;
use fln_unsafe_region::mapping::{MapError, RegionMapping};

use crate::format;

/// Typed failure of header parsing, pointer resolution, object decoding, or
/// budget enforcement. Malformed input must land here — never in a panic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RegionError {
    /// File shorter than the fixed header, or a read past the end.
    Truncated { wanted_end: u64, len: u64 },
    /// Magic bytes differ from the contract's `OLEAN_MAGIC`.
    BadMagic,
    /// Header version not in the contract's `OLEAN_ACCEPTED_VERSIONS`.
    UnsupportedVersion(u8),
    /// `base_addr` violates the contract's `REGION_ALIGN` law.
    MisalignedBase { base_addr: u64 },
    /// A stored pointer resolves outside the data region.
    PtrOutOfBounds { ptr: u64, resolved: i128 },
    /// A stored pointer is not 8-byte aligned.
    MisalignedPtr { ptr: u64 },
    /// A compacted object whose reference count is not the persistent 0.
    NonPersistentRc { offset: u64, rc: i32 },
    /// An object tag that must not appear in a compacted region.
    ForbiddenTag { offset: u64, tag: u8 },
    /// Closure objects are only legal in v3 regions.
    ClosureInV2 { offset: u64 },
    /// String object violating its own size/terminator/UTF-8 laws.
    StringIntegrity { offset: u64, reason: &'static str },
    /// Bignum object with an incoherent limb region.
    MpzIntegrity { offset: u64 },
    /// The traversal budget was exhausted — the graph is NOT validated.
    BudgetExhausted { visited: u64, budget: u64 },
    /// The region root does not have the shape the contract requires.
    RootShape { reason: &'static str },
    /// A semantic decode (Name, Import, pair) met an unexpected shape.
    DecodeShape { offset: u64, reason: &'static str },
}

impl fmt::Display for RegionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated { wanted_end, len } => {
                write!(f, "truncated: read to {wanted_end} in {len}-byte file")
            }
            Self::BadMagic => write!(f, "bad magic (not an olean file)"),
            Self::UnsupportedVersion(v) => write!(f, "unsupported olean version {v}"),
            Self::MisalignedBase { base_addr } => {
                write!(f, "base_addr {base_addr:#x} violates REGION_ALIGN")
            }
            Self::PtrOutOfBounds { ptr, resolved } => {
                write!(f, "pointer {ptr:#x} resolves out of bounds ({resolved})")
            }
            Self::MisalignedPtr { ptr } => write!(f, "pointer {ptr:#x} not 8-byte aligned"),
            Self::NonPersistentRc { offset, rc } => {
                write!(f, "object at {offset} has non-persistent rc {rc}")
            }
            Self::ForbiddenTag { offset, tag } => {
                write!(f, "forbidden object tag {tag} at {offset}")
            }
            Self::ClosureInV2 { offset } => {
                write!(f, "closure object at {offset} in a v2 region")
            }
            Self::StringIntegrity { offset, reason } => {
                write!(f, "string object at {offset}: {reason}")
            }
            Self::MpzIntegrity { offset } => write!(f, "mpz object at {offset} incoherent"),
            Self::BudgetExhausted { visited, budget } => {
                write!(
                    f,
                    "budget exhausted after {visited} objects (budget {budget})"
                )
            }
            Self::RootShape { reason } => write!(f, "root shape: {reason}"),
            Self::DecodeShape { offset, reason } => {
                write!(f, "decode at {offset}: {reason}")
            }
        }
    }
}

type RResult<T> = Result<T, RegionError>;

/// Map a shared-engine [`fln_rt::region::RegionFault`] into this codec's
/// [`RegionError`], shifting payload-relative offsets by `shift` (the file
/// offset where the payload begins) so diagnostics stay file-addressed.
fn shared_fault(
    fault: fln_rt::region::RegionFault,
    shift: u64,
    base_addr: u64,
    file_len: u64,
) -> RegionError {
    use fln_rt::region::RegionFault as F;
    match fault {
        F::Truncated { offset, wanted } => RegionError::Truncated {
            wanted_end: shift + offset as u64 + wanted as u64,
            len: file_len,
        },
        F::BadMagic => RegionError::BadMagic,
        F::UnsupportedVersion(v) => RegionError::UnsupportedVersion(v),
        F::MisalignedBase { base } => RegionError::MisalignedBase { base_addr: base },
        F::RaggedPayload { len } => RegionError::DecodeShape {
            offset: shift + len as u64,
            reason: "region payload not word-aligned",
        },
        F::NonPersistentRc { offset, rc } => RegionError::NonPersistentRc {
            offset: shift + offset as u64,
            rc,
        },
        F::PtrOutOfBounds { offset: _, ptr } => RegionError::PtrOutOfBounds {
            ptr,
            resolved: ptr as i128 - base_addr as i128,
        },
        F::MisalignedPtr { offset: _, ptr } => RegionError::MisalignedPtr { ptr },
        F::BadObjectSize { offset, .. } => RegionError::DecodeShape {
            offset: shift + offset as u64,
            reason: "impossible object size",
        },
        F::ForbiddenTag { offset, tag } => RegionError::ForbiddenTag {
            offset: shift + offset as u64,
            tag,
        },
        // The shared audit has no version context; closure support arrives
        // with the plugin-door beads (sno/83r), so any closure is refused.
        F::ClosureUnsupported { offset } => RegionError::ClosureInV2 {
            offset: shift + offset as u64,
        },
        F::StringIntegrity { offset, reason } => RegionError::StringIntegrity {
            offset: shift + offset as u64,
            reason,
        },
        F::MpzIntegrity { offset } => RegionError::MpzIntegrity {
            offset: shift + offset as u64,
        },
        F::UnsupportedCategory { tag, .. } => RegionError::ForbiddenTag { offset: shift, tag },
        F::BuildShape { reason } => RegionError::DecodeShape {
            offset: shift,
            reason,
        },
    }
}

/// Traversal budget: hard cap on visited objects. Exhaustion is a typed
/// outcome, never a partial "valid".
#[derive(Debug, Clone, Copy)]
pub struct WalkBudget {
    pub max_objects: u64,
}

impl Default for WalkBudget {
    fn default() -> Self {
        // The largest pinned-toolchain module holds ~170k objects; 20M leaves
        // three orders of headroom while still bounding hostile inputs.
        Self {
            max_objects: 20_000_000,
        }
    }
}

/// Parsed fixed header, every field read at its generated-contract offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanHeader {
    pub version: u8,
    pub flags: u8,
    pub lean_version: String,
    pub githash: String,
    pub base_addr: u64,
}

/// Integrity report of a full-graph walk.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WalkReport {
    /// distinct compacted objects visited
    pub objects: u64,
    pub ctors: u64,
    pub arrays: u64,
    pub scalar_arrays: u64,
    pub strings: u64,
    pub mpz: u64,
    pub thunks: u64,
    pub tasks: u64,
    pub refs: u64,
    /// scalar (boxed-value) references seen in pointer positions
    pub scalar_refs: u64,
}

/// One environment-extension block: the extension's name and its opaque
/// payload count. Payloads are walked for integrity but never interpreted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionBlock {
    pub name: String,
    pub entries: u64,
}

/// One losslessly decoded `Lean.Import` row at the pinned epoch.
///
/// The field inventory and physical pointer/scalar split come from
/// [`format::IMPORT_FIELDS`] plus the generated runtime ABI. Array order and
/// duplicate rows are observable and are therefore preserved by
/// [`ModuleDataView::imports`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImport {
    pub module: Name,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

/// Decoded `ModuleData` view (fields per the generated `MODULE_DATA_FIELDS`
/// wire order): counts everywhere, plus fully-decoded constant names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleDataView {
    pub is_module: bool,
    pub imports: Vec<ModuleImport>,
    pub const_names: Vec<String>,
    pub constants: u64,
    pub extra_const_names: u64,
    pub extensions: Vec<ExtensionBlock>,
}

/// `(file offset, length)` views of the ModuleData constant arrays.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ModuleArrays {
    pub(crate) const_names: (u64, u64),
    pub(crate) constants: (u64, u64),
}

/// A parsed olean file: header plus a bounds-checked view of the region bytes.
#[derive(Debug)]
pub struct OleanView<'a> {
    bytes: &'a [u8],
    pub header: OleanHeader,
}

fn field_offset(name: &str) -> u64 {
    // The generated contract table is the single source of header layout;
    // a missing row is a build-time contract break, not a runtime input error.
    format::OLEAN_HEADER_FIELDS
        .iter()
        .find(|f| f.name == name)
        .map(|f| f.offset as u64)
        .unwrap_or(u64::MAX)
}

fn field_size(name: &str) -> u64 {
    format::OLEAN_HEADER_FIELDS
        .iter()
        .find(|f| f.name == name)
        .map(|f| f.size as u64)
        .unwrap_or(0)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ConstructorLayout {
    pointer_fields: u8,
    scalar_bytes: u16,
    padded_bytes: u16,
}

/// Derive the compacted constructor layout from a generated Lean structure
/// contract. The two structures decoded in this module contain heap-valued
/// fields plus unboxed `Bool`s; an unknown scalar type is a contract change,
/// not something the reader may guess at.
fn constructor_layout(fields: &[format::LeanField]) -> Option<ConstructorLayout> {
    let pointer_fields = fields
        .iter()
        .filter(|field| field.lean_type != "Bool")
        .count();
    let scalar_bytes = fields
        .iter()
        .filter(|field| field.lean_type == "Bool")
        .count();
    if pointer_fields.checked_add(scalar_bytes)? != fields.len() {
        return None;
    }

    let word_bytes = field_size("base_addr");
    let align = u64::try_from(abi::OBJECT_SIZE_DELTA).ok()?;
    let pointer_bytes = word_bytes.checked_mul(u64::try_from(pointer_fields).ok()?)?;
    let required = word_bytes
        .checked_add(pointer_bytes)?
        .checked_add(u64::try_from(scalar_bytes).ok()?)?;
    let padded = required.checked_add(align.checked_sub(1)?)? / align * align;
    Some(ConstructorLayout {
        pointer_fields: u8::try_from(pointer_fields).ok()?,
        scalar_bytes: u16::try_from(scalar_bytes).ok()?,
        padded_bytes: u16::try_from(padded).ok()?,
    })
}

fn bool_scalar_index(fields: &[format::LeanField], name: &str) -> Option<u64> {
    fields
        .iter()
        .filter(|field| field.lean_type == "Bool")
        .position(|field| field.name == name)
        .and_then(|index| u64::try_from(index).ok())
}

#[derive(Debug, Clone, Copy)]
struct DecodeBudget {
    max_objects: u64,
    visited: u64,
}

#[derive(Debug)]
enum NameComponent {
    Str(String),
    Num(u64),
}

impl DecodeBudget {
    fn new(budget: WalkBudget) -> Self {
        Self {
            max_objects: budget.max_objects,
            visited: 0,
        }
    }

    fn visit(&mut self) -> RResult<()> {
        self.visited = self.visited.saturating_add(1);
        if self.visited > self.max_objects {
            return Err(RegionError::BudgetExhausted {
                visited: self.visited,
                budget: self.max_objects,
            });
        }
        Ok(())
    }
}

impl<'a> OleanView<'a> {
    /// Parse and validate the fixed header. The envelope laws (length gate,
    /// magic, accepted-version set, base alignment) are judged by the SHARED
    /// region engine — `fln_rt::region::parse_olean_envelope`, the same code
    /// path the runtime's mmap loader runs (§6.4 shared-code-path law); this
    /// codec adds only the identity fields the runtime does not need
    /// (`lean_version`, `githash`, `flags`), read at their generated-contract
    /// offsets.
    pub fn parse(bytes: &'a [u8]) -> RResult<Self> {
        let envelope = fln_rt::region::parse_olean_envelope(bytes)
            .map_err(|fault| shared_fault(fault, 0, 0, bytes.len() as u64))?;
        let flags = bytes[field_offset("flags") as usize];
        let read_str = |name: &str, len: usize| -> String {
            let off = field_offset(name) as usize;
            let raw = &bytes[off..off + len];
            let end = raw.iter().position(|&b| b == 0).unwrap_or(len);
            String::from_utf8_lossy(&raw[..end]).into_owned()
        };
        Ok(Self {
            bytes,
            header: OleanHeader {
                version: envelope.version,
                flags,
                lean_version: read_str("lean_version", 33),
                githash: read_str("githash", 40),
                base_addr: envelope.base_addr,
            },
        })
    }

    /// Full-surface integrity audit through the SHARED region engine
    /// (`fln_rt::region::audit`): every object in the payload — reachable or
    /// not — checked against the category laws at the stored base, read-only.
    /// [`walk`](Self::walk) remains the reachability/module-policy check;
    /// this is the §6.4 single-code-path integrity authority the runtime's
    /// own loader enforces.
    pub fn shared_audit(&self) -> RResult<fln_rt::region::RegionReport> {
        let header = format::OLEAN_HEADER_SIZE as u64;
        let payload = self.read_bytes(header, self.bytes.len() as u64 - header)?;
        fln_rt::region::audit(payload, self.header.base_addr + header).map_err(|fault| {
            shared_fault(
                fault,
                header,
                self.header.base_addr,
                self.bytes.len() as u64,
            )
        })
    }

    pub(crate) fn read_u64(&self, off: u64) -> RResult<u64> {
        let end = off.checked_add(8).ok_or(RegionError::Truncated {
            wanted_end: u64::MAX,
            len: self.bytes.len() as u64,
        })?;
        if end > self.bytes.len() as u64 {
            return Err(RegionError::Truncated {
                wanted_end: end,
                len: self.bytes.len() as u64,
            });
        }
        let mut b = [0u8; 8];
        b.copy_from_slice(&self.bytes[off as usize..end as usize]);
        Ok(u64::from_le_bytes(b))
    }

    pub(crate) fn read_bytes(&self, off: u64, len: u64) -> RResult<&'a [u8]> {
        let end = off.checked_add(len).ok_or(RegionError::Truncated {
            wanted_end: u64::MAX,
            len: self.bytes.len() as u64,
        })?;
        if end > self.bytes.len() as u64 {
            return Err(RegionError::Truncated {
                wanted_end: end,
                len: self.bytes.len() as u64,
            });
        }
        Ok(&self.bytes[off as usize..end as usize])
    }

    /// Resolve a stored pointer to a file offset: the compactor rewrote every
    /// interior pointer to `base_addr + file_offset` (OLEAN_CONTRACT §1).
    pub(crate) fn deref(&self, ptr: u64) -> RResult<u64> {
        let resolved = ptr as i128 - self.header.base_addr as i128;
        let header_size = format::OLEAN_HEADER_SIZE as i128;
        if resolved < header_size || resolved >= self.bytes.len() as i128 {
            return Err(RegionError::PtrOutOfBounds { ptr, resolved });
        }
        if resolved % 8 != 0 {
            return Err(RegionError::MisalignedPtr { ptr });
        }
        Ok(resolved as u64)
    }

    /// Read a compacted `lean_object` header at a file offset: `m_rc` (i32),
    /// then the packed bitfield word `m_cs_sz:16 | m_other:8 | m_tag:8`
    /// (low-to-high, per the generated `LEAN_OBJECT_FIELDS` order).
    pub(crate) fn obj_header(&self, off: u64) -> RResult<(u8, u8, u16)> {
        let word = self.read_u64(off)?;
        let rc = (word & 0xffff_ffff) as u32 as i32;
        if rc != 0 {
            return Err(RegionError::NonPersistentRc { offset: off, rc });
        }
        let packed = (word >> 32) as u32;
        let tag = (packed >> 24) as u8;
        let other = ((packed >> 16) & 0xff) as u8;
        let cs_sz = (packed & 0xffff) as u16;
        Ok((tag, other, cs_sz))
    }

    fn root_ptr(&self) -> RResult<u64> {
        // The root slot is the first word of the data region (allocated first,
        // written last by the compactor).
        self.read_u64(format::OLEAN_HEADER_SIZE as u64)
    }

    /// Walk the entire object graph from the root, checking every pointer,
    /// header, string, and bignum. Iterative and budgeted: hostile depth or
    /// size becomes a typed error, never a stack fault.
    pub fn walk(&self, budget: WalkBudget) -> RResult<WalkReport> {
        let mut report = WalkReport::default();
        let mut seen: HashSet<u64> = HashSet::new();
        let mut stack: Vec<u64> = vec![self.root_ptr()?];
        while let Some(ptr) = stack.pop() {
            if ptr & 1 == 1 {
                report.scalar_refs += 1;
                continue;
            }
            let off = self.deref(ptr)?;
            if !seen.insert(off) {
                continue;
            }
            report.objects += 1;
            if report.objects > budget.max_objects {
                return Err(RegionError::BudgetExhausted {
                    visited: report.objects,
                    budget: budget.max_objects,
                });
            }
            let (tag, other, _cs_sz) = self.obj_header(off)?;
            if tag <= abi::TAG_MAX_CTOR_TAG {
                report.ctors += 1;
                for i in 0..other as u64 {
                    stack.push(self.read_u64(off + 8 + 8 * i)?);
                }
            } else if tag == abi::TAG_ARRAY {
                report.arrays += 1;
                let size = self.read_u64(off + 8)?;
                let capacity = self.read_u64(off + 16)?;
                if size > capacity {
                    return Err(RegionError::DecodeShape {
                        offset: off,
                        reason: "array size > capacity",
                    });
                }
                for i in 0..size {
                    stack.push(self.read_u64(off + 24 + 8 * i)?);
                }
            } else if tag == abi::TAG_SCALAR_ARRAY {
                report.scalar_arrays += 1;
                let size = self.read_u64(off + 8)?;
                self.read_bytes(off + 24, size)?;
            } else if tag == abi::TAG_STRING {
                report.strings += 1;
                self.check_string(off)?;
            } else if tag == abi::TAG_MPZ {
                report.mpz += 1;
                self.check_mpz(off)?;
            } else if tag == abi::TAG_THUNK {
                report.thunks += 1;
                for i in 0..2u64 {
                    let p = self.read_u64(off + 8 + 8 * i)?;
                    if p != 0 {
                        stack.push(p);
                    }
                }
            } else if tag == abi::TAG_TASK {
                report.tasks += 1;
                let p = self.read_u64(off + 8)?;
                if p != 0 {
                    stack.push(p);
                }
            } else if tag == abi::TAG_REF {
                report.refs += 1;
                stack.push(self.read_u64(off + 8)?);
            } else if tag == abi::TAG_CLOSURE {
                // v3-only; this reader's traversal supports the v2 payload.
                return Err(RegionError::ClosureInV2 { offset: off });
            } else {
                // External can never be compacted; StructArray is unused at
                // the pin; Promise/Reserved must not appear in module data.
                return Err(RegionError::ForbiddenTag { offset: off, tag });
            }
        }
        Ok(report)
    }

    fn check_string(&self, off: u64) -> RResult<()> {
        let size = self.read_u64(off + 8)?;
        let capacity = self.read_u64(off + 16)?;
        if size == 0 || size > capacity {
            return Err(RegionError::StringIntegrity {
                offset: off,
                reason: "size/capacity",
            });
        }
        let bytes = self.read_bytes(off + 32, size)?;
        if bytes[bytes.len() - 1] != 0 {
            return Err(RegionError::StringIntegrity {
                offset: off,
                reason: "missing NUL terminator",
            });
        }
        if std::str::from_utf8(&bytes[..bytes.len() - 1]).is_err() {
            return Err(RegionError::StringIntegrity {
                offset: off,
                reason: "invalid UTF-8",
            });
        }
        Ok(())
    }

    fn check_mpz(&self, off: u64) -> RResult<()> {
        // GMP encoding (header flags bit 0 set at the pin): the mpz_object
        // carries {alloc: i32, size: i32, limbs: ptr}; the compactor copies
        // the limb array right after the object and rewrites the one pointer.
        let word = self.read_u64(off + 8)?;
        let mpz_size = ((word >> 32) as u32) as i32;
        let limbs = mpz_size.unsigned_abs() as u64;
        let limb_ptr = self.read_u64(off + 16)?;
        let limb_off = self
            .deref(limb_ptr)
            .map_err(|_| RegionError::MpzIntegrity { offset: off })?;
        self.read_bytes(limb_off, limbs.saturating_mul(8))
            .map_err(|_| RegionError::MpzIntegrity { offset: off })?;
        Ok(())
    }

    /// Read the sign and little-endian 64-bit limbs of a compacted GMP mpz
    /// object (limbs copied right after the object; one rewritten pointer).
    pub(crate) fn mpz_limbs(&self, off: u64) -> RResult<(bool, Vec<u64>)> {
        self.check_mpz(off)?;
        let word = self.read_u64(off + 8)?;
        let mpz_size = ((word >> 32) as u32) as i32;
        let n = mpz_size.unsigned_abs() as u64;
        let limb_off = self.deref(self.read_u64(off + 16)?)?;
        let mut limbs = Vec::with_capacity(n as usize);
        for i in 0..n {
            limbs.push(self.read_u64(limb_off + 8 * i)?);
        }
        Ok((mpz_size < 0, limbs))
    }

    /// Byte-window alias used by the declaration decoder.
    pub(crate) fn read_bytes_at(&self, off: u64, len: u64) -> RResult<&'a [u8]> {
        self.read_bytes(off, len)
    }

    /// String-object reader used by the declaration decoder.
    pub(crate) fn read_string_at(&self, ptr: u64) -> RResult<String> {
        self.read_string_obj(ptr)
    }

    fn read_string_obj(&self, ptr: u64) -> RResult<String> {
        let off = self.deref(ptr)?;
        let (tag, _, _) = self.obj_header(off)?;
        if tag != abi::TAG_STRING {
            return Err(RegionError::DecodeShape {
                offset: off,
                reason: "expected string object",
            });
        }
        self.check_string(off)?;
        let size = self.read_u64(off + 8)?;
        let bytes = self.read_bytes(off + 32, size)?;
        // check_string proved UTF-8; decode defensively anyway.
        match std::str::from_utf8(&bytes[..bytes.len() - 1]) {
            Ok(s) => Ok(s.to_owned()),
            Err(_) => Err(RegionError::StringIntegrity {
                offset: off,
                reason: "invalid UTF-8",
            }),
        }
    }

    /// Decode a `Name` chain (anonymous | str pre s | num pre i, each with a
    /// cached-hash scalar field) into dot-notation. Iterative on the `pre`
    /// chain; bounded by the budget to survive hostile self-references.
    fn read_name(&self, mut ptr: u64, budget: &mut DecodeBudget) -> RResult<Name> {
        let mut components: Vec<NameComponent> = Vec::new();
        loop {
            if ptr & 1 == 1 {
                // enum ctor without fields is boxed: Name.anonymous == box(0)
                if ptr >> 1 != 0 {
                    return Err(RegionError::DecodeShape {
                        offset: 0,
                        reason: "scalar Name not anonymous",
                    });
                }
                break;
            }
            budget.visit()?;
            let off = self.deref(ptr)?;
            let (tag, other, _) = self.obj_header(off)?;
            match tag {
                1 => {
                    // Name.str (pre : Name) (s : String) + cached hash scalar
                    if other != 2 {
                        return Err(RegionError::DecodeShape {
                            offset: off,
                            reason: "Name.str arity",
                        });
                    }
                    budget.visit()?;
                    let s = self.read_string_obj(self.read_u64(off + 16)?)?;
                    components.push(NameComponent::Str(s));
                    ptr = self.read_u64(off + 8)?;
                }
                2 => {
                    // Name.num (pre : Name) (i : Nat) + cached hash scalar
                    if other != 2 {
                        return Err(RegionError::DecodeShape {
                            offset: off,
                            reason: "Name.num arity",
                        });
                    }
                    let nat = self.read_u64(off + 16)?;
                    let component = if nat & 1 == 1 {
                        nat >> 1
                    } else {
                        budget.visit()?;
                        let nat_off = self.deref(nat)?;
                        let (negative, limbs) = self.mpz_limbs(nat_off)?;
                        if negative || limbs.len() > 1 {
                            return Err(RegionError::DecodeShape {
                                offset: nat_off,
                                reason: "Name.num component exceeds u64",
                            });
                        }
                        limbs.first().copied().unwrap_or(0)
                    };
                    components.push(NameComponent::Num(component));
                    ptr = self.read_u64(off + 8)?;
                }
                _ => {
                    return Err(RegionError::DecodeShape {
                        offset: off,
                        reason: "Name tag",
                    });
                }
            }
        }
        components.reverse();
        Ok(components
            .into_iter()
            .fold(Name::anonymous(), |name, component| match component {
                NameComponent::Str(value) => Name::str(name, value),
                NameComponent::Num(value) => Name::num(name, value),
            }))
    }

    /// The `constNames`/`constants` array views of the root `ModuleData`,
    /// as (file offset, length) pairs for the declaration decoder.
    pub(crate) fn module_arrays(&self) -> RResult<ModuleArrays> {
        let n_ptr_fields = format::MODULE_DATA_FIELDS
            .iter()
            .filter(|f| f.lean_type != "Bool")
            .count() as u8;
        let root = self.root_ptr()?;
        if root & 1 == 1 {
            return Err(RegionError::RootShape {
                reason: "root is a scalar",
            });
        }
        let off = self.deref(root)?;
        let (tag, other, _) = self.obj_header(off)?;
        if tag != 0 || other != n_ptr_fields {
            return Err(RegionError::RootShape {
                reason: "root is not a ModuleData constructor",
            });
        }
        Ok(ModuleArrays {
            const_names: self.array_view(self.read_u64(off + 16)?, "constNames not an array")?,
            constants: self.array_view(self.read_u64(off + 24)?, "constants not an array")?,
        })
    }

    fn array_view(&self, ptr: u64, what: &'static str) -> RResult<(u64, u64)> {
        let off = self.deref(ptr)?;
        let (tag, _, _) = self.obj_header(off)?;
        if tag != abi::TAG_ARRAY {
            return Err(RegionError::DecodeShape {
                offset: off,
                reason: what,
            });
        }
        Ok((off, self.read_u64(off + 8)?))
    }

    fn decode_array_view(
        &self,
        ptr: u64,
        what: &'static str,
        budget: &mut DecodeBudget,
    ) -> RResult<(u64, u64)> {
        budget.visit()?;
        self.array_view(ptr, what)
    }

    fn read_canonical_bool(&self, off: u64, reason: &'static str) -> RResult<bool> {
        match self.read_bytes(off, 1)?[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(RegionError::DecodeShape {
                offset: off,
                reason,
            }),
        }
    }

    /// Decode the root `ModuleData` object per the generated wire order:
    /// pointer fields `imports, constNames, constants, extraConstNames,
    /// entries`, then the `isModule` scalar byte.
    pub fn module_data(&self, budget: WalkBudget) -> RResult<ModuleDataView> {
        let module_layout =
            constructor_layout(format::MODULE_DATA_FIELDS).ok_or(RegionError::RootShape {
                reason: "unsupported ModuleData contract layout",
            })?;
        let mut budget = DecodeBudget::new(budget);
        budget.visit()?;
        let root = self.root_ptr()?;
        if root & 1 == 1 {
            return Err(RegionError::RootShape {
                reason: "root is a scalar",
            });
        }
        let off = self.deref(root)?;
        let (tag, other, cs_sz) = self.obj_header(off)?;
        if tag != 0 || other != module_layout.pointer_fields || cs_sz != module_layout.padded_bytes
        {
            return Err(RegionError::RootShape {
                reason: "root is not a ModuleData constructor",
            });
        }
        let field = |i: u64| self.read_u64(off + 8 + 8 * i);
        let module_scalar_base = off + field_size("base_addr") * (1 + u64::from(other));
        let is_module_index = bool_scalar_index(format::MODULE_DATA_FIELDS, "isModule").ok_or(
            RegionError::RootShape {
                reason: "ModuleData contract lacks isModule",
            },
        )?;
        let is_module = self.read_canonical_bool(
            module_scalar_base + is_module_index,
            "noncanonical ModuleData.isModule Bool",
        )?;

        // imports : Array Import — Import is a ctor with one Name pointer and
        // three scalar Bools (module, importAll, isExported, isMeta).
        let import_layout =
            constructor_layout(format::IMPORT_FIELDS).ok_or(RegionError::DecodeShape {
                offset: off,
                reason: "unsupported Import contract layout",
            })?;
        if import_layout.pointer_fields != 1 || import_layout.scalar_bytes != 3 {
            return Err(RegionError::DecodeShape {
                offset: off,
                reason: "unsupported Import contract field inventory",
            });
        }
        let import_all_index = bool_scalar_index(format::IMPORT_FIELDS, "importAll").ok_or(
            RegionError::DecodeShape {
                offset: off,
                reason: "Import contract lacks importAll",
            },
        )?;
        let is_exported_index = bool_scalar_index(format::IMPORT_FIELDS, "isExported").ok_or(
            RegionError::DecodeShape {
                offset: off,
                reason: "Import contract lacks isExported",
            },
        )?;
        let is_meta_index =
            bool_scalar_index(format::IMPORT_FIELDS, "isMeta").ok_or(RegionError::DecodeShape {
                offset: off,
                reason: "Import contract lacks isMeta",
            })?;
        let (imp_off, imp_len) =
            self.decode_array_view(field(0)?, "imports not an array", &mut budget)?;
        let mut imports = Vec::new();
        for i in 0..imp_len {
            budget.visit()?;
            let p = self.read_u64(imp_off + 24 + 8 * i)?;
            let io = self.deref(p)?;
            let (itag, iother, ics_sz) = self.obj_header(io)?;
            if itag != 0
                || iother != import_layout.pointer_fields
                || ics_sz != import_layout.padded_bytes
            {
                return Err(RegionError::DecodeShape {
                    offset: io,
                    reason: "Import shape",
                });
            }
            let scalar_base = io + field_size("base_addr") * (1 + u64::from(iother));
            let module = self.read_name(self.read_u64(io + 8)?, &mut budget)?;
            let import_all = self.read_canonical_bool(
                scalar_base + import_all_index,
                "noncanonical Import.importAll Bool",
            )?;
            let is_exported = self.read_canonical_bool(
                scalar_base + is_exported_index,
                "noncanonical Import.isExported Bool",
            )?;
            let is_meta = self.read_canonical_bool(
                scalar_base + is_meta_index,
                "noncanonical Import.isMeta Bool",
            )?;
            imports.push(ModuleImport {
                module,
                import_all,
                is_exported,
                is_meta,
            });
        }

        let (cn_off, cn_len) =
            self.decode_array_view(field(1)?, "constNames not an array", &mut budget)?;
        let mut const_names = Vec::new();
        for i in 0..cn_len {
            const_names.push(
                self.read_name(self.read_u64(cn_off + 24 + 8 * i)?, &mut budget)?
                    .to_display_string(),
            );
        }

        let (_, constants) =
            self.decode_array_view(field(2)?, "constants not an array", &mut budget)?;
        let (_, extra) =
            self.decode_array_view(field(3)?, "extraConstNames not an array", &mut budget)?;

        // entries : Array (Name × Array EnvExtensionEntry) — the pair is a
        // two-field ctor; payloads stay opaque (counted, never interpreted).
        let (en_off, en_len) =
            self.decode_array_view(field(4)?, "entries not an array", &mut budget)?;
        let mut extensions = Vec::new();
        for i in 0..en_len {
            budget.visit()?;
            let p = self.read_u64(en_off + 24 + 8 * i)?;
            let po = self.deref(p)?;
            let (ptag, pother, _) = self.obj_header(po)?;
            if ptag != 0 || pother != 2 {
                return Err(RegionError::DecodeShape {
                    offset: po,
                    reason: "entries pair shape",
                });
            }
            let name = self
                .read_name(self.read_u64(po + 8)?, &mut budget)?
                .to_display_string();
            let (_, payloads) = self.decode_array_view(
                self.read_u64(po + 16)?,
                "extension payload not an array",
                &mut budget,
            )?;
            extensions.push(ExtensionBlock {
                name,
                entries: payloads,
            });
        }

        if cn_len != constants {
            // Environment.lean documents constNames as exactly the names of
            // `constants`; a mismatch is a malformed module, not a tolerance.
            return Err(RegionError::DecodeShape {
                offset: off,
                reason: "constNames/constants length mismatch",
            });
        }

        Ok(ModuleDataView {
            is_module,
            imports,
            const_names,
            constants,
            extra_const_names: extra,
            extensions,
        })
    }
}

/// Typed failure of the mmap-backed load path: the mapping layer's fault or
/// the codec's region fault, never a panic (FL-INV-07).
#[derive(Debug)]
pub enum MappedOleanError {
    /// The mmap/seal primitive failed.
    Map(MapError),
    /// The envelope or region content failed validation.
    Region(RegionError),
}

impl fmt::Display for MappedOleanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Map(e) => write!(f, "olean mapping: {e}"),
            Self::Region(e) => write!(f, "olean region: {e}"),
        }
    }
}

impl std::error::Error for MappedOleanError {}

/// An olean held open through the production mmap path — the fln-20n ×
/// fln-wgp seam (§6.4): the file is mapped privately via [`RegionMapping`]
/// (untouched pages stay page-cache-shared with every other consumer of the
/// same artifact — the PG-4/PG-6 mechanism), validated through the SHARED
/// engine (envelope parse + full-surface audit), then SEALED read-only, so
/// region hygiene holds while the view is live: hardened builds trap any
/// write. The by-value decoders run over the mapping unchanged — stored
/// pointers stay `base_addr`-relative because this path never relocates, so
/// a load never dirties a shared page.
pub struct MappedOlean {
    mapping: RegionMapping,
    header: OleanHeader,
}

impl MappedOlean {
    /// Map, validate through the shared engine, and seal. Any failure
    /// releases the mapping (no half-open state).
    pub fn open(path: &Path) -> Result<MappedOlean, MappedOleanError> {
        let mut mapping = RegionMapping::map_file_private(path).map_err(MappedOleanError::Map)?;
        let header = {
            let view = OleanView::parse(mapping.as_slice()).map_err(MappedOleanError::Region)?;
            view.shared_audit().map_err(MappedOleanError::Region)?;
            view.header
        };
        mapping.seal().map_err(MappedOleanError::Map)?;
        Ok(MappedOlean { mapping, header })
    }

    pub fn header(&self) -> &OleanHeader {
        &self.header
    }

    pub fn len(&self) -> usize {
        self.mapping.len()
    }

    pub fn is_empty(&self) -> bool {
        self.mapping.is_empty()
    }

    /// The mapping is sealed by construction; exposed for hygiene asserts.
    pub fn is_sealed(&self) -> bool {
        self.mapping.is_sealed()
    }

    /// Borrow the by-value decoding view over the sealed mapping.
    pub fn view(&self) -> OleanView<'_> {
        OleanView {
            bytes: self.mapping.as_slice(),
            header: self.header.clone(),
        }
    }
}
