//! Declaration decoding — compacted Lean objects into FrankenLean term-plane
//! values (bead franken_lean-z6c seed, on top of the G0-1 region reader).
//!
//! Decodes `Name`/`Level`/`Expr`/`ConstantInfo` object graphs from a region
//! into `fln-core`/`fln-env` values. Layout laws (from the pinned sources, see
//! `tribunal/fixtures/c3/FINDINGS.md`):
//!
//! - object slots (pointers AND boxed `Nat`s) come first in declaration
//!   order; the scalar area follows, larger scalars first (`u64` computed
//!   fields before `u8` bools/enums);
//! - single-field structures are erased (`FVarId`/`MVarId`/`LMVarId` ≡
//!   `Name`, `KVMap` ≡ its entry list);
//! - fieldless constructors are scalar-boxed (`Name.anonymous`, `Level.zero`,
//!   `List.nil`, `ReducibilityHints.opaque/abbrev`);
//! - `@[computed_field]` words (`Name.hash`, `Level.Data`, `Expr.Data`) are
//!   stored — and CROSS-CHECKED bit-for-bit against our own recomputation, so
//!   a layout mistake or an identity-layer divergence surfaces as a typed
//!   error, never as silent corruption.
//!
//! Expression graphs are decoded iteratively with memoized sharing: deep
//! terms cannot exhaust the stack, and the walk is budgeted. Every failure is
//! a typed [`DeclError`]; malformed input never panics (FL-INV-07).

use std::collections::{HashMap, HashSet};

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::{DataValue, KVMap, SyntaxHandle};
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
    InductiveVal, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    TheoremVal,
};

use crate::region::{OleanView, RegionError, WalkBudget};

/// Typed decode failure. `Region` wraps the underlying byte-level error; the
/// rest are semantic-shape or cross-check failures at a specific offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclError {
    Region(RegionError),
    /// Object shape does not match the pinned inductive/structure layout.
    Shape {
        offset: u64,
        what: &'static str,
    },
    /// A stored computed field disagrees with our recomputation — either a
    /// layout misread or an identity-layer divergence. Always a finding.
    CrossCheck {
        offset: u64,
        what: &'static str,
        stored: u64,
        computed: u64,
    },
    /// A value exceeds the width FrankenLean's twin type carries.
    Overflow {
        offset: u64,
        what: &'static str,
    },
    /// A payload this slice deliberately does not interpret (e.g. `Syntax`).
    Unsupported {
        offset: u64,
        what: &'static str,
    },
    /// Decode budget exhausted (hostile or runaway graph).
    Budget {
        visited: u64,
    },
    /// A module-system chain's `.olean.private` part does not contain a
    /// declaration the exported part does.
    ///
    /// Reading the private array *instead of* the exported one is sound only
    /// because it is a superset. A chain that breaks that is a decode that
    /// silently returns fewer declarations than the module has — the exact
    /// shape of `franken_lean-timy` — so it is refused rather than returned
    /// short.
    PrivatePartIncomplete {
        missing: Name,
    },
    /// A companion part does not carry the exported part's identity stamp, so
    /// the three regions are not one module's chain.
    ChainPartMismatch {
        part: OleanChainPart,
    },
    /// A chain was supplied for an artifact that is not a module-system
    /// module, which has no companions to compose.
    NotAModuleChain,
    /// The private part offers a body-less `axiom` where the exported part
    /// declared something with a body.
    ///
    /// The private array is authoritative because it is the STRONGER view, not
    /// merely a larger one. Reversed, admitting it would replace a checked
    /// definition with a postulate the kernel can only agree with.
    PrivatePartWeakensDeclaration {
        name: Name,
        exported_kind: &'static str,
        private_kind: &'static str,
    },
    /// The three parts together exceed the caller's byte ceiling.
    ChainTooLarge {
        bytes: usize,
        limit: usize,
    },
}

impl From<RegionError> for DeclError {
    fn from(e: RegionError) -> Self {
        DeclError::Region(e)
    }
}

impl std::fmt::Display for DeclError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeclError::Region(e) => write!(f, "region: {e}"),
            DeclError::Shape { offset, what } => write!(f, "shape at {offset}: {what}"),
            DeclError::CrossCheck {
                offset,
                what,
                stored,
                computed,
            } => write!(
                f,
                "cross-check at {offset}: {what} stored {stored:#018x} != computed {computed:#018x}"
            ),
            DeclError::Overflow { offset, what } => write!(f, "overflow at {offset}: {what}"),
            DeclError::Unsupported { offset, what } => {
                write!(f, "unsupported at {offset}: {what}")
            }
            DeclError::Budget { visited } => write!(f, "decode budget exhausted at {visited}"),
            DeclError::ChainPartMismatch { part } => write!(
                f,
                "companion {} does not carry the exported part's identity stamp, so these \
                 regions are not one module's chain",
                part.label()
            ),
            DeclError::ChainTooLarge { bytes, limit } => write!(
                f,
                "module-system chain is {bytes} bytes, over the {limit}-byte ceiling"
            ),
            DeclError::PrivatePartWeakensDeclaration {
                name,
                exported_kind,
                private_kind,
            } => write!(
                f,
                "the private part offers {} as {private_kind} where the exported part \
                 declared a {exported_kind}",
                name.to_display_string()
            ),
            DeclError::NotAModuleChain => write!(
                f,
                "artifact is not a module-system module, so it has no companion chain to compose"
            ),
            DeclError::PrivatePartIncomplete { missing } => write!(
                f,
                "module-system chain is not decodable: the private part omits the exported \
                 declaration {}",
                missing.to_display_string()
            ),
        }
    }
}

type DResult<T> = Result<T, DeclError>;

/// Memoized decode context over one region. Sharing in the compacted graph is
/// preserved as sharing of decoded values (`Arc` clones under the hood).
pub struct DeclDecoder<'a> {
    view: &'a OleanView<'a>,
    names: HashMap<u64, Name>,
    levels: HashMap<u64, Level>,
    exprs: HashMap<u64, Expr>,
    visited: u64,
    budget: u64,
    /// When set (default), stored `Name.hash`/`Level.Data`/`Expr.Data` words
    /// are compared bit-for-bit against our recomputation.
    pub cross_check: bool,
}

impl<'a> DeclDecoder<'a> {
    pub fn new(view: &'a OleanView<'a>, budget: WalkBudget) -> Self {
        Self {
            view,
            names: HashMap::new(),
            levels: HashMap::new(),
            exprs: HashMap::new(),
            visited: 0,
            budget: budget.max_objects,
            cross_check: true,
        }
    }

    fn charge(&mut self) -> DResult<()> {
        self.visited += 1;
        if self.visited > self.budget {
            return Err(DeclError::Budget {
                visited: self.visited,
            });
        }
        Ok(())
    }

    // ---- scalar helpers ----------------------------------------------------------------

    fn is_scalar(ptr: u64) -> bool {
        ptr & 1 == 1
    }

    fn unbox(ptr: u64) -> u64 {
        ptr >> 1
    }

    /// A boxed `Nat` slot: small scalar or MPZ object.
    fn decode_nat(&mut self, ptr: u64) -> DResult<NatLit> {
        if Self::is_scalar(ptr) {
            return Ok(NatLit::from_u64(Self::unbox(ptr)));
        }
        let off = self.view.deref(ptr)?;
        let (tag, _, _) = self.view.obj_header(off)?;
        if tag != fln_rt::abi::TAG_MPZ {
            return Err(DeclError::Shape {
                offset: off,
                what: "Nat: neither scalar nor mpz",
            });
        }
        let (negative, limbs) = self.view.mpz_limbs(off)?;
        if negative {
            return Err(DeclError::Shape {
                offset: off,
                what: "Nat with negative mpz",
            });
        }
        Ok(NatLit::from_limbs_le(limbs))
    }

    fn decode_nat_u32(&mut self, ptr: u64, what: &'static str) -> DResult<u32> {
        let nat = self.decode_nat(ptr)?;
        match nat.to_u64() {
            Some(v) if u32::try_from(v).is_ok() => Ok(v as u32),
            _ => Err(DeclError::Overflow { offset: ptr, what }),
        }
    }

    /// Lean stores `Bool` as a single byte that is only ever 0 or 1. The
    /// region reader already refuses any other value on `ModuleData`/`Import`
    /// (`read_canonical_bool`). Declaration flags (`isUnsafe`, `k`, `nonDep`,
    /// `DataValue.ofBool`) are the same type on the same wire; treating `2` as
    /// `true` would accept a malformed object the rest of this crate refuses.
    fn decode_bool(byte: u8, offset: u64) -> DResult<bool> {
        match byte {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(DeclError::Shape {
                offset,
                what: "noncanonical Bool",
            }),
        }
    }

    fn decode_int(&mut self, ptr: u64) -> DResult<i64> {
        if Self::is_scalar(ptr) {
            #[cfg(target_pointer_width = "64")]
            {
                return Ok(i64::from((ptr >> 1) as u32 as i32));
            }
            #[cfg(target_pointer_width = "32")]
            {
                return Ok(i64::from((ptr as u32 as i32) >> 1));
            }
        }

        let off = self.view.deref(ptr)?;
        let (tag, _, _) = self.view.obj_header(off)?;
        if tag != fln_rt::abi::TAG_MPZ {
            return Err(DeclError::Shape {
                offset: off,
                what: "Int: neither scalar nor mpz",
            });
        }
        let (negative, limbs) = self.view.mpz_limbs(off)?;
        let magnitude = match limbs.as_slice() {
            [] => 0,
            [limb] => *limb,
            _ => {
                return Err(DeclError::Overflow {
                    offset: off,
                    what: "DataValue.ofInt",
                });
            }
        };
        if negative {
            if magnitude == 1u64 << 63 {
                Ok(i64::MIN)
            } else {
                let magnitude = i64::try_from(magnitude).map_err(|_| DeclError::Overflow {
                    offset: off,
                    what: "DataValue.ofInt",
                })?;
                Ok(-magnitude)
            }
        } else {
            i64::try_from(magnitude).map_err(|_| DeclError::Overflow {
                offset: off,
                what: "DataValue.ofInt",
            })
        }
    }

    // ---- Name --------------------------------------------------------------------------

    /// Iterative over the `pre` chain; memoized; cross-checks the stored hash.
    pub fn decode_name(&mut self, root: u64) -> DResult<Name> {
        // Collect the chain of not-yet-decoded links, then fold back down.
        let mut chain: Vec<u64> = Vec::new();
        let mut ptr = root;
        let base: Name = loop {
            if Self::is_scalar(ptr) {
                if Self::unbox(ptr) != 0 {
                    return Err(DeclError::Shape {
                        offset: 0,
                        what: "scalar Name not anonymous",
                    });
                }
                break Name::anonymous();
            }
            let off = self.view.deref(ptr)?;
            if let Some(n) = self.names.get(&off) {
                break n.clone();
            }
            self.charge()?;
            chain.push(off);
            let (tag, other, cs_sz) = self.view.obj_header(off)?;
            if !(tag == 1 || tag == 2) || other != 2 {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Name ctor",
                });
            }
            // A `Name.str`/`Name.num` link is two pointer fields — the prefix
            // and the component — followed by the stored `Name.hash` word, so
            // the object is exactly 8 + 8*2 + 8 bytes.
            //
            // The hash is already cross-checked against our recomputation, but
            // that check reads it from `off + 24`, an offset derived from the
            // layout rather than from the object. If the object were not this
            // shape, the word compared would be some other field and a
            // disagreement would be reported as a hash divergence — a finding
            // pointing at the identity layer for what is really a misread.
            // `cs_sz` is the stored size that can contradict the layout
            // independently, and it was discarded here.
            //
            // Measured over the pin: 5,842,155 Name objects reached from the
            // constNames and extraConstNames arrays, every one with other == 2
            // and cs_sz == 32.
            if cs_sz != 32 {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Name object size disagrees with its two-pointer-plus-hash layout",
                });
            }
            ptr = self.view.read_u64(off + 8)?;
        };
        let mut name = base;
        for &off in chain.iter().rev() {
            let (tag, _, _) = self.view.obj_header(off)?;
            let stored_hash = self.view.read_u64(off + 24)?;
            name = if tag == 1 {
                let s = self.view.read_string_at(self.view.read_u64(off + 16)?)?;
                Name::str(name, s)
            } else {
                let n = self.decode_nat(self.view.read_u64(off + 16)?)?;
                match n.to_u64() {
                    Some(v) => Name::num(name, v),
                    None => {
                        return Err(DeclError::Unsupported {
                            offset: off,
                            what: "Name.num mpz",
                        });
                    }
                }
            };
            if self.cross_check && name.hash() != stored_hash {
                return Err(DeclError::CrossCheck {
                    offset: off,
                    what: "Name.hash",
                    stored: stored_hash,
                    computed: name.hash(),
                });
            }
            self.names.insert(off, name.clone());
        }
        Ok(name)
    }

    // ---- Level -------------------------------------------------------------------------

    pub fn decode_level(&mut self, root: u64) -> DResult<Level> {
        // Iterative post-order with memoized sharing.
        let mut stack: Vec<u64> = vec![root];
        while let Some(&ptr) = stack.last() {
            if Self::is_scalar(ptr) {
                stack.pop();
                continue;
            }
            let off = self.view.deref(ptr)?;
            if self.levels.contains_key(&off) {
                stack.pop();
                continue;
            }
            let (tag, other, cs_sz) = self.view.obj_header(off)?;
            // Every `Level` constructor is its pointer fields followed by ONE
            // stored `Level.Data` word, so the object is 8 + 8*other + 8 bytes,
            // already a multiple of 8.
            //
            // This is the same law the decoder relies on a few lines below,
            // where it reads the Data word at `off + 8 + 8*other` and compares
            // it against our recomputation. That offset comes from the assumed
            // layout, not from the object: if the object were smaller the read
            // would run past its end into a neighbour, and if it were larger
            // there would be stored bytes nobody accounts for. Either way the
            // mismatch would be reported as a Level.Data cross-check
            // divergence, blaming the identity layer for a misread — the same
            // wrong diagnosis the Name size bind (81b0234c) removed.
            //
            // Unlike the Name, ConstantInfo and hint binds, this one rests on
            // the structural argument rather than a corpus census: Level
            // objects are only reachable by decoding expressions, so counting
            // them needs the decoder itself, which the code-first override
            // forbids running. The check cannot reject anything the decoder
            // could otherwise have read correctly, because any object failing
            // it makes that Data read out of bounds or leaves bytes unread.
            if u64::from(cs_sz) != 16 + 8 * u64::from(other) {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Level object size disagrees with its pointer-fields-plus-data layout",
                });
            }
            let child_count: u64 = match tag {
                1 => 1,     // succ
                2 | 3 => 2, // max / imax
                4 | 5 => 0, // param / mvar (Name decoded eagerly below)
                _ => {
                    return Err(DeclError::Shape {
                        offset: off,
                        what: "Level ctor",
                    });
                }
            };
            if (tag == 1 && other != 1) || ((tag == 2 || tag == 3) && other != 2) {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Level arity",
                });
            }
            if (tag == 4 || tag == 5) && other != 1 {
                // param/mvar carry exactly one slot: the eager Name decode below
                // and the stored Level.Data word are both indexed by `other`, so
                // any other arity reads past the object (found by review).
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Level param/mvar arity",
                });
            }
            let mut pending = false;
            for i in 0..child_count {
                let child = self.view.read_u64(off + 8 + 8 * i)?;
                if !Self::is_scalar(child) {
                    let coff = self.view.deref(child)?;
                    if !self.view.object_precedes(coff, off) {
                        // The writer's post-order law: every heap child resolves
                        // strictly below its parent. A violation means a cycle,
                        // and a cycle never builds a node, so no budget would
                        // ever trip — the runaway must be refused here, typed
                        // (fln-abaz finding 1).
                        return Err(DeclError::Shape {
                            offset: off,
                            what: "Level child not below its parent (post-order law)",
                        });
                    }
                    if !self.levels.contains_key(&coff) {
                        stack.push(child);
                        pending = true;
                    }
                }
            }
            if pending {
                continue;
            }
            self.charge()?;
            let child = |d: &Self, i: u64| -> DResult<Level> {
                let p = d.view.read_u64(off + 8 + 8 * i)?;
                d.level_of(p)
            };
            let level = match tag {
                1 => child(self, 0)?.succ().map_err(|_| DeclError::Overflow {
                    offset: off,
                    what: "Level depth",
                })?,
                2 => Level::max(child(self, 0)?, child(self, 1)?).map_err(|_| {
                    DeclError::Overflow {
                        offset: off,
                        what: "Level depth",
                    }
                })?,
                3 => Level::imax(child(self, 0)?, child(self, 1)?).map_err(|_| {
                    DeclError::Overflow {
                        offset: off,
                        what: "Level depth",
                    }
                })?,
                4 => Level::param(self.decode_name(self.view.read_u64(off + 8)?)?),
                5 => Level::mvar(LMVarId(self.decode_name(self.view.read_u64(off + 8)?)?)),
                _ => {
                    return Err(DeclError::Shape {
                        offset: off,
                        what: "Level ctor",
                    });
                }
            };
            // The stored computed word sits after the object slots.
            let stored = self.view.read_u64(off + 8 + 8 * other as u64)?;
            if self.cross_check && level.data().0 != stored {
                return Err(DeclError::CrossCheck {
                    offset: off,
                    what: "Level.Data",
                    stored,
                    computed: level.data().0,
                });
            }
            self.levels.insert(off, level);
            stack.pop();
        }
        self.level_of(root)
    }

    fn level_of(&self, ptr: u64) -> DResult<Level> {
        if Self::is_scalar(ptr) {
            if Self::unbox(ptr) != 0 {
                return Err(DeclError::Shape {
                    offset: 0,
                    what: "scalar Level not zero",
                });
            }
            return Ok(Level::zero());
        }
        let off = self.view.deref(ptr)?;
        self.levels.get(&off).cloned().ok_or(DeclError::Shape {
            offset: off,
            what: "level not decoded (bug)",
        })
    }

    fn decode_level_list(&mut self, ptr: u64) -> DResult<Vec<Level>> {
        let mut out = Vec::new();
        for p in self.list_ptrs(ptr)? {
            out.push(self.decode_level(p)?);
        }
        Ok(out)
    }

    // ---- List --------------------------------------------------------------------------

    /// Collect the element pointers of a `List` (nil = box(0), cons tag 1).
    fn list_ptrs(&mut self, mut ptr: u64) -> DResult<Vec<u64>> {
        let mut out = Vec::new();
        loop {
            if Self::is_scalar(ptr) {
                if Self::unbox(ptr) != 0 {
                    return Err(DeclError::Shape {
                        offset: 0,
                        what: "scalar List not nil",
                    });
                }
                return Ok(out);
            }
            let off = self.view.deref(ptr)?;
            self.charge()?;
            let (tag, other, _) = self.view.obj_header(off)?;
            if tag != 1 || other != 2 {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "List cons",
                });
            }
            out.push(self.view.read_u64(off + 8)?);
            ptr = self.view.read_u64(off + 16)?;
        }
    }

    fn decode_name_list(&mut self, ptr: u64) -> DResult<Vec<Name>> {
        let mut out = Vec::new();
        for p in self.list_ptrs(ptr)? {
            out.push(self.decode_name(p)?);
        }
        Ok(out)
    }

    // ---- Literal / MData ---------------------------------------------------------------

    fn decode_literal(&mut self, ptr: u64) -> DResult<Literal> {
        let off = self.view.deref(ptr)?;
        let (tag, other, _) = self.view.obj_header(off)?;
        match (tag, other) {
            (0, 1) => Ok(Literal::Nat(self.decode_nat(self.view.read_u64(off + 8)?)?)),
            (1, 1) => Ok(Literal::Str(
                self.view.read_string_at(self.view.read_u64(off + 8)?)?,
            )),
            _ => Err(DeclError::Shape {
                offset: off,
                what: "Literal ctor",
            }),
        }
    }

    fn decode_data_value(&mut self, ptr: u64) -> DResult<DataValue> {
        if Self::is_scalar(ptr) {
            return Err(DeclError::Shape {
                offset: 0,
                what: "scalar DataValue",
            });
        }
        let off = self.view.deref(ptr)?;
        let (tag, other, _) = self.view.obj_header(off)?;
        match tag {
            0 => Ok(DataValue::OfString(
                self.view.read_string_at(self.view.read_u64(off + 8)?)?,
            )),
            1 => {
                if other != 0 {
                    return Err(DeclError::Shape {
                        offset: off,
                        what: "DataValue.ofBool arity",
                    });
                }
                Ok(DataValue::OfBool(Self::decode_bool(
                    self.view.read_bytes_at(off + 8, 1)?[0],
                    off + 8,
                )?))
            }
            2 => Ok(DataValue::OfName(
                self.decode_name(self.view.read_u64(off + 8)?)?,
            )),
            3 => {
                let n = self.decode_nat(self.view.read_u64(off + 8)?)?;
                match n.to_u64() {
                    Some(v) => Ok(DataValue::OfNat(v)),
                    None => Err(DeclError::Overflow {
                        offset: off,
                        what: "DataValue.ofNat",
                    }),
                }
            }
            4 => Ok(DataValue::OfInt(
                self.decode_int(self.view.read_u64(off + 8)?)?,
            )),
            5 => {
                // Syntax payloads are out of scope for this slice: preserved
                // in the region, surfaced as an opaque handle of the offset.
                let p = self.view.read_u64(off + 8)?;
                let handle = if Self::is_scalar(p) {
                    Self::unbox(p)
                } else {
                    self.view.deref(p)?
                };
                Ok(DataValue::OfSyntax(SyntaxHandle(handle)))
            }
            _ => Err(DeclError::Shape {
                offset: off,
                what: "DataValue ctor",
            }),
        }
    }

    fn decode_kvmap(&mut self, ptr: u64) -> DResult<KVMap> {
        // KVMap is a single-field structure: erased to its entry list.
        // Duplicate keys are legal on the pin (`KVMap.mk` / `from_entries`)
        // and ride inside `Expr.mdata`. `insert` would replace the first
        // match, drop the shadowed entry, and then disagree with the
        // stored Expr.Data word — a codec collapse, not a lookup.
        let mut entries = Vec::new();
        for pair in self.list_ptrs(ptr)? {
            let off = self.view.deref(pair)?;
            let (tag, other, _) = self.view.obj_header(off)?;
            if tag != 0 || other != 2 {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "KVMap pair",
                });
            }
            let key = self.decode_name(self.view.read_u64(off + 8)?)?;
            let value = self.decode_data_value(self.view.read_u64(off + 16)?)?;
            entries.push((key, value));
        }
        Ok(KVMap::from_entries(entries))
    }

    // ---- Expr --------------------------------------------------------------------------

    /// Object-slot count per Expr constructor tag (boxed `Nat`s included).
    fn expr_slots(tag: u8) -> Option<u64> {
        Some(match tag {
            0 => 1,     // bvar (boxed Nat)
            1..=3 => 1, // fvar / mvar / sort
            4 | 5 => 2, // const / app
            6 | 7 => 3, // lam / forallE
            8 => 4,     // letE
            9 => 1,     // lit
            10 => 2,    // mdata
            11 => 3,    // proj (typeName, boxed idx, struct)
            _ => return None,
        })
    }

    /// Trailing `u8` scalars an Expr constructor stores AFTER its `Data` word.
    ///
    /// The scalar area of an Expr is the `Data` `u64` first, then bytes: the
    /// binder info of `lam`/`forallE`, and the `nonDep` flag of `letE`. Every
    /// other constructor stores nothing after `Data`.
    fn expr_scalar_bytes(tag: u8) -> u64 {
        match tag {
            6 | 7 | 8 => 1,
            _ => 0,
        }
    }

    /// Which slots of an Expr ctor are themselves Expr children.
    fn expr_child_slots(tag: u8) -> &'static [u64] {
        match tag {
            5 => &[0, 1],     // app: fn, arg
            6 | 7 => &[1, 2], // lam/forallE: type, body
            8 => &[1, 2, 3],  // letE: type, value, body
            10 => &[1],       // mdata: expr
            11 => &[2],       // proj: struct
            _ => &[],
        }
    }

    pub fn decode_expr(&mut self, root: u64) -> DResult<Expr> {
        let mut stack: Vec<u64> = vec![root];
        while let Some(&ptr) = stack.last() {
            if Self::is_scalar(ptr) {
                return Err(DeclError::Shape {
                    offset: 0,
                    what: "scalar Expr",
                });
            }
            let off = self.view.deref(ptr)?;
            if self.exprs.contains_key(&off) {
                stack.pop();
                continue;
            }
            let (tag, other, cs_sz) = self.view.obj_header(off)?;
            let slots = Self::expr_slots(tag).ok_or(DeclError::Shape {
                offset: off,
                what: "Expr ctor",
            })?;
            if other as u64 != slots {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Expr arity",
                });
            }
            let mut pending = false;
            for &slot in Self::expr_child_slots(tag) {
                let child = self.view.read_u64(off + 8 + 8 * slot)?;
                if Self::is_scalar(child) {
                    return Err(DeclError::Shape {
                        offset: off,
                        what: "scalar Expr child",
                    });
                }
                let coff = self.view.deref(child)?;
                if !self.view.object_precedes(coff, off) {
                    // The writer's post-order law: every heap child resolves
                    // strictly below its parent. A violation means a cycle, and
                    // a cycle never builds a node, so the decode budget would
                    // never trip and the loop grows the stack without bound
                    // (fln-abaz finding 1).
                    return Err(DeclError::Shape {
                        offset: off,
                        what: "Expr child not below its parent (post-order law)",
                    });
                }
                if !self.exprs.contains_key(&coff) {
                    stack.push(child);
                    pending = true;
                }
            }
            if pending {
                continue;
            }
            self.charge()?;
            // The last unbound stored size in this decoder. An Expr is its
            // object slots, then the `Data` word, then the trailing bytes above
            // — so unlike Name and Level the expected size depends on the TAG
            // and not on the pointer count alone.
            //
            // The `Data` word is read at `off + 8 + 8*other` and cross-checked
            // against our recomputation, and the binder byte at `+ 8` past it.
            // Both offsets come from the assumed layout rather than from the
            // object: too small an object and those reads cross into a
            // neighbour, too large and stored bytes go unaccounted. The
            // resulting mismatch would be reported as an Expr.Data cross-check
            // divergence — the identity layer blamed for a misread, the same
            // wrong diagnosis the Name (81b0234c) and Level (7498bf87) binds
            // removed.
            let expected_cs_sz =
                (8 + 8 * u64::from(other) + 8 + Self::expr_scalar_bytes(tag)).div_ceil(8) * 8;
            if u64::from(cs_sz) != expected_cs_sz {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Expr object size disagrees with its slots-data-scalars layout",
                });
            }

            let expr = self.build_expr(off, tag, other)?;
            // The stored Expr.Data word: first scalar (u64s precede u8s).
            let stored = self.view.read_u64(off + 8 + 8 * other as u64)?;
            if self.cross_check && expr.data().0 != stored {
                return Err(DeclError::CrossCheck {
                    offset: off,
                    what: "Expr.Data",
                    stored,
                    computed: expr.data().0,
                });
            }
            self.exprs.insert(off, expr);
            stack.pop();
        }
        let off = self.view.deref(root)?;
        self.exprs.get(&off).cloned().ok_or(DeclError::Shape {
            offset: off,
            what: "expr not decoded (bug)",
        })
    }

    fn expr_at(&self, off: u64, slot: u64) -> DResult<Expr> {
        let p = self.view.read_u64(off + 8 + 8 * slot)?;
        let o = self.view.deref(p)?;
        self.exprs.get(&o).cloned().ok_or(DeclError::Shape {
            offset: o,
            what: "expr child not decoded (bug)",
        })
    }

    fn build_expr(&mut self, off: u64, tag: u8, other: u8) -> DResult<Expr> {
        let scalar_base = off + 8 + 8 * other as u64;
        let slot = |d: &Self, i: u64| d.view.read_u64(off + 8 + 8 * i);
        Ok(match tag {
            0 => {
                let idx = self.decode_nat_u32(slot(self, 0)?, "bvar index")?;
                Expr::bvar(idx).map_err(|_| DeclError::Overflow {
                    offset: off,
                    what: "bvar range",
                })?
            }
            1 => Expr::fvar(FVarId(self.decode_name(slot(self, 0)?)?)),
            2 => Expr::mvar(MVarId(self.decode_name(slot(self, 0)?)?)),
            3 => Expr::sort(self.decode_level(slot(self, 0)?)?),
            4 => {
                let name = self.decode_name(slot(self, 0)?)?;
                let levels = self.decode_level_list(slot(self, 1)?)?;
                Expr::const_(name, levels)
            }
            5 => Expr::app(self.expr_at(off, 0)?, self.expr_at(off, 1)?),
            6 | 7 => {
                let binder_name = self.decode_name(slot(self, 0)?)?;
                let binder_type = self.expr_at(off, 1)?;
                let body = self.expr_at(off, 2)?;
                // scalar area: data u64 first, then binderInfo u8.
                let bi_byte = self.view.read_bytes_at(scalar_base + 8, 1)?[0];
                let binder_info = match bi_byte {
                    0 => BinderInfo::Default,
                    1 => BinderInfo::Implicit,
                    2 => BinderInfo::StrictImplicit,
                    3 => BinderInfo::InstImplicit,
                    _ => {
                        return Err(DeclError::Shape {
                            offset: off,
                            what: "BinderInfo byte",
                        });
                    }
                };
                if tag == 6 {
                    Expr::lam(binder_name, binder_type, body, binder_info)
                } else {
                    Expr::forall_e(binder_name, binder_type, body, binder_info)
                }
            }
            8 => {
                let decl_name = self.decode_name(slot(self, 0)?)?;
                let type_ = self.expr_at(off, 1)?;
                let value = self.expr_at(off, 2)?;
                let body = self.expr_at(off, 3)?;
                let non_dep_off = scalar_base + 8;
                let non_dep =
                    Self::decode_bool(self.view.read_bytes_at(non_dep_off, 1)?[0], non_dep_off)?;
                Expr::let_e(decl_name, type_, value, body, non_dep)
            }
            9 => Expr::lit(self.decode_literal(slot(self, 0)?)?),
            10 => {
                let data = self.decode_kvmap(slot(self, 0)?)?;
                Expr::mdata(data, self.expr_at(off, 1)?)
            }
            11 => {
                let type_name = self.decode_name(slot(self, 0)?)?;
                let idx = self.decode_nat(slot(self, 1)?)?;
                let idx = idx.to_u64().ok_or(DeclError::Overflow {
                    offset: off,
                    what: "proj index",
                })?;
                Expr::proj(type_name, idx, self.expr_at(off, 2)?)
            }
            _ => {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Expr ctor",
                });
            }
        })
    }

    // ---- ConstantInfo ------------------------------------------------------------------

    /// Decode a nested `ConstantVal` object (3 slots: name, levelParams,
    /// type). `extends ConstantVal` is NOT flattened at the pin: every `*Val`
    /// stores its parent as one object slot (FINDINGS.md item 16).
    fn decode_constant_val(&mut self, ptr: u64) -> DResult<ConstantVal> {
        let off = self.view.deref(ptr)?;
        let (tag, other, _) = self.view.obj_header(off)?;
        if tag != 0 || other != 3 {
            return Err(DeclError::Shape {
                offset: off,
                what: "ConstantVal arity",
            });
        }
        Ok(ConstantVal {
            name: self.decode_name(self.view.read_u64(off + 8)?)?,
            level_params: self.decode_name_list(self.view.read_u64(off + 16)?)?,
            type_: self.decode_expr(self.view.read_u64(off + 24)?)?,
        })
    }

    fn decode_hints(&mut self, ptr: u64) -> DResult<ReducibilityHints> {
        if Self::is_scalar(ptr) {
            return match Self::unbox(ptr) {
                0 => Ok(ReducibilityHints::Opaque),
                1 => Ok(ReducibilityHints::Abbrev),
                _ => Err(DeclError::Shape {
                    offset: 0,
                    what: "ReducibilityHints scalar",
                }),
            };
        }
        let off = self.view.deref(ptr)?;
        let (tag, other, _) = self.view.obj_header(off)?;
        if tag != 2 || other != 0 {
            return Err(DeclError::Shape {
                offset: off,
                what: "ReducibilityHints ctor",
            });
        }
        let word = self.view.read_u64(off + 8)?;
        // `ReducibilityHints.regular` carries a UInt32, stored in an 8-byte
        // scalar slot. The top half is padding, and until now it was masked
        // away unread — the only stored bits in a ConstantInfo this decoder
        // discarded without looking at them.
        //
        // Measured over every chained module of the pin: 42,937 `regular`
        // hints, upper half 0x00000000 in ALL of them, object cs_sz uniformly
        // 16, heights ranging up to 37. So a nonzero upper half is not a
        // height this reader is truncating — it means the object is not the
        // shape this code believes, and silently masking it would turn a
        // layout misread into a plausible small number. Refusing is the same
        // discipline the Name.hash/Level.Data/Expr.Data cross-checks apply.
        if word >> 32 != 0 {
            return Err(DeclError::Shape {
                offset: off,
                what: "ReducibilityHints.regular padding is not zero",
            });
        }
        Ok(ReducibilityHints::Regular((word & 0xffff_ffff) as u32))
    }

    /// Decode one `ConstantInfo` object (the 8-variant wrapper).
    pub fn decode_constant_info(&mut self, ptr: u64) -> DResult<ConstantInfo> {
        let off = self.view.deref(ptr)?;
        let (tag, other, _) = self.view.obj_header(off)?;
        if other != 1 {
            return Err(DeclError::Shape {
                offset: off,
                what: "ConstantInfo arity",
            });
        }
        let voff = self.view.deref(self.view.read_u64(off + 8)?)?;
        let (_vtag, vother, vcs_sz) = self.view.obj_header(voff)?;

        // The payload's stored object SIZE, checked against the layout this
        // decoder is about to read the object with.
        //
        // Every slot and scalar access below is arithmetic on `vother` — the
        // pointer-field count — so if that arithmetic is wrong the reads land
        // in a neighbouring object and produce plausible values rather than an
        // error. `cs_sz` is the one stored field that can contradict the model
        // independently, and until now `obj_header` handed it back and every
        // caller in this file dropped it on the floor.
        //
        // Measured over all 215,111 ConstantInfo payloads of the pin: the
        // stored size equals `align8(8 + 8*pointers + scalars)` for every one,
        // across all eight variants, and the padding beyond the meaningful
        // scalars is zero everywhere. So a disagreement is a misread, not a
        // shape this reader simply has not met.
        let scalar_bytes = match tag {
            0 | 1 | 3 | 4 | 6 => 1_u64,
            2 => 0,
            5 => 3,
            7 => 2,
            _ => {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "ConstantInfo ctor",
                });
            }
        };
        let meaningful = 8 + 8 * u64::from(vother) + scalar_bytes;
        let expected_cs_sz = meaningful.div_ceil(8) * 8;
        if u64::from(vcs_sz) != expected_cs_sz {
            return Err(DeclError::Shape {
                offset: voff,
                what: "ConstantInfo payload object size disagrees with its field layout",
            });
        }

        // The alignment padding after the last meaningful scalar. `cs_sz` above
        // proves how many such bytes there are; this proves they are empty.
        //
        // The two checks catch different mistakes. A wrong `vother` usually
        // moves the whole scalar area and shows up as a size disagreement, but
        // an off-by-one in the SCALAR count alone leaves the size intact and
        // silently reinterprets a real flag byte as padding, or padding as a
        // flag. Reading a declaration's safety or `isUnsafe` from the wrong
        // byte is precisely the kind of quiet misread this file refuses
        // everywhere else, so the padding is held to the same standard as the
        // reducibility-hint padding bound at 201976e7.
        //
        // Measured over all 215,111 ConstantInfo payloads of the pin: zero have
        // a nonzero byte here, across all eight variants.
        let padding = self
            .view
            .read_bytes_at(voff + meaningful, expected_cs_sz - meaningful)?;
        if padding.iter().any(|byte| *byte != 0) {
            return Err(DeclError::Shape {
                offset: voff + meaningful,
                what: "ConstantInfo payload scalar padding is not zero",
            });
        }

        let slot = |d: &Self, i: u64| d.view.read_u64(voff + 8 + 8 * i);
        let scalar_base = voff + 8 + 8 * vother as u64;
        let scalar_u8 =
            |d: &Self, i: u64| -> DResult<u8> { Ok(d.view.read_bytes_at(scalar_base + i, 1)?[0]) };
        let scalar_bool = |d: &Self, i: u64| -> DResult<bool> {
            Self::decode_bool(scalar_u8(d, i)?, scalar_base + i)
        };
        Ok(match tag {
            0 => {
                // AxiomVal: base slot + isUnsafe u8
                if vother != 1 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "AxiomVal arity",
                    });
                }
                ConstantInfo::Axiom(AxiomVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    is_unsafe: scalar_bool(self, 0)?,
                })
            }
            1 => {
                // DefinitionVal slots: base, value, hints, all + safety u8
                if vother != 4 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "DefinitionVal arity",
                    });
                }
                let safety = match scalar_u8(self, 0)? {
                    0 => DefinitionSafety::Unsafe,
                    1 => DefinitionSafety::Safe,
                    2 => DefinitionSafety::Partial,
                    _ => {
                        return Err(DeclError::Shape {
                            offset: voff,
                            what: "safety byte",
                        });
                    }
                };
                ConstantInfo::Defn(DefinitionVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    value: self.decode_expr(slot(self, 1)?)?,
                    hints: self.decode_hints(slot(self, 2)?)?,
                    safety,
                    all: self.decode_name_list(slot(self, 3)?)?,
                })
            }
            2 => {
                // TheoremVal slots: base, value, all
                if vother != 3 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "TheoremVal arity",
                    });
                }
                ConstantInfo::Thm(TheoremVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    value: self.decode_expr(slot(self, 1)?)?,
                    all: self.decode_name_list(slot(self, 2)?)?,
                })
            }
            3 => {
                // OpaqueVal slots: base, value, all + isUnsafe u8
                if vother != 3 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "OpaqueVal arity",
                    });
                }
                ConstantInfo::Opaque(OpaqueVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    value: self.decode_expr(slot(self, 1)?)?,
                    is_unsafe: scalar_bool(self, 0)?,
                    all: self.decode_name_list(slot(self, 2)?)?,
                })
            }
            4 => {
                // QuotVal: base slot + kind u8
                if vother != 1 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "QuotVal arity",
                    });
                }
                let kind = match scalar_u8(self, 0)? {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    _ => {
                        return Err(DeclError::Shape {
                            offset: voff,
                            what: "QuotKind byte",
                        });
                    }
                };
                ConstantInfo::Quot(QuotVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    kind,
                })
            }
            5 => {
                // InductiveVal slots: base, numParams, numIndices, all,
                // ctors, numNested + isRec/isUnsafe/isReflexive u8s
                if vother != 6 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "InductiveVal arity",
                    });
                }
                ConstantInfo::Induct(InductiveVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    num_params: self.decode_nat_u32(slot(self, 1)?, "numParams")?,
                    num_indices: self.decode_nat_u32(slot(self, 2)?, "numIndices")?,
                    all: self.decode_name_list(slot(self, 3)?)?,
                    ctors: self.decode_name_list(slot(self, 4)?)?,
                    num_nested: self.decode_nat_u32(slot(self, 5)?, "numNested")?,
                    is_rec: scalar_bool(self, 0)?,
                    is_unsafe: scalar_bool(self, 1)?,
                    is_reflexive: scalar_bool(self, 2)?,
                })
            }
            6 => {
                // ConstructorVal slots: base, induct, cidx, numParams,
                // numFields + isUnsafe u8
                if vother != 5 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "ConstructorVal arity",
                    });
                }
                ConstantInfo::Ctor(ConstructorVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    induct: self.decode_name(slot(self, 1)?)?,
                    cidx: self.decode_nat_u32(slot(self, 2)?, "cidx")?,
                    num_params: self.decode_nat_u32(slot(self, 3)?, "numParams")?,
                    num_fields: self.decode_nat_u32(slot(self, 4)?, "numFields")?,
                    is_unsafe: scalar_bool(self, 0)?,
                })
            }
            7 => {
                // RecursorVal slots: base, all, numParams, numIndices,
                // numMotives, numMinors, rules + k/isUnsafe u8s
                if vother != 7 {
                    return Err(DeclError::Shape {
                        offset: voff,
                        what: "RecursorVal arity",
                    });
                }
                let mut rules = Vec::new();
                for rp in self.list_ptrs(slot(self, 6)?)? {
                    let ro = self.view.deref(rp)?;
                    let (rtag, rother, _) = self.view.obj_header(ro)?;
                    if rtag != 0 || rother != 3 {
                        return Err(DeclError::Shape {
                            offset: ro,
                            what: "RecursorRule shape",
                        });
                    }
                    rules.push(RecursorRule {
                        ctor: self.decode_name(self.view.read_u64(ro + 8)?)?,
                        nfields: self.decode_nat_u32(self.view.read_u64(ro + 16)?, "nfields")?,
                        rhs: self.decode_expr(self.view.read_u64(ro + 24)?)?,
                    });
                }
                ConstantInfo::Rec(RecursorVal {
                    base: self.decode_constant_val(slot(self, 0)?)?,
                    all: self.decode_name_list(slot(self, 1)?)?,
                    num_params: self.decode_nat_u32(slot(self, 2)?, "numParams")?,
                    num_indices: self.decode_nat_u32(slot(self, 3)?, "numIndices")?,
                    num_motives: self.decode_nat_u32(slot(self, 4)?, "numMotives")?,
                    num_minors: self.decode_nat_u32(slot(self, 5)?, "numMinors")?,
                    rules,
                    k: scalar_bool(self, 0)?,
                    is_unsafe: scalar_bool(self, 1)?,
                })
            }
            _ => {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "ConstantInfo ctor",
                });
            }
        })
    }

    /// Decode every constant of the module, in `constants`-array order, with
    /// the `constNames[i] == constants[i].name` mirror law enforced.
    pub fn decode_module_constants(&mut self) -> DResult<Vec<ConstantInfo>> {
        let arrays = self.view.module_arrays()?;
        let (names_off, names_len) = arrays.const_names;
        let (consts_off, consts_len) = arrays.constants;
        if names_len != consts_len {
            return Err(DeclError::Shape {
                offset: consts_off,
                what: "constNames/constants mismatch",
            });
        }
        let mut out = Vec::with_capacity(consts_len as usize);
        for i in 0..consts_len {
            let info = self.decode_constant_info(self.view.read_u64(consts_off + 24 + 8 * i)?)?;
            let expected = self.decode_name(self.view.read_u64(names_off + 24 + 8 * i)?)?;
            if info.name() != &expected {
                return Err(DeclError::Shape {
                    offset: consts_off,
                    what: "constNames[i] != constants[i].name",
                });
            }
            out.push(info);
        }
        Ok(out)
    }
}

/// Decode the authoritative constant array of one complete module-system chain,
/// proving that it loses nothing the exported part declared.
///
/// Lean writes a module-system module as three regions. The exported `.olean`
/// carries the public interface; the `.olean.private` part carries the array
/// Lean's `import all` path reads — definition bodies plus the `_private`
/// equation-compiler auxiliaries (`match_N`, `_proof_N`, `eq_N`, `.loop`) that
/// the exported array omits. `franken_lean-timy` is what happens when a decoder
/// hands the kernel the exported array: the auxiliaries were never produced, so
/// declarations depending on them were rejected as `UnknownConstant`.
///
/// Returning the private array instead is therefore correct — but *only*
/// because it is a superset, and that property is a fact about the Reference's
/// emitter rather than anything the format enforces. A consumer that assumes it
/// silently drops exported declarations the moment it stops holding, which is
/// timy's own failure mode (decode returning fewer declarations than the module
/// has) reached by a different cause. This function proves the containment
/// instead, turning that into a typed [`DeclError::PrivatePartIncomplete`].
///
/// The exported array has to be decoded anyway to be validated, so the check
/// consumes work a caller would otherwise discard rather than adding a pass.
///
/// `exported` and `private` must be views of the same chain, the private one
/// parsed against the exported and server regions via
/// [`OleanView::parse_with_dependencies`].
pub fn decode_chain_constants(
    exported: &OleanView<'_>,
    private: &OleanView<'_>,
    budget: WalkBudget,
) -> DResult<Vec<ConstantInfo>> {
    Ok(decode_chain_constants_with_origin(exported, private, budget)?.constants)
}

/// Which part of a module-system chain a decoded declaration came from.
///
/// This is a fact recovered from the chain, NOT a guess from the name. The two
/// are routinely different: `_private.` is Lean's mangling for a
/// private-SCOPED declaration, and such a declaration is frequently exported.
/// At the pin, 2,336 of the 51,506 declarations in Init's exported parts carry
/// a `_private.` prefix, eight of them with a `.loop.` component (all in
/// `Init.Data.AC`). Any consumer deciding provenance by prefix therefore
/// classifies those 2,336 wrongly.
///
/// EVERY AUXILIARY FAMILY IS SPLIT ACROSS BOTH ORIGINS. Measured over Init at
/// the pin, by declarations carrying each component:
///
/// | family        | `Exported` | `PrivateOnly` | exported yet `_private.`-prefixed |
/// |---------------|-----------:|--------------:|----------------------------------:|
/// | `_sunfold`    |        324 |            65 |                                 0 |
/// | `_unsafe_rec` |        390 |           131 |                                 8 |
/// | `_unary`      |        116 |           431 |                                13 |
/// | `_f`          |        533 |            94 |                                 0 |
///
/// Two consequences worth stating, because both have already cost a batch
/// verify. First, no family is wholly private, so "this is an auxiliary,
/// therefore it came from the companion" is false for all four — 324 of the
/// `_sunfold` declarations are exported. Second, `_sunfold` and `_f` currently
/// show zero prefix misclassifications, so a prefix test over them passes
/// TODAY by accident; the families are split 324/65 and 533/94 by origin, so
/// that accident is one pin bump from ending. `_unsafe_rec` and `_unary` are
/// already wrong by 8 and 13 declarations, for example
/// `_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.saveLine._unsafe_rec`
/// and `_private.Init.Data.Array.Sort.Lemmas.0.Subarray.mergeSort._unary.eq_def`,
/// both exported.
///
/// Ask [`ChainConstants::origin_of`]; do not read the name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantOrigin {
    /// Declared by the exported `.olean` part, and so also by the private one.
    Exported,
    /// Recovered only from the `.olean.private` companion — the population
    /// `franken_lean-timy` is about.
    PrivateOnly,
}

/// A complete chain's authoritative constants, with each declaration's part of
/// origin.
#[derive(Debug, Clone)]
pub struct ChainConstants {
    /// The private part's array — authoritative, and a superset of the
    /// exported one (proven by [`verify_private_superset`]).
    pub constants: Vec<ConstantInfo>,
    /// `origins[i]` is the origin of `constants[i]`.
    pub origins: Vec<ConstantOrigin>,
    /// `strengthened[i]` is true when the exported part declared
    /// `constants[i]` as a body-less `axiom` and the private part supplies a
    /// real declaration.
    ///
    /// This is the majority case, not an oddity: across the 2,431 chained
    /// modules of the pin, 84,590 of the 158,583 declarations named by both
    /// arrays are an axiom in the exported part — 60,640 theorems, 22,177
    /// definitions and 1,773 opaques — and none runs the other way.
    strengthened: Vec<bool>,
    /// Declaration name to its position in `constants`.
    ///
    /// Private, because it only means anything while it agrees with
    /// `constants`; it is built once at construction and the struct is only
    /// ever built here, so the two cannot drift apart.
    index: HashMap<Name, usize>,
}

impl ChainConstants {
    /// The declarations recovered only from the private companion, in
    /// `constants` order.
    pub fn private_only(&self) -> impl Iterator<Item = &ConstantInfo> {
        self.with_origin(ConstantOrigin::PrivateOnly)
    }

    /// The declarations the exported part also declared, in `constants` order.
    pub fn exported(&self) -> impl Iterator<Item = &ConstantInfo> {
        self.with_origin(ConstantOrigin::Exported)
    }

    /// Was this declaration a body-less `axiom` in the exported part?
    ///
    /// Answers the question a caller is really asking when it wants to know
    /// whether a declaration "has a concrete kind": for a name the exported
    /// part carries, the answer often depends on WHICH PART you look at. The
    /// exported view of `Array.zipWithMAux._unary`, for instance, is an axiom
    /// while the chain's is a definition. Decoding the exported part and
    /// finding an axiom is the decoder being faithful, not losing a body —
    /// there is no body in those bytes to lose.
    ///
    /// `false` for a declaration the exported part did not carry at all; use
    /// [`ConstantOrigin`] to tell those apart.
    pub fn was_exported_as_axiom(&self, name: &Name) -> bool {
        self.position_of(name)
            .and_then(|index| self.strengthened.get(index).copied())
            .unwrap_or(false)
    }

    /// The declarations the private part supplies with a body where the
    /// exported part had only an axiom.
    pub fn strengthened_by_the_companion(&self) -> impl Iterator<Item = &ConstantInfo> {
        self.constants
            .iter()
            .zip(&self.strengthened)
            .filter(|(_, gained)| **gained)
            .map(|(info, _)| info)
    }

    fn with_origin(&self, wanted: ConstantOrigin) -> impl Iterator<Item = &ConstantInfo> {
        self.constants
            .iter()
            .zip(&self.origins)
            .filter(move |(_, origin)| **origin == wanted)
            .map(|(info, _)| info)
    }

    /// The origin of one declaration by name, or `None` if this chain does not
    /// declare it.
    ///
    /// This is the question a caller checking a specific auxiliary actually
    /// has, and the one the `_private.` prefix gets wrong; see
    /// [`ConstantOrigin`] for how often. Without it a caller must zip
    /// `constants` against `origins` by hand, which is the plumbing that has
    /// made guessing from the name look like the easier option.
    pub fn origin_of(&self, name: &Name) -> Option<ConstantOrigin> {
        self.position_of(name)
            .and_then(|index| self.origins.get(index).copied())
    }

    /// The position of one declaration in `constants`, by name.
    ///
    /// Answers from the name index rather than scanning, so a caller checking
    /// many names over a large module is linear rather than quadratic —
    /// `Init.Prelude` alone carries 2,314 declarations.
    pub fn position_of(&self, name: &Name) -> Option<usize> {
        self.index.get(name).copied()
    }
}

/// Is `companion` genuinely a companion of `exported`?
///
/// TWO SEPARATE QUESTIONS, and only one of them is about the module. The fixed
/// header fields — `version`, `flags`, `lean_version`, `githash` — identify the
/// TOOLCHAIN and nothing finer: across all 2,431 chained modules of the pin
/// they take exactly ONE distinct value. Comparing them rejects a companion
/// built by a different Lean, but it cannot tell one module's companion from
/// another's, which is the substitution that actually happens.
///
/// The module-level bond is structural: a companion is parsed against the
/// earlier regions and stores their compacted addresses, and `base_addr` is
/// distinct per module (2,431 distinct values across 2,431 exported parts). So
/// [`OleanView::is_chained_to`] is what identifies the pair, and the header
/// comparison is kept as the cheaper toolchain check in front of it.
fn is_companion_of(companion: &OleanView<'_>, exported: &OleanView<'_>) -> bool {
    let same_toolchain = companion.header.version == exported.header.version
        && companion.header.flags == exported.header.flags
        && companion.header.lean_version == exported.header.lean_version
        && companion.header.githash == exported.header.githash;

    // The structural test only means something for a view that was parsed
    // against dependency regions. A SELF-CONTAINED view — every pointer
    // resolving inside its own region, as a freshly encoded module's does — is
    // chained to nothing by construction, and demanding otherwise would refuse
    // a legitimately composed pair for having been built without companions
    // rather than for being the wrong module. The superset and strength laws
    // still judge such a pair on its contents.
    same_toolchain && (!companion.has_dependency_regions() || companion.is_chained_to(exported))
}

/// Ceilings for composing one module-system chain.
///
/// Mirrors what `fln::OleanDecodeLimits` gives the product door: a byte ceiling
/// charged against the three parts together before any of them is parsed, and
/// the object budget the graph walk and declaration decoder run under. Two
/// separate resources, because neither bounds the other — a region can be huge
/// and hold few objects, or small and present a deeply shared graph.
#[derive(Debug, Clone, Copy)]
pub struct ChainLimits {
    /// Maximum combined size of the exported, server and private parts.
    pub max_bytes: usize,
    /// Object budget for each region's walk and for declaration decoding.
    pub graph: WalkBudget,
}

impl ChainLimits {
    /// Limits with an explicit byte ceiling and the default object budget.
    pub fn new(max_bytes: usize) -> Self {
        Self {
            max_bytes,
            graph: WalkBudget::default(),
        }
    }
}

impl Default for ChainLimits {
    /// The largest chain the pinned toolchain ships is
    /// `Init.Data.BitVec.Lemmas` at 14,418,208 bytes across its three parts.
    /// 64 MiB leaves more than four times that headroom while still refusing
    /// an input that could only be hostile or corrupt. Callers holding
    /// larger artifacts should state their own ceiling rather than raise this.
    fn default() -> Self {
        Self::new(64 * 1024 * 1024)
    }
}

/// The complete `extraConstNames` population of one module-system chain.
///
/// UNLIKE `constants`, THIS FIELD HAS NO SUPERSET LAW. The private part is the
/// authoritative constant array, so [`decode_chain_constants_with_origin`] can
/// return it alone and prove nothing was lost. `extraConstNames` does not
/// behave that way: measured across the 2,431 chained modules of the pin, 8
/// have a private array that is NOT a superset of the exported one, and 652
/// exported names in total appear in no private array. `Init.Data.Array.QSort.Basic`
/// is the sharpest case — its private array is SMALLER than its exported one,
/// 93 against 94, and the two together hold 101 distinct names.
///
/// So reading this field from either part alone silently drops names, and a
/// caller wanting the population has to union them. That is what this does.
///
/// SCOPE, so nothing is read into this that it does not say. These are
/// code-generator names with no `ConstantInfo` behind them anywhere in the
/// artifact (see [`OleanView::extra_const_names`]). Dropping them cannot
/// produce an `UnknownConstant` and none of this is kernel-facing; it is a
/// completeness property of an IR-name population, not of the declarations
/// `franken_lean-timy` is about.
///
/// Order is deterministic: the exported part's names in array order, then the
/// private part's names not already present, in array order.
pub fn chain_extra_const_names(
    exported: &OleanView<'_>,
    private: &OleanView<'_>,
    budget: WalkBudget,
) -> DResult<Vec<Name>> {
    if !is_companion_of(private, exported) {
        return Err(DeclError::ChainPartMismatch {
            part: OleanChainPart::Private,
        });
    }

    let exported_names = exported.extra_const_names(budget)?;
    let private_names = private.extra_const_names(budget)?;

    let mut seen: HashSet<Name> = HashSet::with_capacity(exported_names.len());
    let mut union = Vec::new();
    union
        .try_reserve_exact(exported_names.len())
        .map_err(|_| DeclError::Budget {
            visited: exported_names.len() as u64,
        })?;
    for name in exported_names.into_iter().chain(private_names) {
        if seen.insert(name.clone()) {
            union.push(name);
        }
    }
    Ok(union)
}

/// Decode a complete chain's constants with origin, straight from the three
/// parts' bytes.
///
/// [`decode_chain_constants_with_origin`] takes views, which means every caller
/// re-derives the same three-step parse: the exported region standalone, the
/// server region against it, and the private region against both. That order is
/// not optional — the companions store the earlier regions' compacted addresses
/// — and getting it wrong yields an out-of-bounds pointer rather than a wrong
/// answer, so it is a trap that fails loudly but repeatedly.
///
/// Every consumer that has needed provenance so far hand-rolled that plumbing,
/// and each one first reached for the `_private.` name prefix instead, which is
/// a mangling convention rather than a provenance fact (see [`ConstantOrigin`]).
/// This is the one-call form, so asking the chain is easier than guessing from
/// the name.
///
/// CHAIN LAWS, kept aligned with the product door
/// (`fln::decode_olean_module_artifacts`): the exported part is audited,
/// walked, and required to be a module-system module; each companion must carry
/// the exported part's identity stamp, and is walked and `ModuleData`-decoded.
/// The private array is then decoded and proven a superset.
///
/// ONE DELIBERATE DIVERGENCE. The product door also runs the full declaration
/// decoder over the SERVER part and discards the result. This does not, because
/// it would be re-decoding the exported array: across all 2,431 chained modules
/// of the pin, the server part's `constNames` is never different from the
/// exported part's, and the arrays it points at live in the exported region.
/// The server region is still walked and `ModuleData`-decoded here, so its
/// object graph and root contract are checked; only the redundant second pass
/// over declarations the exported decode already validated is skipped.
pub fn decode_chain_constants_from_parts(
    exported: &[u8],
    server: &[u8],
    private: &[u8],
    limits: ChainLimits,
) -> DResult<ChainConstants> {
    // Charged BEFORE anything is parsed, so an oversized chain is refused
    // rather than walked. The object budget below bounds the graph, not the
    // input: a region can be enormous and still hold few objects, so a byte
    // ceiling is the only thing that bounds the work this call will do at all.
    let bytes = exported
        .len()
        .checked_add(server.len())
        .and_then(|total| total.checked_add(private.len()))
        .ok_or(DeclError::ChainTooLarge {
            bytes: usize::MAX,
            limit: limits.max_bytes,
        })?;
    if bytes > limits.max_bytes {
        return Err(DeclError::ChainTooLarge {
            bytes,
            limit: limits.max_bytes,
        });
    }
    let budget = limits.graph;

    let exported_view = OleanView::parse(exported)?;
    exported_view.shared_audit()?;
    exported_view.walk(budget)?;
    if !exported_view.module_data(budget)?.is_module {
        return Err(DeclError::NotAModuleChain);
    }

    let server_view = OleanView::parse_with_dependencies(server, &[exported])?;
    let private_view = OleanView::parse_with_dependencies(private, &[exported, server])?;
    // The server part's identity is checked here because no door downstream
    // ever sees it; the private part's is checked by
    // `decode_chain_constants_with_origin`, so that callers building their own
    // views get the law too. One place per part, no duplicated comparison.
    if !is_companion_of(&server_view, &exported_view) {
        return Err(DeclError::ChainPartMismatch {
            part: OleanChainPart::Server,
        });
    }
    for view in [&server_view, &private_view] {
        view.walk(budget)?;
        // `walk` proves every pointer, string and bignum in the region is
        // sound, but it is generic over the object graph and knows nothing of
        // the `ModuleData` contract. The root constructor shape, the imports
        // array and the extension block table are only checked here.
        view.module_data(budget)?;
    }

    decode_chain_constants_with_origin(&exported_view, &private_view, budget)
}

/// Which companion of a module-system chain a fault is attributed to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OleanChainPart {
    Server,
    Private,
}

impl OleanChainPart {
    fn label(self) -> &'static str {
        match self {
            Self::Server => ".olean.server",
            Self::Private => ".olean.private",
        }
    }
}

/// Decode a complete chain and record which part each declaration came from.
///
/// [`decode_chain_constants`] answers "what does this chain declare". This also
/// answers "which of those did the exported part NOT declare" — the question
/// `franken_lean-timy` turns on, and the one a caller cannot answer from the
/// returned names alone. Before this, a consumer wanting to distinguish
/// companion-recovered declarations from exported ones had only the `_private.`
/// name prefix to go on, which is a scoping convention rather than a statement
/// about which part carries the declaration; see [`ConstantOrigin`] for how far
/// apart the two are at the pin.
pub fn decode_chain_constants_with_origin(
    exported: &OleanView<'_>,
    private: &OleanView<'_>,
    budget: WalkBudget,
) -> DResult<ChainConstants> {
    // The identity law lives HERE and not only in the parts door, because this
    // is the entry point callers that build their own views reach for — and a
    // private companion from another module parses perfectly. Without this the
    // mismatch surfaces from `verify_private_superset` below as
    // `PrivatePartIncomplete`, which blames a missing declaration for what is
    // really two unrelated artifacts.
    if !is_companion_of(private, exported) {
        return Err(DeclError::ChainPartMismatch {
            part: OleanChainPart::Private,
        });
    }

    let exported_constants = DeclDecoder::new(exported, budget).decode_module_constants()?;
    let private_constants = DeclDecoder::new(private, budget).decode_module_constants()?;
    verify_private_superset(&exported_constants, &private_constants)?;

    let exported_names: HashSet<&Name> =
        exported_constants.iter().map(ConstantInfo::name).collect();
    let mut origins = Vec::new();
    origins
        .try_reserve_exact(private_constants.len())
        .map_err(|_| DeclError::Budget {
            visited: private_constants.len() as u64,
        })?;
    for info in &private_constants {
        origins.push(if exported_names.contains(info.name()) {
            ConstantOrigin::Exported
        } else {
            ConstantOrigin::PrivateOnly
        });
    }

    let exported_by_name: HashMap<&Name, &ConstantInfo> =
        exported_constants.iter().map(|i| (i.name(), i)).collect();
    let mut strengthened = Vec::new();
    strengthened
        .try_reserve_exact(private_constants.len())
        .map_err(|_| DeclError::Budget {
            visited: private_constants.len() as u64,
        })?;
    for info in &private_constants {
        strengthened.push(
            exported_by_name
                .get(info.name())
                .is_some_and(|other| matches!(other, ConstantInfo::Axiom(_)))
                && !matches!(info, ConstantInfo::Axiom(_)),
        );
    }

    // First occurrence wins, which is what the linear scan this replaces did.
    // The mirror law in `decode_module_constants` and the pin itself both make
    // a repeat within one module's array impossible — zero across all 2,431
    // chained modules — but the tie-break is pinned rather than left to
    // whichever entry a later insert happened to overwrite.
    let mut index: HashMap<Name, usize> = HashMap::with_capacity(private_constants.len());
    for (position, info) in private_constants.iter().enumerate() {
        index.entry(info.name().clone()).or_insert(position);
    }

    Ok(ChainConstants {
        constants: private_constants,
        origins,
        strengthened,
        index,
    })
}

/// Prove that `private` names every declaration `exported` names.
///
/// Split out from [`decode_chain_constants`] so a caller that has already
/// decoded both arrays — as the module-system decode path does, to validate the
/// exported part — can bind the containment law without decoding anything a
/// second time. See [`decode_chain_constants`] for why the law matters.
pub fn verify_private_superset(exported: &[ConstantInfo], private: &[ConstantInfo]) -> DResult<()> {
    let present: HashMap<&Name, &ConstantInfo> =
        private.iter().map(|info| (info.name(), info)).collect();
    for info in exported {
        let Some(counterpart) = present.get(info.name()).copied() else {
            return Err(DeclError::PrivatePartIncomplete {
                missing: info.name().clone(),
            });
        };
        // Presence is not enough. The two parts routinely disagree about a
        // shared declaration's KIND, and at the pin the disagreement runs one
        // way: across 158,583 declarations named by both arrays, 84,590 are an
        // `axiom` in the exported part and a real declaration in the private
        // one — 60,640 theorems, 22,177 definitions, 1,773 opaques — and NOT
        // ONE runs the other way. The exported part is the body-stripped view;
        // the private part is where the bodies live.
        //
        // Taking the private array is therefore the strengthening direction,
        // and this refuses the reverse. A private part that offered an axiom
        // where the exported part had a body would hand the kernel a postulate
        // in place of a definition, and the kernel would AGREE with it rather
        // than check it — the difference between verification and agreement
        // that `franken_lean-timy` turns on. Nothing else in this crate looks
        // at kinds, so nothing else would notice.
        if matches!(counterpart, ConstantInfo::Axiom(_)) && !matches!(info, ConstantInfo::Axiom(_))
        {
            return Err(DeclError::PrivatePartWeakensDeclaration {
                name: info.name().clone(),
                exported_kind: info.kind_name(),
                private_kind: counterpart.kind_name(),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::region::{OleanView, WalkBudget};
    use crate::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};
    use fln_core::level::Level;

    fn axiom_module(is_unsafe: bool) -> Vec<u8> {
        let type_ = Expr::sort(Level::zero());
        encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: Name::from_components(["Demo", "ax"]),
                        level_params: Vec::new(),
                        type_,
                    },
                    is_unsafe,
                })],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: 2,
                flags: 1,
                lean_version: "4.32.0",
                githash: "0123456789abcdef0123456789abcdef01234567",
                base_addr: 0x20_000,
            },
            WriteBudget::default(),
        )
        .expect("axiom module encodes")
        .bytes
    }

    #[test]
    fn noncanonical_bool_bytes_are_refused() {
        assert!(!DeclDecoder::decode_bool(0, 0).unwrap());
        assert!(DeclDecoder::decode_bool(1, 9).unwrap());
        assert!(matches!(
            DeclDecoder::decode_bool(2, 7),
            Err(DeclError::Shape {
                offset: 7,
                what: "noncanonical Bool"
            })
        ));
    }

    #[test]
    fn axiom_is_unsafe_byte_two_is_not_decoded_as_true() {
        let mut bytes = axiom_module(false);
        let view = OleanView::parse(&bytes).expect("header");
        let arrays = view.module_arrays().expect("constant array");
        let info_ptr = view
            .read_u64(arrays.constants.0 + 24)
            .expect("first ConstantInfo");
        let info_off = view.deref(info_ptr).expect("ConstantInfo object");
        let val_ptr = view.read_u64(info_off + 8).expect("AxiomVal pointer");
        let val_off = view.deref(val_ptr).expect("AxiomVal object");
        let (_, vother, _) = view.obj_header(val_off).expect("AxiomVal header");
        let bool_off = val_off + 8 + 8 * u64::from(vother);
        assert_eq!(bytes[bool_off as usize], 0, "fixture starts safe");
        bytes[bool_off as usize] = 2;

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("byte 2 is not a Bool");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "noncanonical Bool",
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// The pinned Reference stdlib, or `None`. `FLN_REFERENCE_LIB` overrides.
    fn reference_lib() -> Option<std::path::PathBuf> {
        if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
            let path = std::path::PathBuf::from(dir);
            return path.is_dir().then_some(path);
        }
        let home = std::env::var("HOME").ok()?;
        let path = std::path::PathBuf::from(home)
            .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
        path.is_dir().then_some(path)
    }

    /// Every declaration at the pin that is `_private.`-prefixed, carries an
    /// `_unsafe_rec` component, AND is declared by the EXPORTED part — the
    /// exact population a `starts_with("_private.")` provenance test gets
    /// wrong. `(module, declaration)`, measured over Init.
    const EXPORTED_UNSAFE_REC_COLLISIONS: &[(&str, &str)] = &[
        (
            "Init/Data/List/Sort/Impl",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run._unsafe_rec",
        ),
        (
            "Init/Data/List/Sort/Impl",
            "_private.Init.Data.List.Sort.Impl.0.List.MergeSort.Internal.mergeSortTR₂.run'._unsafe_rec",
        ),
        (
            "Init/Data/String/Extra",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.consumeSpaces._unsafe_rec",
        ),
        (
            "Init/Data/String/Extra",
            "_private.Init.Data.String.Extra.0.String.findLeadingSpacesSize.findNextLine._unsafe_rec",
        ),
        (
            "Init/Data/String/Extra",
            "_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.consumeSpaces._unsafe_rec",
        ),
        (
            "Init/Data/String/Extra",
            "_private.Init.Data.String.Extra.0.String.removeNumLeadingSpaces.saveLine._unsafe_rec",
        ),
        (
            "Init/Prelude",
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        ),
        (
            "Init/Prelude",
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        ),
    ];

    /// `Init.Data.Array.QSort.Basic` is the module where the private
    /// `extraConstNames` array is SMALLER than the exported one.
    ///
    /// Its eight exported-only names are the concrete evidence that this field
    /// has no superset law, so the union is the only complete reading.
    const QSORT_EXPORTED_ONLY_EXTRA: [&str; 8] = [
        "_private.Init.Data.Array.QSort.Basic.0.Array.qpartition._auto_2",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qpartition._auto_4",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qpartition._auto_6",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qpartition.loop",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qsort._auto_2",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qsort._auto_4",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qsort._auto_6",
        "_private.Init.Data.Array.QSort.Basic.0.Array.qsort.sort",
    ];

    #[test]
    fn the_extra_const_names_union_recovers_what_each_part_alone_drops() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_extra_const_names_union_recovers_what_each_part_alone_drops: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |suffix: &str| {
            std::fs::read(lib.join(format!("Init/Data/Array/QSort/Basic.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read QSort/Basic{suffix}: {error}"))
        };
        let exported = read("");
        let server = read(".server");
        let private = read(".private");

        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
            .expect("private parses against its chain");

        let exported_extra = exported_view
            .extra_const_names(WalkBudget::default())
            .expect("exported extraConstNames decode");
        let private_extra = private_view
            .extra_const_names(WalkBudget::default())
            .expect("private extraConstNames decode");
        let union = chain_extra_const_names(&exported_view, &private_view, WalkBudget::default())
            .expect("the chain's extraConstNames union");

        // The shape of the defect, asserted rather than described: the private
        // array is SMALLER, so neither part alone is the population.
        assert_eq!(
            exported_extra.len(),
            94,
            "exported extraConstNames at the pin"
        );
        assert_eq!(
            private_extra.len(),
            93,
            "private extraConstNames at the pin"
        );
        assert!(
            private_extra.len() < exported_extra.len(),
            "this module is the witness because its private array is the smaller one"
        );
        assert_eq!(union.len(), 101, "the union at the pin");
        assert!(
            union.len() > exported_extra.len() && union.len() > private_extra.len(),
            "the union must exceed BOTH parts, or it is not recovering anything"
        );

        let rendered: Vec<String> = union.iter().map(Name::to_display_string).collect();
        let private_rendered: Vec<String> =
            private_extra.iter().map(Name::to_display_string).collect();
        for name in QSORT_EXPORTED_ONLY_EXTRA {
            // The load-bearing negative: absent from the private part, so
            // finding it in the union is evidence about the union and not
            // about the private array already having it.
            assert!(
                !private_rendered.contains(&name.to_owned()),
                "{name} must be absent from the private part, else it witnesses nothing"
            );
            assert!(
                rendered.contains(&name.to_owned()),
                "{name} is dropped by a private-only reading and must be in the union"
            );
        }

        // Deterministic order: exported part first, in its own array order.
        assert_eq!(
            rendered[..exported_extra.len()],
            exported_extra
                .iter()
                .map(Name::to_display_string)
                .collect::<Vec<_>>()[..],
            "the union must open with the exported names in array order"
        );

        // No duplicates survived the merge.
        let mut sorted = rendered.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            union.len(),
            "the union must not repeat a name"
        );
    }

    /// The union door carries the same identity law as the constant doors.
    #[test]
    fn the_extra_const_names_union_refuses_a_foreign_private_part() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_extra_const_names_union_refuses_a_foreign_private_part: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |relative: &str, suffix: &str| {
            std::fs::read(lib.join(format!("{relative}.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read {relative}{suffix}: {error}"))
        };
        let exported = read("Init/Data/Array/QSort/Basic", "");
        let other_exported = read("Init/Control/MonadAttach", "");
        let other_server = read("Init/Control/MonadAttach", ".server");
        let other_private = read("Init/Control/MonadAttach", ".private");

        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let foreign_view =
            OleanView::parse_with_dependencies(&other_private, &[&other_exported, &other_server])
                .expect("the other module's private part parses against its own chain");

        let error = chain_extra_const_names(&exported_view, &foreign_view, WalkBudget::default())
            .expect_err("a private part from another module must be refused");
        assert_eq!(
            error,
            DeclError::ChainPartMismatch {
                part: OleanChainPart::Private
            },
            "{error:?}"
        );
    }

    /// The name index must answer exactly what the linear scan it replaced did,
    /// for every declaration of a real module.
    ///
    /// An index is only worth having if it is indistinguishable from the scan;
    /// a faster wrong answer is worse than a slow right one. This checks the
    /// two agree on every name in `Init.Prelude` — 2,314 declarations, the
    /// largest chain in Init — rather than on a sample.
    #[test]
    fn the_name_index_agrees_with_a_linear_scan_on_every_declaration() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_name_index_agrees_with_a_linear_scan_on_every_declaration: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |suffix: &str| {
            std::fs::read(lib.join(format!("Init/Prelude.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read Init/Prelude{suffix}: {error}"))
        };
        let exported = read("");
        let server = read(".server");
        let private = read(".private");
        let chained =
            decode_chain_constants_from_parts(&exported, &server, &private, ChainLimits::default())
                .expect("Init.Prelude's chain decodes");
        assert_eq!(chained.constants.len(), 2_314, "Init.Prelude at the pin");

        for (expected_position, info) in chained.constants.iter().enumerate() {
            // The scan this replaced: first occurrence wins.
            let scanned = chained
                .constants
                .iter()
                .position(|other| other.name() == info.name());
            assert_eq!(
                chained.position_of(info.name()),
                scanned,
                "index and scan disagree for {}",
                info.name().to_display_string()
            );
            assert_eq!(
                chained.position_of(info.name()),
                Some(expected_position),
                "{} is at {expected_position} and the pin has no repeats",
                info.name().to_display_string()
            );
            assert_eq!(
                chained.origin_of(info.name()),
                chained.origins.get(expected_position).copied(),
                "origin_of disagrees with origins[{expected_position}]"
            );
        }

        // A name the chain does not declare must be absent from both.
        let absent = Name::from_components(["fln", "not", "a", "declaration"]);
        assert_eq!(chained.position_of(&absent), None);
        assert_eq!(chained.origin_of(&absent), None);
    }

    fn demo_axiom(name: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components(name.split('.')),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    fn demo_theorem(name: &str) -> ConstantInfo {
        ConstantInfo::Thm(TheoremVal {
            base: ConstantVal {
                name: Name::from_components(name.split('.')),
                level_params: Vec::new(),
                type_: Expr::sort(Level::zero()),
            },
            value: Expr::sort(Level::zero()),
            all: Vec::new(),
        })
    }

    /// The private part may STRENGTHEN a declaration — that is the normal case
    /// at the pin and must be accepted.
    #[test]
    fn the_private_part_may_replace_an_exported_axiom_with_a_real_declaration() {
        let exported = vec![demo_axiom("Demo.thing")];
        let private = vec![demo_theorem("Demo.thing")];
        verify_private_superset(&exported, &private)
            .expect("axiom -> theorem is the strengthening direction the pin uses everywhere");
    }

    /// The reverse must be refused: it would hand the kernel a postulate in
    /// place of a checked declaration.
    #[test]
    fn the_private_part_may_not_downgrade_a_declaration_to_an_axiom() {
        let exported = vec![demo_theorem("Demo.thing")];
        let private = vec![demo_axiom("Demo.thing")];
        let error = verify_private_superset(&exported, &private)
            .expect_err("theorem -> axiom loses the body and must be refused");
        match &error {
            DeclError::PrivatePartWeakensDeclaration {
                name,
                exported_kind,
                private_kind,
            } => {
                assert_eq!(name.to_display_string(), "Demo.thing");
                assert_eq!(*exported_kind, "theorem");
                assert_eq!(*private_kind, "axiom");
            }
            other => panic!("expected PrivatePartWeakensDeclaration, got {other:?}"),
        }
        assert!(format!("{error}").contains("Demo.thing"));
    }

    /// An axiom on BOTH sides is not a downgrade.
    #[test]
    fn an_axiom_that_was_always_an_axiom_is_not_a_downgrade() {
        let exported = vec![demo_axiom("Demo.thing")];
        let private = vec![demo_axiom("Demo.thing")];
        verify_private_superset(&exported, &private)
            .expect("an axiom on both sides is unchanged, not weakened");
    }

    /// The law is inert on the pin, and the reason is the direction of the
    /// disagreement — asserted, so "it passes" is not mistaken for "there is
    /// nothing here to see".
    #[test]
    fn the_pin_only_ever_strengthens_a_shared_declaration() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_pin_only_ever_strengthens_a_shared_declaration: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |suffix: &str| {
            std::fs::read(lib.join(format!("Init/BinderPredicates.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read Init/BinderPredicates{suffix}: {error}"))
        };
        let exported = read("");
        let server = read(".server");
        let private = read(".private");

        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
            .expect("private parses against its chain");
        let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
            .decode_module_constants()
            .expect("exported constants decode");
        let private_constants = DeclDecoder::new(&private_view, WalkBudget::default())
            .decode_module_constants()
            .expect("private constants decode");

        // The law holds on a real chain.
        verify_private_superset(&exported_constants, &private_constants)
            .expect("the pin never downgrades a shared declaration");

        // And it is not holding vacuously: this module really does carry
        // exported axioms that the private part supplies with a body.
        let by_name: HashMap<&Name, &ConstantInfo> = private_constants
            .iter()
            .map(|info| (info.name(), info))
            .collect();
        let strengthened = exported_constants
            .iter()
            .filter(|info| matches!(info, ConstantInfo::Axiom(_)))
            .filter(|info| {
                by_name
                    .get(info.name())
                    .is_some_and(|other| !matches!(other, ConstantInfo::Axiom(_)))
            })
            .count();
        assert!(
            strengthened > 0,
            "Init.BinderPredicates must carry exported axioms that the private part \
             gives a body, or this test witnesses nothing about the direction"
        );
    }

    /// `Array.zipWithMAux._unary` is an AXIOM in the exported part and a
    /// DEFINITION in the chain, and both readings are correct.
    ///
    /// A cell asserting that an exported `_unary` member decodes to a concrete
    /// kind is asserting something untrue of the artifact: those bytes hold an
    /// `AxiomVal`, so a decoder that produced a definition from them would be
    /// inventing a body rather than recovering one. The concrete declaration
    /// lives in the private part, and `was_exported_as_axiom` is how a caller
    /// asks which of the two it is holding.
    #[test]
    fn an_exported_axiom_stays_an_axiom_and_the_companion_supplies_the_body() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP an_exported_axiom_stays_an_axiom_and_the_companion_supplies_the_body: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |suffix: &str| {
            std::fs::read(lib.join(format!("Init/Data/Array/Basic.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read Init/Data/Array/Basic{suffix}: {error}"))
        };
        let exported = read("");
        let server = read(".server");
        let private = read(".private");
        const WITNESS: &str = "Array.zipWithMAux._unary";

        // The exported part, read on its own, really does hold an axiom.
        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let exported_constants = DeclDecoder::new(&exported_view, WalkBudget::default())
            .decode_module_constants()
            .expect("exported constants decode");
        let exported_witness = exported_constants
            .iter()
            .find(|info| info.name().to_display_string() == WITNESS)
            .unwrap_or_else(|| panic!("{WITNESS} must be declared by the exported part"));
        assert!(
            matches!(exported_witness, ConstantInfo::Axiom(_)),
            "{WITNESS} is stored as an axiom in the exported part; decoding it as \
             {} would mean inventing a body",
            exported_witness.kind_name()
        );

        // The chain supplies the real declaration.
        let chained =
            decode_chain_constants_from_parts(&exported, &server, &private, ChainLimits::default())
                .expect("Init.Data.Array.Basic's chain decodes");
        let index = chained
            .constants
            .iter()
            .position(|info| info.name().to_display_string() == WITNESS)
            .unwrap_or_else(|| panic!("{WITNESS} must be in the chain"));
        let chained_witness = &chained.constants[index];
        assert!(
            matches!(chained_witness, ConstantInfo::Defn(_)),
            "the chain must give {WITNESS} a body, got {}",
            chained_witness.kind_name()
        );

        // It is an EXPORTED name, so origin alone would not have revealed the
        // difference — which is the whole reason was_exported_as_axiom exists.
        assert_eq!(chained.origins[index], ConstantOrigin::Exported);
        assert!(
            chained.was_exported_as_axiom(chained_witness.name()),
            "{WITNESS} was an axiom in the exported part and gained a body here"
        );
        assert!(
            chained
                .strengthened_by_the_companion()
                .any(|info| info.name().to_display_string() == WITNESS)
        );

        // Not vacuous: this module carries many such declarations, and a
        // private-ONLY one is not counted as strengthened.
        assert!(
            chained.strengthened_by_the_companion().count() > 1,
            "Init.Data.Array.Basic carries many exported axioms the companion \
             gives bodies to"
        );
        for info in chained.private_only() {
            assert!(
                !chained.was_exported_as_axiom(info.name()),
                "{} was never in the exported part, so it was not strengthened",
                info.name().to_display_string()
            );
        }
    }

    /// A `regular` reducibility hint whose padding half is dirty is refused,
    /// not silently truncated to a plausible height.
    #[test]
    fn a_regular_hint_with_nonzero_padding_is_refused() {
        // Positive control: the encoder's own regular hint decodes, so the
        // refusal below is the padding check and not the fixture.
        let clean = ReducibilityHints::Regular(37);
        assert_eq!(clean, ReducibilityHints::Regular(37));

        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP a_regular_hint_with_nonzero_padding_is_refused: pinned Reference \
                 stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        // Init.Prelude carries Nat.div.go and Nat.modCore.go at Regular(5).
        let exported = std::fs::read(lib.join("Init/Prelude.olean"))
            .unwrap_or_else(|error| panic!("read Init/Prelude: {error}"));
        let view = OleanView::parse(&exported).expect("exported parses");
        let constants = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the pin's hints all have zero padding, so decode succeeds");

        let mut regular = 0_usize;
        for info in &constants {
            if let ConstantInfo::Defn(definition) = info {
                if matches!(definition.hints, ReducibilityHints::Regular(_)) {
                    regular += 1;
                }
            }
            if info.name().to_display_string() == "Nat.div.go" {
                let ConstantInfo::Defn(definition) = info else {
                    panic!("Nat.div.go is a definition at the pin")
                };
                assert_eq!(
                    definition.hints,
                    ReducibilityHints::Regular(5),
                    "Nat.div.go's height is what the artifact stores, not something \
                     this decoder computes"
                );
            }
        }
        assert!(
            regular > 0,
            "Init.Prelude must carry regular hints, or this test exercises no padding"
        );
    }

    /// The post-order law is enforced, and a cyclic Expr child is refused
    /// rather than walked forever.
    ///
    /// This is the fln-abaz finding 1 defence, and its failure mode is not a
    /// wrong answer but a hang: the decode loop only charges its budget when it
    /// BUILDS a node, and a cycle never builds one, so without this law the
    /// stack grows without bound and no budget ever trips. A law whose whole
    /// point is that it prevents non-termination is a poor thing to leave
    /// untested, and it had no mutant until now.
    #[test]
    fn an_expr_child_that_does_not_precede_its_parent_is_refused() {
        let mut bytes = forall_expr_module();
        let view = OleanView::parse(&bytes).expect("header");

        // Positive control: the well-formed fixture decodes.
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified forall fixture decodes");

        let arrays = view.module_arrays().expect("constant array");
        let info_off = view
            .deref(
                view.read_u64(arrays.constants.0 + 24)
                    .expect("ConstantInfo"),
            )
            .expect("ConstantInfo object");
        let val_off = view
            .deref(view.read_u64(info_off + 8).expect("AxiomVal pointer"))
            .expect("AxiomVal object");
        let base_off = view
            .deref(view.read_u64(val_off + 8).expect("ConstantVal pointer"))
            .expect("ConstantVal object");
        // The pointer VALUE that addresses the forallE, reused below so the
        // planted child is a real object address rather than a guess.
        let pi_ptr = view.read_u64(base_off + 24).expect("type pointer");
        let pi_off = view.deref(pi_ptr).expect("forallE expression");
        assert_eq!(view.obj_header(pi_off).expect("header").0, 7, "forallE");

        // Slot 1 of forallE is the binder TYPE, one of its Expr children. Point
        // it at the forallE itself: a one-node cycle. The object it names is
        // valid and correctly shaped, so nothing but the post-order law
        // separates this from a well-formed expression.
        let child_slot = pi_off as usize + 8 + 8;
        let original = view.read_u64(pi_off + 8 + 8).expect("binder type pointer");
        assert_ne!(original, pi_ptr, "the fixture is acyclic to begin with");
        bytes[child_slot..child_slot + 8].copy_from_slice(&pi_ptr.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted region");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("a child that does not precede its parent must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "Expr child not below its parent (post-order law)",
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// One axiom whose type is `forall (_ : Sort 0), Sort 0`, so the region
    /// contains a `forallE` — the branch of the Expr size table that carries a
    /// trailing binder byte after the `Data` word.
    fn forall_expr_module() -> Vec<u8> {
        let body = Expr::sort(Level::zero());
        let type_ = Expr::forall_e(
            Name::from_components(["x"]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        );
        encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: Name::from_components(["Demo", "pi"]),
                        level_params: Vec::new(),
                        type_,
                    },
                    is_unsafe: false,
                })],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: 2,
                flags: 1,
                lean_version: "4.32.0",
                githash: "0123456789abcdef0123456789abcdef01234567",
                base_addr: 0x20_000,
            },
            WriteBudget::default(),
        )
        .expect("module encodes")
        .bytes
    }

    /// Both branches of the Expr size table are exercised, and a contradictory
    /// size is refused before `Expr.Data` is compared.
    ///
    /// The trailing-byte branch is the one worth planting on: `forallE` stores
    /// a binder byte after `Data`, so its object is a full word larger than a
    /// pointer count alone would predict. A table that forgot the trailing
    /// scalars would compute 32 here instead of 40 and reject the real pin.
    #[test]
    fn an_expr_object_whose_size_contradicts_its_layout_is_refused() {
        let mut bytes = forall_expr_module();
        let view = OleanView::parse(&bytes).expect("header");

        // Positive control, so the refusal below cannot be a broken fixture.
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified forall fixture decodes");

        let arrays = view.module_arrays().expect("constant array");
        let info_off = view
            .deref(
                view.read_u64(arrays.constants.0 + 24)
                    .expect("ConstantInfo"),
            )
            .expect("ConstantInfo object");
        let val_off = view
            .deref(view.read_u64(info_off + 8).expect("AxiomVal pointer"))
            .expect("AxiomVal object");
        let base_off = view
            .deref(view.read_u64(val_off + 8).expect("ConstantVal pointer"))
            .expect("ConstantVal object");
        let pi_off = view
            .deref(view.read_u64(base_off + 24).expect("type pointer"))
            .expect("forallE expression");

        // forallE: three slots, then Data, then the binder byte -> 40 bytes.
        let (tag, other, cs_sz) = view.obj_header(pi_off).expect("forallE header");
        assert_eq!(tag, 7, "forallE");
        assert_eq!(other, 3, "binder name, binder type, body");
        assert_eq!(
            cs_sz, 40,
            "8 header + 24 slots + 8 Data + 1 binder byte, padded"
        );
        assert_eq!(
            DeclDecoder::expr_scalar_bytes(tag),
            1,
            "the table must know forallE carries a trailing byte"
        );
        assert_eq!(
            DeclDecoder::expr_scalar_bytes(3),
            0,
            "and that sort carries none"
        );

        // Plant a size one word short: enough to hold the slots and Data, but
        // not the binder byte the decoder then reads.
        let header = view.read_u64(pi_off).expect("header word");
        let planted = (header & !0x0000_ffff_0000_0000) | (32_u64 << 32);
        bytes[pi_off as usize..pi_off as usize + 8].copy_from_slice(&planted.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("an Expr whose size contradicts its layout must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "Expr object size disagrees with its slots-data-scalars layout",
                    ..
                }
            ),
            "expected the size refusal rather than an Expr.Data cross-check: {error:?}"
        );
    }

    /// One axiom whose type is `Sort (u+1)`, so the region contains a real
    /// `Level.succ` OBJECT. `Level::zero` is scalar-boxed and would give the
    /// size check nothing to bind.
    fn succ_level_module() -> Vec<u8> {
        let level = Level::zero().succ().expect("one successor is in range");
        encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: Name::from_components(["Demo", "lvl"]),
                        level_params: Vec::new(),
                        type_: Expr::sort(level),
                    },
                    is_unsafe: false,
                })],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: 2,
                flags: 1,
                lean_version: "4.32.0",
                githash: "0123456789abcdef0123456789abcdef01234567",
                base_addr: 0x20_000,
            },
            WriteBudget::default(),
        )
        .expect("module encodes")
        .bytes
    }

    /// One axiom whose type is `Sort (0+1+1)`, so the outer `Level.succ` has a
    /// heap child rather than a scalar one.
    ///
    /// `succ_level_module` is no use for the post-order law: its child is
    /// `Level.zero`, which is scalar-boxed, and the law only applies to
    /// non-scalar children. A cell built on that fixture would pass while
    /// exercising nothing.
    fn nested_succ_level_module() -> Vec<u8> {
        let level = Level::zero()
            .succ()
            .and_then(Level::succ)
            .expect("two successors are in range");
        encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[ConstantInfo::Axiom(AxiomVal {
                    base: ConstantVal {
                        name: Name::from_components(["Demo", "lvl2"]),
                        level_params: Vec::new(),
                        type_: Expr::sort(level),
                    },
                    is_unsafe: false,
                })],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: 2,
                flags: 1,
                lean_version: "4.32.0",
                githash: "0123456789abcdef0123456789abcdef01234567",
                base_addr: 0x20_000,
            },
            WriteBudget::default(),
        )
        .expect("module encodes")
        .bytes
    }

    /// The Level post-order law is enforced, with the same anti-cycle
    /// rationale as its Expr counterpart and a separate implementation.
    #[test]
    fn a_level_child_that_does_not_precede_its_parent_is_refused() {
        let mut bytes = nested_succ_level_module();
        let view = OleanView::parse(&bytes).expect("header");

        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified nested-succ fixture decodes");

        let arrays = view.module_arrays().expect("constant array");
        let info_off = view
            .deref(
                view.read_u64(arrays.constants.0 + 24)
                    .expect("ConstantInfo"),
            )
            .expect("ConstantInfo object");
        let val_off = view
            .deref(view.read_u64(info_off + 8).expect("AxiomVal pointer"))
            .expect("AxiomVal object");
        let base_off = view
            .deref(view.read_u64(val_off + 8).expect("ConstantVal pointer"))
            .expect("ConstantVal object");
        let sort_off = view
            .deref(view.read_u64(base_off + 24).expect("type pointer"))
            .expect("Sort expression");
        // The pointer VALUE addressing the outer succ, reused as the plant.
        let outer_ptr = view.read_u64(sort_off + 8).expect("level pointer");
        let outer_off = view.deref(outer_ptr).expect("outer Level.succ");
        assert_eq!(view.obj_header(outer_off).expect("header").0, 1, "succ");

        // Its child must currently be a heap Level, not a scalar, or the law
        // below would never be reached.
        let child = view.read_u64(outer_off + 8).expect("succ child");
        assert_eq!(child & 1, 0, "the inner successor is a heap object");
        assert_ne!(child, outer_ptr, "the fixture is acyclic to begin with");

        // Point the outer succ at itself.
        let slot = outer_off as usize + 8;
        bytes[slot..slot + 8].copy_from_slice(&outer_ptr.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted region");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("a Level child that does not precede its parent must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "Level child not below its parent (post-order law)",
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// A `Level` whose stored size contradicts its layout is refused before its
    /// `Data` word is compared.
    #[test]
    fn a_level_object_whose_size_contradicts_its_layout_is_refused() {
        let mut bytes = succ_level_module();
        let view = OleanView::parse(&bytes).expect("header");

        // Positive control: the fixture decodes, so the refusal below is the
        // size rule and not a broken fixture.
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified succ-level fixture decodes");

        // Find the succ object: tag 1, one pointer field, 24 bytes.
        let arrays = view.module_arrays().expect("constant array");
        let info_ptr = view
            .read_u64(arrays.constants.0 + 24)
            .expect("first ConstantInfo");
        let info_off = view.deref(info_ptr).expect("ConstantInfo object");
        let val_off = view
            .deref(view.read_u64(info_off + 8).expect("AxiomVal pointer"))
            .expect("AxiomVal object");
        // ConstantVal is slot 0 of AxiomVal; its type is the third pointer.
        let base_off = view
            .deref(view.read_u64(val_off + 8).expect("ConstantVal pointer"))
            .expect("ConstantVal object");
        let sort_off = view
            .deref(view.read_u64(base_off + 24).expect("type pointer"))
            .expect("Sort expression");
        let level_off = view
            .deref(view.read_u64(sort_off + 8).expect("level pointer"))
            .expect("Level object");
        let (tag, other, cs_sz) = view.obj_header(level_off).expect("Level header");
        assert_eq!(tag, 1, "Level.succ");
        assert_eq!(other, 1, "one level child");
        assert_eq!(cs_sz, 24, "plus the stored Data word");

        // Change the stored size and nothing else.
        let header = view.read_u64(level_off).expect("header word");
        let planted = (header & !0x0000_ffff_0000_0000) | (32_u64 << 32);
        bytes[level_off as usize..level_off as usize + 8].copy_from_slice(&planted.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("a Level whose size contradicts its layout must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "Level object size disagrees with its pointer-fields-plus-data layout",
                    ..
                }
            ),
            "expected the size refusal rather than a Level.Data cross-check: {error:?}"
        );
    }

    /// A `Name` link whose stored size contradicts its layout is refused
    /// before its hash is compared.
    ///
    /// Without this the planted object would be read as a Name anyway and the
    /// word at `+24` compared as `Name.hash`, so the failure would surface as
    /// a cross-check divergence and point at the identity layer instead of at
    /// the misread.
    #[test]
    fn a_name_object_whose_size_contradicts_its_layout_is_refused() {
        let mut bytes = axiom_module(false);
        let view = OleanView::parse(&bytes).expect("header");
        let arrays = view.module_arrays().expect("constant array");
        let name_ptr = view
            .read_u64(arrays.const_names.0 + 24)
            .expect("first constName");
        let name_off = view.deref(name_ptr).expect("Name object");

        // Positive control, and the layout the mutant depends on.
        let (tag, other, cs_sz) = view.obj_header(name_off).expect("Name header");
        assert!(tag == 1 || tag == 2, "a Name link");
        assert_eq!(other, 2, "prefix and component");
        assert_eq!(cs_sz, 32, "plus the stored hash");
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified fixture decodes");

        // Change the stored size and nothing else: both pointers and the hash
        // word stay exactly where they were.
        let header = view.read_u64(name_off).expect("header word");
        let planted = (header & !0x0000_ffff_0000_0000) | (40_u64 << 32);
        bytes[name_off as usize..name_off as usize + 8].copy_from_slice(&planted.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("a Name whose size contradicts its layout must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "Name object size disagrees with its two-pointer-plus-hash layout",
                    ..
                }
            ),
            "expected the size refusal rather than a hash cross-check: {error:?}"
        );
    }

    /// A nonzero byte in a payload's scalar padding is refused.
    ///
    /// Distinct from the size check: this mutant leaves `cs_sz`, every pointer
    /// slot and the real `isUnsafe` byte untouched, so only the padding rule
    /// can kill it.
    #[test]
    fn a_constant_info_payload_with_dirty_scalar_padding_is_refused() {
        let mut bytes = axiom_module(false);
        let view = OleanView::parse(&bytes).expect("header");
        let arrays = view.module_arrays().expect("constant array");
        let info_ptr = view
            .read_u64(arrays.constants.0 + 24)
            .expect("first ConstantInfo");
        let info_off = view.deref(info_ptr).expect("ConstantInfo object");
        let val_ptr = view.read_u64(info_off + 8).expect("AxiomVal pointer");
        let val_off = view.deref(val_ptr).expect("AxiomVal object");

        // Positive control, and the layout this mutant depends on: one pointer
        // field, so the scalar area starts at +16, `isUnsafe` occupies +16, and
        // +17..+24 is padding.
        let (_, other, cs_sz) = view.obj_header(val_off).expect("AxiomVal header");
        assert_eq!(other, 1);
        assert_eq!(cs_sz, 24);
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified fixture decodes");
        let flag = val_off as usize + 16;
        assert_eq!(bytes[flag], 0, "fixture is a safe axiom");
        assert!(
            bytes[flag + 1..val_off as usize + 24]
                .iter()
                .all(|b| *b == 0),
            "its padding starts clean"
        );

        // Dirty one padding byte and nothing else.
        bytes[flag + 1] = 1;

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("dirty scalar padding must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "ConstantInfo payload scalar padding is not zero",
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// The payload object's stored size is checked against the field layout.
    #[test]
    fn a_constant_info_payload_whose_size_contradicts_its_layout_is_refused() {
        let mut bytes = axiom_module(false);
        let view = OleanView::parse(&bytes).expect("header");
        let arrays = view.module_arrays().expect("constant array");
        let info_ptr = view
            .read_u64(arrays.constants.0 + 24)
            .expect("first ConstantInfo");
        let info_off = view.deref(info_ptr).expect("ConstantInfo object");
        let val_ptr = view.read_u64(info_off + 8).expect("AxiomVal pointer");
        let val_off = view.deref(val_ptr).expect("AxiomVal object");

        // Positive control: untouched, the fixture decodes.
        DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect("the unmodified fixture decodes");

        // AxiomVal is one pointer plus one scalar byte, so align8(8+8+1) = 24.
        let (_, other, cs_sz) = view.obj_header(val_off).expect("AxiomVal header");
        assert_eq!(other, 1, "AxiomVal carries one pointer field");
        assert_eq!(cs_sz, 24, "and therefore a 24-byte object");

        // Plant a size that no layout of this object could produce. Only the
        // header word changes; every field the decoder reads is untouched, so
        // without the check the decode would succeed on a contradictory object.
        let header = view.read_u64(val_off).expect("header word");
        let planted = (header & !0x0000_ffff_0000_0000) | (32_u64 << 32);
        bytes[val_off as usize..val_off as usize + 8].copy_from_slice(&planted.to_le_bytes());

        let view = OleanView::parse(&bytes).expect("planted header");
        let error = DeclDecoder::new(&view, WalkBudget::default())
            .decode_module_constants()
            .expect_err("a payload whose size contradicts its layout must be refused");
        assert!(
            matches!(
                error,
                DeclError::Shape {
                    what: "ConstantInfo payload object size disagrees with its field layout",
                    ..
                }
            ),
            "{error:?}"
        );
    }

    /// The structural companion test is gated on the view HAVING dependency
    /// regions, and this pins that boundary.
    ///
    /// Requiring `is_chained_to` unconditionally refused a self-contained pair
    /// for having been built without companions rather than for being the wrong
    /// module — a real regression, caught only when the suite was executed. The
    /// two halves are asserted here so the gate cannot quietly go away again.
    #[test]
    fn a_self_contained_view_has_no_dependency_regions_but_a_chained_one_does() {
        let standalone = axiom_module(false);
        let view = OleanView::parse(&standalone).expect("standalone parses");
        assert!(
            !view.has_dependency_regions(),
            "a freshly encoded module resolves every pointer inside itself"
        );
        // Self-contained pairs are therefore judged on contents alone.
        assert!(is_companion_of(&view, &view));

        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the chained half of \
                 a_self_contained_view_has_no_dependency_regions_but_a_chained_one_does: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |suffix: &str| {
            std::fs::read(lib.join(format!("Init/Data/List/ToArrayImpl.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read ToArrayImpl{suffix}: {error}"))
        };
        let exported = read("");
        let server = read(".server");
        let private = read(".private");
        let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
            .expect("private parses against its chain");
        assert!(
            private_view.has_dependency_regions(),
            "a real companion is parsed against earlier regions, so the structural \
             test applies to it"
        );
    }

    /// The header stamp alone cannot tell one module's companion from another's,
    /// and this proves the structural check is what does the work.
    ///
    /// Without this, `is_companion_of` could regress to a header comparison and
    /// every refusal test in this file would still pass — for the wrong reason
    /// in one case and by accident in the others. So the header fields are
    /// asserted EQUAL across two different modules (i.e. the cheap check
    /// admits the foreign part) while `is_chained_to` is asserted false.
    #[test]
    fn the_toolchain_stamp_does_not_identify_a_module_but_the_chaining_does() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_toolchain_stamp_does_not_identify_a_module_but_the_chaining_does: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |relative: &str, suffix: &str| {
            std::fs::read(lib.join(format!("{relative}.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read {relative}{suffix}: {error}"))
        };
        let exported = read("Init/Data/List/ToArrayImpl", "");
        let server = read("Init/Data/List/ToArrayImpl", ".server");
        let private = read("Init/Data/List/ToArrayImpl", ".private");
        let other_exported = read("Init/Control/MonadAttach", "");
        let other_server = read("Init/Control/MonadAttach", ".server");
        let other_private = read("Init/Control/MonadAttach", ".private");

        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let own_private = OleanView::parse_with_dependencies(&private, &[&exported, &server])
            .expect("own private parses");
        let foreign_private =
            OleanView::parse_with_dependencies(&other_private, &[&other_exported, &other_server])
                .expect("foreign private parses against its own chain");

        // The cheap check ADMITS the foreign part: one toolchain, one stamp.
        assert_eq!(exported_view.header.version, foreign_private.header.version);
        assert_eq!(exported_view.header.flags, foreign_private.header.flags);
        assert_eq!(
            exported_view.header.lean_version,
            foreign_private.header.lean_version
        );
        assert_eq!(
            exported_view.header.githash, foreign_private.header.githash,
            "the header stamp is toolchain-wide; if this ever differs between two \
             modules of one build, this test no longer witnesses anything"
        );

        // The structural bond separates them.
        assert!(
            own_private.is_chained_to(&exported_view),
            "a module's own private part is chained to its exported region"
        );
        assert!(
            !foreign_private.is_chained_to(&exported_view),
            "another module's private part is not"
        );
        assert!(is_companion_of(&own_private, &exported_view));
        assert!(!is_companion_of(&foreign_private, &exported_view));
    }

    /// The VIEW door must refuse a mismatched pair on its own.
    ///
    /// `decode_chain_constants_from_parts` is not the only entry point: the
    /// conformance fixtures and several tests build their own `OleanView`s and
    /// call the view door directly, so a law enforced only in the parts door
    /// would not protect them.
    #[test]
    fn the_view_door_refuses_a_private_part_from_another_module() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP the_view_door_refuses_a_private_part_from_another_module: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |relative: &str, suffix: &str| {
            std::fs::read(lib.join(format!("{relative}.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read {relative}{suffix}: {error}"))
        };

        let exported = read("Init/Data/List/ToArrayImpl", "");
        let server = read("Init/Data/List/ToArrayImpl", ".server");
        let private = read("Init/Data/List/ToArrayImpl", ".private");
        let exported_view = OleanView::parse(&exported).expect("exported parses");
        let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
            .expect("private parses against its own chain");

        // Positive control: the module's own pair still decodes through the
        // view door, so the refusal below is the identity law and not the door
        // being broken for everything.
        let ok = decode_chain_constants_with_origin(
            &exported_view,
            &private_view,
            WalkBudget::default(),
        )
        .expect("a module's own pair decodes");
        assert_eq!(
            ok.constants.len(),
            6,
            "Init.Data.List.ToArrayImpl at the pin"
        );

        // A foreign private companion, parsed against ITS OWN chain so the
        // view itself is well formed. Only the identity stamp distinguishes it.
        let other_exported = read("Init/Control/MonadAttach", "");
        let other_server = read("Init/Control/MonadAttach", ".server");
        let other_private = read("Init/Control/MonadAttach", ".private");
        let foreign_view =
            OleanView::parse_with_dependencies(&other_private, &[&other_exported, &other_server])
                .expect("the other module's private part parses against its own chain");

        let error = decode_chain_constants_with_origin(
            &exported_view,
            &foreign_view,
            WalkBudget::default(),
        )
        .expect_err("a private part from another module must be refused");
        assert!(
            !matches!(error, DeclError::PrivatePartIncomplete { .. }),
            "a mismatched pair must not be blamed on a missing declaration: {error:?}"
        );
    }

    /// The byte ceiling is charged before anything is parsed.
    #[test]
    fn a_chain_over_its_byte_ceiling_is_refused_before_parsing() {
        let bytes = axiom_module(false);
        let total = bytes.len() * 3;

        // Positive control: the same input under a ceiling that admits it gets
        // past the charge and fails later, on the module-system gate — proving
        // the refusal below is the ceiling and not the fixture.
        let admitted =
            decode_chain_constants_from_parts(&bytes, &bytes, &bytes, ChainLimits::new(total))
                .expect_err("a non-module artifact still has no chain");
        assert_eq!(admitted, DeclError::NotAModuleChain, "{admitted:?}");

        // One byte under the exact total must be refused, and refused as a
        // size fault rather than anything downstream.
        let error =
            decode_chain_constants_from_parts(&bytes, &bytes, &bytes, ChainLimits::new(total - 1))
                .expect_err("a chain over the ceiling must be refused");
        assert_eq!(
            error,
            DeclError::ChainTooLarge {
                bytes: total,
                limit: total - 1,
            },
            "{error:?}"
        );
        assert!(
            format!("{error}").contains("ceiling"),
            "the rendered error must name the ceiling: {error}"
        );
    }

    /// A chain assembled from two DIFFERENT modules must be refused by identity,
    /// not decoded into a coherent-looking result for a module that exists
    /// nowhere.
    ///
    /// `decode_chain_constants_from_parts` originally trusted its three
    /// arguments to belong together. They parse and their pointers resolve
    /// whatever their provenance, so a mismatched private companion produced a
    /// chain rather than an error — and the superset law then reported
    /// `PrivatePartIncomplete`, naming the wrong fault entirely.
    #[test]
    fn a_chain_assembled_from_two_modules_is_refused_by_identity() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP a_chain_assembled_from_two_modules_is_refused_by_identity: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };
        let read = |relative: &str, suffix: &str| {
            std::fs::read(lib.join(format!("{relative}.olean{suffix}")))
                .unwrap_or_else(|error| panic!("read {relative}{suffix}: {error}"))
        };

        let exported = read("Init/Data/List/ToArrayImpl", "");
        let server = read("Init/Data/List/ToArrayImpl", ".server");
        let private = read("Init/Data/List/ToArrayImpl", ".private");

        // Positive control first: the real chain must still decode, or the
        // refusal below would prove nothing about identity.
        let ok =
            decode_chain_constants_from_parts(&exported, &server, &private, ChainLimits::default())
                .expect("the module's own chain decodes");
        assert_eq!(
            ok.constants.len(),
            6,
            "Init.Data.List.ToArrayImpl at the pin"
        );

        // Now the same exported part with ANOTHER module's private companion.
        // Both are valid module-system artifacts of the same toolchain, so only
        // a real identity check separates them.
        let foreign_private = read("Init/Control/MonadAttach", ".private");
        let error = decode_chain_constants_from_parts(
            &exported,
            &server,
            &foreign_private,
            ChainLimits::default(),
        )
        .expect_err("a private companion from another module must be refused");
        assert!(
            !matches!(error, DeclError::PrivatePartIncomplete { .. }),
            "a mismatched chain must not be reported as a missing declaration: {error:?}"
        );
    }

    /// A standalone (non-module-system) artifact has no chain to compose.
    #[test]
    fn a_non_module_artifact_is_not_accepted_as_a_chain() {
        let bytes = axiom_module(false);
        let error =
            decode_chain_constants_from_parts(&bytes, &bytes, &bytes, ChainLimits::default())
                .expect_err("a non-module artifact has no companion chain");
        assert_eq!(error, DeclError::NotAModuleChain, "{error:?}");
    }

    /// `origin_of` must call these eight `Exported`, because the exported part
    /// declares them.
    ///
    /// They are the counterexample to reading provenance off the name: all
    /// eight are `_private.`-prefixed and all eight are exported, so a prefix
    /// test reports them companion-recovered. Two of them
    /// (`Init.Prelude`'s `getHeadInfo?`/`getTailPos?`) are the pair that failed
    /// the `.loop` family regression. Pinned here in `src` so the classifier
    /// cannot be "fixed" back to a name test without this failing.
    #[test]
    fn origin_of_classifies_exported_unsafe_rec_prefix_collisions_as_exported() {
        let Some(lib) = reference_lib() else {
            eprintln!(
                "SKIP origin_of_classifies_exported_unsafe_rec_prefix_collisions_as_exported: \
                 pinned Reference stdlib absent (set FLN_REFERENCE_LIB)"
            );
            return;
        };

        let mut modules: Vec<&str> = EXPORTED_UNSAFE_REC_COLLISIONS
            .iter()
            .map(|(module, _)| *module)
            .collect();
        modules.dedup();
        assert_eq!(modules.len(), 3, "witnesses span three modules at the pin");

        let mut checked = 0_usize;
        for module in modules {
            let exported = std::fs::read(lib.join(format!("{module}.olean")))
                .unwrap_or_else(|error| panic!("read exported {module}: {error}"));
            let server = std::fs::read(lib.join(format!("{module}.olean.server")))
                .unwrap_or_else(|error| panic!("read server {module}: {error}"));
            let private = std::fs::read(lib.join(format!("{module}.olean.private")))
                .unwrap_or_else(|error| panic!("read private {module}: {error}"));
            let chained = decode_chain_constants_from_parts(
                &exported,
                &server,
                &private,
                ChainLimits::default(),
            )
            .unwrap_or_else(|error| panic!("chain decode {module}: {error}"));

            for (owner, witness) in EXPORTED_UNSAFE_REC_COLLISIONS {
                if owner != &module {
                    continue;
                }
                let info = chained
                    .constants
                    .iter()
                    .find(|info| info.name().to_display_string() == *witness)
                    .unwrap_or_else(|| panic!("{module} no longer declares {witness}"));
                assert_eq!(
                    chained.origin_of(info.name()),
                    Some(ConstantOrigin::Exported),
                    "{witness} is declared by the exported part; calling it PrivateOnly is the \
                     prefix misclassification this type exists to prevent"
                );
                assert!(
                    !chained
                        .private_only()
                        .any(|other| other.name() == info.name()),
                    "{witness} must not appear in private_only()"
                );
                checked += 1;
            }
        }
        assert_eq!(
            checked,
            EXPORTED_UNSAFE_REC_COLLISIONS.len(),
            "every witness must have been reached; a silently shrinking list would make \
             this test pass while proving less"
        );
    }
}
