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
            let (tag, other, _) = self.view.obj_header(off)?;
            if !(tag == 1 || tag == 2) || other != 2 {
                return Err(DeclError::Shape {
                    offset: off,
                    what: "Name ctor",
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
            let (tag, other, _) = self.view.obj_header(off)?;
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
            let (tag, other, _) = self.view.obj_header(off)?;
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
        let (_vtag, vother, _) = self.view.obj_header(voff)?;
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
        self.constants
            .iter()
            .position(|info| info.name() == name)
            .and_then(|index| self.origins.get(index).copied())
    }
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
pub fn decode_chain_constants_from_parts(
    exported: &[u8],
    server: &[u8],
    private: &[u8],
    budget: WalkBudget,
) -> DResult<ChainConstants> {
    let exported_view = OleanView::parse(exported)?;
    let server_view = OleanView::parse_with_dependencies(server, &[exported])?;
    // Parsed to prove the middle region is well-formed in its own dependency
    // address space; its constants are not part of the authoritative array.
    let _ = &server_view;
    let private_view = OleanView::parse_with_dependencies(private, &[exported, server])?;
    decode_chain_constants_with_origin(&exported_view, &private_view, budget)
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

    Ok(ChainConstants {
        constants: private_constants,
        origins,
    })
}

/// Prove that `private` names every declaration `exported` names.
///
/// Split out from [`decode_chain_constants`] so a caller that has already
/// decoded both arrays — as the module-system decode path does, to validate the
/// exported part — can bind the containment law without decoding anything a
/// second time. See [`decode_chain_constants`] for why the law matters.
pub fn verify_private_superset(exported: &[ConstantInfo], private: &[ConstantInfo]) -> DResult<()> {
    let present: HashSet<&Name> = private.iter().map(ConstantInfo::name).collect();
    for info in exported {
        if !present.contains(info.name()) {
            return Err(DeclError::PrivatePartIncomplete {
                missing: info.name().clone(),
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
                WalkBudget::default(),
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
