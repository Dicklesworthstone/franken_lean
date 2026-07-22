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

use std::collections::HashMap;

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

    fn decode_bool(byte: u8) -> bool {
        byte != 0
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
            let mut pending = false;
            for i in 0..child_count {
                let child = self.view.read_u64(off + 8 + 8 * i)?;
                if !Self::is_scalar(child) {
                    let coff = self.view.deref(child)?;
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
                )))
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
            4 => {
                let p = self.view.read_u64(off + 8)?;
                if Self::is_scalar(p) {
                    // Int scalar boxing: signed value in the tagged word.
                    Ok(DataValue::OfInt((p as i64) >> 1))
                } else {
                    Err(DeclError::Unsupported {
                        offset: off,
                        what: "DataValue.ofInt mpz",
                    })
                }
            }
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
        let mut map = KVMap::new();
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
            map.insert(key, value);
        }
        Ok(map)
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
                let non_dep = Self::decode_bool(self.view.read_bytes_at(scalar_base + 8, 1)?[0]);
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
                    is_unsafe: Self::decode_bool(scalar_u8(self, 0)?),
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
                    is_unsafe: Self::decode_bool(scalar_u8(self, 0)?),
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
                    is_rec: Self::decode_bool(scalar_u8(self, 0)?),
                    is_unsafe: Self::decode_bool(scalar_u8(self, 1)?),
                    is_reflexive: Self::decode_bool(scalar_u8(self, 2)?),
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
                    is_unsafe: Self::decode_bool(scalar_u8(self, 0)?),
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
                    k: Self::decode_bool(scalar_u8(self, 0)?),
                    is_unsafe: Self::decode_bool(scalar_u8(self, 1)?),
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
